#!/usr/bin/env bash
# pdmask — build/run/deploy helper
set -euo pipefail

NAME="pdmask"
IMAGE="pdmask:latest"
CONTAINER="pdmask"
PORT="${PORT:-8080}"
HOST_PORT="${HOST_PORT:-80}"

cd "$(dirname "$0")"

cmd="${1:-help}"

case "$cmd" in
  host)
    echo "==> host tuning (sysctl, ulimit, mmap, numa)"
    # --- сеть: очередь приёма, TIME_WAIT, буферы сокетов ---
    sudo sysctl -w net.core.somaxconn=4096 >/dev/null 2>&1 || true
    sudo sysctl -w net.ipv4.tcp_max_syn_backlog=4096 >/dev/null 2>&1 || true
    sudo sysctl -w net.ipv4.tcp_tw_reuse=1 >/dev/null 2>&1 || true
    sudo sysctl -w net.core.rmem_max=16777216 >/dev/null 2>&1 || true
    sudo sysctl -w net.core.wmem_max=16777216 >/dev/null 2>&1 || true
    # --- память: mmap-регионы и overcommit (OCaml GC + Eio) ---
    sudo sysctl -w vm.max_map_count=1048576 >/dev/null 2>&1 || true
    sudo sysctl -w vm.overcommit_memory=1 >/dev/null 2>&1 || true
    # --- файловые дескрипторы ---
    ulimit -n 65535 2>/dev/null || true
    # --- CPU: изоляция ядер и NUMA (требуют reboot/спец.железа, опционально) ---
    # isolcpus=0,1,2,3 в /etc/default/grub (GRUB_CMDLINE_LINUX) + update-grub + reboot
    # привязка процесса к ядрам: taskset -c 0-3 ./run.sh up
    # NUMA: numactl --cpunodebind=0 --membind=0 ./run.sh up
    echo "host: OK"
    echo "  совет: для максимальной производительности добавьте isolcpus=0,1,2,3"
    echo "  в GRUB_CMDLINE_LINUX и перезагрузитесь; запускайте с taskset -c 0-3"
    ;;

  build)
    echo "==> building image $IMAGE"
    docker build -t "$IMAGE" .
    echo "build: OK"
    ;;

  up)
    echo "==> starting container $CONTAINER on port $HOST_PORT"
    docker rm -f "$CONTAINER" >/dev/null 2>&1 || true
    # CPU pinning: CPUS="0-3" привязывает контейнер к ядрам (--cpuset-cpus).
    # NUMA: NUMA_NODE="0" привязывает к NUMA-узлу (--cpuset-mems).
    cpuset=""
    if [ -n "${CPUS:-}" ]; then cpuset="$cpuset --cpuset-cpus=$CPUS"; fi
    if [ -n "${NUMA_NODE:-}" ]; then cpuset="$cpuset --cpuset-mems=$NUMA_NODE"; fi
    # Дескрипторы. По умолчанию в контейнере 1024, и это упирается раньше
    # процессора: сервис ограничивает себя по живому лимиту и на 1024 держит
    # 896 соединений, остальные ждут в очереди сокета. Ядра при этом заняты
    # меньше чем наполовину.
    nofile="${NOFILE:-65536}"
    # shellcheck disable=SC2086
    docker run -d --name "$CONTAINER" --restart unless-stopped \
      -p "$HOST_PORT:$PORT" \
      -e PORT="$PORT" \
      --ulimit "nofile=$nofile:$nofile" \
      $cpuset \
      "$IMAGE"
    echo "up: OK (http://localhost:$HOST_PORT)"
    echo "  pinning: ${cpuset:-не задано (CPUS=0-3 для привязки к ядрам)}"
    echo "  дескрипторов: $nofile (NOFILE=... чтобы изменить)"
    ;;

  down)
    echo "==> stopping container $CONTAINER"
    docker rm -f "$CONTAINER" >/dev/null 2>&1 || true
    echo "down: OK"
    ;;

  reload)
    echo "reload: конфиг и горячая перезагрузка — M6, см. раздел 12 спеки"
    ;;

  selfcheck)
    base="http://localhost:$HOST_PORT"
    fail=0
    # Каждый шаг сверяет и код, и содержимое, и на первом же расхождении
    # selfcheck выходит с ненулевым кодом. Раньше здесь печаталось OK
    # безусловно — в том числе когда на порту отвечал чужой сервер и все
    # шаги возвращали 404.
    body() { printf '%s' "${1%$'\n'*}"; }
    code() { printf '%s' "${1##*$'\n'}"; }
    unwrap() { printf '%s' "$1" | sed -n 's/^{"result":"\(.*\)"}$/\1/p'; }
    step() { # step <шаг> <название> <0|1> <подробности>
      d=$(printf '%s' "$4" | tr '\n\r\t' '   ' | cut -c1-96)
      if [ "$3" = 1 ]; then printf '[%s] %s  OK    %s\n' "$1" "$2" "$d"
      else printf '[%s] %s  СБОЙ  %s\n' "$1" "$2" "$d"; fail=1; fi
    }
    if [ "${2:-}" = "--envelope" ]; then
      echo "==> selfcheck envelope (mask -> unmask with OTP -> one-time -> exp)"
      orig='Иванов Иван Иванович, паспорт 4509 123456'
      hdr=$(mktemp)
      r=$(curl -s -D "$hdr" -w '\n%{http_code}' -X POST "$base/mask" \
        -H 'Content-Type: application/json' -H 'X-PDMask-System: demo' \
        -d "{\"payload\":\"$orig\"}")
      c=$(code "$r"); masked=$(unwrap "$(body "$r")")
      env=$(grep -i '^X-PDMask-Envelope:' "$hdr" | sed 's/^[^:]*: *//' | tr -d '\r')
      ok=1; [ "$c" = 200 ] && [ -n "$env" ] && [ -n "$masked" ] || ok=0
      case "$masked" in *Иванов*|*123456*) ok=0 ;; esac
      step 1/4 "/mask -> конверт  " "$ok" "$c конверт ${#env} Б, тело: $masked"

      # OTP по RFC 6238, HMAC-SHA256, 8 цифр
      mkotp() {
        python3 -c "
import hmac, hashlib, struct, time
secret = b'pdmask-dev-otp-secret-0000000000000000'
T = int(time.time()) // 30
mac = hmac.new(secret, struct.pack('>Q', T), hashlib.sha256).digest()
off = mac[-1] & 0x0F
code = ((mac[off] & 0x7F) << 24) | (mac[off+1] << 16) | (mac[off+2] << 8) | mac[off+3]
print(f'{code % 100000000:08d}')
"
      }
      # возвращаем ровно то, что отдал /mask, а не выдуманные имена токенов
      unm() { # unm [система], по умолчанию demo
        curl -s -w '\n%{http_code}' -X POST "$base/unmask" \
          -H 'Content-Type: application/json' -H "X-PDMask-System: ${1:-demo}" \
          -H "X-PDMask-Envelope: $env" -H "X-PDMask-OTP: $otp" \
          -d "{\"payload\":\"$masked\"}"
      }
      otp=$(mkotp)
      r=$(unm); c=$(code "$r")
      if [ "$c" = 401 ]; then
        # код этого 30-секундного окна уже израсходован (прошлым прогоном или
        # ручной проверкой) — ждём следующего окна и берём свежий. Конверт
        # живёт пять минут, так что ожидание в него укладывается.
        w=$(( 31 - $(date +%s) % 30 ))
        echo "      ... код текущего окна уже использован, жду ${w} с"
        sleep "$w"
        otp=$(mkotp)
        r=$(unm); c=$(code "$r")
      fi
      back=$(unwrap "$(body "$r")")
      ok=1; [ "$c" = 200 ] && [ "$back" = "$orig" ] || ok=0
      step 2/4 "/unmask с OTP     " "$ok" "$c ${back:-$(body "$r")}"

      r=$(unm); c=$(code "$r")
      ok=1; [ "$c" = 401 ] || ok=0
      step 3/4 "повтор того же OTP" "$ok" "$c (ожидался 401)"

      # Счётчик принятых шагов свой у каждой системы. Когда он был один на
      # сервис, вторая система с собственным верным кодом получала 401 просто
      # потому, что первая успела в это же тридцатисекундное окно, и во всём
      # сервисе проходило одно демаскирование в полминуты. Здесь crm обязана
      # пройти проверку кода — и остановиться уже на конверте, который запечатан
      # ключом demo.
      r=$(unm crm); c=$(code "$r"); e=$(body "$r")
      ok=1; [ "$c" = 400 ] || ok=0
      case "$e" in *"does not open with this system key"*) ;; *) ok=0 ;; esac
      step 4/4 "своё окно у системы" "$ok" "$c $e"
      rm -f "$hdr"
      if [ "$fail" = 0 ]; then echo "envelope: OK"
      else echo "envelope: СБОЙ"; exit 1; fi
    else
      echo "==> selfcheck (contract: mask -> demask -> retry)"
      orig='Иванов Иван Иванович, +7 916 123-45-67, ivanov@mail.ru'
      plain='Заявка принята, ответим в течение дня.'
      # id обязан быть свежим на каждый прогон: на второй вызов с тем же
      # payload_id сервис по контракту отвечает демаскированием, и селфчек
      # на фиксированных sc-1/sc-2 ломался бы начиная со второго запуска
      run="sc-$$-$(date +%s)"
      post() { # post <payload> <payload_id> -> тело, последняя строка = код
        curl -s -w '\n%{http_code}' -X POST "$base/process" \
          -H 'Content-Type: application/json' \
          -d "{\"payload\":\"$1\",\"payload_id\":\"$2\"}"
      }
      r=$(post "$orig" "$run-1"); c=$(code "$r"); m1=$(unwrap "$(body "$r")")
      ok=1; [ "$c" = 200 ] && [ -n "$m1" ] || ok=0
      case "$m1" in *Иванов*|*916*|*ivanov@mail.ru*) ok=0 ;; esac
      step 1/6 "маскирование        " "$ok" "$c ${m1:-$(body "$r")}"

      r=$(post "$m1" "$run-1"); c=$(code "$r"); d1=$(unwrap "$(body "$r")")
      ok=1; [ "$c" = 200 ] && [ "$d1" = "$orig" ] || ok=0
      step 2/6 "демаскирование      " "$ok" "$c ${d1:-$(body "$r")}"

      r=$(post "$orig" "$run-1"); c=$(code "$r"); m2=$(unwrap "$(body "$r")")
      ok=1; [ "$c" = 200 ] && [ "$m2" = "$m1" ] || ok=0
      step 3/6 "ретрай маски        " "$ok" "$c ${m2:-$(body "$r")}"

      r=$(post "$orig" "$run-2"); c=$(code "$r"); m3=$(unwrap "$(body "$r")")
      ok=1; [ "$c" = 200 ] && [ -n "$m3" ] || ok=0
      case "$m3" in *Иванов*|*916*|*ivanov@mail.ru*) ok=0 ;; esac
      step 4/6 "новый id            " "$ok" "$c ${m3:-$(body "$r")}"

      # текст без персональных данных обязан вернуться байт в байт
      r=$(post "$plain" "$run-3"); c=$(code "$r"); p1=$(unwrap "$(body "$r")")
      ok=1; [ "$c" = 200 ] && [ "$p1" = "$plain" ] || ok=0
      step 5/6 "без ПДн — не трогаем" "$ok" "$c ${p1:-$(body "$r")}"

      c=$(curl -s -o /dev/null -w '%{http_code}' -X POST "$base/process" \
        -H 'Content-Type: application/json' -H 'Expect: 100-continue' \
        -d "{\"payload\":\"$orig\",\"payload_id\":\"$run-4\"}")
      ok=1; [ "$c" = 200 ] || ok=0
      step 6/6 "Expect: 100-continue" "$ok" "$c"

      if [ "$fail" = 0 ]; then echo "selfcheck: OK"
      else echo "selfcheck: СБОЙ (порт $HOST_PORT — там точно pdmask?)"; exit 1; fi
    fi
    ;;

  eval)
    echo "eval: эталонный набор — M5, см. раздел 12 спеки"
    ;;

  tune)
    echo "tune: подбор весов требует эталонного набора — M5"
    ;;

  bench)
    echo "bench: используйте ab, замеры в docs/STATUS.md — M8"
    ;;

  big)
    echo "big: текст на 100k токенов — M8"
    ;;

  fmt)
    v=$(ocamlformat --version 2>/dev/null) || {
        echo "ocamlformat не установлен: opam install -y ocamlformat" >&2
        exit 1
    }
    grep -qx "version = $v" .ocamlformat || sed -i "s/^version = .*/version = $v/" .ocamlformat
    dune fmt || true
    echo "fmt: OK"
    ;;

  check)
    dune build @fmt 2>&1 | head -20   # непустой вывод = что-то не отформатировано
    dune build 2>&1 | head -50
    ;;

  zip)
    echo "==> creating pdmask.zip"
    rm -f pdmask.zip
    zip -r pdmask.zip \
      dune-project Dockerfile run.sh .ocamlformat README.md \
      bin lib config dicts models tools web \
      -x '*/_build/*' -x '*/.git/*' -x '*.zip' \
      -x 'tools/.pii_bench_cache/*' \
      -x 'tools/bench/corpus/external/*' \
      -x '*/.gitkeep'
    echo "zip: OK (pdmask.zip)"
    ;;

  help|*)
    echo "usage: ./run.sh {host|build|up|down|reload|selfcheck|eval|tune|bench|big|zip|fmt|check}"
    ;;
esac