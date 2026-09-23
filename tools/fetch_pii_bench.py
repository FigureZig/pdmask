#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Конвертер hivetrace/pii-bench в формат корпуса pdmask.

    python3 tools/fetch_pii_bench.py            # скачать и сконвертировать
    python3 tools/fetch_pii_bench.py --offline  # только сконвертировать из кэша

Датасет: https://huggingface.co/datasets/hivetrace/pii-bench, Apache-2.0,
1810 строк русского текста со span-разметкой по символьным смещениям.

Скрипт нужен только для обновления корпуса и в сборке решения не участвует —
как и tools/build_dicts.py. Результат лежит в репозитории готовым файлом,
чтобы прогон не требовал сети.

Две вещи, которые скрипт делает и о которых легко забыть:

1. Смещения переводятся из символьных в байтовые. Датасет размечен по
   символам, сервис работает с байтами, и кириллица сдвинула бы всё вдвое.

2. Типы датасета шире перечня ТЗ. KPP, OGRN, OGRNIP и TOKEN — реквизиты
   организации и ключи доступа, а не персональные данные из раздела 4.1.
   Они сохраняются под своими именами: score_pdmask считает неизвестный тип
   нейтральным — не требует его замаскировать и не штрафует, если он попал
   под маску. Так видно, что мы их не ловим, но метрика по ТЗ не портится.
"""
import argparse, io, json, os, sys, urllib.request

BASE = "https://huggingface.co/datasets/hivetrace/pii-bench/resolve/main/data"
SPLITS = ("entity", "domain")
HERE = os.path.dirname(os.path.abspath(__file__))
CACHE = os.path.join(HERE, ".pii_bench_cache")
OUT = os.path.join(HERE, "bench", "corpus", "pii_bench.txt")

# Типы датасета -> типы pdmask. Слева то, что размечено в pii-bench, справа
# имя из Spans.ty_name. Незамапленные остаются как есть и считаются
# нейтральными при оценке.
TYPE_MAP = {
    "NAME": "fio",
    "PHONE_NUMBER": "phone",
    "EMAIL": "email",
    "ADDRESS": "address",
    "BANK_CARD_NUMBER": "card",
    "CVC": "cvv",
    "INN": "inn",
    "SNILS": "snils",
    "PASSPORT_NUMBER": "passport",
    # вне перечня ТЗ: реквизиты организации и ключи доступа
    "KPP": "x_kpp",
    "OGRN": "x_ogrn",
    "OGRNIP": "x_ogrnip",
    "TOKEN": "x_token",
}


def fetch(offline):
    os.makedirs(CACHE, exist_ok=True)
    for split in SPLITS:
        path = os.path.join(CACHE, f"{split}.parquet")
        if os.path.exists(path):
            continue
        if offline:
            sys.exit(f"нет кэша {path}, запустите без --offline")
        url = f"{BASE}/{split}-00000-of-00001.parquet"
        print(f"качаю {url}")
        urllib.request.urlretrieve(url, path)


def rows():
    import pyarrow.parquet as pq

    for split in SPLITS:
        table = pq.read_table(os.path.join(CACHE, f"{split}.parquet"))
        for r in table.to_pylist():
            yield split, r


def escape(text, spans):
    """Вставляет разметку {{тип|значение}} по спанам. Спаны приходят в
    символьных смещениях; сортируем и идём слева направо."""
    out, pos = [], 0
    for st, en, ty in sorted(spans):
        if st < pos:  # пересекающиеся спаны датасет не обещает, но бережёмся
            continue
        out.append(text[pos:st])
        value = text[st:en]
        # разметка не должна ломаться о собственные скобки в значении
        if "{{" in value or "}}" in value or "|" in value:
            out.append(value)
        else:
            out.append("{{%s|%s}}" % (ty, value))
        pos = en
    out.append(text[pos:])
    return "".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--offline", action="store_true")
    args = ap.parse_args()
    fetch(args.offline)

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    n, n_spans, n_clean, skipped = 0, 0, 0, 0
    with io.open(OUT, "w", encoding="utf-8") as f:
        f.write(
            "# hivetrace/pii-bench, сконвертировано tools/fetch_pii_bench.py.\n"
            "# Источник: https://huggingface.co/datasets/hivetrace/pii-bench (Apache-2.0)\n"
            "# Не править руками: файл пересобирается скриптом.\n"
            "#\n"
            "# Типы x_kpp, x_ogrn, x_ogrnip, x_token лежат вне перечня 17 типов ТЗ\n"
            "# (реквизиты организации и ключи доступа). score_pdmask считает их\n"
            "# нейтральными: не требует маскировать и не штрафует за маску.\n"
        )
        for split, r in rows():
            text = r["text"]
            if "@end" in text or "@case" in text:
                skipped += 1
                continue
            spans = []
            for e in r.get("entities") or []:
                ty = TYPE_MAP.get(e["type"])
                if ty is None:
                    skipped += 1
                    continue
                spans.append((e["start"], e["end"], ty))
            marked = escape(text, spans)
            polarity = "pos" if spans else "neg"
            expect = "mask" if spans else "clean"
            f.write(
                "\n@case id=hf-%s-%s size=sentence polarity=%s expect=%s\n"
                % (split, r["id"], polarity, expect)
            )
            f.write("@probes pii-bench/%s, домен %s\n@text\n%s\n@end\n" % (split, r["domain"], marked))
            n += 1
            n_spans += len(spans)
            if not spans:
                n_clean += 1
    size = os.path.getsize(OUT)
    print(
        "записано %d кейсов (%d без ПДН), %d спанов, %d Б -> %s"
        % (n, n_clean, n_spans, size, os.path.relpath(OUT, os.path.dirname(HERE)))
    )
    if skipped:
        print("пропущено спанов/строк: %d" % skipped)


if __name__ == "__main__":
    main()
