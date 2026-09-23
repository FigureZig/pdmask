# pdmask — multi-stage Docker build
# Stage 1: build the OCaml binary
FROM ocaml/opam:ubuntu-26.04-ocaml-5.4 AS build
WORKDIR /build

# Ensure the opam user owns the build directory
RUN sudo chown -R opam:opam /build

# Install system deps for opam packages
RUN sudo apt-get update && sudo apt-get install -y --no-install-recommends \
    libgmp-dev pkg-config libev-dev \
    && sudo rm -rf /var/lib/apt/lists/*

# Copy project files
COPY --chown=opam:opam dune-project ./
COPY --chown=opam:opam bin/ ./bin/
COPY --chown=opam:opam lib/ ./lib/

# Install OCaml dependencies and dune
RUN opam install -y dune eio eio_main mirage-crypto mirage-crypto-rng \
    mirage-crypto-pk yaml base64 alcotest digestif zarith

# Build
RUN opam exec -- dune build --profile release

# Stage 2: runtime image
FROM ubuntu:26.04
WORKDIR /app

RUN apt-get update && apt-get install -y --no-install-recommends \
    libgmp10 ca-certificates curl \
    && rm -rf /var/lib/apt/lists/*

COPY --from=build /build/_build/default/bin/main.exe /app/pdmask

# Словари и конфиг обязаны попасть в образ. Без них сервис поднимается молча,
# отвечает 200 и возвращает payload незамаскированным: Dictload не находит
# файлов и отдаёт пустые списки. Проверено — утекает всё, до единого типа.
COPY dicts/ /app/dicts/
COPY config/ /app/config/

EXPOSE 8080
ENV PORT=8080
CMD ["/app/pdmask"]