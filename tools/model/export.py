# -*- coding: utf-8 -*-
"""Экспорт обученной модели в двоичный файл для OCaml.

Формат (всё little-endian):
  "PDMSEQ01"                8 байт
  n_tags, n_feat, tbl_size  3 × int32
  переходы                  (n_tags+1) * n_tags   float32
  таблица хешей             tbl_size              int64   (0 = пусто)
  таблица идентификаторов   tbl_size              int32
  веса                      n_feat * n_tags       float32

Хеш признака — FNV-1a по байтам UTF-8, маскированный 62 битами, чтобы он
совпадал с OCaml, где int 63-битный. Таблица открытой адресации с линейным
пробированием: поиск признака — один-два обращения в память.
"""
import sys, os, io, struct
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import features as F

FNV_OFF = 0x3bf29ce484222325
FNV_PRIME = 0x100000001b3
MASK = 0x3FFFFFFFFFFFFFFF

def fhash(s):
    h = FNV_OFF
    for b in s.encode("utf-8"):
        h = ((h ^ b) * FNV_PRIME) & MASK
    return h if h else 1   # 0 зарезервирован под «пусто»

def export(model_npz, feats_txt, out_bin):
    d = np.load(model_npz)
    W = d["W"].astype(np.float32); T = d["T"].astype(np.float32)
    names = io.open(feats_txt, encoding="utf-8").read().split("\n")
    assert len(names) == W.shape[0], (len(names), W.shape)
    keep = np.abs(W).max(axis=1) > 0.0
    names = [n for n, k in zip(names, keep) if k]
    W = W[keep]
    nfeat, ntags = W.shape
    size = 1
    while size < nfeat * 2: size <<= 1
    th = np.zeros(size, dtype=np.uint64); ti = np.zeros(size, dtype=np.int32)
    coll = 0
    for i, n in enumerate(names):
        h = fhash(n); p = h & (size - 1)
        while th[p] != 0:
            if th[p] == h: raise SystemExit("коллизия хеша на " + n)
            p = (p + 1) & (size - 1); coll += 1
        th[p] = h; ti[p] = i
    with io.open(out_bin, "wb") as f:
        f.write(b"PDMSEQ01")
        f.write(struct.pack("<iii", ntags, nfeat, size))
        f.write(T.astype("<f4").tobytes())
        f.write(th.astype("<u8").tobytes())
        f.write(ti.astype("<i4").tobytes())
        f.write(W.astype("<f4").tobytes())
    print("признаков %d, таблица %d, пробирований при вставке %d" % (nfeat, size, coll))
    print("файл %s: %.2f МБ" % (out_bin, os.path.getsize(out_bin) / 1048576.0))
    return names, W, T

if __name__ == "__main__":
    export(sys.argv[1] + "/model.npz", sys.argv[1] + "/feats.txt", sys.argv[2])
