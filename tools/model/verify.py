# -*- coding: utf-8 -*-
"""Сверка двух реализаций признаков: Python и OCaml.

Одни и те же предложения прогоняются обеими и теги сравниваются токен в токен.
Расхождение означает, что веса применяются не к тем признакам, и модель молча
деградирует — поймать это иначе нельзя.
"""
import sys, os, subprocess, io
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, features as F, train as T

ner, exe = sys.argv[1], sys.argv[2]
limit = int(sys.argv[3]) if len(sys.argv) > 3 else 10**9
dicts = F.load_dicts("dicts")
d = np.load(ner + "/model.npz"); W = d["W"].astype(np.float64); Tr = d["T"].astype(np.float64)
idx = {f: i for i, f in enumerate(io.open(ner + "/feats.txt", encoding="utf-8").read().split("\n"))}

sents = T.read_conll(ner + "/test.txt.gz")[:limit]
# предложения, где токен содержит пробел, сверять нельзя
sents = [s for s in sents if all(" " not in t for t, _ in s)]
lines = [" ".join(t for t, _ in s) for s in sents]

r = subprocess.run([exe], input="\n".join(lines) + "\n", capture_output=True, text=True)
oc = r.stdout.rstrip("\n").split("\n")
print("предложений отправлено:", len(lines), "получено:", len(oc))

same = diff = skipped = 0
bad = []
for k, s in enumerate(sents):
    toks = [t for t, _ in s]
    fo, fl = F.prepare(toks, dicts)
    enc = [np.array([idx[f] for f in F.token_feats(toks, fo, fl, i) if f in idx], dtype=np.int32)
           for i in range(len(toks))]
    py = [T.TAGS[t] for t in T.viterbi(enc, W, Tr)]
    ml = oc[k].split() if k < len(oc) else []
    if len(ml) != len(py):
        skipped += 1
        if len(bad) < 3: bad.append(("длина", toks[:8], len(py), len(ml)))
        continue
    for a, b in zip(py, ml):
        if a == b: same += 1
        else:
            diff += 1
            if len(bad) < 8: bad.append(("тег", toks[:8], a, b))
print("совпало токенов: %d, разошлось: %d, пропущено предложений (разная токенизация): %d"
      % (same, diff, skipped))
if diff: print("доля расхождений: %.4f%%" % (100.0 * diff / max(1, same + diff)))
for b in bad[:8]: print("  ", b)
