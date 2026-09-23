# -*- coding: utf-8 -*-
"""Обучение структурного усреднённого перцептрона на Collection3.

Почему перцептрон, а не CRF и не трансформер:
  - трансформер отпадает по времени: T5-small это 1.46 с на сообщение, у нас
    бюджет в доли миллисекунды;
  - CRF даёт примерно то же качество на тех же признаках, но требует
    нормализации и экспонент в рантайме; перцептрон — это скалярные
    произведения и Viterbi, то есть сложение целых чисел;
  - усреднение весов по Коллинзу закрывает основную слабость перцептрона.

Признаки берутся из features.py и там же описаны. Словарные флаги проекта
входят в признаки — это и есть гибрид: словарь не решает сам, а подсказывает
модели.
"""
import sys, os, gzip, io, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import features as F

TAGS = F.TAGS
NT = len(TAGS)
TIDX = {t: i for i, t in enumerate(TAGS)}

def read_conll(path):
    sents = []
    cur = []
    op = gzip.open if path.endswith(".gz") else io.open
    with op(path, "rt", encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line or line.startswith("<DOCSTART>"):
                if cur: sents.append(cur); cur = []
                continue
            p = line.split("\t")
            if len(p) >= 2:
                cur.append((p[0], p[1] if p[1] in TIDX else "O"))
    if cur: sents.append(cur)
    return sents

def read_wikiann(path):
    """WikiANN-ru: токены и числовые метки. Порядок меток у них свой:
       0 O, 1 B-PER, 2 I-PER, 3 B-ORG, 4 I-ORG, 5 B-LOC, 6 I-LOC."""
    import pyarrow.parquet as pq
    m = {0: "O", 1: "B-PER", 2: "I-PER", 3: "B-ORG", 4: "I-ORG", 5: "B-LOC", 6: "I-LOC"}
    out = []
    for r in pq.read_table(path).to_pylist():
        toks = r["tokens"]; tags = r["ner_tags"]
        if not toks: continue
        out.append([(t, m.get(int(g), "O")) for t, g in zip(toks, tags)])
    return out

def featurize(sents, dicts):
    out = []
    for s in sents:
        toks = [t for t, _ in s]
        gold = [TIDX[g] for _, g in s]
        fo, fl = F.prepare(toks, dicts)
        feats = [F.token_feats(toks, fo, fl, i) for i in range(len(toks))]
        out.append((feats, gold))
    return out

def build_index(data, min_count):
    c = collections.Counter()
    for feats, _ in data:
        for fs in feats:
            c.update(fs)
    idx = {}
    for f, n in c.items():
        if n >= min_count:
            idx[f] = len(idx)
    return idx

def encode(data, idx):
    out = []
    for feats, gold in data:
        enc = [np.array([idx[f] for f in fs if f in idx], dtype=np.int32) for fs in feats]
        out.append((enc, np.array(gold, dtype=np.int32)))
    return out

def viterbi(enc, W, T):
    n = len(enc)
    if n == 0: return []
    sc = np.empty((n, NT), dtype=np.float64)
    for i in range(n):
        ids = enc[i]
        sc[i] = W[ids].sum(axis=0) if ids.size else 0.0
    dp = np.empty((n, NT)); bp = np.zeros((n, NT), dtype=np.int32)
    dp[0] = T[NT] + sc[0]
    for i in range(1, n):
        m = dp[i-1][:, None] + T[:NT]
        bp[i] = m.argmax(axis=0)
        dp[i] = m.max(axis=0) + sc[i]
    path = [int(dp[n-1].argmax())]
    for i in range(n-1, 0, -1):
        path.append(int(bp[i][path[-1]]))
    return path[::-1]

def train(data, nfeat, epochs, seed=1):
    W = np.zeros((nfeat, NT)); T = np.zeros((NT+1, NT))
    Wa = np.zeros_like(W); Ta = np.zeros_like(T)
    Wts = np.zeros_like(W); Tts = np.zeros_like(T)
    t = 0
    rng = np.random.default_rng(seed)
    order = np.arange(len(data))
    for ep in range(epochs):
        rng.shuffle(order); wrong = 0; total = 0
        t0 = time.time()
        for si in order:
            enc, gold = data[si]
            pred = viterbi(enc, W, T)
            t += 1
            n = len(gold)
            total += n
            for i in range(n):
                g, p = int(gold[i]), pred[i]
                if g == p: continue
                wrong += 1
                ids = enc[i]
                if ids.size:
                    Wa[ids, g] += (t - Wts[ids, g]) * W[ids, g]; Wts[ids, g] = t; W[ids, g] += 1
                    Wa[ids, p] += (t - Wts[ids, p]) * W[ids, p]; Wts[ids, p] = t; W[ids, p] -= 1
            pg = NT
            pp = NT
            for i in range(n):
                g, p = int(gold[i]), pred[i]
                if pg != pp or g != p:
                    Ta[pg, g] += (t - Tts[pg, g]) * T[pg, g]; Tts[pg, g] = t; T[pg, g] += 1
                    Ta[pp, p] += (t - Tts[pp, p]) * T[pp, p]; Tts[pp, p] = t; T[pp, p] -= 1
                pg, pp = g, p
        print("  эпоха %d: ошибок по токенам %.2f%%  (%.0f с)" % (ep+1, 100.0*wrong/total, time.time()-t0), flush=True)
    Wa += (t - Wts) * W; Ta += (t - Tts) * T
    return Wa / t, Ta / t

def spans(tags):
    out = []; i = 0
    while i < len(tags):
        name = TAGS[tags[i]]
        if name.startswith("B-"):
            ty = name[2:]; j = i + 1
            while j < len(tags) and TAGS[tags[j]] == "I-" + ty: j += 1
            out.append((ty, i, j)); i = j
        else: i += 1
    return out

def evaluate(data, W, T):
    tp = collections.Counter(); fp = collections.Counter(); fn = collections.Counter()
    for enc, gold in data:
        pred = viterbi(enc, W, T)
        g = set(spans(list(gold))); p = set(spans(pred))
        for s in p & g: tp[s[0]] += 1
        for s in p - g: fp[s[0]] += 1
        for s in g - p: fn[s[0]] += 1
    print("  тип      P      R      F1    сущностей")
    allt = alp = alf = 0
    for ty in ("PER", "LOC", "ORG"):
        P = tp[ty] / max(1, tp[ty] + fp[ty]); R = tp[ty] / max(1, tp[ty] + fn[ty])
        Fm = 2*P*R/max(1e-9, P+R)
        print("  %-6s %.3f  %.3f  %.3f  %d" % (ty, P, R, Fm, tp[ty]+fn[ty]))
        allt += tp[ty]; alp += tp[ty]+fp[ty]; alf += tp[ty]+fn[ty]
    P = allt/max(1,alp); R = allt/max(1,alf)
    print("  ИТОГО  %.3f  %.3f  %.3f" % (P, R, 2*P*R/max(1e-9,P+R)))
    return 2*P*R/max(1e-9,P+R)

if __name__ == "__main__":
    ner = sys.argv[1]; epochs = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    mc = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    import os as _os
    if _os.environ.get("NODICT"):
        dicts = {}
        print("АБЛЯЦИЯ: словари отключены")
    else:
        dicts = F.load_dicts("dicts")
    print("словарных слов:", len(dicts))
    base = read_conll(ner + "/train.txt.gz")
    extra = []
    if os.environ.get("WIKIANN"):
        extra = read_wikiann(ner + "/wikiann_ru.parquet")
        print("добавлено из WikiANN-ru предложений:", len(extra))
    tr = featurize(base + extra, dicts)
    va = featurize(read_conll(ner + "/valid.txt.gz"), dicts)
    te = featurize(read_conll(ner + "/test.txt.gz"), dicts)
    print("предложений: train=%d valid=%d test=%d" % (len(tr), len(va), len(te)))
    idx = build_index(tr, mc)
    print("признаков (порог %d): %d" % (mc, len(idx)))
    trE, vaE, teE = encode(tr, idx), encode(va, idx), encode(te, idx)
    W, T = train(trE, len(idx), epochs)
    print("valid:"); evaluate(vaE, W, T)
    print("test:");  f1 = evaluate(teE, W, T)
    np.savez_compressed(ner + "/model.npz", W=W.astype(np.float32), T=T.astype(np.float32))
    io.open(ner + "/feats.txt", "w", encoding="utf-8").write("\n".join(
        f for f, _ in sorted(idx.items(), key=lambda kv: kv[1])))
    print("сохранено:", ner + "/model.npz", ner + "/feats.txt")
