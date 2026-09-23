# -*- coding: utf-8 -*-
"""Признаки токена для последовательной модели.

ВАЖНО: этот файл — единственный источник правды о признаках. Всё, что здесь
описано, реализовано один в один в lib/core/seqmodel.ml. Любое расхождение
между Python и OCaml означает, что обученные веса применяются не к тем
признакам, и модель молча деградирует.

Свёртка повторяет Classes.fold_*: строчная латиница, строчная кириллица,
Ё и ё сводятся к «е».
"""
import io, os

def fold(s):
    return s.lower().replace("ё", "е")

SHAPE_OTHER, SHAPE_LOWER, SHAPE_CAP, SHAPE_ALLCAP, SHAPE_DIGIT, SHAPE_PUNCT = range(6)

def shape(tok):
    if not tok:
        return SHAPE_OTHER
    if tok.isdigit():
        return SHAPE_DIGIT
    letters = [c for c in tok if c.isalpha()]
    if not letters:
        return SHAPE_PUNCT
    if all(c.isupper() for c in letters) and len(letters) > 1:
        return SHAPE_ALLCAP
    if tok[0].isupper():
        return SHAPE_CAP
    if all(c.islower() for c in letters):
        return SHAPE_LOWER
    return SHAPE_OTHER

def lenbucket(n):
    if n <= 2: return n
    if n <= 4: return 3
    if n <= 6: return 4
    if n <= 9: return 5
    return 6

# --- словарные флаги -------------------------------------------------------
FLAG_FILES = [
    ("name",   "names.txt"),
    ("surn",   "surnames.txt"),
    ("patr",   "patronymics.txt"),
    ("geo",    "geox.txt"),
    ("cntr",   "countries.txt"),
    ("role",   "roles.txt"),
    ("month",  "months.txt"),
    ("addrm",  "address_markers.txt"),
    ("stop",   "stop_context.txt"),
    ("epon",   "heads_eponym.txt"),
    ("poss",   "heads_possess.txt"),
]

def load_dicts(dicts_dir):
    d = {}
    for i, (flag, fn) in enumerate(FLAG_FILES):
        p = os.path.join(dicts_dir, fn)
        if not os.path.exists(p):
            continue
        for line in io.open(p, encoding="utf-8"):
            w = fold(line.strip())
            if not w or w.startswith("#"):
                continue
            d[w] = d.get(w, 0) | (1 << i)
    # keywords.txt: «слово флаг», все ключевые слова под одним битом
    p = os.path.join(dicts_dir, "keywords.txt")
    kwbit = 1 << len(FLAG_FILES)
    if os.path.exists(p):
        for line in io.open(p, encoding="utf-8"):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            w = fold(line.split()[0])
            d[w] = d.get(w, 0) | kwbit
    return d

NFLAGS = len(FLAG_FILES) + 1

# --- морфологические суффиксы ---------------------------------------------
# Русское имя размечает себя само: отчество и фамилия имеют жёсткие окончания.
PATR_SUF = ("ович", "евич", "ьич", "овна", "евна", "ична", "инична", "иничн")
SURN_SUF = ("ов", "ев", "ин", "ын", "ский", "цкий", "ская", "цкая", "ской", "ко",
            "ук", "юк", "ян", "дзе", "швили", "ия", "их", "ых", "ова", "ева",
            "ина", "ына", "ову", "еву", "ину", "овым", "евым", "иным", "овой",
            "евой", "иной", "овы", "евы", "ины")

def morph(w):
    m = 0
    if w.endswith(PATR_SUF): m |= 1
    if w.endswith(SURN_SUF): m |= 2
    return m

def token_feats(toks, folded, flags, i):
    """Признаки токена i как список строк."""
    n = len(toks)
    f = []
    w = folded[i]
    sh = shape(toks[i])
    f.append("w=" + w)
    f.append("sh=%d" % sh)
    f.append("len=%d" % lenbucket(len(w)))
    for k in (2, 3, 4):
        if len(w) >= k: f.append("suf%d=%s" % (k, w[-k:]))
    for k in (2, 3):
        if len(w) >= k: f.append("pre%d=%s" % (k, w[:k]))
    fl = flags[i]
    for b in range(NFLAGS):
        if fl & (1 << b): f.append("d%d" % b)
    mo = morph(w)
    if mo & 1: f.append("mpatr")
    if mo & 2: f.append("msurn")
    if i == 0: f.append("bos")
    if i == n - 1: f.append("eos")
    # контекст: форма и флаги соседей, слово соседей
    for off in (-2, -1, 1, 2):
        j = i + off
        if 0 <= j < n:
            f.append("sh%+d=%d" % (off, shape(toks[j])))
            fj = flags[j]
            for b in range(NFLAGS):
                if fj & (1 << b): f.append("d%+d_%d" % (off, b))
            if abs(off) == 1:
                f.append("w%+d=%s" % (off, folded[j]))
                mj = morph(folded[j])
                if mj & 1: f.append("mpatr%+d" % off)
                if mj & 2: f.append("msurn%+d" % off)
        else:
            f.append("sh%+d=X" % off)
    # биграмма форм
    if i > 0: f.append("shb=%d_%d" % (shape(toks[i-1]), sh))
    return f

def prepare(toks, dicts):
    folded = [fold(t) for t in toks]
    flags = [dicts.get(w, 0) for w in folded]
    return folded, flags

TAGS = ["O", "B-PER", "I-PER", "B-LOC", "I-LOC", "B-ORG", "I-ORG"]
