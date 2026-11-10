#!/usr/bin/env python3
"""Enforce the build rules of docs/ARCHITECTURE.md. Exit 1 on any violation.

1. No file imports all of Mathlib (`import Mathlib`): import the specific modules a file needs.
2. A topic (UndergradKB.<Topic>.*) imports Mathlib, UndergradKB.Common.* and its own topic only, never another topic.
3. UndergradKB.Common imports nothing of ours except Common.
4. Every topic file is reachable from its topic root (so the topic library builds and checks all of it).
5. Size guard: a topic file over 1500 lines is reported (split it so edits rebuild less)."""
import pathlib, re, sys
root = pathlib.Path(__file__).resolve().parent.parent
src = root / "UndergradKB"
imp = re.compile(r"^import\s+(\S+)", re.M)
errs, warns = [], []
mods = {}
for f in sorted(src.rglob("*.lean")):
    mod = ".".join(f.relative_to(root).with_suffix("").parts)
    mods[mod] = (f, imp.findall(f.read_text(encoding="utf-8")))
def topic(m):
    p = m.split(".")
    return p[1] if len(p) > 1 and p[0] == "UndergradKB" else None
for m, (f, ims) in mods.items():
    t = topic(m)
    for i in ims:
        if i == "Mathlib":
            errs.append(f"{m}: imports all of Mathlib; import the specific modules")
        ti = topic(i)
        if ti and ti not in ("Common", t):
            errs.append(f"{m}: imports {i} (topic {ti}); topics may import only Common and themselves")
    n = sum(1 for _ in f.open(encoding="utf-8"))
    if n > 1500 and t != "Common":
        warns.append(f"{m}: {n} lines (split it)")
for t in {topic(m) for m in mods} - {None}:
    rootmod = f"UndergradKB.{t}"
    if rootmod not in mods:
        errs.append(f"topic {t} has no root file UndergradKB/{t}.lean"); continue
    seen, todo = set(), [rootmod]
    while todo:
        m = todo.pop()
        if m in seen or m not in mods: continue
        seen.add(m); todo += mods[m][1]
    for m in mods:
        if topic(m) == t and m not in seen:
            errs.append(f"{m}: not imported (directly or indirectly) by {rootmod}")
for w in warns: print("warning:", w)
for e in errs: print("error:", e)
print(f"{len(mods)} files, {len(errs)} errors, {len(warns)} warnings")
sys.exit(1 if errs else 0)
