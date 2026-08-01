#!/usr/bin/env python3
"""Regenerate docs/INVENTORY.md, and report duplicate declaration names across modules.

Run from the repository root.  The duplicate scan is the important half: Lean's import
checker accepts two modules declaring the same name when the statements are
alpha-equivalent Props, because proof irrelevance makes them defeq.  So a clean build is
NOT a sufficient collision check.
"""
import re, glob, collections, sys

def decls():
    out = collections.defaultdict(list)
    for f in sorted(glob.glob("Schoenflies/**/*.lean", recursive=True)):
        ns = []
        for line in open(f):
            m = re.match(r'^namespace\s+([A-Za-z_0-9.]+)', line)
            if m: ns.extend(m.group(1).split('.')); continue
            m = re.match(r'^end\s+([A-Za-z_0-9.]+)\s*$', line)
            if m:
                p = m.group(1).split('.')
                if ns[-len(p):] == p: ns = ns[:-len(p)]
                continue
            m = re.match(r'^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+|noncomputable\s+)*'
                         r'(theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+'
                         r"([A-Za-z_0-9.']+)", line)
            if m and 'private' not in line:
                out[".".join(ns + [m.group(2)])].append(f)
    return out

d = decls()
dups = {k: sorted(set(v)) for k, v in d.items() if len(set(v)) > 1}
for k, v in sorted(dups.items()):
    print("DUPLICATE", k, "->", v, file=sys.stderr)
print(f"{len(d)} declarations, {len(dups)} duplicated", file=sys.stderr)
