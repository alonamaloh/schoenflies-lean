#!/usr/bin/env python3
"""Axiom audit: check that EVERY declaration in the library rests only on Lean's three
standard axioms.  Run from the repository root, after a successful build:

    python3 docs/audit-axioms.py

It scans the sources with the same reader `regen-inventory.py` uses, emits one
`#print axioms` per declaration into a scratch file, runs it, and reports anything that
depends on an axiom outside {propext, Classical.choice, Quot.sound} — `sorryAx` above all.
Whole run is a couple of seconds, because the environment is loaded once.

This is the check that makes "sorry-free" a guarantee rather than a grep.  A `sorry` inside a
term that some other declaration later reuses is invisible to a grep of the file that
consumes it; `sorryAx` is not.

Exit status is 1 if any declaration is unclean, or if any name in the source scan fails to
resolve — the latter means the scanner and Lean disagree about what was declared, which is
itself a defect worth fixing, since the same scanner gates merges for duplicate names.

The scratch file imports every module found on disk, NOT the root `Schoenflies`. A worker
adding a leaf module is told not to edit `Schoenflies.lean` — the integrator adds the import —
so a root-only import made this gate fail on every branch it was supposed to certify, and
three separate agents wasted time diagnosing it as their own bug.
"""
import glob, os, re, subprocess, sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
SCRATCH = "AxiomAudit.lean"


def load_scanner():
    """Reuse regen-inventory.py's reader without running its main body."""
    src = open("docs/regen-inventory.py").read()
    head = src[: src.index("owners, per_file = scan()")]
    ns = {}
    exec(compile(head, "docs/regen-inventory.py", "exec"), ns)
    return ns["scan"]


owners, per_file = load_scanner()()
names = sorted(owners)

# Import every module on disk, so that a leaf module not yet listed in Schoenflies.lean is
# still audited. Module name is the path with separators as dots and the .lean suffix dropped.
modules = sorted(p[: -len(".lean")].replace(os.sep, ".") for p in per_file)

with open(SCRATCH, "w") as f:
    for m in modules:
        f.write(f"import {m}\n")
    for n in names:
        f.write(f"#print axioms {n}\n")

try:
    proc = subprocess.run(["lake", "env", "lean", SCRATCH],
                          capture_output=True, text=True)
finally:
    os.remove(SCRATCH)

unclean, unresolved = [], []
for line in (proc.stdout + proc.stderr).splitlines():
    if "unknownIdentifier" in line or "Unknown constant" in line:
        unresolved.append(line.strip())
    elif "depends on axioms:" in line:
        decl, axs = line.split(" depends on axioms: ")
        used = {a.strip() for a in axs.strip("[]").split(",") if a.strip()}
        if not used <= ALLOWED:
            unclean.append(f"{decl.strip()}  ->  {sorted(used - ALLOWED)}")

for u in unclean:
    print("UNCLEAN", u, file=sys.stderr)
for u in unresolved[:20]:
    print("UNRESOLVED", u, file=sys.stderr)
if len(unresolved) > 20:
    print(f"... and {len(unresolved) - 20} more unresolved", file=sys.stderr)
print(f"{len(names)} declarations audited, {len(unclean)} unclean,"
      f" {len(unresolved)} unresolved", file=sys.stderr)
sys.exit(1 if unclean or unresolved else 0)
