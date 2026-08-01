#!/usr/bin/env python3
"""Regenerate docs/INVENTORY.md, and report duplicate declaration names across modules.

Run from the repository root:  python3 docs/regen-inventory.py

The duplicate scan is the important half: Lean's import checker accepts two modules declaring
the same name when the statements are alpha-equivalent Props, because proof irrelevance makes
them defeq.  So a clean build is NOT a sufficient collision check.  Exit status is 1 when any
duplicate is found, so this can gate a merge.

Comment and docstring text is skipped.  Without that, a docstring line that happens to wrap
onto the word "theorem" is read as a declaration, which is where the phantom entries
`actually`, `is` and `of` in earlier inventories came from.

The name pattern is a negated character class, not `[A-Za-z_0-9.']+`.  Lean identifiers here
routinely carry subscripts — `carrier₁`, `cell_subset₂`, `J₁` — and an ASCII-only pattern
truncates them, so `carrier₁` and `carrier₂` both register as `carrier`.  That both loses real
names from the inventory and manufactures a phantom duplicate inside a single file.

`private` declarations are skipped: they are invisible outside their module, so they cannot
collide, and their real names are mangled.
"""
import re, glob, collections, sys

INVENTORY = "docs/INVENTORY.md"

# Anything up to the first character that cannot occur in a Lean identifier.  Deliberately
# permissive about Unicode: subscripts, primes and Greek letters are all in normal use here.
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|noncomputable\s+|scoped\s+|partial\s+|unsafe\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+"
    r"([^\s(){}\[\]⟨⟩:=,←→↔|]+)")

PRIVATE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?private\b")


def strip_comments(text):
    """Blank out `/- ... -/` blocks (docstrings included) and `--` line comments.

    Newlines are preserved so that line-oriented scanning still sees the right structure.
    Nesting is honoured, because Lean block comments nest.
    """
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def scan():
    """Return {fully-qualified name: [files]} and {file: [names in source order]}."""
    owners = collections.defaultdict(list)
    per_file = collections.OrderedDict()
    for f in sorted(glob.glob("Schoenflies/**/*.lean", recursive=True)):
        source = strip_comments(open(f).read())
        names, ns = [], []
        for line in source.splitlines():
            m = re.match(r"^namespace\s+([A-Za-z_0-9.]+)", line)
            if m:
                ns.extend(m.group(1).split("."))
                continue
            m = re.match(r"^end\s+([A-Za-z_0-9.]+)\s*$", line)
            if m:
                p = m.group(1).split(".")
                if ns[-len(p):] == p:
                    ns = ns[:-len(p)]
                continue
            if PRIVATE.match(line):
                continue
            m = DECL.match(line)
            if not m:
                continue
            name = m.group(2)
            # `_root_.Foo` escapes the enclosing namespaces entirely.
            full = name[len("_root_."):] if name.startswith("_root_.") else ".".join(ns + [name])
            names.append(full)
            owners[full].append(f)
        per_file[f] = names
    return owners, per_file


def line_count(path):
    with open(path) as h:
        return sum(1 for _ in h)


owners, per_file = scan()

with open(INVENTORY, "w") as out:
    out.write("# Inventory of `main` — generated\n\n")
    out.write("Regenerate with `python3 docs/regen-inventory.py`, from the repository root.\n")
    out.write("GREP THIS BEFORE STATING ANY LEMMA: re-proving something already here is the\n")
    out.write("commonest way parallel builds collide, and it has cost six rebuilds so far — one\n")
    out.write("of which compiled silently, because two alpha-equivalent `Prop`s pass the import\n")
    out.write("checker under proof irrelevance.\n")
    for f, names in per_file.items():
        out.write(f"\n## {f}  ({line_count(f)} lines)\n\n")
        out.write((", ".join(f"`{n}`" for n in names) + "\n") if names else "_(no declarations)_\n")

dups = {k: sorted(set(v)) for k, v in owners.items() if len(set(v)) > 1}
for k, v in sorted(dups.items()):
    print("DUPLICATE", k, "->", v, file=sys.stderr)
print(f"{len(owners)} declarations in {len(per_file)} modules, {len(dups)} duplicated;"
      f" wrote {INVENTORY}", file=sys.stderr)
sys.exit(1 if dups else 0)
