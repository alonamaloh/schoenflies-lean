# Comparator check

This directory configures
[`leanprover/comparator`](https://github.com/leanprover/comparator) to check the project's
headline theorem, `Schoenflies.jordan_schoenflies_of_homeomorph`.

## What it checks

`Challenge.lean` is the trusted statement: it imports the prerequisites but not the module that
proves the theorem. `Solution.lean` imports the actual proof. They are separate Lean libraries,
matching Comparator's challenge/solution trust boundary. Comparator verifies that the
solution theorem:

1. has exactly the challenge statement;
2. is accepted by the Lean kernel; and
3. uses no axioms beyond `propext`, `Quot.sound`, and `Classical.choice`.

This is deliberately narrower than `docs/audit-axioms.py`. Comparator protects the identity and
axioms of the public headline result; the existing build and audit cover every declaration in
the library.

## Running it

First build the project and its two Comparator modules:

```sh
lake build Schoenflies Challenge Solution
```

Build Comparator following its upstream instructions, with a compatible `lean4export` and
`landrun` in `PATH`. From this repository's root, run:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$(pwd)" -- \
  bash -c 'lake env /path/to/comparator Comparator/schoenflies.json'
```

The trustworthy sandboxed check requires Linux, `systemd-run`, and a working `landrun`.
Comparator's `scripts/fake-landrun.sh` can help test configuration on other systems, but such a
run does not provide the production sandbox guarantee.
