"""Run the seed<->PoC structural fidelity check on one PoC.

usage:
  python3 run_verifier.py <seed_dir> <poc.c> [--work DIR] [--check-fixed] [--require-fixed]

<seed_dir> is one of seeds/<id>/ (seed_buggy.c, seed_fixed.c, fix.patch, slices.json).
The PoC must define `<fn>_buggy`, where <fn> is the seed's bug function; `<fn>_fixed` is
optional (required only with --require-fixed). Prints one verdict row per line; exit code 0 = OK, 1 = rejected,
2 = the check could not run.
"""

import argparse
import json
import sys
from pathlib import Path

import verifier


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("seed_dir", type=Path)
    ap.add_argument("poc", type=Path)
    ap.add_argument("--work", type=Path, help="scratch directory (default: ./work/<seed>)")
    ap.add_argument("--check-fixed", action="store_true",
                    help="also check that PoC _buggy -> _fixed moves like the seed's fix")
    ap.add_argument("--require-fixed", action="store_true",
                    help="reject a PoC without a `_fixed` function")
    a = ap.parse_args()

    meta = json.loads((a.seed_dir / "slices.json").read_text())
    work = a.work or Path("work") / meta["seed"]
    v = verifier.run(meta["pattern"], (a.seed_dir / "fix.patch").read_text(),
                     a.seed_dir / "seed_buggy.c", a.seed_dir / "seed_fixed.c",
                     meta["buggy_fns"], meta["fixed_fns"], a.poc, work,
                     require_fixed=a.require_fixed, check_fixed=a.check_fixed)
    print("\n".join(v.rows))
    if v.error:
        return 2
    return 0 if v.ok else 1


if __name__ == "__main__":
    sys.exit(main())
