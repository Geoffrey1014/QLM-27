# Seed↔PoC structural fidelity check

Before a PoC is used to validate queries, this check confirms that the PoC's `_buggy`
function still contains the seed bug. It compares structural feature counts between the
seed's bug function (copied verbatim from the kernel, buggy and fixed versions) and the
PoC's `<fn>_buggy` function. The counting is done by a CodeQL query (`ql/features.ql`)
and the verdict by `verifier.py`. No LLM is involved.

## Usage

Requires CodeQL CLI (tested with 2.25.6) and gcc.

```bash
export QLM_CODEQL=/path/to/codeql          # default: `codeql` on PATH
(cd ql && $QLM_CODEQL pack install)        # once: fetch codeql/cpp-all
python3 run_verifier.py seeds/lin-1 path/to/poc.c [--check-fixed] [--require-fixed]
```

The command prints one verdict row per line. Exit code: 0 = accepted,
1 = rejected (`MISMATCH`), 2 = the check could not run (build or query error).

## Files

| File | Role |
|---|---|
| `verifier.py` | derives seed-specific API names from the fix patch, runs the feature query, judges |
| `run_verifier.py` | command-line entry point |
| `ql/features.ql`, `ql/Features.qll` | per-function structural feature counts |
| `codeql_cli.py`, `cfunctions.py` | CodeQL CLI wrappers; C function finder |
| `seeds/<id>/` | for each of the 25 RQ2–RQ4 seeds: `seed_buggy.c` / `seed_fixed.c` (the bug function verbatim, plus a declarations-only preamble so it compiles), `fix.patch`, `slices.json` |

## What is checked

### Features counted per function

| Pattern | Pattern features |
|---|---|
| four-features (Lin, Lu) | `ff.acquire` calls to acquire APIs; `ff.release` calls to release APIs; `ff.leaky_exit` returns reached after an acquire with none of the patch's releases in between |
| missing-check | `mc.producer` calls whose value the fix starts to check; `mc.unchecked` producer calls whose result is never tested; `mc.deref_before_check` producer variables dereferenced before their first test |
| delay-gfp | `dg.busy_wait` (`mdelay`/`udelay`/`ndelay`); `dg.sleep` (`msleep`/`usleep_range`/...); `dg.gfp_atomic`; `dg.gfp_kernel`; `dg.atomic_ctx` (spin/rw locks, irq/preempt/bh disable, `rcu_read_lock`) |
| error-return | `er.exit_branch` if-branches that leave the function; `er.unset_exit` exit branches that leave without setting the return variable |

Control-flow features, counted for every pattern: `if`, exits (`goto` + `return`), loops, `switch`.

Acquire/release/producer API names are derived per seed from the fix patch and the
buggy function (`derive_api`), on top of a base list of common `of_*` and allocation APIs.

### Rules applied to PoC `_buggy`

Only the pattern features **the fix changes** (seed buggy ≠ seed fixed) are judged:

| Rule | Meaning |
|---|---|
| KEEP_BUG | each changed feature present in the seed's buggy function occurs at least once in PoC `_buggy` |
| NO_FIX_IN_BUGGY | a feature the fix adds (e.g. the release, the sleeping call) does not occur more often than in the seed's buggy function |
| KEEP_CF | the bug's control flow occurs at least once when the seed has it: `if` and an exit for four-features and error-return; nothing for missing-check (the bug is a missing `if`) and delay-gfp (the bug depends on calling context) |
| NO_NEW_CF | PoC `_buggy` has no more `if`s, exits or loops than the seed's buggy function |

The PoC may simplify (drop code) but must keep the bug's ingredients. If the fix changes
none of the pattern features, the verdict carries `BLIND`: the check cannot see this bug.
The PoC only needs a `<fn>_buggy` function; `<fn>_fixed` is optional unless `--require-fixed`.
With `--check-fixed`, PoC `_buggy` → `_fixed` must additionally move in the same direction
as the seed's fix on every changed feature.
