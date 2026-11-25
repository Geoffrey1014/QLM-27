# KBH-Bench

KBH-Bench is the set of ground-truth Linux kernel bug-fix commits used to score
recall in RQ2–RQ4. It has **500 commits** across five patterns; **390** of them
are *in-DB*. These are the numbers in the paper's Table I (`tab:kbh_composition`).

| Pattern (paper label) | `pattern` id | KBH-Bench DB | Collected | In-DB |
|---|---|---|---:|---:|
| resource-leak (v5.15) | `four-features-Lin` | `linux-v5.15-arm-am` | 165 | 115 |
| resource-leak (v5.0) | `four-features-Lu` | `linux-v5.0-arm-am-legacy` | 53 | 45 |
| missing-check (v4.19) | `missing-check` | `linux-v4.19-arm-am-legacy` | 130 | 110 |
| delay-gfp (v4.14) | `delay-gfp` | `linux-v4.14-arm-am-legacy` | 125 | 93 |
| error-return (v5.10) | `error-return` | `linux-v5.10-arm-am` | 27 | 27 |
| **Total** | | | **500** | **390** |

## Definitions

- **Collected**: every ground-truth fix commit gathered for the pattern.
- **In-DB**: at least one C file changed by the fix is compiled into that
  pattern's CodeQL database, i.e. the file has at least one extracted function.
  A bug that is not in the database cannot be found by any query, so recall uses
  In-DB as its denominator. Most bugs that are not in-DB change code that
  `ARCH=arm64 allmodconfig` does not build: other architectures and
  platform-specific drivers.
- The bugs do not depend on the architecture. 481 of the 500 fixes are outside
  `arch/`, and none is in `arch/arm64`. In the DB names, "-arm-am" means
  `ARCH=arm64 allmodconfig`, and "-legacy" means the older toolchain
  (Ubuntu 18.04, GCC 7) that the older kernels need.
- When a query synthesized from a seed is scored, the seed's own commit is held
  out of the ground truth.

## Files

| File | Contents |
|---|---|
| `kbh-bench.csv` | One row per commit (500 rows). |
| `ground-truth/*.json` | The per-pattern ground-truth files that `code/scoring/score-cell-pattern.py` reads (`gt_file`), with the buggy hunk ranges (`file`, `func`, `buggy_start`, `buggy_count`) used for matching. |

Columns of `kbh-bench.csv`:

| Column | Meaning |
|---|---|
| `pattern` | Pattern id used by the scorer and in `data/seeds/` |
| `paper_label` | Row label in Table I |
| `kernel` | Kernel version the pattern's database is built from |
| `kbh_db` | CodeQL database name |
| `fix_sha` | Upstream fix commit (full SHA) |
| `subject` | Commit subject |
| `c_files` | C files changed by the fix (`;`-separated) |
| `in_db` | 1 if any of `c_files` is in the database, otherwise 0 |
| `in_db_files` | The changed C files that are in the database |
| `seed_id` | Seed id if this commit is one of the 25 RQ2–RQ4 seeds (`data/seeds/`), otherwise empty |
| `source` | Where the commit comes from (see below) |

All 25 seeds are KBH-Bench commits; 20 of them are in-DB.

## Provenance

- resource-leak (v5.15): bug mining by the APHP authors.
- resource-leak (v5.0): bug mining by the CRIX authors.
- missing-check (v4.19): CRIX's own `Fixes:`-tagged commits.
- delay-gfp (v4.14): Bai et al.'s DCNS static-analysis reports.
- error-return (v5.10): the 27 fixes reported by TOTE Robot (Tsinghua OSLAB,
  credited via `Reported-by:`) between March and October 2021.

## Recomputing In-DB

`in_db` was computed against the list of files with extracted functions in each
KBH-Bench database. That list is not shipped because it is about 30 MB per
database. To recompute it after rebuilding a database, export every function's
file and check each commit's `c_files` against that set:

```ql
import cpp
from Function f
where f.hasDefinition()
select f.getFile().getRelativePath() as file, f.getName() as fname
```
