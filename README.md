# JAWS Artifact

Reproduction package for the paper *"JAWS: Compositional CodeQL Query
Synthesis from Bug-Fix Seed Patches"* (submission version).

This artifact contains:
- **The prompts** used to invoke the LLM for each cell of the ablation
  (C0–C3) and each level of the RQ4 ablation ladder (L0/L1/L3).
- **The generated CodeQL queries** for every (cell × seed × repeat)
  combination in the paper (500 queries for RQ2/RQ3, plus 125 L0 +
  partial L1 for the RQ4 synthesis-cost side notes).
- **The scoring aggregates** from D4 — one JSON per (cell, pattern)
  combination, with per-query and pattern-aggregate metrics.
- **The pipeline scripts**: the batched scoring driver, the per-query
  scorer, and the seed↔PoC consistency verifier.

## Directory layout

```
jaws-artifact/
├── README.md                  # this file
├── data/
│   ├── seeds/                 # 25 seeds × 5 patterns (metadata)
│   │   ├── seeds.json
│   │   └── seeds.csv
│   ├── generated-queries/     # LLM-generated CodeQL queries
│   │   ├── C0/  (125 .ql + 125 .audit.json)   # KNighter baseline
│   │   ├── C1/  (120 .ql + 121 .audit.json)   # mono + PoC
│   │   ├── C2/  (125 .ql + 125 .audit.json)   # compositional
│   │   ├── C3/  (124 .ql + 125 .audit.json)   # JAWS (full)
│   │   ├── L0/  (123 .ql + 125 .audit.json)   # RQ4 zero-shot
│   │   └── L1/  (partial audits, synthesis-side only)
│   └── scoring/               # D4 aggregate metrics
│       ├── C0-<pattern>.json  # 5 patterns
│       ├── C1-<pattern>.json
│       ├── C2-<pattern>.json
│       ├── C3-<pattern>.json
│       └── run-summary.json   # top-level 20-cell matrix
└── code/
    ├── prompts/               # LLM prompt templates (Markdown)
    │   ├── C0-prompt.md       # RQ2/RQ3 cells
    │   ├── C1-prompt.md
    │   ├── C2-prompt.md
    │   ├── C3-prompt.md       # = JAWS full pipeline
    │   ├── L0-prompt.md       # RQ4 zero-shot compositional
    │   ├── L1-prompt.md       # RQ4 mono + compile self-fix
    │   └── L3-prompt.md       # RQ4 closed-list surgical edits (future work)
    ├── scoring/
    │   ├── score-cell-pattern.py     # per (cell, pattern) scorer
    │   ├── run-d4-batched.sh         # per-pattern-serial × 5-parallel driver
    │   ├── orphan-watchdog.sh        # subprocess-lifecycle safety net
    │   └── recover-from-workdir.py   # partial-recovery aggregator
    └── verifier/
        ├── verifier-v1.ql            # seed↔PoC structural consistency
        ├── run-verifier.sh           # CLI wrapper
        └── calibration-report.md     # v1 calibration test suite
```

## Path convention in this artifact

All script paths use `<REPO_ROOT>` as the placeholder for the local
repository root, and `<HOME_DIR>` as the placeholder for the user's
home directory. When you re-run any script, replace these tokens (or
export equivalent shell variables) with your local paths.

## What is *not* in this artifact (and why)

- **Full per-generation working directories.** Every generation
  spawns a workdir under `experiments/rq3/d3-prep/<cell>/<seed>-rep<N>/`
  containing intermediate files: the extracted seed slice, the PoC
  source, the PoC mini-DB (`poc-db/`), per-predicate `.ql` files, and
  stage-by-stage audit logs. These are ~2 GB in aggregate and are
  reproducible from the artifact's prompts + seeds; we exclude them
  to keep the artifact under 10 MB.
- **The KBH-Bench CodeQL databases.** Five kernel CodeQL databases
  (linux-v4.14/v4.19/v5.0/v5.10/v5.15 built with CodeQL 2.23.0 or
  2.25.6, ARM `allmodconfig` builds) are ~40 GB in aggregate. Build
  scripts and configuration are documented in the paper's
  supplementary material; database blobs must be regenerated locally
  (see `code/scoring/score-cell-pattern.py::PATTERN_CONFIG` for
  expected paths).
- **The 126 pair-wise mini-databases.** These are built per seed
  from the buggy and fixed versions of each seed's touched
  function, using `codeql database create --language=cpp
  --command="gcc -O0 -w -c <slice>.c"`. Total ~1 GB; regeneration
  script is provided in the paper's supplementary material.
- **The Linux kernel source tree.** Any recent Linux tag (v6.19-rc5
  in our runs) suffices; build databases against the same tag used
  when scoring.

## How to re-run the pipeline

Prerequisites:
- Docker + docker-compose (the pipeline runs inside a container image
  with GCC, Java 17, Python 3, and CodeQL CLI installed).
- CodeQL CLI 2.25.6 (2.23.0 for legacy databases; see the paper's
  supplementary material for the CLI-vs-DB version matrix).
- Access to an LLM API endpoint compatible with the `claude-opus-4`
  series (temperature 0.2, max_tokens 8192).

Reproduction steps:

```bash
# 1. Rebuild the ground-truth CodeQL databases from your local Linux
#    tree at tag v6.19-rc5. See the paper for the KCFLAGS / EDG
#    workarounds required for full extractor coverage.
codeql database create <REPO_ROOT>/codeql-dbs/linux-<version>-arm-am \
  --language=cpp --command="make -j$(nproc) ARCH=arm allmodconfig ..."

# 2. Regenerate the 126 pair-wise mini-DBs (script in supplementary).

# 3. Regenerate the 500 LLM queries.
#    For each (cell, seed, repeat) triple, invoke the LLM with the
#    corresponding <cell>-prompt.md file substituted with the seed
#    metadata from data/seeds/seeds.json. The prompt files include
#    the exact stage-by-stage protocol (features → PoC → plan →
#    per-predicate validation → assembly).

# 4. Run the scorer.
tmux new-window -n d4 'bash code/scoring/run-d4-batched.sh'
tmux new-window -n watchdog 'bash code/scoring/orphan-watchdog.sh'
# Wall time ~13 h on a 20-core machine.

# 5. Aggregate metrics.
#    The scorer writes data/scoring/<cell>-<pattern>.json; the paper's
#    Tables 2–4 are built from these.
```

## Contents check summary

| category | count | size |
|---|---|---|
| seeds metadata | 2 files | <10 KB |
| generated queries (all cells + levels) | ~1,300 files | ~5 MB |
| D4 scoring aggregates | 20+1 files | ~2 MB |
| prompts + scripts + verifier | ~15 files | ~200 KB |
| **total** | **~1,400 files** | **~8 MB** |

## Licence

Code and prompts in this artifact are released under the same licence
as the paper (see the accompanying LICENCE file when the artifact is
released publicly). Bug-fix commit metadata (seed SHAs, subjects,
file paths) is derived from public upstream Linux kernel commits and
is available in `data/seeds/seeds.json`.
