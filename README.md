# QLM 
## Abstract

Automating the synthesis of CodeQL vulnerability detectors from bug-fix patches is an
appealing alternative to manual query authoring, but using LLM to generate queries in a
single monolithic pass frequently compiles yet fails to generalize beyond the seed
instance. We present QLM, a compositional synthesis framework that tackles this problem
along two axes. First, QLM constructs a minimal Proof-of-Concept (PoC) program from each
patch and gates it through a deterministic structural verifier that checks feature counts
against the original bug-relevant slice, producing a faithful oracle for the synthesis
loop. Second, a top-down planner decomposes each query into atomic predicates whose
correctness is validated individually against the PoC before the full query is
assembled. Predicates that miss known-buggy cases or fire on safe cases are rejected and
refined with targeted diagnostic feedback. On the Linux kernel, QLM discovered 49
previously unknown vulnerabilities, of which 5 have been confirmed by maintainers and 17
merged upstream, while another 10 were fixed by other developers; these 32 already fixed
or confirmed bugs had persisted undetected for a median of 8.3 years (up to 15.3 years).
On KBH-Bench, a new benchmark of 500 ground-truth kernel bug-fix commits, QLM raises
normalized recall 2.6× over a monolithic baseline (5.6% → 14.8%) and doubles
analyze-survival on the full kernel database (46% → 92%).

## Overview

![Overview of QLM](figures/overview.png)

Given a seed bug-fix patch, QLM first extracts a bug schema that captures the semantic
obligation restored by the patch. It then synthesizes a compact PoC containing buggy and
safe cases, checks it against the seed with a structural fidelity check, and compiles it into a lightweight CodeQL database.
Top-down query planning translates the schema into a query skeleton and a set of
predicate specifications; the predicates are then generated bottom-up, each validated by
compilation and PoC execution, and assembled into the final query, which is run on the
full codebase.

QLM synthesizes CodeQL queries that detect a bug pattern, using a
single bug-fix commit (the *seed*) as the specification. This artifact
lets you inspect the exact prompts, the queries the LLM produced, and
the scoring metrics behind the paper's tables — and gives you the
scripts to re-run the scoring pipeline once the (large, regenerable)
CodeQL databases are rebuilt locally.

## What's in here

- **Prompts** — the LLM prompt template for every ablation cell
  (C0–C3) and every level of the RQ4 ablation ladder (L0/L1/L3).
- **Generated queries** — the CodeQL queries the LLM produced for each
  *(cell × seed × repeat)* combination in the paper, each paired with a
  stage-by-stage `*.audit.json` log.
- **Scoring aggregates** — the D4 output, one JSON per *(cell,
  pattern)*, plus a top-level 20-cell run summary. The paper's Tables
  2–4 are computed from these.
- **Pipeline scripts** — the batched scoring driver, the per-query
  scorer, and the seed↔PoC consistency verifier.
- **Seed metadata** — the 25 seeds (5 patterns × 5 seeds), as JSON and
  CSV.

## Directory layout

```
qlm-artifact/
├── README.md                  # this file
├── canonical-queries/         # reserved for hand-written reference
│                              #   queries (empty in this release)
├── figures/
│   └── overview.png           # QLM workflow (paper Fig. overview)
├── data/
│   ├── seeds/                 # 25 seeds × 5 patterns (metadata only)
│   │   ├── seeds.json
│   │   └── seeds.csv
│   ├── generated-queries/     # LLM-generated CodeQL queries + audit logs
│   │   ├── C0/  (125 .ql + 125 .audit.json)   # KNighter-style baseline
│   │   ├── C1/  (120 .ql + 121 .audit.json)   # monolithic + PoC
│   │   ├── C2/  (125 .ql + 125 .audit.json)   # compositional
│   │   ├── C3/  (124 .ql + 125 .audit.json)   # QLM (full pipeline)
│   │   ├── L0/  (123 .ql + 125 .audit.json)   # RQ4 zero-shot
│   │   └── L1/  ( 63 .ql +  63 .audit.json)   # RQ4 mono + compile self-fix
│   ├── schemas/               # bug schema definition + 125 C3 schema instances
│   │   ├── README.md
│   │   └── instances/  (125 .json)
│   └── scoring/               # D4 aggregate metrics
│       ├── C{0,1,2,3}-<pattern>.json          # 4 cells × 5 patterns = 20
│       └── run-summary.json                   # top-level 20-cell matrix
└── code/
    ├── prompts/               # LLM prompt templates (Markdown)
    │   ├── C0-prompt.md       # RQ2/RQ3 cells
    │   ├── C1-prompt.md
    │   ├── C2-prompt.md
    │   ├── C3-prompt.md       # = QLM full pipeline
    │   ├── L0-prompt.md       # RQ4 zero-shot compositional
    │   ├── L1-prompt.md       # RQ4 monolithic + compile self-fix
    │   └── L3-prompt.md       # RQ4 closed-list surgical edits (future work)
    ├── scoring/
    │   ├── score-cell-pattern.py     # per (cell, pattern) scorer
    │   ├── run-d4-batched.sh         # pattern-serial × 5-parallel driver
    │   ├── orphan-watchdog.sh        # subprocess-lifecycle safety net
    │   └── recover-from-workdir.py   # partial-recovery aggregator
    └── verifier/                     # seed↔PoC structural fidelity check (see its README)
        ├── verifier.py               # API derivation + verdict rules
        ├── run_verifier.py           # CLI entry point
        ├── ql/                       # CodeQL feature-count query
        └── seeds/                    # 25 verbatim seed slices + fix patches
```

> **Note on file counts.** A handful of *(cell × seed × repeat)* slots
> are missing a `.ql` or `.audit.json` because the corresponding
> generation hit an iteration cap or a transient LLM/API error and was
> not retried. Every `.audit.json` records the outcome, so the missing
> slots are visible as gaps in the audit set and are reflected in the
> per-cell `n_queries` fields in the scoring JSON. L1 is a
> synthesis-cost side experiment and was only run to partial depth.

## The five bug patterns

Each seed belongs to one of five patterns; the seed↔pattern mapping is
in [`data/seeds/seeds.json`](data/seeds/seeds.json) (and `.csv`).

| pattern             | seed prefix | description                                   |
|---------------------|-------------|-----------------------------------------------|
| `four-features-Lin` | `lin-*`     | reference-count / device-node leaks           |
| `four-features-Lu`  | `lu-*`      | memory leaks on error paths                   |
| `missing-check`     | `mc-*`      | missing return-value / validity checks        |
| `delay-gfp`         | `dg-*`      | sleeping allocation (`GFP_KERNEL`) in atomic  |
| `error-return`      | `er-*`      | incorrect / missing error-code propagation    |

## The ablation cells

Cells sweep two axes — *compositional* synthesis and *PoC*
(proof-of-concept) grounding:

| cell | compositional | PoC | description                                 |
|------|:-------------:|:---:|---------------------------------------------|
| C0   | off           | off | KNighter-style monolithic baseline          |
| C1   | off           | on  | monolithic generation grounded on a PoC     |
| C2   | on            | off | compositional, no PoC                       |
| C3   | on            | on  | **QLM** — the full pipeline                 |

The RQ4 ladder (L0/L1/L3) probes synthesis cost at lower levels of the
compositional pipeline; L3 (closed-list surgical edits) is described as
future work and ships as a prompt only.

## Scoring metrics

Each scoring JSON reports both per-query and pattern-aggregate metrics.
The key fields (see [`data/scoring/run-summary.json`](data/scoring/run-summary.json)):

- **`pair_wise`** — over the seed's held-out buggy/fixed function
  pairs, the query *fires on buggy AND stays silent on fixed*. The
  headline correctness signal.
- **`recall_in_db`** — of the known ground-truth bug sites in the
  KBH-Bench CodeQL database, the fraction the query flags.
- **`fires_buggy_rate`** — the query fires on the buggy version of a
  pair (ignoring the fixed-version check).
- `*_mean` / `*_best` — averaged across the repeats of a seed vs. the
  single best repeat.

## Path convention

All script paths use `<REPO_ROOT>` for the local repository root and
`<HOME_DIR>` for the user's home directory. When you re-run a script,
replace these tokens (or export equivalent shell variables) with your
local paths.

## What is *not* in this artifact (and why)

- **Full per-generation working directories.** Each generation spawns a
  workdir under `experiments/rq3/d3-prep/<cell>/<seed>-rep<N>/`
  containing the extracted seed slice, PoC source, PoC mini-DB
  (`poc-db/`), per-predicate `.ql` files, and stage-by-stage logs.
  These are ~2 GB in aggregate and are reproducible from the prompts +
  seeds; excluded to keep the artifact small.
- **The KBH-Bench CodeQL databases.** Five kernel databases
  (linux-v4.14 / v4.19 / v5.0 / v5.10 / v5.15, built with CodeQL 2.23.0
  or 2.25.6, ARM `allmodconfig`) total ~40 GB. Expected paths are in
  [`code/scoring/score-cell-pattern.py`](code/scoring/score-cell-pattern.py)
  (`PATTERN_CONFIG`); build scripts are in the paper's supplementary
  material.
- **The 126 pair-wise mini-databases.** Built per seed from the buggy
  and fixed versions of each touched function via `codeql database
  create --language=cpp --command="gcc -O0 -w -c <slice>.c"`. Total
  ~1 GB; regeneration script is in the supplementary material.
- **The Linux kernel source tree.** Any recent tag (v6.19-rc5 in our
  runs) suffices; build databases against the same tag used for scoring.

## How to re-run the scoring pipeline

**Prerequisites**

- Docker + docker-compose (the pipeline runs in a container with GCC,
  Java 17, Python 3, and the CodeQL CLI).
- CodeQL CLI 2.25.6 (2.23.0 for the legacy databases; see the
  supplementary material for the CLI-vs-DB version matrix).
- An LLM API endpoint compatible with the `claude-opus-4` series
  (temperature 0.2, max_tokens 8192) — only needed to regenerate
  queries, not to re-score the ones already shipped here.

**Steps**

```bash
# 1. Rebuild the ground-truth CodeQL databases from your local Linux
#    tree at tag v6.19-rc5. See the paper for the KCFLAGS / EDG
#    workarounds required for full extractor coverage.
codeql database create <REPO_ROOT>/codeql-dbs/linux-<version>-arm-am \
  --language=cpp --command="make -j$(nproc) ARCH=arm allmodconfig ..."

# 2. Regenerate the 126 pair-wise mini-DBs (script in supplementary).

# 3. (Optional) Regenerate the LLM queries.
#    For each (cell, seed, repeat) triple, invoke the LLM with the
#    corresponding code/prompts/<cell>-prompt.md, substituting the seed
#    metadata from data/seeds/seeds.json. The prompt files encode the
#    exact stage-by-stage protocol (features -> PoC -> plan ->
#    per-predicate validation -> assembly). Skip this to score the
#    queries already in data/generated-queries/.

# 4. Run the scorer.
tmux new-window -n d4       'bash code/scoring/run-d4-batched.sh'
tmux new-window -n watchdog 'bash code/scoring/orphan-watchdog.sh'
# Wall time ~13 h on a 20-core machine.

# 5. Read the aggregates.
#    The scorer writes data/scoring/<cell>-<pattern>.json; the paper's
#    Tables 2-4 are built from these plus run-summary.json.
```

## Contents check summary

| category                                   | count        | size    |
|--------------------------------------------|--------------|---------|
| seeds metadata                             | 2 files      | <10 KB  |
| generated queries + audit logs (all cells) | ~1,300 files | ~5 MB   |
| D4 scoring aggregates                       | 20 + 1 files | ~2 MB   |
| prompts + scripts + verifier (incl. seed slices) | ~120 files | ~800 KB |
| **total**                                  | **~1,400 files** | **~8 MB** |

## Licence

Code and prompts in this artifact are released under the licence in the
accompanying `LICENCE` file (added when the artifact is released
publicly). Bug-fix commit metadata (seed SHAs, subjects, file paths) is
derived from public upstream Linux kernel commits and is available in
[`data/seeds/seeds.json`](data/seeds/seeds.json).
