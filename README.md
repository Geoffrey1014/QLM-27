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

## Linux kernel findings (RQ1)

QLM-synthesized queries found **49 previously unknown bugs** in mainline Linux (v6.19-rc), status as of 2026-11-20. Reports from different queries were deduplicated by source location, so each bug is counted once; one function can hold several bugs (e.g. two separate leaks). Lifetime is measured from the commit that introduced the bug (found with `git blame`, the patch's `Fixes:` tag) to our fix. The full list is also in [`data/rq1-findings.csv`](data/rq1-findings.csv).

| Status | Bugs |
|---|---:|
| Fixed — our patch merged upstream | 17 |
| Confirmed by maintainer | 5 |
| Fixed upstream by another developer | 10 |
| Patch under LKML review | 11 |
| Pending — patch prepared, not yet sent | 6 |
| **Total** | **49** |

The 32 bugs that are fixed or confirmed had persisted for a median of 8.3 years (up to 15.3).

| Bug type | Bugs |
|---|---:|
| Refcount leak | 27 |
| Unbounded buffer accumulation | 5 |
| Integer overflow | 5 |
| Out-of-bounds index | 4 |
| Memory leak | 2 |
| sysfs buffer overflow | 2 |
| ERR_PTR dereference | 2 |
| Sleep in atomic context | 1 |
| Out-of-bounds read | 1 |

### Fixed — our patch merged upstream (17)

| No. | File | Function | Bug type | Introduced | Lifetime (y) |
|---:|---|---|---|---:|---:|
| 1 | `drivers/video/of_display_timing.c` | `of_get_display_timings` | Refcount leak | 2012 | 13.3 |
| 2 | `arch/arm/mach-imx/src.c` | `imx_src_init` | Refcount leak | 2013 | 13.3 |
| 3 | `arch/arm/mach-imx/src.c` | `imx7_src_init` (first lookup) | Refcount leak | 2021 | 5.1 |
| 4 | `arch/arm/mach-imx/src.c` | `imx7_src_init` (second lookup) | Refcount leak | 2021 | 5.1 |
| 5 | `scripts/tracepoint-update.c` | `add_string` | Memory leak | 2025 | 0.3 |
| 6 | `drivers/greybus/gb-beagleplay.c` | `hdlc_tx_frames` | Sleep in atomic context | 2023 | 2.7 |
| 7 | `drivers/media/cec/platform/stm32/stm32-cec.c` | `stm32_rx_done` | Out-of-bounds index | 2017 | 9.0 |
| 8 | `drivers/mtd/parsers/ofpart_core.c` | `parse_fixed_partitions` | Refcount leak | 2021 | 4.7 |
| 9 | `drivers/of/base.c` | `of_alias_scan` | Refcount leak | 2011 | 14.4 |
| 10 | `drivers/pinctrl/pinctrl-single.c` | `pcs_add_gpio_func` | Refcount leak | 2012 | 13.5 |
| 11 | `drivers/soc/samsung/exynos-pmu.c` | `exynos_get_pmu_regmap` | Refcount leak | 2017 | 9.4 |
| 27 | `arch/arm/mach-versatile/platsmp-vexpress.c` | `vexpress_smp_dt_prepare_cpus` | Refcount leak | 2013 | 13.0 |
| 28 | `arch/arm/mach-versatile/v2m.c` | `vexpress_flags_set` | Refcount leak | 2014 | 12.4 |
| 33 | `drivers/media/rc/fintek-cir.c` | `fintek_get_rx_ir_data` | Unbounded buffer accumulation | 2011 | 15.3 |
| 34 | `drivers/mtd/parsers/qcomsmempart.c` | `parse_qcomsmem_part` (offset) | Integer overflow | 2021 | 5.7 |
| 35 | `drivers/mtd/parsers/qcomsmempart.c` | `parse_qcomsmem_part` (size) | Integer overflow | 2021 | 5.7 |
| 42 | `drivers/thermal/sprd_thermal.c` | `sprd_thm_probe` | Out-of-bounds index | 2020 | 6.6 |

### Confirmed by maintainer (5)

| No. | File | Function | Bug type | Introduced | Lifetime (y) |
|---:|---|---|---|---:|---:|
| 21 | `arch/arm/mach-mstar/mstarv7.c` | `mstarv7_boot_secondary` | Refcount leak | 2020 | 5.5 |
| 22 | `arch/arm/mach-mstar/mstarv7.c` | `mstarv7_init` | Refcount leak | 2020 | 5.9 |
| 23 | `drivers/bus/ti-sysc.c` | `sysc_init_static_data` | Refcount leak | 2017 | 8.3 |
| 24 | `drivers/bus/vexpress-config.c` | `vexpress_syscfg_probe` | Refcount leak | 2020 | 6.2 |
| 25 | `tools/objtool/elf.c` | `elf_alloc_reloc` | Memory leak | 2016 | 9.9 |

### Fixed upstream by another developer (10)

| No. | File | Function | Bug type | Introduced | Lifetime (y) |
|---:|---|---|---|---:|---:|
| 12 | `drivers/thermal/thermal_of.c` | `thermal_of_cm_lookup` | Refcount leak | 2025 | 0.9 |
| 13 | `arch/arm/mach-imx/avic.c` | `mxc_init_irq` (fsl,avic node) | Refcount leak | 2012 | 14.0 |
| 14 | `drivers/memory/emif.c` | `of_get_memory_device_details` | Refcount leak | 2012 | 13.8 |
| 15 | `drivers/bus/ti-sysc.c` | `sysc_init_stdout_path` | Refcount leak | 2017 | 8.3 |
| 16 | `arch/arm/mach-imx/avic.c` | `mxc_init_irq` (fsl,imx25-ccm node) | Refcount leak | 2018 | 8.3 |
| 17 | `arch/arm/mach-tegra/irq.c` | `tegra_init_irq` | Refcount leak | 2015 | 11.2 |
| 18 | `arch/arm/mach-tegra/irq.c` | `tegra114_gic_cpu_pm_registration` | Refcount leak | 2013 | 12.9 |
| 19 | `drivers/platform/chrome/cros_ec_typec.c` | `cros_typec_register_partner_pdos` (sink caps) | Unbounded buffer accumulation | 2022 | 3.8 |
| 20 | `drivers/platform/chrome/cros_ec_typec.c` | `cros_typec_register_partner_pdos` (source caps) | Unbounded buffer accumulation | 2022 | 3.8 |
| 43 | `drivers/iio/imu/bno055/bno055.c` | `BNO055_SCAN_CH_COUNT` | Unbounded buffer accumulation | 2022 | 3.4 |

### Patch under LKML review (11)

| No. | File | Function | Bug type | Introduced | Lifetime (y) |
|---:|---|---|---|---:|---:|
| 26 | `arch/arm/mach-alpine/alpine_cpu_pm.c` | `alpine_cpu_pm_init` | Refcount leak | 2015 | 11.5 |
| 29 | `drivers/bus/ti-sysc.c` | `sysc_exit` (module unload) | Refcount leak | 2017 | 8.3 |
| 30 | `drivers/firmware/trusted_foundations.c` | `of_register_trusted_foundations` | Refcount leak | 2013 | 12.6 |
| 31 | `drivers/iio/adc/xilinx-ams.c` | `ams_init_module` | Unbounded buffer accumulation | 2021 | 4.8 |
| 32 | `drivers/mailbox/omap-mailbox.c` | `omap_mbox_probe` | Refcount leak | 2014 | 11.3 |
| 36 | `drivers/net/ethernet/freescale/fman/fman.c` | `fman_set_port_params` (LIODN tables) | Out-of-bounds index | 2015 | 10.8 |
| 37 | `drivers/net/ethernet/freescale/fman/fman.c` | `fman_set_port_params` (MAC tables) | Out-of-bounds index | 2015 | 10.8 |
| 38 | `drivers/soc/dove/pmu.c` | `dove_init_pmu` (domains_node) | Refcount leak | 2015 | 10.9 |
| 39 | `drivers/soc/dove/pmu.c` | `dove_init_pmu` (np_pmu) | Refcount leak | 2015 | 10.9 |
| 40 | `drivers/soundwire/master.c` | `clock_frequencies_show` | sysfs buffer overflow | 2020 | 6.4 |
| 41 | `drivers/soundwire/master.c` | `clock_gears_show` | sysfs buffer overflow | 2020 | 6.4 |

### Pending — patch prepared, not yet sent (6)

| No. | File | Function | Bug type | Introduced | Lifetime (y) |
|---:|---|---|---|---:|---:|
| 44 | `drivers/mtd/nand/raw/diskonchip.c` | `inftl_partscan` (offset) | Integer overflow | 2005 | 21.4 |
| 45 | `drivers/mtd/nand/raw/diskonchip.c` | `inftl_partscan` (size) | Integer overflow | 2005 | 21.4 |
| 46 | `drivers/mtd/nand/raw/diskonchip.c` | `nftl_partscan` (size) | Integer overflow | 2005 | 21.5 |
| 47 | `drivers/mtd/nand/raw/nand_toshiba.c` | `toshiba_nand_benand_read_eccstatus_op` | ERR_PTR dereference | 2020 | 6.5 |
| 48 | `drivers/thermal/ti-soc-thermal/ti-thermal-common.c` | `ti_thermal_report_sensor_temperature` | ERR_PTR dereference | 2012 | 14.2 |
| 49 | `sound/usb/midi.c` | `find_usb_ijack` | Out-of-bounds read | 2024 | 2.6 |

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
- **RQ1 findings** — the 49 Linux kernel bugs, as a CSV.
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
│   ├── rq1-findings.csv       # the 49 Linux kernel bugs found in RQ1
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
