# qlm — QLM generation pipeline

Runs one generation per (cell, seed, repeat): seed fix commit → CodeQL query + `audit.json`.
Cells C0–C3 are the 2×2 of compositional × PoC (`pipeline.py`). The LLM only writes text
(features, PoC, plan, predicate bodies, queries); code does the rest: function extraction,
seed slices, gcc, CodeQL databases, the structural fidelity check, compilation, running on
the PoC, oracle checks and iteration caps.

## Requirements

- Python ≥ 3.10, gcc, CodeQL CLI (tested with 2.25.6)
- a Linux git tree that contains the seed commits (`data/seeds/seeds.json`)
- an LLM backend: the `claude` CLI (default), or the `anthropic` package plus `ANTHROPIC_API_KEY`

## Usage

```bash
export QLM_CODEQL=/path/to/codeql        # default: `codeql` on PATH
export QLM_LINUX=/path/to/linux          # default: <repo>/linux
(cd code/qlm/ql && $QLM_CODEQL pack install)   # once: fetch codeql/cpp-all

cd code
python3 -m qlm run    --cell C3 --seed lin-1 --repeat 1
python3 -m qlm batch  --cells C0,C1,C2,C3 --repeats 5 --jobs 4
python3 -m qlm verify --seed lin-1 --poc path/to/poc.c --work /tmp/v
```

Optional: `--backend cli|api`, `--seeds <file>`, `--out <dir>` (default `<repo>/out`);
`QLM_MODEL`, `QLM_TEMPERATURE` (API backend only), `QLM_MAX_TOKENS`.

## Outputs

`<out>/<cell>/<seed>-rep<N>/` holds the full run (`features.json`, `poc.c`, `plan.json`,
`preds/`, `final.ql`, `audit.json`, `llm-trace/`). Flat copies
`<out>/<cell>/<seed>-rep<N>.ql` / `.audit.json` use the layout `code/scoring/` reads.

## Modules

| module | role |
|---|---|
| `pipeline.py` | cells C0–C3 and their stages |
| `prompts.py` | prompt templates |
| `kernel.py` | git access; finds the function(s) a fix touches |
| `seed.py` | seed slices: touched functions verbatim, plus an LLM-written declarations-only preamble |
| `verifier.py`, `ql/verifier/` | structural fidelity check (same rules as `code/verifier/`) |
| `oracle.py`, `ql/oracle/` | attributes query results to PoC functions; expectation and final oracle |
| `codeql.py`, `llm.py`, `config.py` | CodeQL CLI wrappers, LLM backend, paths and caps |
