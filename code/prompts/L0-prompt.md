# RQ4 Level L0 — Zero-Shot Compositional (single-predicate, no retry, no refine)

> **RQ4 capability-boundary point L0**: the weakest LLM configuration on
> the ablation ladder. Establishes the "zero-shot" floor — the raw LLM
> output before any of QLM's scaffolding kicks in.
>
> Reads: [`C3-prompt.md`](C3-prompt.md) is the reference full pipeline;
> this file lists only the deltas from C3.

## 0. Inputs

Identical to C3 (`seed_id, commit_sha, c_file, commit_subject, repeat_idx, out_dir`).

`out_dir` default: `$QLLLM_ROOT/experiments/rq3/d5/L0/<seed_id>-rep<N>/`
final `.ql` copied to `$QLLLM_ROOT/experiments/rq3/d5/L0/<seed_id>-rep<N>.ql`
audit → `$QLLLM_ROOT/experiments/rq3/d5/L0/<seed_id>-rep<N>.audit.json`

## 1. Ablation deltas from C3

| knob | C3 (=QLM) | **L0** |
|---|---|---|
| Compositional decomposition | ON (multiple predicates) | ON, but **`N_PRED = 1`** — the planner emits exactly one predicate + assembly |
| Per-predicate compile-repair loop | ≤ 4 iters | **0 iters** (first-compile-fail → predicate marked fail, whole gen aborts) |
| Assemble-refine loop | ≤ 4 iters | **0 iters** (first-compile-fail on final → gen aborts with status=fail) |
| POC synthesis | ON | ON (still needed as fixture) |
| verifier-v1 POC gate | ON (up to 3 regens) | ON (same; keep POC quality high — L0 ablates *query-side* scaffolding, not POC-side) |
| POC pair-wise oracle on final | ON (require fires-buggy ∧ silent-fixed) | **OFF** — L0 accepts the first compilable, POC-verifier-approved query and stops |

Everything else is inherited from C3-prompt.md verbatim (LLM model,
temperature, container commands, CodeQL CLI path, seed slice extraction,
POC synthesis prompt, plan-JSON schema, output file layout).

## 2. Pipeline (delta view)

```
Stage 1 — Features (LLM call #1)          [SAME AS C3]
Stage 2 — POC synthesis (LLM call #2)      [SAME AS C3]
Stage 2.5 — POC verifier gate (v1)         [SAME AS C3, ≤3 POC regens]
Stage 2.6 — Build POC mini-DB              [SAME AS C3]

Stage 3 — QueryPlan synthesis (LLM call #3):
  Same PLAN_PROMPT template as C3 BUT emit exactly 1 predicate + assembly.
  If plan.predicates has >1 predicate → drop all but the first;
  merge remaining logic into `assembly.where` clause.

Stage 4 — Per-predicate fill + validate:
  N_PRED = 1. For the single predicate p:
    build p.ql (with p body only)
    codeql query compile p.ql
    if compile fails → return fail(stage="predicate", predicate=p.name)
                       (NO REFINE — that's the ablation)
    codeql query run p.ql --database=poc-db
    (NO expected-output check either — that's C3's refinement)
    mark p VALIDATED (loosely)
  DO NOT retry on any error.

Stage 5 — Assemble + validate final query:
  write out_dir/final.ql = imports + p.body + assembly clause
  codeql query compile final.ql
  if fails → return fail(stage="assemble")
             (NO REFINE — ablation)
  codeql database analyze poc-db final.ql --format=csv --output=poc-result.csv
  (L0 does NOT require pair-wise oracle to pass — accept ANY successful
  compile as the L0 output. The oracle is C3-specific.)
  → status = "pass" (if compile succeeded, regardless of POC hit pattern)

Stage 6 — Outputs                         [SAME AS C3, minus preds/ dir since only 1]
```

## 3. Audit schema (`audit.json`)

Same as C3 with these constants:

```json
{
  "seed_id": "...",
  "repeat": N,
  "cell": "L0",
  "fix_sha": "...",
  "llm_calls": 3,            // features + POC + plan; exactly 3 unless verifier regen or POC fits_pattern=false
  "compile_iters": 0,        // ablation: no retries
  "poc_regens": 0..3,        // POC gate is not ablated
  "verifier_passes": bool,
  "predicate_iters": {"<p.name>": 1},  // always 1 (no retry)
  "final_compiles": bool,
  "final_runs_on_poc": bool, // recorded but not used as accept criterion
  "status": "pass" | "fail",
  "fail_stage": null | "features" | "verifier" | "predicate:<name>" | "assemble",
  "wall_seconds": float,
  "notes": "L0 = zero-shot compositional; N_PRED=1; no refine loops"
}
```

## 4. Cost expectation

Per generation (target vs cap):
- LLM calls: **3** typical (features + poc + plan). Add 0–3 for POC regen.
- Wall-time: **60–90 s** typical, ≤ 3 min cap. (No compile-repair loops
  and no assemble-refine loops = biggest time savings vs C3.)
- LLM cost: ~1/4 of C3.

Expected success_rate (paper §RQ4.2 hypothesis): **20–40%**. If L0
frequently fails, that IS the finding — "LLM cannot zero-shot
production CodeQL even for simple patterns" (§4.4 risk-mitigation
list).

## 5. Outputs (for D6 scoring)

- `experiments/rq3/d5/L0/<seed_id>-rep<N>.ql` — final query (only when status=pass)
- `experiments/rq3/d5/L0/<seed_id>-rep<N>.audit.json` — always
- `experiments/rq3/d5/d5-prep/L0/<seed_id>-rep<N>/` — full working dir
  (features.json, plan.json, poc.c, seed.c, poc.sha256, final.ql, etc.)
  — same layout as C3's `d3-prep/C3/…` for auditability.
