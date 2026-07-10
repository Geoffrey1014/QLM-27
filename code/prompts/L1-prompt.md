# RQ4 Level L1 — Compile Self-Fix (compositional, POC oracle off)

> **RQ4 capability-boundary point L1**: adds *compile-repair loop* on
> top of L0. Isolates the marginal value of "let the LLM fix its own
> compile errors" vs pure zero-shot.
>
> Reads: [`L0-prompt.md`](L0-prompt.md) is the direct ancestor;
> [`C3-prompt.md`](C3-prompt.md) is the full pipeline spec.

## 0. Inputs

Identical to C3/L0. `out_dir` default:
`$QLLLM_ROOT/experiments/rq3/d5/L1/<seed_id>-rep<N>/`

## 1. Ablation deltas from C3

| knob | C3 (=QLM) | **L1** |
|---|---|---|
| N_PRED cap | ≤ 5 | **≤ 2** (planner may emit 1 or 2 predicates; more collapse into assembly) |
| Per-predicate compile-repair loop | ≤ 4 iters | **≤ 2 iters** |
| Per-predicate POC-run validation | ON (expected_on_poc check) | **OFF** — after compile passes, mark predicate validated regardless of POC hits |
| Assemble compile-repair loop | ≤ 4 iters | **≤ 2 iters** |
| POC pair-wise oracle on final (buggy_fires ∧ !fixed_fires ∧ !fp_fires) | ON (accept iff pair-wise passes) | **OFF** — accept any successfully compiled final query as L1 output |
| POC synthesis + verifier-v1 gate | ON | ON (unchanged — L1 ablates *query-side* validation, not POC-side) |

Everything else — model, temperature, container commands, POC synthesis
prompt, plan schema, output layout — inherited from C3-prompt.md.

## 2. Pipeline (delta view)

```
Stage 1–2.6                                [SAME AS C3]

Stage 3 — QueryPlan synthesis (LLM call #3):
  Same PLAN_PROMPT as C3 BUT emit ≤ 2 predicates + assembly.
  If plan.predicates has >2 → keep first 2, fold rest into assembly.

Stage 4 — Per-predicate fill + validate:
  For predicate p in topo order:
    for iter in 1..2:                       # L1 cap = 2 (was 4 in C3)
      build p.ql with p body + transitive deps
      codeql query compile p.ql
      if compile ok:
        (SKIP the C3 "run on poc-db + compare to expected_on_poc" step)
        mark p VALIDATED; break
      else:
        REFINE_PRED_PROMPT(p, deps, stderr, poc.c)   # same as C3
    else:                                             # 2 iters exhausted
      return fail(stage="predicate", predicate=p.name)

Stage 5 — Assemble + validate final query:
  for iter in 1..2:                         # L1 cap = 2 (was 4)
    write out_dir/final.ql = imports + predicates + assembly
    codeql query compile final.ql
    if fails:
      ASSEMBLE_REFINE_PROMPT(final.ql, stderr, poc.c)   # same as C3
      continue
    codeql database analyze poc-db final.ql --format=csv --output=poc-result.csv
    (L1 does NOT gate on pair-wise oracle — accept as long as compile
    passes and analyze completes. The oracle is C2/C3 territory.)
    break
  else:
    return fail(stage="assemble")

Stage 6                                     [SAME AS C3, up to 2 predicates in preds/ dir]
```

## 3. Audit schema (`audit.json`)

Same as C3 with:
- `cell: "L1"`
- `compile_iters`: sum across predicate+assemble compile attempts, ≤ 4 total (2×preds + 2×assemble worst case)
- `predicate_iters`: per-predicate count, ≤ 2 each
- `final_runs_on_poc`: recorded but not used as accept criterion (like L0)
- `notes: "L1 = compositional + compile self-fix; POC-run oracle OFF"`

## 4. Cost expectation

- LLM calls: **3–7** (features + poc + plan + up to 2 refines/predicate × 2 preds + up to 2 assemble refines).
- Wall-time: **120–200 s** typical, ≤ 5 min cap.
- LLM cost: ~1/2 of C3.

Expected success_rate: **50–70%**. If L1 is close to L2/C3 recall,
this suggests **most of C3's uplift over L0 comes from just "let the
LLM see its compile errors"** — that would be a clean paper finding
(reviewer-favorable: shows even a small refinement loop provides
outsized gains).

## 5. Outputs

Same as L0 but under `experiments/rq3/d5/L1/`.
