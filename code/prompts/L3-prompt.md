# RQ4 Level L3 — L2 + ≤3 LLM-applied surgical edits

> **RQ4 capability-boundary point L3**: adds *≤3 targeted post-hoc
> query edits* on top of a completed L2 (= C3 = full JAWS) query.
> Isolates the marginal value of a small "human-like" fix-up loop.
>
> Per §9.2 sign-off, edits are applied by **the LLM (Claude Opus)
> acting as the operator**, following a closed 6-type edit list. This
> keeps L3 reproducible and removes human subjectivity.
>
> Reads: [`C3-prompt.md`](C3-prompt.md) is the L2 baseline;
> [`§9.2 of Option A plan`](../../docs/paper/qlm-rq-refactor-plan-optionA.md#92-l3-edit-budget-n3-atomic-edits-llm-applied-not-human)
> for the sign-off spec.

## 0. Inputs

Per (seed_id, repeat_idx) L3 run, the required upstream artefacts are
**the corresponding L2 output** (= C3 output from D3):

| field | value |
|---|---|
| `seed_id`, `commit_sha`, `c_file`, `repeat_idx` | same as C3 inputs |
| `l2_query_path` | `$QLLLM_ROOT/experiments/rq3/d3/C3/<seed_id>-rep<N>.ql` |
| `l2_audit_path` | `$QLLLM_ROOT/experiments/rq3/d3/C3/<seed_id>-rep<N>.audit.json` |
| `l2_workdir` | `$QLLLM_ROOT/experiments/rq3/d3-prep/C3/<seed_id>-rep<N>/` (features.json, poc.c, plan.json, preds/, final.ql, poc-db) |
| `l2_scoring` | `experiments/rq3/d4/C3-<pattern>.json` `per_query[].kbh` for this (seed, rep) — the recall_in_db, hits, coverage |
| `out_dir` | `$QLLLM_ROOT/experiments/rq3/d5/L3/<seed_id>-rep<N>/` |

**If L2 has `status != "pass"`** (e.g. verifier fail, err-5-rep3), skip:
write `status="skipped", reason="L2_not_pass"` to L3 audit. Do NOT
attempt edits on a broken L2.

## 1. The closed 6-edit list

Per §9.2 sign-off, exactly these 6 atomic edit types are allowed. Each
edit = 1 tool-call-equivalent action. **Total edit budget: ≤ 3 per
run** (LLM may apply 0, 1, 2, or 3).

| # | Edit type | Description |
|---|---|---|
| **E1** | Add/remove `not exists(...)` filter | Add or drop a negative-quantifier subclause in the `where` clause. |
| **E2** | Add/remove function-name list entry | Extend or contract the API-name list in an acquire/release predicate. |
| **E3** | Name-check swap: `getName()` ↔ `hasGlobalName()` ↔ `matches(...)` | Change how a function name is matched (broadens or narrows). |
| **E4** | Local narrowing: `LocalVariable` ↔ `Variable` | Restrict variable class to local scope, or widen to any variable. |
| **E5** | Add/remove `getEnclosingFunction()` join | Add or drop a same-function join constraint. |
| **E6** | Regex ↔ enumerated list swap | Replace a regex match with an equivalent explicit list of names, or vice versa. |

No other transformations permitted. The LLM prompt (§3) enumerates
these 6 with example diffs.

## 2. Pipeline

```
Stage 0 — Load L2 artefacts:
  copy l2_query_path to out_dir/final-l2.ql
  read audit + scoring; record `l2_recall_in_db`, `l2_pair_wise_pass_rate`

Stage 1 — Edit-selection (LLM call #1, EDIT_PLAN_PROMPT):
  in : preamble + closed 6-edit list + final-l2.ql + poc.c + summarised
       L2 diagnostics (recall_in_db, coverage_in_db, top 3 uncovered
       bug SHAs from `experiments/rq3/d4/C3-<pattern>.json`)
  out: JSON list of up to 3 edits, each of shape
       {edit_index: 1|2|3, edit_type: "E1".."E6",
        target: "predicate:isXxx" | "assembly.where",
        before_snippet: "…",
        after_snippet: "…",
        rationale_1line: "…"}
  Constraints in prompt: must be from the closed 6-type list;
  before_snippet must appear verbatim in final-l2.ql; total edit count
  ≤ 3.
  Save to out_dir/edit_plan.json.

Stage 2 — Apply edits sequentially:
  current_ql = read final-l2.ql
  for edit in edit_plan (index order):
    apply: replace edit.before_snippet with edit.after_snippet in
    current_ql (fail-fast if before_snippet not unique / not found).
    write current_ql to out_dir/final-after-e{i}.ql
    codeql query compile out_dir/final-after-e{i}.ql
    if compile fails:
      log edit as "rejected_compile_fail" in e3-edit-log.csv;
      REVERT this edit (current_ql = pre-edit state);
      continue to next edit
    codeql database analyze poc-db out_dir/final-after-e{i}.ql
      --format=csv --output=poc-after-e{i}.csv
    compute new_pair_wise_pass_rate from POC pair-wise runs
      (buggy fires, fixed fires, fp fires — same as C3 stage 5 oracle,
      only against the POC mini-DB, not real kernel).
    log to e3-edit-log.csv row:
      (seed, repeat, edit_index, edit_type,
       before_snippet, after_snippet,
       recall_before, recall_after,       # recall_after ← from poc.csv row count for now; D6 gives real KBH recall
       pair_wise_before, pair_wise_after,
       kept: true|false)
    KEEP edit iff (pair_wise_after >= pair_wise_before) AND
                  (fires_buggy_after >= fires_buggy_before);
    otherwise REVERT (current_ql = pre-edit state) and mark kept=false.
  final_l3 = current_ql (after up to 3 kept edits)
  write out_dir/final.ql = final_l3

Stage 3 — Outputs:
  copy final.ql → experiments/rq3/d5/L3/<seed_id>-rep<N>.ql
  write audit.json (schema below) → experiments/rq3/d5/L3/<seed_id>-rep<N>.audit.json
  append per-edit rows to $QLLLM_ROOT/experiments/rq3/d5/e3-edit-log.csv
```

## 3. Prompt skeleton — `EDIT_PLAN_PROMPT` (Stage 1)

```
SYSTEM:
  You are refining an already-working CodeQL query. The base query
  passed compile, POC pair-wise oracle, and returned N hits on the
  {pattern} bug set of the {kernel_version} Linux kernel with recall
  = {l2_recall_in_db}. Your job: propose UP TO 3 atomic surgical
  edits from the closed list below, aimed at raising recall (or
  raising pair_wise precision without dropping recall).

  Closed edit list (you may only use these):
    E1: add/remove `not exists(...)` filter
    E2: add/remove function-name list entry
    E3: name-check swap getName()↔hasGlobalName()↔matches(...)
    E4: LocalVariable ↔ Variable narrowing
    E5: add/remove getEnclosingFunction() join
    E6: regex ↔ enumerated list swap

  Constraints:
    - Each edit MUST correspond to exactly one E1–E6 type.
    - Each edit has a unique before_snippet found verbatim in the
      current query.
    - Total edits ≤ 3.
    - Do not touch @-comment metadata, imports, or the from-where-select
      column list (only where clause and predicate bodies).

USER:
  == pattern ==
  {pattern}

  == kernel DB / GT summary ==
  KBH-Bench DB = {kbh_db}
  L2 recall = {l2_recall_in_db}
  L2 hits = {l2_hits}/{l2_bugs_in_db}
  Top 3 uncovered bug shortlisted from GT (SHAs + function names): {top3_uncovered}

  == POC (read-only) ==
  {contents of out_dir/poc.c}

  == current query (final-l2.ql) ==
  {contents of out_dir/final-l2.ql}

  == task ==
  Emit a JSON array of ≤ 3 edits following the schema in the SYSTEM
  message. Order edits by expected value (biggest expected recall
  lift first). If no useful edit exists, emit [].
  Output ONLY the JSON.
```

## 4. Audit schema (`audit.json`)

```json
{
  "seed_id": "...",
  "repeat": N,
  "cell": "L3",
  "fix_sha": "...",
  "l2_source_path": ".../d3/C3/<seed>-rep<N>.ql",
  "l2_recall_in_db": 0.XX,
  "l2_pair_wise_pass_rate": 0.XX,
  "edits_proposed": 0..3,
  "edits_kept": 0..3,
  "edits": [
    {"edit_index": 1, "edit_type": "E2",
     "kept": true, "compile_ok": true,
     "before_snippet": "...", "after_snippet": "...",
     "pair_wise_before": 0.XX, "pair_wise_after": 0.XX,
     "fires_buggy_before": true, "fires_buggy_after": true},
    ...
  ],
  "final_recall_in_db": null,    // will be filled by D6 scoring
  "status": "pass" | "skipped" | "fail",
  "fail_stage": null | "l2_missing" | "l2_not_pass" | "edit_plan" | "no_valid_edit",
  "wall_seconds": float,
  "notes": "L3 = L2 + ≤3 LLM-applied edits per closed 6-type list"
}
```

## 5. `e3-edit-log.csv` schema

Global CSV at `$QLLLM_ROOT/experiments/rq3/d5/e3-edit-log.csv`.
One row per edit attempt (across all L3 runs).

Columns:
`seed_id,repeat,edit_index,edit_type,target,before_snippet_hash,after_snippet_hash,recall_before,recall_after,pair_wise_before,pair_wise_after,fires_buggy_before,fires_buggy_after,compile_ok,kept,rationale`

(`*_snippet_hash` = SHA256 of the snippet body, to keep CSV size sane.
Full snippets go in per-run audit.json.)

## 6. Cost expectation

- LLM calls: **1** (EDIT_PLAN_PROMPT emits all ≤3 edits in one call).
- CodeQL calls per generation: **1 compile + 1 pair-wise analyze per
  edit** ≈ up to 3 × (1 compile + 16–30 pair analyzes). Per pair ~10 s.
- Wall-time: **10–20 min** per generation (dominated by pair-wise
  re-scoring per edit). This is the highest per-gen cost in D5.
- LLM cost: ~1/3 of C3 (only 1 LLM call vs C3's 6–10).

Expected impact (§4.3 §RQ4.2):
- If L3 recall ≈ L2 recall: paper claim "1-shot LLM edits provide
  little marginal lift on top of full JAWS pipeline — the ceiling
  has essentially been reached at L2".
- If L3 recall >> L2 recall on select patterns (e.g. err): paper
  claim "closed-list surgical edits recover a further +X pp of
  ground-truth bugs; suggests future work in edit-suggestion loops".

## 7. Outputs

- `experiments/rq3/d5/L3/<seed_id>-rep<N>.ql` — final query after
  applied edits
- `experiments/rq3/d5/L3/<seed_id>-rep<N>.audit.json`
- `experiments/rq3/d5/L3/d5-prep/<seed_id>-rep<N>/` — per-edit workdir
  (final-l2.ql, edit_plan.json, final-after-e{i}.ql, poc-after-e{i}.csv)
- `experiments/rq3/d5/e3-edit-log.csv` — append-only across all L3 runs
