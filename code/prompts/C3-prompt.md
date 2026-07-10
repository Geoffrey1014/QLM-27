# RQ3 Cell C3 — Full QLM pipeline (compositional ON + POC ON)

> Loaded by D3-main per-generation agents. One invocation = one (seed × repeat)
> pair. Output: a final `.ql` file + audit log JSON.

## Cell knob settings (binding)

| knob | value |
|---|---|
| compositional | **ON** (predicate decomposition + per-predicate validation) |
| POC | **ON** (POC.c generated, verifier-v1 gated, mini-DB built) |
| compile-repair iterations per predicate | ≤ 4 |
| assembly-repair iterations | ≤ 4 |
| POC regeneration rounds | ≤ 3 |
| LLM | `claude-opus-4-7`, temperature 0.2 |

## Inputs

```
seed_id     e.g. lin-1
fix_sha     e.g. 74139a64e8ce
c_file      e.g. arch/arm/mach-omap2/pm33xx-core.c
subject     commit subject line (sanity check only)
pattern     four-features-Lin | four-features-Lu | missing-check | delay-gfp | error-return-code
out_dir     experiments/rq3/d3-prep/C3/<seed_id>-rep<N>/
```

## Common environment

| name | value |
|---|---|
| container exec | `docker compose exec -T qlllm bash -c '<cmd>'` (from `$ENV_ROOT`) |
| CodeQL CLI | `<REPO_ROOT>/codeql-2.25.6/codeql` |
| Linux source | `<REPO_ROOT>/linux` (container path) |
| verifier-v1 script | `<REPO_ROOT>/scripts/verifier/run-verifier.sh` |
| verifier-v1 query | `<REPO_ROOT>/scripts/verifier/verifier-v1.ql` |

Host paths for the same tree are under `<REPO_ROOT>/...`; the
two are bind-mounted so the agent may write on the host and read from the container.

## Stage 1 — Feature extraction (LLM call #1)

**Prompt template** `COMPOSITIONAL_FEATURES_PROMPT`:

```
SYSTEM:
  You are analyzing a Linux kernel bug-fix commit for a CodeQL query generator.
  The pattern under study is <pattern>. Use the QLM four-features schema:
  target_api / post_operation / critical_variable / path_conditions.

USER:
  Commit:        <fix_sha>
  Subject:       <subject>
  Affected file: <c_file>

  Buggy version (fix^):
  <git show ${fix_sha}^:${c_file}>

  Fixed version:
  <git show ${fix_sha}:${c_file}>

  Patch (unified diff):
  <git show ${fix_sha} -- ${c_file}>

  Task: emit ONE JSON document with keys
    {target_api, post_operation, critical_variable, path_conditions,
     fits_pattern, bug_type, cwe}
  Apply the 4-question fit test. If fits_pattern=false, set bug_type to a
  human description and STOP — no further stages run.
```

Save output to `out_dir/features.json`.

## Stage 2 — POC synthesis (LLM call #2)

**Prompt template** `POC_SYNTHESIS_PROMPT`:

```
SYSTEM: <same preamble as Stage 1>

USER:
  Commit:   <fix_sha>
  Features: <features.json>
  Buggy slice (just the bug-touched function):
  <extracted from git show ${fix_sha}^:${c_file}>

  Task: write a self-contained C file `poc_<bug_type>.c` that:
    - includes minimal stub typedefs and #defines (no kernel headers)
    - defines `<fn>_buggy()` that reproduces the bug pattern
    - defines `<fn>_fixed()` that shows the correct cleanup
    - defines 3-5 variants: tp1..tp3 (other buggy shapes),
      tn1..tn3 (other fixed shapes), fp1..fp3 (look-alike safe shapes)
    - has main() so it compiles with `gcc -c poc_<bug_type>.c -o /tmp/poc.o`
  Output ONLY the C file body.
```

Save to `out_dir/poc.c`.

### Stage 2.5 — POC verifier gate (verifier-v1)

```bash
# stage seed slice (extract the bug-touched function only)
write out_dir/seed.c       # body of the function from fix^
write out_dir/poc.c        # from Stage 2

docker compose exec -T qlllm bash -c \
  '<REPO_ROOT>/scripts/verifier/run-verifier.sh \
     <seed_id>-rep<N> \
     <REPO_ROOT>/experiments/rq3/d3-prep/C3/<seed_id>-rep<N>/seed.c \
     <REPO_ROOT>/experiments/rq3/d3-prep/C3/<seed_id>-rep<N>/poc.c'
```

Read `verdict.csv`. Accept iff every row starts with `OK(`. Otherwise feed
the MISMATCH messages back to the LLM with
`REFINE_POC_PROMPT(features, prev_poc, verdict_rows)`, regenerate POC,
re-run verifier. **Cap = 3 regenerations.** On exhaustion → mark
`verifier_passes=false` and abort this generation with status=fail.

After passing: `chmod 444 out_dir/poc.c`; record `out_dir/poc.sha256`.

## Stage 2.6 — Build POC mini-DB

```bash
docker compose exec -T qlllm bash -c '
  cd <REPO_ROOT>/experiments/rq3/d3-prep/C3/<seed_id>-rep<N> &&
  <REPO_ROOT>/codeql-2.25.6/codeql database create poc-db \
    --language=cpp \
    --command="gcc -O0 -w -c poc.c -o /tmp/poc.o" \
    --source-root=. --overwrite > db-build.log 2>&1
'
```

## Stage 3 — QueryPlan synthesis (LLM call #3)

**Prompt template** `PLAN_PROMPT`:

```
SYSTEM: <same preamble + CodeQL cpp pointer>

USER:
  Features:   <features.json>
  POC source: <poc.c>

  Task: emit JSON QueryPlan with shape
    {
      "imports": ["cpp"],
      "predicates": [
        {
          "name": "isAcquire",
          "signature": "predicate isAcquire(FunctionCall fc)",
          "body": "{ fc.getTarget().getName() in [\"of_parse_phandle\", ...] }",
          "depends_on": [],
          "test_query":
            "import cpp\\nimport poc\\nfrom FunctionCall fc where isAcquire(fc) select fc",
          "expected_on_poc":
            "fires on _buggy variants and on _fixed (just structural match)"
        }, ...
      ],
      "assembly": "from FunctionCall acquire, Variable v
                   where isAcquire(acquire) and v = getAcquired(acquire)
                         and hasNullCheck(acquire, v)
                         and not hasMatchingRelease(acquire, v)
                         and not isInFixedFunction(acquire)
                   select acquire, '...'"
    }
  Each predicate body MUST be ≤ 30 lines. Predicates referenced in
  `depends_on` MUST appear earlier in the list (topological order). DO NOT
  import any external `.qll` libraries beyond `cpp`.
```

Save to `out_dir/plan.json`.

## Stage 4 — Per-predicate fill + validate

```
for predicate p in plan.predicates (topological order):
    for iter in 1..4:
        build minimal .ql:
            <imports>
            <bodies of p + transitive deps>
            <p.test_query>
        write out_dir/preds/<p.name>.ql
        codeql query compile out_dir/preds/<p.name>.ql
        if compile fails:
            REFINE_PRED_PROMPT(p, deps_bodies, compile_stderr, poc.c)
            continue
        codeql query run out_dir/preds/<p.name>.ql --database=poc-db
        compare result to p.expected_on_poc
        if mismatch:
            REFINE_PRED_PROMPT(p, deps_bodies, run_diagnostic, poc.c)
            continue
        mark p VALIDATED; record audit row; break
    else:  # 4 iters exhausted
        return fail(stage="predicate", predicate=p.name)
```

**Refine prompt** `REFINE_PRED_PROMPT`:

```
SYSTEM: <preamble>
USER:
  Predicate <p.name> failed.
  Body:
  <body>
  Dependencies (read-only):
  <bodies of dep predicates>
  Failure:
  <"compile error: <stderr>" OR "wrong test_query output: expected=<E> got=<G>">
  POC source (read-only):
  <poc.c>
  Task: emit a corrected body block for <p.name> ONLY (the
  `predicate <p.name>(...) { ... }` form). Do not re-emit other predicates,
  do not change the signature. Output ONLY the corrected predicate block.
```

## Stage 5 — Assemble + validate final query

```
write out_dir/final.ql:
    <imports>
    <all validated predicate bodies, topo order>
    <assembly from-where-select>
for iter in 1..4:
    codeql query compile out_dir/final.ql
    if fails: ASSEMBLE_REFINE_PROMPT(final.ql, compile_stderr, poc.c) ; continue
    codeql database analyze poc-db out_dir/final.ql --format=csv --output=poc-result.csv
    parse poc-result.csv:
        if any row mentions a *_buggy or _buggy_tpN function:    buggy_fires=true
        if any row mentions a *_fixed or _fixed_tnN function:    fixed_fires=true
        if any row mentions a *_fp_  / lookalike-safe variant:    fp_fires=true
    accept iff (buggy_fires and not fixed_fires and not fp_fires)
    if not accepted:
        ASSEMBLE_REFINE_PROMPT(final.ql, oracle_diagnostic, poc.c)
        continue
    break
else:
    return fail(stage="assemble")
```

**Refine prompt** `ASSEMBLE_REFINE_PROMPT`:

```
SYSTEM: <preamble>
USER:
  Final query failed:
  <final.ql>
  Failure:
  <compile stderr OR "expected: _buggy fires & _fixed silent; got: <table>">
  POC source (read-only):
  <poc.c>
  Task: emit a corrected complete `.ql` file (imports + all predicates + final
  from-where-select). Output ONLY the file body.
```

## Stage 6 — Outputs

Always emit:

| path | content |
|---|---|
| `out_dir/features.json` | Stage-1 output |
| `out_dir/poc.c` (mode 444) | Stage-2 output, verifier-v1 OK |
| `out_dir/poc.sha256` | sha256 of `poc.c` |
| `out_dir/poc-verifier-verdict.csv` | the OK row(s) from verifier-v1 |
| `out_dir/plan.json` | Stage-3 output |
| `out_dir/preds/*.ql` | per-predicate validated minimal queries |
| `out_dir/final.ql` | the assembled, POC-validated query |
| `out_dir/audit.json` | structured audit log (schema below) |

### Audit schema (`audit.json`)

```json
{
  "seed_id": "lin-1",
  "repeat": 1,
  "cell": "C3",
  "fix_sha": "74139a64e8ce",
  "llm_calls": <int>,
  "compile_iters": <int sum across stages>,
  "poc_regens": <int 0..3>,
  "verifier_passes": <bool>,
  "predicate_iters": {"<p.name>": <int>},
  "final_compiles": <bool>,
  "final_runs_on_poc": <bool>,
  "status": "pass" | "fail",
  "fail_stage": <null | "verifier" | "predicate:<name>" | "assemble">,
  "wall_seconds": <float>
}
```

## Cost notes (for D3-main planning)

- Expected LLM calls per generation: 3 (features+poc+plan) + ~K predicates × 1-2
  refinements + 1-2 assemble refinements ≈ **6-10 calls**
- Expected wall-time per generation: ~6-8 min for CodeQL stages + LLM latency
  ≈ **10-15 min target, 20 min cap**
- POC mini-DB build cached per (seed, POC sha): if POC stable across repeats,
  reuse same DB.
