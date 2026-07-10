# C2 Cell Prompt — Compositional, POC-OFF, Compile-Only Validation

> Cell coordinate in the RQ3 2x2: **compositional = ON, POC = OFF**.
> Loaded once per *generation* by D3-main; one generation = one seed × one repeat.
> Companion cells: C0 (-,-), C1 (-,+POC), C3 (+,+).

## 0. Mission

Given **one** bug-fix commit (seed), produce **one** CodeQL `.ql` query that, in
the team's hypothesis, captures the underlying bug pattern. You may **not**
synthesise a POC, build a POC mini-DB, or run the query — only `codeql query
compile` is permitted as a validator. Compositional decomposition into named
predicates **is** required; library imports are **not** permitted (predicates
must be self-contained in the final `.ql`).

Pipeline = features → plan → per-predicate fill+compile → assemble+compile.

## 1. Inputs (D3-main supplies)

| key | meaning |
|---|---|
| `SEED_ID`        | e.g. `lin-1` |
| `COMMIT_SHA`     | full sha of the bug-fix commit |
| `C_FILE`         | path relative to kernel root, e.g. `arch/arm/mach-omap2/pm33xx-core.c` |
| `FUNCTION_NAME`  | the function the fix touches (optional hint, helps Stage 1) |
| `REPEAT_IX`      | 1, 2 or 3 |
| `OUT_DIR`        | absolute, e.g. `$QLLLM_ROOT/experiments/rq3/d3-prep/C2/` (or D3-main's per-generation dir) |
| `WORK_DIR`       | scratch dir for intermediate predicate bodies & compile logs |

The driver also reads the patch via the container:

```bash
docker compose -f <REPO_ROOT>/docker-compose.yml exec -T qlllm \
  git -C <REPO_ROOT>/linux show "$COMMIT_SHA" -- "$C_FILE"
```

and (for Stage 1 context) the buggy + fixed file bodies:

```bash
docker compose ... exec -T qlllm git -C .../linux show "$COMMIT_SHA^:$C_FILE"
docker compose ... exec -T qlllm git -C .../linux show "$COMMIT_SHA:$C_FILE"
```

## 2. Environment

- Container: `docker compose -f <REPO_ROOT>/docker-compose.yml exec -T qlllm bash`
- CodeQL CLI (in container): `<REPO_ROOT>/codeql-2.25.6/codeql`
- Compile-only validator: `codeql query compile <file.ql>` (exit 0 = pass).
- Model: `claude-opus-4-7`, temperature 0.2.
- **Forbidden** in this cell: `codeql database create`, `codeql query run`,
  POC `.c` synthesis, anything labelled "verifier-v1", any reference to
  `cpp-queries/rq3-lib/*.qll` in `.ql` imports.
- Allowed `.ql` imports: `import cpp` only (and optionally `import semmle.code.cpp.controlflow.Guards` if a predicate needs it; no `rq3-lib`).

## 3. Pipeline

### Stage 1 — Features extraction (1 LLM call)

Prompt: `COMPOSITIONAL_FEATURES_PROMPT` (lifted from
`agents/four-features-bug-pattern-analyzer-prompt.md` Phase 1.3).

```
SYSTEM: You are a Linux kernel static-analyzer designer. You will analyse a bug-fix commit
        and extract the four features (target_api, post_operation, critical_variable,
        path_conditions) needed to build a CodeQL checker.
USER:   commit: <COMMIT_SHA>
        file:   <C_FILE>
        --- patch ---
        <git show output, full diff>
        --- buggy file (excerpt around touched function) ---
        <±40 lines around the hunks>
        --- task ---
        Output ONLY one JSON object, no prose:
        {
          "target_api":          "<C function that acquires the resource>",
          "post_operation":      "<C function that must be called to release it>",
          "critical_variable":   "<the variable holding the resource, by name>",
          "path_conditions":     "<plain-English summary of when post_operation is required>",
          "fits_pattern":        true|false,
          "fit_test_reasoning":  "<3-4 sentences applying the 4-question fit test>"
        }
```

If `fits_pattern == false`: **stop**, write `OUT_DIR/<seed>-rep<N>.audit.json`
with `validation_status="skip-mismatch"`, exit.

### Stage 2 — Plan (1 LLM call)

Prompt: `PLAN_PROMPT_C2` (Stage-3-of-ours minus the POC and library
catalogue).

```
SYSTEM: You are designing a CodeQL query for the Linux kernel. The query must be
        decomposed into named predicates that are explicit and self-contained — DO NOT
        import any custom .qll library; everything you define lives in the single .ql
        file you will eventually emit. You may rely on `import cpp` and optionally
        `import semmle.code.cpp.controlflow.Guards`.
USER:   commit:   <COMMIT_SHA>
        features: <Stage-1 JSON, pretty-printed>

        Task: emit ONE JSON object QueryPlan with the schema:
        {
          "imports": ["cpp"],
          "predicates": [
            { "name": "<snake_case>",
              "signature": "predicate <name>(<params>)",
              "body": "",                       // leave empty; Stage 3 will fill it
              "depends_on": ["<other predicate names>"] }
          ],
          "assembly": "from <decls> where <conjunction of predicates> select <expr>, \"<msg>\""
        }

        Constraints:
        - 3 to 6 predicates total.
        - Each predicate ≤ 30 lines when filled.
        - depends_on must be a DAG (topological).
        - Predicate names must be unique and the assembly's `where` clause must reference
          them.
        - NO library imports beyond what's listed above.
        Output ONLY the JSON.
```

### Stage 3 — Per-predicate fill + compile-only validation

For each predicate `p` in **topo order** (parents before children):

1. Build a *scaffold* `.ql` consisting of `imports`, all *already-filled*
   predicate bodies (parents), the bare *signature* of `p`, and a **harness**
   bottom: a trivial `select` clause that mentions `p` to force the compiler
   to type-check it.

   Concretely:

   ```ql
   import cpp
   <parents already filled>
   <signature of p> { /* TODO_BODY */ }

   from <reasonable decls covering p's params>
   where <name>(<args>)
   select <one of those decls>, "harness"
   ```

2. LLM call: `FILL_PRED_PROMPT_C2`

   ```
   SYSTEM: <same preamble as Stage 2>
   USER:   You will fill the body of ONE CodeQL predicate.

           Plan context:
           <full QueryPlan JSON, parents already filled>

           Predicate to fill:
           name:        <p.name>
           signature:   <p.signature>
           depends_on:  <p.depends_on>

           Constraints:
           - Body ≤ 30 lines.
           - Use only AST nodes/predicates from `import cpp` (+ Guards if Stage 2 imported it).
           - Refer to parent predicates by name when needed.
           - Do NOT redeclare imports or other predicates.
           - Output ONLY the predicate block (signature included), no prose.
   ```

3. Substitute the returned body into the scaffold, write to
   `WORK_DIR/<seed>-rep<N>-pred-<p.name>-iter0.ql`, run
   `codeql query compile`.

4. **Compile-repair loop**, up to **4 iterations** (per plan §3.4):
   - On compile failure, call `REFINE_PRED_PROMPT_C2`:

     ```
     SYSTEM: <same preamble>
     USER:   Predicate <p.name> failed to compile.

             Current code:
             <full scaffold .ql, predicate highlighted with /* >>> */ markers>

             Compile diagnostic:
             <stderr, first 80 lines>

             Task: produce a corrected predicate body only. Same signature.
             Output ONLY the predicate block. No prose.
     ```
   - Apply, re-write to `...-iter<k>.ql`, recompile.
   - If still failing after 4 attempts: mark predicate `failed`, abort the
     generation, write audit and exit with `validation_status="fail-predicate"`.

5. Stash the validated body in `plan.predicates[i].body`.

### Stage 4 — Assemble + compile-only validation

1. Build final `.ql`:
   ```ql
   /**
    * @name  rq3-c2-<seed>-rep<N>
    * @id    cpp/rq3/c2/<seed>-rep<N>
    * @kind  problem
    * @problem.severity warning
    * @description Compositional + POC-OFF generation for RQ3 cell C2.
    */
   <imports as `import X` per plan.imports>

   <each predicate body, in topo order>

   <plan.assembly>
   ```

2. `codeql query compile` on the assembled file.

3. **Compile-repair loop**, up to **4 iterations**. Refine prompt:

   ```
   SYSTEM: <same preamble>
   USER:   The assembled query failed to compile.

           Current query:
           <full .ql>

           Compile diagnostic:
           <stderr, first 80 lines>

           Task: produce a corrected complete .ql file.
           - Keep the same predicate names and assembly intent.
           - You MAY adjust predicate bodies and the assembly clause.
           - Do NOT add `.qll` library imports.
           Output ONLY the .ql file body.
   ```

4. If still failing after 4 attempts: write the *last* attempt anyway, set
   `validation_status="fail-assemble"`, exit.

### Stage 5 — Output

Write:
- `OUT_DIR/<seed>-rep<N>.ql`               — the final query (last attempt, even if failed)
- `OUT_DIR/<seed>-rep<N>.audit.json`       — see schema below
- `OUT_DIR/<seed>-rep<N>.plan.json`        — the QueryPlan (with filled bodies)
- `WORK_DIR/<seed>-rep<N>-*.ql`            — per-iteration scaffolds for forensics

Audit JSON schema (mirror the D3-main audit shape):

```json
{
  "cell": "C2",
  "seed_id": "<SEED_ID>",
  "repeat": <REPEAT_IX>,
  "commit_sha": "<COMMIT_SHA>",
  "llm_calls": <int>,                  // features + plan + sum(per-predicate fill+refine) + sum(assembly refine)
  "compile_iters": <int>,              // total compile-only invocations across predicates + assembly
  "poc_regens": 0,                     // C2 never makes POC
  "verifier_passes": null,             // C2 has no verifier
  "final_compiles": <bool>,
  "final_runs_on_poc": null,           // C2 never runs
  "validation_status": "pass"|"fail-predicate"|"fail-assemble"|"skip-mismatch",
  "per_predicate_iters": { "<pred_name>": <int>, ... },
  "assembly_iters": <int>,
  "wall_seconds": <float>
}
```

## 4. Caps (binding)

- Compile-repair per predicate: **≤ 4**
- Compile-repair on assembled query: **≤ 4**
- POC regens: **0** (cell definition)
- Verifier passes: **0** (cell definition)
- LLM calls upper bound (typical, not a hard cap):
  `1 (features) + 1 (plan) + Σ(predicate fill+refine) + Σ(assembly refine)`
  ≈ `2 + 6×(1+1.5 refines) + 1.5` ≈ **18-20 calls** worst case for a 6-predicate plan.

## 5. Failure modes & recovery

| failure | response |
|---|---|
| Stage 1 returns `fits_pattern=false` | exit with `skip-mismatch`; **no** queries written |
| Stage 2 returns malformed JSON | retry once with "Output ONLY valid JSON" reinforcement; if still fails, log `fail-plan` and exit |
| `depends_on` is cyclic | topo-sort fails → `fail-plan`, exit |
| Stage 3 predicate budget exhausted | exit with `fail-predicate`, *but still* write the last scaffold so D3-main can inspect |
| Stage 4 assembly budget exhausted | write the last attempt, `fail-assemble` |
| Container call dies (docker exec / network) | retry once after 5 s, then fail this generation |

## 6. Drift prevention

Since C2 has no POC and no run, there is no POC-drift hazard. The only drift
risk is **plan drift**: Stage 4 refine is allowed to mutate predicate bodies
to make assembly compile. Record `final_predicates_differ_from_stage3` in the
audit if any body changed during Stage 4. (Compositionality on its own is
still measured; that's the whole point of C2 vs C0.)

## 7. Per-generation wall-time target

- Aim **6-12 min** per generation. Compile-only is fast (each `codeql query
  compile` is 2-5 s once `~/.codeql` cache is warm). The wall-time floor is
  dominated by the LLM round-trips (avg ~15 s each at 20 calls = ~5 min).
- For D3-main planning use **~10 min/gen** as the budget.

## 8. Invocation contract for D3-main

D3-main spawns a subagent with: this prompt + the inputs in §1 +
`StructuredOutput` schema matching the audit JSON in Stage 5. The subagent
returns the audit dict; D3-main appends to `e2-results.csv` and triggers
scoring (recall, pair-wise, F1_pair) **out-of-band** — scoring is not part of
the cell.
