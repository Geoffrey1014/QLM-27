# C1 Cell Prompt — Monolithic + POC ON + Verifier

> Per `docs/paper/qlm-rq3-experiment-plan.md` §3.4, §5.5.
> Cell ID: **C1**  ·  Compositional: **OFF**  ·  POC: **ON**  ·  Verifier: **v1**
> Output: ONE monolithic `.ql` file (≤ 200 LOC, single `from–where–select`).

This document is the **driver spec** loaded by every D3-main per-generation agent
running C1. It encodes (a) the per-stage prompt skeletons, (b) the loop budgets,
(c) the drift-prevention contract, (d) the audit log shape. Do not silently
deviate — if you discover a stage that must change, edit this file and bump the
schema version comment in `experiments/rq3/d3-prep/C1/CELL_VERSION`.

---

## 0. Inputs (provided by D3-main caller)

| name | example | source |
|---|---|---|
| `seed_id` | `lin-1` | row in `experiments/rq3/seeds.csv` |
| `seed_sha` | `74139a64e8ce` | git sha of the fix commit |
| `c_file` | `arch/arm/mach-omap2/pm33xx-core.c` | from seeds.csv |
| `func_name` | `amx3_idle_init` | from seeds.csv |
| `kernel_repo` | `<REPO_ROOT>/linux` | container path |
| `rep_id` | `rep1` … `rep3` | repeat index |
| `out_dir` | `experiments/rq3/d3-prep/C1/<seed_id>-<rep_id>/` | host path |

The caller must already have produced:
- buggy version of `c_file` (= `git show <sha>^:<c_file>`)
- fixed version of `c_file` (= `git show <sha>:<c_file>`)
- patch (= `git show <sha> -- <c_file>`)

into `out_dir/seed-buggy.c`, `out_dir/seed-fixed.c`, `out_dir/seed.patch`.

---

## 1. Pipeline overview

```
Stage A: POC generation                  [LLM call #1, regen up to 3]
   │
   ▼
Stage B: Verifier-v1 gate                [CodeQL run; if FAIL → goto A]
   │     (pass = all dimensions OK or
   │      explicit reviewer note attached)
   ▼
Stage C: POC freeze (chmod 444 + sha)    [drift prevention §5.5]
   │
   ▼
Stage D: POC mini-DB build               [single-TU codeql DB]
   │
   ▼
Stage E: Monolithic .ql synthesis        [LLM call #2 — the C1 call]
   │
   ▼
Stage F: Compile + run-on-POC validation [≤ 4 repair iterations]
   │     fire on _buggy / silent on _fixed
   ▼
Stage G: Emit final .ql + audit log
```

All "LLM call" lines call **Claude Opus 4.7** via the configured harness
(parent Claude Code session acts as the LLM in prep; in D3-main the API client
makes the call, transcript captured under `out_dir/llm-trace/`).

Budgets (per §RQ3 §3.4):
- POC regen rounds: **≤ 3** (`POC_MAX_REGEN = 3`)
- Compile+POC repair iterations: **≤ 4** (`REPAIR_MAX_ITERS = 4`)

---

## 2. Stage A — POC generation prompt (LLM call #1)

```
SYSTEM:
You are writing a minimal, self-contained C proof-of-concept that demonstrates
the bug fixed by the given commit. The POC will be compiled with `gcc -O0 -w
-c` into a CodeQL mini-database and used as the oracle for a CodeQL detector.

Hard requirements (NON-NEGOTIABLE):
  R1. The file MUST contain exactly two functions whose names end with
      `_buggy` and `_fixed`. Their parameter lists must be identical.
  R2. `_buggy()` MUST contain the bug pattern the patch removes; `_fixed()`
      MUST contain the bug-free counterpart. The control flow of `_buggy()`
      should mirror the buggy version's relevant control flow (same number
      of returns, gotos, and ifs around the resource lifecycle).
  R3. Stub any kernel APIs / types you reference with `static`-linkage
      declarations or `extern` prototypes; no kernel headers.
  R4. The file MUST compile cleanly under `gcc -O0 -w -c -std=gnu11` (no
      warnings beyond -w-suppressed). Provide a trivial `int main(void)`.
  R5. ≤ 200 LOC. No `#include`s beyond <stddef.h>, <stdint.h>, <stdbool.h>,
      <stdlib.h>, <stdio.h>.

Output ONLY the C source. No markdown, no commentary.

USER:
Commit subject:  <subject>
Affected file:   <c_file>
Affected fn:     <func_name>

--- PATCH ---
<seed.patch>

--- BUGGY VERSION OF THE AFFECTED FUNCTION (and a few helpers) ---
<extracted func body from seed-buggy.c>

--- FIXED VERSION OF THE AFFECTED FUNCTION ---
<extracted func body from seed-fixed.c>
```

On regen (rounds 2, 3), append:

```
--- PREVIOUS POC (failed verifier) ---
<previous POC body>

--- VERIFIER VERDICT ---
<verifier rows>

Regenerate honoring the failed dimension(s). Keep _buggy() / _fixed() names.
```

Save to `out_dir/POC.c.tmp`.

---

## 3. Stage B — Verifier-v1 gate

Run, inside container:

```bash
docker compose -f <REPO_ROOT>/docker-compose.yml exec -T qlllm bash -c \
  '<REPO_ROOT>/scripts/verifier/run-verifier.sh \
     <seed_id>-<rep_id> \
     <REPO_ROOT>/experiments/rq3/d3-prep/C1/<seed_id>-<rep_id>/seed-buggy.c \
     <REPO_ROOT>/experiments/rq3/d3-prep/C1/<seed_id>-<rep_id>/POC.c.tmp'
```

The verifier emits one CSV row per checked dimension (F1.acquire,
F1.release, F3.goto, F5.return, F2.if). PASS condition:

- **strict pass** = every emitted row starts with `OK(...)`
- **lenient pass** (allowed for C1 since v1 is known too-strict on F2.if /
  F3.goto when POC adds 1 boilerplate stub branch) = only the F2.if or
  F3.goto dimension mismatches AND the absolute delta is `≤ 1`. The audit
  log records `lenient_pass=true` so reviewers can re-score later if v2
  comes online.

On FAIL (and rounds remaining): loop back to Stage A with the previous POC
and verdict in context.

On FAIL with rounds exhausted: emit `out_dir/STATUS=poc-verifier-fail`,
write audit log with `verifier_passes=false`, **STOP** (no .ql produced).

---

## 4. Stage C — POC freeze

```bash
mv out_dir/POC.c.tmp out_dir/POC.c
chmod 444 out_dir/POC.c
sha=$(sha256sum out_dir/POC.c | cut -d' ' -f1)
jq --arg k "<seed_sha>-<rep_id>-C1" --arg v "$sha" \
   '. + {($k): $v}' experiments/rq3/poc-sha.json > /tmp/.psha && \
   mv /tmp/.psha experiments/rq3/poc-sha.json
```

The POC is now frozen for this seed-repeat-cell triple. Any later stage
that re-checks the sha MUST find it unchanged.

---

## 5. Stage D — POC mini-DB build

Single-TU CodeQL DB built inside container with the same gcc invocation
that the verifier used (so semantics match), but into the cell-private DB
path:

```bash
WORK=out_dir/poc-db
rm -rf "$WORK" && mkdir -p "$WORK"
cp out_dir/POC.c "$WORK/POC.c"
cat > "$WORK/build.sh" <<'EOF'
#!/bin/bash
set -e
gcc -O0 -w -c POC.c -o /tmp/POC.o
EOF
chmod +x "$WORK/build.sh"
CODEQL=<REPO_ROOT>/codeql-2.25.6/codeql
(cd "$WORK" && "$CODEQL" database create db --language=cpp \
   --command=./build.sh --source-root=. --overwrite > build.log 2>&1)
```

DB lives at `out_dir/poc-db/db`.

---

## 6. Stage E — Monolithic .ql synthesis (LLM call #2 — THE C1 CALL)

```
SYSTEM:
You write ONE monolithic CodeQL query (CodeQL CLI 2.25.6, language cpp) that
detects the bug pattern shown by the patch and the POC. Output ONLY the .ql
body — no markdown fences, no commentary, no extra files.

Hard requirements:
  Q1. ≤ 200 LOC, single `from – where – select`.
  Q2. The .ql must compile cleanly under `codeql query compile`.
  Q3. When run on the POC mini-DB it MUST report a result whose location is
      inside the function whose name ends with `_buggy`, and MUST NOT report
      any result inside the function whose name ends with `_fixed`.
  Q4. Standard query header (@name, @kind problem, @problem.severity warning,
      @id qlm/c1-<seed_id>) is mandatory.
  Q5. Use only library imports that ship with cpp-all (e.g., `import cpp`).
      Do NOT import custom .qll files; this is the monolithic cell.
  Q6. Do NOT hard-code file paths, function names containing `_buggy` /
      `_fixed`, or any artifact of the POC scaffolding. The query must be
      generic over the bug pattern — it has to work later on the full Linux
      DB, not just this POC.

USER:
Patch:
<seed.patch>

POC.c (frozen, sha256=<sha>):
<POC.c contents>

Verifier-v1 verdict (passed):
<verdict rows>

POC oracle:
  - MUST fire on a location inside `<func>_buggy` (any one row suffices).
  - MUST NOT fire on any location inside `<func>_fixed`.

Write the .ql now.
```

Save the model's verbatim output to `out_dir/query.ql` (no edits).

---

## 7. Stage F — Compile + POC repair loop (≤ 4 iters)

For `iter = 1 … REPAIR_MAX_ITERS`:

1. **Compile** with
   ```
   $CODEQL query compile out_dir/query.ql --search-path=<REPO_ROOT>/codeql-2.25.6
   ```
   On error → goto step 4 with `diag = stderr_first_50_lines`.

2. **Run on POC DB**:
   ```
   $CODEQL database analyze out_dir/poc-db/db out_dir/query.ql \
       --format=csv --output=out_dir/poc-run.csv --rerun
   ```
   On error → goto step 4 with `diag = analyze stderr`.

3. **Oracle check** — parse `poc-run.csv`:
   - `fired_on_buggy = any row whose location resolves into a function whose
     name matches `%_buggy`.
   - `fired_on_fixed = any row whose location resolves into a function whose
     name matches `%_fixed`.
   - PASS iff `fired_on_buggy && !fired_on_fixed`.
   On PASS → break loop, success.
   On FAIL → goto step 4 with `diag` describing which side fired/silent.

4. **Refine call (LLM call #2+iter)** — REFINE_MONO_POC_PROMPT:
   ```
   SYSTEM: same as Stage E SYSTEM.
   USER:
     The previous query failed validation.
     --- PREVIOUS QUERY ---
     <out_dir/query.ql>
     --- DIAGNOSTIC ---
     <diag>
     --- POC ORACLE (unchanged) ---
     fire on <func>_buggy ; silent on <func>_fixed.
     The POC is FIXED (sha256=<sha>). Modify only the query.
   Output ONLY the corrected .ql body.
   ```
   Overwrite `out_dir/query.ql`. Continue loop.

If loop exits without PASS: emit `out_dir/STATUS=repair-budget-exhausted`,
keep the last `query.ql`, set audit `final_runs_on_poc=false`.

---

## 8. Stage G — Final artifacts

```
out_dir/
├── seed.patch
├── seed-buggy.c
├── seed-fixed.c
├── POC.c                    (mode 444, sha logged)
├── poc-db/                  (CodeQL mini-DB)
├── query.ql                 (the final monolithic detector)
├── poc-run.csv              (last analyze run on POC DB)
├── llm-trace/               (full prompt+response per call)
│   ├── 01-poc-gen.json
│   ├── 02-query-gen.json
│   └── 03-repair-iterN.json
├── audit.json               (schema in §9 below)
└── STATUS                   ('ok' or one of the fail states)
```

`audit.json` MUST conform to the StructuredOutput schema the orchestrator
expects. Field reference:

| field | type | meaning |
|---|---|---|
| `llm_calls` | int | total Claude calls this generation |
| `compile_iters` | int | how many of the ≤4 repair iters fired |
| `poc_regens` | int | how many of the ≤3 POC re-generations happened (0 if first POC passed) |
| `verifier_passes` | bool | did the final POC pass verifier-v1 (lenient or strict) |
| `final_compiles` | bool | does the final query.ql compile? |
| `final_runs_on_poc` | bool | does it fire on _buggy AND stay silent on _fixed? |

---

## 9. Failure modes & their STATUS strings

| STATUS | meaning |
|---|---|
| `ok` | every gate passed; final query is correct on the POC. |
| `poc-verifier-fail` | 3 POC regens exhausted, verifier still mismatches. No query emitted. |
| `repair-budget-exhausted` | query compiles but never satisfies the oracle within 4 iters. Last `query.ql` is kept. |
| `compile-budget-exhausted` | query never compiled. (Subset of above; still kept.) |
| `infra-fail` | CodeQL CLI / docker / git failed in a non-deterministic way. Re-run the rep. |

Drift-prevention enforcement (§5.5):
- Stage F MUST `sha256sum POC.c` before each iteration and compare against
  `experiments/rq3/poc-sha.json`. Any drift → `STATUS=infra-fail`, abort.
- The `REFINE_MONO_POC_PROMPT` MUST include the exact line: *"The POC is
  FIXED. Modify only the query."*

---

## 10. Notes for the D3-main caller

- C1 is **stateless across reps**: each `(seed_id, rep_id)` gets its own
  POC, sha, mini-DB. Do not share across reps.
- Three reps per seed (per §3.4); seeds drawn from `experiments/rq3/seeds.csv`.
- Estimated wall time: **6-10 min per generation** on a warm container
  (POC gen ~30s, verifier ~45s, mini-DB ~30s, query gen ~30s, repair iters
  ~60s each).
- C1 has no compositional library calls, so no Stage 1 / Stage 2 like C3.
  Total LLM calls per generation: 2 (best case) + up to 3 regen + up to 4
  repair = bounded at 9.
