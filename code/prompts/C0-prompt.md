# RQ3 Cell C0 — KNighter-Style Monolithic Baseline (no POC, no compositional, no iteration on results)

> Cell coordinates: compositional=OFF, POC=OFF. This is the canonical KNighter-minimal
> baseline used in §3 of `docs/paper/qlm-rq3-experiment-plan.md`. The driver here is the
> per-generation skeleton used by D3-main when it invokes a generation worker for cell C0.
>
> Linked plan sections: §2.2 (KNighter-minimal pipeline), §2.6 (prompt skeletons),
> §3.1–3.4 (E2 cell C0 row), §5.5.7 (iteration caps).

---

## 0. Inputs (provided by the D3-main per-generation invoker)

| field | type | example |
|---|---|---|
| `seed_id` | string | `lin-1` |
| `commit_sha` | string | `74139a64e8cedb6d971c78d5d17384efeced1725` |
| `c_file` | repo-relative path | `arch/arm/mach-omap2/pm33xx-core.c` |
| `commit_subject` | string | `ARM: OMAP2+: pm33xx-core: ix device node reference leaks in amx3_idle_init` |
| `repeat_idx` | int (1..3) | `1` |
| `out_dir` | abs path | `$QLLLM_ROOT/experiments/rq3/d3-prep/C0/` |

The patch text + commit message are looked up at call-time from the kernel git tree
(`$QLLLM_ROOT/linux`). The driver does NOT need POC, mini-DB, predicate library, or
verifier wiring — those are only for cells C1/C2/C3.

---

## 1. Pipeline (synchronous, single worker)

```
Stage 0: fetch
    diff = `git show <sha> -- <c_file>`
    msg  = `git show -s --format=%B <sha>`

Stage 1 (LLM call #1, KNIGHTER_CHECKER_PROMPT):
    in : preamble + diff + msg
    out: a single CodeQL .ql file body
    note: NO separate plan stage — the plan is implicit in the single prompt.
          (The §2.2 spec lists a Stage 1 "plan" call, but §3.4 cell C0 collapses
          it into one prompt to match the canonical KNighter-minimal pipeline as
          used in the RQ2 pilot.)

Stage 2 (compile-only repair, up to 4 iters total):
    iter = 0
    while iter < 4:
        write query.ql
        run `codeql query compile query.ql` (with qlpack pointing at codeql/cpp-all)
        if compile ok: break
        else:
            iter += 1
            call LLM with KNIGHTER_REPAIR_PROMPT(query, stderr)
    if still failing: emit FAIL artifact, stop

Stage 3 (terminate):
    save final .ql, save audit json, return.

NO POC mini-DB. NO predicate splitting. NO verifier. NO run-on-target gating.
The next step (KBH-Bench scoring) is performed by a separate D3 evaluator and
is OUT OF SCOPE for this cell.
```

Iteration cap = **4 compile-repair rounds** (plan §RQ3 §3.4; this absorbs the
original §2.2 "3 syntax-repair iters" and lifts to 4 per the RQ3 ceiling).

---

## 2. LLM contract

- Model: `claude-opus-4-5-20251101` (= "claude-opus-4-7" in the plan's shorthand).
- Temperature: `0.2` (plan §3.3 — non-zero so 3 repeats vary; the §2.2 spec said 0.0
  but §3.3 overrides for the ablation cells so we can estimate variance).
- `max_tokens`: 8192.
- ONE system prompt (the preamble) + ONE user message per call.
- Stop sequences: none.

---

## 3. Prompt skeletons (verbatim text the driver injects)

### 3.1 PREAMBLE (system) — shared by both stages

```
You are a senior Linux-kernel static-analysis engineer. You write CodeQL queries that
detect bug PATTERNS (not single-bug regressions) across the entire mainline kernel
source.

Working assumptions about the CodeQL DB you target:
- language: cpp
- built from a mainline-ish Linux source tree with KCFLAGS='-Dasm=__asm__'
- DB version: CodeQL 2.25.6 (`codeql/cpp-all` stdlib)

Output discipline:
- When asked for a `.ql` file, output ONLY the file body. No prose. No code fences.
- Every `.ql` must start with a doc comment containing @name, @description, @kind,
  @problem.severity, @id (use kind=problem unless the task specifically asks for
  path-problem).
- Imports: at minimum `import cpp`. Add any `import semmle.code.cpp.*` you need.
- No `.qll` files. No external library imports beyond `import cpp` + the cpp stdlib.
- Single `from-where-select`. Aim for ≤200 LOC total.
- Predicates inside the same file are FINE; multiple files are NOT.

Pattern-generalization guidance:
- The provided patch is one INSTANCE of a class of bugs. Your query must find
  OTHER instances across the kernel — not just this one commit.
- Generalize the acquire/release pair where applicable (e.g. of_parse_phandle has
  a whole family of of_* siblings; spin_lock pairs with spin_unlock variants).
- Avoid hard-coding file names, line numbers, or specific identifiers from the
  patched file unless they are the API name itself.

You may use any of the standard cpp stdlib modules:
- `semmle.code.cpp.controlflow.ControlFlowGraph`
- `semmle.code.cpp.dataflow.DataFlow` / `DataFlow2`
- `semmle.code.cpp.dataflow.TaintTracking`
- `semmle.code.cpp.controlflow.Guards`
- `semmle.code.cpp.controlflow.SSA`
```

### 3.2 KNIGHTER_CHECKER_PROMPT (Stage 1 user message)

```
Bug-fix commit you are reverse-engineering into a checker:

== commit sha ==
{commit_sha}

== commit subject ==
{commit_subject}

== full commit message ==
{commit_message_body}

== patch diff (this is the entire input — there is no separate "plan" turn) ==
{patch_diff}

== task ==
Write ONE CodeQL .ql file (≤200 LOC) that detects the BUG PATTERN this commit
fixes, across the whole Linux kernel CodeQL database. The query should fire on
the buggy version of `{c_file}` (and on analogous bugs in other files), and stay
silent on the fixed version.

Constraints:
  - single from-where-select clause
  - imports: `import cpp` plus any stdlib modules you need
  - top of file: @kind problem (or @kind problem-path if you really need it),
    @id (use form `cpp/<short-slug>`), @name, @description, @problem.severity
  - generalize beyond the single API in the patch where the pattern obviously
    has siblings (e.g. of_parse_phandle → of_* node-acquiring family)
  - do NOT hard-code the patched filename or line numbers

Output ONLY the .ql file body. No markdown fences. No commentary.
```

### 3.3 KNIGHTER_REPAIR_PROMPT (Stage 2 user message, sent on every failed compile)

```
The CodeQL query below failed to compile.

== current .ql ==
{query_body}

== `codeql query compile` stderr ==
{stderr}

== task ==
Produce a corrected .ql file body. Fix ONLY what the diagnostic complains about,
and keep the original detection logic intact unless the diagnostic forces a
structural change. Output ONLY the .ql file body. No commentary, no fences.
```

---

## 4. Driver invocation (what D3-main runs per generation)

```bash
# D3-main pseudo-call (one (seed, repeat) → one .ql)
python3 $QLLLM_ROOT/experiments/rq3/d3-prep/C0/c0_driver.py \
    --seed-id        lin-1 \
    --commit-sha     74139a64e8cedb6d971c78d5d17384efeced1725 \
    --c-file         arch/arm/mach-omap2/pm33xx-core.c \
    --commit-subject "ARM: OMAP2+: pm33xx-core: ix device node reference leaks in amx3_idle_init" \
    --repeat-idx     1 \
    --out-dir        $QLLLM_ROOT/experiments/rq3/d3-prep/C0/
```

Outputs (per generation):
- `<out_dir>/<seed_id>-rep<n>.ql` — final .ql file (compile-clean or last-attempt
  on exhaustion)
- `<out_dir>/<seed_id>-rep<n>.audit.json` — schema:
  ```json
  {
    "cell": "C0",
    "seed_id": "lin-1",
    "repeat_idx": 1,
    "commit_sha": "74139a64...",
    "llm_calls": 2,
    "compile_iters": 1,
    "poc_regens": 0,
    "verifier_passes": null,
    "final_compiles": true,
    "final_runs_on_poc": null,
    "elapsed_seconds": 32.4,
    "model": "claude-opus-4-5-20251101",
    "temperature": 0.2,
    "stop_reason": "ok" | "compile-exhausted" | "llm-error"
  }
  ```

POC-related fields (`poc_regens`, `verifier_passes`, `final_runs_on_poc`) are
always `0`/`null` for C0 since this cell has no POC. They are kept in the schema
so the aggregator handles all four cells uniformly.

---

## 5. Expected wall-time per generation

From plan §2.7 (~3-4 LLM calls per seed for baseline, ~30 sec compile per iter):

| component | typical | worst |
|---|---|---|
| Stage 0 (git fetch + format) | <1 s | 2 s |
| Stage 1 (LLM call #1) | 20 s | 60 s |
| Stage 2 compile + 1 repair iter (50% of seeds need ≥1 repair) | 30 s | 120 s |
| Stage 2 worst case (4 repairs) | — | 4 × (20 s LLM + 30 s compile) = ~3.5 min |

**Target: ~45 s typical, ≤4 min worst-case per generation.**

---

## 6. Cross-cell sibling notes (for the other cells the orchestrator will spawn)

- C1 (POC=ON, comp=OFF): same monolithic prompt + adds POC.c body to the user
  message + replaces compile-only loop with compile+poc-run loop (≤3 POC regen
  rounds via verifier-v1). See `C1-prompt.md`.
- C2 (POC=OFF, comp=ON): emits QueryPlan JSON with predicates + per-predicate
  compile-only validation. See `C2-prompt.md`.
- C3 (POC=ON, comp=ON): the full pipeline = current QLM agent lineage. See
  `C3-prompt.md`.

The shared preamble (§3.1) is identical across all four cells so the synthesis-strategy
axis is the only thing that varies.
