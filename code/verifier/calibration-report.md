# Seed↔POC Consistency Verifier — v1 Calibration Report

> Plan reference: [`docs/paper/qlm-rq-refactor-plan-optionA.md`](../../docs/paper/qlm-rq-refactor-plan-optionA.md) §5.5 + §5.5.6.
> Date: 2026-06-30. Verifier: `verifier-v1.ql` (count-based, F1+F2.basic+F3.count+F5.count).

## 1. Calibration design

The verifier is exercised on three classes of paired inputs, all built from the existing
`tmp-pair-wise/` POC slices for the 5 reference bugs (e-01, e-02, e-06, tp-01, e-09).
For each class we know the expected verdict a-priori; the verifier passes calibration if
**every** scenario's verdict matches expectation.

| class | scenarios | expected verdict | what it tests |
|---|---|---|---|
| **A. Self-pair** | seed_X = poc_X for each of the 5 bugs | `OK` | reflexivity: the verifier never rejects identical inputs |
| **B. Cross-pair** | seed_X vs poc_Y, X ≠ Y | `MISMATCH` | discrimination: the verifier rejects unrelated bugs |
| **C. Corrupted POC** | seed_X vs (poc_X + dead `goto unrelated;` block) | `MISMATCH` | sensitivity: the verifier catches structural drift even when bug-relevant code is unchanged |
| **D. Buggy-vs-Fixed** | seed_X (buggy) vs poc_X (fixed-after-patch) | `MISMATCH` | fidelity: the verifier rejects pairing a buggy seed against a post-fix POC (the fix changes release-count) |

A note on POC vs seed-slice for fresh bugs: §5.5.6 of the plan notes that "the fresh POCs
ARE the seed slices" because we extracted them verbatim from kernel master. We therefore
do not have an independently-LLM-generated POC in the calibration set; class A (self-pair)
exercises the verifier on the seed=POC trivial case, and classes B/C/D exercise it on
deliberately-different inputs that we know should fail.

## 2. Calibration matrix — actual run

Output of `./run-calibration.sh`, executed in the qlllm container against the 12
calibration scenarios (full `stdout` saved to `calibration-stdout.log`).

| scenario              | expect    | actual    | calib  | first-msg |
|-----------------------|-----------|-----------|--------|-----------|
| self-e01              | OK        | OK        | OK     | `OK(F1.acq=5 F1.rel=0 F3.goto=0 F5.ret=2 F2.if=11)` |
| self-e02              | OK        | OK        | OK     | `OK(F1.acq=2 F1.rel=0 F3.goto=0 F5.ret=4 F2.if=10)` |
| self-e06              | OK        | OK        | OK     | `OK(F1.acq=3 F1.rel=1 F3.goto=1 F5.ret=6 F2.if=12)` |
| self-tp01             | OK        | OK        | OK     | `OK(F1.acq=1 F1.rel=0 F3.goto=0 F5.ret=2 F2.if=1)` |
| self-e09              | OK        | OK        | OK     | `OK(F1.acq=6 F1.rel=6 F3.goto=6 F5.ret=4 F2.if=10)` |
| cross-e01vs02         | MISMATCH  | MISMATCH  | OK     | `MISMATCH(F2.if: seed=11, poc=10)` |
| cross-e01vse09        | MISMATCH  | MISMATCH  | OK     | `MISMATCH(F2.if: seed=11, poc=10)` |
| cross-tp01vse06       | MISMATCH  | MISMATCH  | OK     | `MISMATCH(F2.if: seed=1, poc=12)` |
| corrupt-e01           | MISMATCH  | MISMATCH  | OK     | `MISMATCH(F2.if: seed=11, poc=12)` |
| buggy-vs-fixed-e01    | MISMATCH  | MISMATCH  | OK     | `MISMATCH(F1.release: seed=0, poc=2)` |
| buggy-vs-fixed-e02    | MISMATCH  | MISMATCH  | OK     | `MISMATCH(F1.release: seed=0, poc=1)` |
| buggy-vs-fixed-tp01   | MISMATCH  | MISMATCH  | OK     | `MISMATCH(F1.release: seed=0, poc=1)` |

**Result: 12/12 scenarios match expectation.** v1 is neither too loose (no false-OK)
nor too strict (no false-MISMATCH on self-pair) on this calibration set.

When MISMATCH fires the verifier emits one row per failing dimension; the "first-msg"
column shows just the first one. Notable detail rows from class C/D:

- `corrupt-e01` emits both `MISMATCH(F2.if: seed=11, poc=12)` **and** `MISMATCH(F3.goto: seed=0, poc=1)` — catching both the added dead `if` and the dead `goto unrelated;`.
- `cross-e01vse09` emits **5 distinct mismatches** (F1.acquire, F1.release, F2.if, F3.goto, F5.return) — large structural delta, as expected for unrelated bugs.

## 3. v1 design — feature dimensions wired

| dim | what v1 counts | source predicate |
|---|---|---|
| F1.acquire | calls to acquire APIs (resource gain) | `isAcquireApi/1` enumerated list — 14 names covering `of_*` (device tree), `k*alloc`, and libc allocators |
| F1.release | calls to release APIs (resource drop) | `isReleaseApi/1` enumerated list — `of_node_put`, `kfree`, `free` |
| F2.if | `IfStmt` count in file | direct CodeQL `count(IfStmt …)` |
| F3.goto | `GotoStmt` count in file | direct CodeQL `count(GotoStmt …)` |
| F5.return | `ReturnStmt` count in file | direct CodeQL `count(ReturnStmt …)` |

F2.b (max nesting depth), F3.b (label-has-release boolean), F4 (data-flow chain),
F5.b (exit-path released-or-not multiset), and F2.b (loop count) are **deferred to v2/v3**
per §5.5.3. The calibration matrix already exercises the dimensions v1 implements; the
deferred dimensions are needed when v1 mis-classifies, which does not occur on the
present 12-scenario set.

## 4. Per-bug API coverage

The v1 acquire/release lists are a union over the 5 reference bugs. v2 (per-pattern
configuration) will narrow them; for v1 a union is acceptable because mismatches still
fire — a bug with one acquire API (e-09 uses `of_get_child_by_name`, etc.) is unaffected
by the presence of unrelated names in the list (no calls = no count contribution).

| bug   | acquire API(s) referenced              | release API(s)  | counts (acq/rel/goto/ret/if) |
|-------|----------------------------------------|-----------------|------------------------------|
| e-01  | `of_find_node_by_path`, `of_find_node_opts_by_path` (+ `dt_alloc` via fn-pointer; not detected) | none in buggy   | 5/0/0/2/11 |
| e-02  | `of_find_node_by_path`, `kzalloc`      | none in buggy   | 2/0/0/4/10 |
| e-06  | `realloc`, `malloc`, `calloc`          | `free` (1x)     | 3/1/1/6/12 |
| tp-01 | `of_find_matching_node`                | none in buggy   | 1/0/0/2/1 |
| e-09  | `of_get_child_by_name`, `of_parse_phandle`, `of_get_next_child`, `kzalloc`, `kmalloc`, `kcalloc` | `of_node_put` (6x in error paths) | 6/6/6/4/10 |

> e-01's `dt_alloc` is invoked via a function pointer (`void *(*dt_alloc)(u64, u64)`); the
> CodeQL `getTarget()` resolves the static target only, so the indirect call is not
> counted. This is a v1-known-limitation and is **not** a calibration miss because the
> e-01 self-pair compares the same file on both sides — the missed call is consistently
> missed on both, leaving counts equal.

## 5. Decision — version pinning

v1 passes calibration on every reference bug. We **pin v1 for all five patterns** in
`verifier-vN.json`. v2 (structural fingerprint) is deferred to D2.5+ if any of the
following triggers fire during D4 generation:

- v1 emits OK on a regenerated POC that downstream pair-wise scoring rejects (false-OK)
- the same POC repeatedly fails v1 on a single dimension with the LLM unable to fix it
  (suggesting the dimension is too strict for the pattern; v1 → v2 swap)
- a new pattern is added whose acquire/release vocabulary is not in the v1 union list
  (v1 → v2 swap with per-pattern config)

## 6. Known v1 limitations (forward-looking)

These do **not** affect the present calibration set but **will** likely fire on real
LLM-generated POCs during D4:

1. **Same-count-different-shape (too-loose)**: a POC that hits identical (acq, rel, goto, ret, if)
   counts but with a structurally different control-flow skeleton will pass v1 incorrectly.
   v2's F3.b (label-has-release boolean), F2.b (max nesting depth), and F5.b
   (per-exit-path released boolean) catch this.
2. **Stub-induced count drift (too-strict)**: a faithful POC may add 1 extra `if (!ptr) return;`
   stub guard relative to the seed slice, changing both F2.if (+1) and F5.return (+1).
   v2 with ±1 tolerance on size-related counts addresses this. v1 would reject; an LLM
   regen loop is the temporary workaround.
3. **Indirect calls invisible**: function-pointer dispatch (e-01's `dt_alloc`) is not
   resolved. v2 would not change this; a per-pattern allowlist with regex
   names would.

## 7. Files produced

- `verifier-v1.ql` — the QL query (calibrated)
- `qlpack.yml` — pack metadata so `import cpp` resolves
- `run-verifier.sh` — single-scenario runner (build 2-TU mini-DB → run query → print verdict)
- `run-calibration.sh` — full matrix driver
- `calibration-fixtures/e01-corrupt.c` — the dead-goto corruption fixture
- `calibration-stdout.log` — captured stdout of last calibration run
- `calibration-work/<scenario>/` — per-scenario `db/`, `build.log`, `analyze.log`, `verdict.csv`
- `verifier-vN.json` — version pinning manifest (this run: all 5 patterns → v1)

## 8. Time budget actual

Plan budgeted 2–3 hours for D2.5. Actual: ~1.5 hours (single session, no v2 needed yet).
Bank ~1 hour for v2 prototype if a D4 regen fails.
