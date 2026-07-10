/**
 * @name JAWS seed<->POC consistency verifier v1 (count-based)
 * @description Compares structural feature counts (F1 acquire/release,
 *              F2.basic control-flow, F3.count goto, F5.count returns)
 *              between two source files in a mini-DB and reports any
 *              mismatch. The two files are identified by environment-
 *              independent stem prefixes: the file whose base name
 *              starts with the value of the `seed_prefix` extensible
 *              predicate is taken as the seed-patch slice; the other
 *              candidate file (matching `poc_prefix`) is taken as the
 *              POC. The query emits exactly one row per dimension
 *              compared, with verdict OK / MISMATCH.
 *
 *              v1 weakness (documented per §5.5.3): count-equality is
 *              too strict (POC may legitimately have +1 stub if-stmt)
 *              AND too loose (3 gotos in seed and POC may serve
 *              different purposes). Escalate to v2 when this trips.
 *
 *              This query is intended to be driven by
 *              `run-verifier.sh`, which constructs a 2-file DB from
 *              the seed slice + POC pair, sets the prefixes via
 *              command-line --tuple-vars, and parses the row stream.
 *
 * @kind problem
 * @problem.severity warning
 * @id qlm/verifier-v1
 */

import cpp

/* ---------------------------------------------------------------------
 * Configurable API set (broad enough to cover the 5 calibration bugs:
 * e-01 / e-02 / e-06 / tp-01 / e-09). The verifier is per-pattern in
 * the full pipeline, so this set will be parameterised at run time in
 * v2; for v1 we ship a union list and let the count comparison handle
 * patterns where only a subset is referenced.
 * ------------------------------------------------------------------- */

predicate isAcquireApi(string name) {
  name = "of_find_node_by_path" or
  name = "of_find_node_opts_by_path" or
  name = "of_find_matching_node" or
  name = "of_find_compatible_node" or
  name = "of_get_child_by_name" or
  name = "of_get_next_child" or
  name = "of_get_parent" or
  name = "of_parse_phandle" or
  name = "kzalloc" or
  name = "kmalloc" or
  name = "kcalloc" or
  name = "malloc" or
  name = "calloc" or
  name = "realloc"
}

predicate isReleaseApi(string name) {
  name = "of_node_put" or
  name = "kfree" or
  name = "free"
}

/* ---------------------------------------------------------------------
 * Per-file feature extractor. Joins only on the file (cheap), then
 * runs five counts at once. Anonymous Microsoft-Office-style helpers
 * are inlined for clarity.
 * ------------------------------------------------------------------- */
predicate fileFeaturesV1(
  File f, int nAcquire, int nRelease, int nGoto, int nReturn, int nIf
) {
  f.fromSource() and
  nAcquire = count(FunctionCall c |
                     c.getFile() = f and isAcquireApi(c.getTarget().getName())) and
  nRelease = count(FunctionCall c |
                     c.getFile() = f and isReleaseApi(c.getTarget().getName())) and
  nGoto    = count(GotoStmt g     | g.getLocation().getFile() = f) and
  nReturn  = count(ReturnStmt r   | r.getLocation().getFile() = f) and
  nIf      = count(IfStmt i       | i.getLocation().getFile() = f)
}

/* ---------------------------------------------------------------------
 * Seed/POC pairing.
 *
 * Convention adopted by `run-verifier.sh`:
 *   - copy the seed slice into the mini-DB as `seed_<bug>.c`
 *   - copy the POC slice into the mini-DB as `poc_<bug>.c`
 * The verifier picks them up by base-name prefix.
 * ------------------------------------------------------------------- */
predicate isSeedFile(File f) {
  f.fromSource() and f.getBaseName().matches("seed_%")
}

predicate isPocFile(File f) {
  f.fromSource() and f.getBaseName().matches("poc_%")
}

/* ---------------------------------------------------------------------
 * Per-dimension consistency.
 *
 * Each mismatching dimension emits its own row; if every dimension
 * matches, a single OK row is emitted. The `@kind problem` schema
 * needs (Element, string); we anchor the Element on the POC file so
 * the row points at the artifact under test.
 * ------------------------------------------------------------------- */
from File seed, File poc, string verdict
where
  isSeedFile(seed) and
  isPocFile(poc) and
  exists(int a1, int r1, int g1, int ret1, int if1,
         int a2, int r2, int g2, int ret2, int if2 |
    fileFeaturesV1(seed, a1, r1, g1, ret1, if1) and
    fileFeaturesV1(poc,  a2, r2, g2, ret2, if2) and
    (
      a1 != a2 and verdict = "MISMATCH(F1.acquire: seed=" + a1 + ", poc=" + a2 + ")"
      or
      r1 != r2 and verdict = "MISMATCH(F1.release: seed=" + r1 + ", poc=" + r2 + ")"
      or
      g1 != g2 and verdict = "MISMATCH(F3.goto: seed=" + g1 + ", poc=" + g2 + ")"
      or
      ret1 != ret2 and verdict = "MISMATCH(F5.return: seed=" + ret1 + ", poc=" + ret2 + ")"
      or
      if1 != if2 and verdict = "MISMATCH(F2.if: seed=" + if1 + ", poc=" + if2 + ")"
      or
      a1 = a2 and r1 = r2 and g1 = g2 and ret1 = ret2 and if1 = if2 and
      verdict = "OK(F1.acq=" + a1 + " F1.rel=" + r1 + " F3.goto=" + g1 +
                " F5.ret=" + ret1 + " F2.if=" + if1 + ")"
    )
  )
select poc, verdict
