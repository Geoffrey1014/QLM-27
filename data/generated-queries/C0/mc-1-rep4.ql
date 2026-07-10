/**
 * @name Unchecked regmap_*_read return value
 * @description Calls to regmap_read / regmap_bulk_read / regmap_raw_read / regmap_noinc_read
 *              (and friends) can return non-zero error codes on failure. Ignoring the return
 *              value and proceeding to use the (potentially uninitialised / stale) buffer
 *              leads to incorrect device behaviour. This query flags call sites where the
 *              return value is discarded.
 * @kind problem
 * @problem.severity warning
 * @id cpp/regmap-read-unchecked
 * @tags reliability
 *       correctness
 *       linux-kernel
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions in the regmap family that read from a device and return an
 * int error code (0 on success, negative errno on failure). We intentionally
 * generalise beyond `regmap_bulk_read` (the API the patch fixed) to the
 * full read-family because the same "ignore return value" bug occurs for
 * all of them.
 */
predicate isRegmapReadFn(Function f) {
  exists(string n | n = f.getName() |
    n = "regmap_read" or
    n = "regmap_raw_read" or
    n = "regmap_bulk_read" or
    n = "regmap_noinc_read" or
    n = "regmap_multi_reg_read" or
    n = "regmap_fields_read" or
    n = "regmap_async_complete" or
    n = "regmap_field_read" or
    n = "regmap_test_bits"
  )
}

/**
 * A call whose result is discarded: the call is used as an
 * ExprStmt (i.e. `foo(...);` with no assignment, no comparison, no cast).
 */
predicate isResultDiscarded(FunctionCall fc) {
  // The expression statement parent means the call's value is thrown away.
  exists(ExprStmt es | es.getExpr() = fc)
  or
  // Cast to void: also discarded.
  exists(CStyleCast c | c.getExpr() = fc and c.getType() instanceof VoidType)
}

/**
 * The call appears inside an IRQ handler or other callback whose name
 * hints at interrupt / completion / timer context where silently
 * proceeding on a failed read is especially dangerous. We don't restrict
 * to this though — we just flag all unchecked sites.
 */
predicate inRiskyContext(FunctionCall fc) {
  exists(Function enclosing | enclosing = fc.getEnclosingFunction() |
    enclosing.getName().matches("%irq%") or
    enclosing.getName().matches("%isr%") or
    enclosing.getName().matches("%handler%") or
    enclosing.getName().matches("%interrupt%") or
    enclosing.getName().matches("%timer%") or
    enclosing.getName().matches("%poll%") or
    enclosing.getName().matches("%work%")
  )
}

from FunctionCall fc, Function target
where
  fc.getTarget() = target and
  isRegmapReadFn(target) and
  isResultDiscarded(fc)
select fc,
  "Return value of " + target.getName() +
    "() is discarded; on I/O failure the read buffer is undefined and downstream " +
    "use (e.g. mod_timer / report) proceeds with stale data."
