/**
 * @name Missing error code assignment before goto cleanup on allocation failure
 * @description Detects allocation-failure branches that jump to a cleanup label
 *              without first assigning an error code to the function's return
 *              variable, so the function silently returns 0 (success) despite
 *              having failed.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-code-before-goto
 * @tags correctness
 *       error-handling
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions whose return value indicates allocation success/failure via NULL.
 * Generalised beyond the patched `vzalloc` to the full mainline allocator
 * family that returns NULL on failure.
 */
predicate isAllocReturningNullOnFailure(Function f) {
  f.getName() =
    [
      "vzalloc", "vmalloc", "vzalloc_node", "vmalloc_node", "vmalloc_user",
      "kmalloc", "kzalloc", "kcalloc", "kmalloc_array", "krealloc",
      "kmalloc_node", "kzalloc_node",
      "kmem_cache_alloc", "kmem_cache_zalloc",
      "alloc_percpu", "__alloc_percpu",
      "devm_kzalloc", "devm_kmalloc", "devm_kcalloc",
      "alloc_pages", "__get_free_pages", "get_zeroed_page",
      "kstrdup", "kstrndup", "kmemdup",
      "alloc_workqueue", "alloc_skb", "alloc_etherdev",
      "ioremap", "ioremap_nocache"
    ]
}

/** A call to an allocator whose result is checked against NULL. */
class AllocCall extends FunctionCall {
  AllocCall() { isAllocReturningNullOnFailure(this.getTarget()) }
}

/**
 * A local "ret"-like variable that holds the function's intended return value.
 * Heuristic: an int/long-typed local whose name hints at error reporting.
 */
class RetVar extends LocalVariable {
  RetVar() {
    this.getType().getUnspecifiedType() instanceof IntegralType and
    this.getName().toLowerCase() in [
      "ret", "rc", "err", "error", "retval", "result", "status"
    ]
  }
}

/**
 * The variable assigned the alloc result (the "critical variable").
 * It is either an explicit assignment `v = alloc(...)` or an initializer.
 */
predicate assignedFromAlloc(Variable v, AllocCall ac) {
  exists(AssignExpr ae | ae.getLValue() = v.getAnAccess() and ae.getRValue() = ac)
  or
  exists(Initializer init | init.getDeclaration() = v and init.getExpr() = ac)
}

/**
 * `gs` is an IfStmt that tests `v` for NULL-ness in its condition
 * (covers `if (!v)`, `if (v == NULL)`, `if (v == 0)`).
 */
predicate ifTestsForNull(IfStmt ifs, Variable v) {
  exists(Expr cond | cond = ifs.getCondition().getFullyConverted().(Expr) |
    // `if (!v)`
    exists(NotExpr ne |
      ne = ifs.getCondition().getAChild*() and ne.getOperand() = v.getAnAccess()
    )
    or
    // `if (v == NULL)` / `if (v == 0)`
    exists(EQExpr eq |
      eq = ifs.getCondition().getAChild*() and
      eq.getAnOperand() = v.getAnAccess() and
      eq.getAnOperand().getValue() = "0"
    )
  )
}

/**
 * The error-handling block of an if(NULL) test:
 * the "then" branch of `if (!v)` or `if (v == NULL)`.
 */
predicate errorBlockFor(Variable v, Stmt errBlock) {
  exists(IfStmt ifs |
    ifTestsForNull(ifs, v) and
    errBlock = ifs.getThen()
  )
}

/**
 * Does `s` (or any nested sub-statement) assign to `ret`?
 */
predicate assignsRet(Stmt s, RetVar ret) {
  exists(AssignExpr ae |
    ae.getEnclosingStmt() = s.getAChild*() and
    ae.getLValue() = ret.getAnAccess()
  )
  or
  exists(AssignExpr ae |
    ae.getEnclosingStmt() = s and
    ae.getLValue() = ret.getAnAccess()
  )
}

/**
 * Does `s` contain a `goto` to some label (cleanup-style early exit)?
 */
predicate containsGoto(Stmt s, GotoStmt g) {
  g = s
  or
  g.getParent+() = s
}

/**
 * Does `s` contain an explicit `return <expr>` with a non-zero/error value?
 * Used to exclude branches that already return directly with a constant.
 */
predicate containsExplicitReturn(Stmt s) {
  exists(ReturnStmt r | r.getParent*() = s)
}

from
  Function f, AllocCall ac, Variable critVar, Stmt errBlock,
  GotoStmt g, RetVar ret
where
  ac.getEnclosingFunction() = f and
  assignedFromAlloc(critVar, ac) and
  errorBlockFor(critVar, errBlock) and
  containsGoto(errBlock, g) and
  not containsExplicitReturn(errBlock) and
  ret.getFunction() = f and
  // The function returns an integer error code.
  f.getType().getUnspecifiedType() instanceof IntegralType and
  // The error block does NOT assign to the return variable.
  not assignsRet(errBlock, ret) and
  // The function does have a `return ret;` somewhere (so `ret` is the channel).
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr() = ret.getAnAccess()
  ) and
  // The goto target is reached without ret being assigned in between
  // (label is the cleanup path; we approximate by requiring the goto is the
  // immediate exit of the error block).
  g.getEnclosingFunction() = f
select g,
  "Allocation of '" + critVar.getName() + "' via '" + ac.getTarget().getName() +
    "' failed but '" + ret.getName() +
    "' is not assigned an error code before jumping to cleanup label '" +
    g.getName() + "'; function may return success (0) on failure."
