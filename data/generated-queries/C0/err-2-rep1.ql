/**
 * @name Missing error return code before goto cleanup
 * @description A function that returns int error codes detects a failure condition
 *              (allocation failure or zero/negative count) and jumps to a cleanup label,
 *              but the error path does not assign a negative errno to the return
 *              variable. The function therefore returns 0 (success) despite the failure,
 *              hiding the error from the caller.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-return-code-before-goto
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

/** A function that returns a signed integer error code (e.g. -ENOMEM). */
class IntReturningFunction extends Function {
  IntReturningFunction() {
    this.getType().getUnspecifiedType() instanceof IntType and
    // Must contain at least one assignment to an errno-like negative value
    exists(AssignExpr a |
      a.getEnclosingFunction() = this and
      a.getRValue().getValue().toInt() < 0
    )
  }
}

/** A local variable used to hold the return code (commonly named `ret`, `err`, `rc`, `error`). */
class RetVariable extends LocalVariable {
  RetVariable() {
    this.getFunction() instanceof IntReturningFunction and
    this.getType().getUnspecifiedType() instanceof IntType and
    this.getName().regexpMatch("(?i)ret|err|rc|error|status|rv")
  }
}

/** A return statement that returns the value of a RetVariable. */
predicate returnsRetVariable(ReturnStmt rs, RetVariable v) {
  exists(VariableAccess va |
    va = rs.getExpr().(VariableAccess) and
    va.getTarget() = v
  )
}

/** A function that allocates memory or counts phandles — returns NULL/zero/negative on failure. */
class FailableCall extends FunctionCall {
  FailableCall() {
    exists(string n | n = this.getTarget().getName() |
      n.matches("kmalloc%") or
      n.matches("kzalloc%") or
      n.matches("kcalloc%") or
      n.matches("vmalloc%") or
      n.matches("vzalloc%") or
      n.matches("kmem_cache_alloc%") or
      n.matches("devm_kzalloc%") or
      n.matches("devm_kcalloc%") or
      n.matches("devm_kmalloc%") or
      n = "of_count_phandle_with_args" or
      n = "of_property_count_strings" or
      n = "of_property_count_u32_elems" or
      n.matches("of_count_%") or
      n = "of_get_child_count"
    )
  }
}

/** A goto-statement that jumps to a cleanup label (commonly `end`, `out`, `err`, `cleanup`, `fail`). */
class CleanupGoto extends GotoStmt {
  CleanupGoto() {
    this.getName().regexpMatch("(?i)end|out|out_.*|err|err_.*|fail|fail_.*|cleanup|done|unlock|free|release|exit")
  }
}

/**
 * Holds if `g` is a goto to a cleanup label that is reached due to a failure of `fc`
 * (either NULL pointer or zero/negative count check), but no assignment to `ret`
 * with a negative value happens between the check and the goto on the same path.
 */
predicate badErrorPathToGoto(FailableCall fc, CleanupGoto g, RetVariable ret, IfStmt ifs) {
  // The failable call result is checked in `ifs`
  exists(Variable checked, Expr cond |
    cond = ifs.getCondition() and
    (
      // pattern: if (!__tcbp) — NULL check on the variable that received the call
      cond.(NotExpr).getOperand().(VariableAccess).getTarget() = checked
      or
      // pattern: if (!count)
      cond.(NotExpr).getOperand().(VariableAccess).getTarget() = checked
      or
      // pattern: if (count <= 0)
      exists(RelationalOperation ro | ro = cond and
        ro.getAnOperand().(VariableAccess).getTarget() = checked)
      or
      // pattern: if (count == 0) / if (count < 0)
      exists(EqualityOperation eo | eo = cond and
        eo.getAnOperand().(VariableAccess).getTarget() = checked)
    ) and
    // checked is assigned the result of fc
    exists(AssignExpr ae |
      ae.getLValue().(VariableAccess).getTarget() = checked and
      ae.getRValue() = fc
    )
    or
    // direct check: if (!fc()) — inline
    exists(FunctionCall innerFc |
      innerFc = cond.(NotExpr).getOperand() and innerFc = fc
    )
  ) and
  // ret is the return variable of the enclosing function
  ret.getFunction() = ifs.getEnclosingFunction() and
  ret.getFunction() = g.getEnclosingFunction() and
  ret.getFunction() = fc.getEnclosingFunction() and
  // the goto is in the then-branch of the if (the failure path)
  g.getParentStmt*() = ifs.getThen() and
  // there exists at least one return-statement at the cleanup label area that
  // returns the value of ret (i.e. function returns `ret`)
  exists(ReturnStmt rs | returnsRetVariable(rs, ret) and
    rs.getEnclosingFunction() = g.getEnclosingFunction()) and
  // No assignment of a negative value to ret appears inside the then-branch
  // before the goto
  not exists(AssignExpr ae |
    ae.getLValue().(VariableAccess).getTarget() = ret and
    ae.getRValue().getValue().toInt() < 0 and
    ae.getEnclosingStmt().getParentStmt*() = ifs.getThen()
  ) and
  // Also: ret must not have been initialized to a negative value at its
  // declaration (otherwise the goto is fine).
  not exists(Expr init |
    init = ret.getInitializer().getExpr() and
    init.getValue().toInt() < 0
  ) and
  // And: ret is not unconditionally set to a negative value before the if.
  not exists(AssignExpr ae |
    ae.getLValue().(VariableAccess).getTarget() = ret and
    ae.getRValue().getValue().toInt() < 0 and
    ae.getEnclosingStmt().(ExprStmt) = ifs.getEnclosingBlock().getAStmt() and
    // ae appears textually before ifs
    ae.getLocation().getStartLine() < ifs.getLocation().getStartLine()
  )
}

from FailableCall fc, CleanupGoto g, RetVariable ret, IfStmt ifs
where badErrorPathToGoto(fc, g, ret, ifs)
select g,
  "Goto to cleanup label '" + g.getName() +
    "' on failure path of $@ does not set error code in $@; function may return success despite failure.",
  fc, fc.getTarget().getName(), ret, ret.getName()
