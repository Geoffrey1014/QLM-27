/**
 * @name Missing error code assignment before goto cleanup
 * @description A failure-handling branch (NULL-check on an allocator, or
 *              zero/negative-check on a count/lookup helper) uses `goto`
 *              to a cleanup label that returns a status variable, but does
 *              not assign a negative errno to that variable on this path.
 *              The function will then return whatever value the status
 *              variable held previously (often 0), silently reporting
 *              success on a real failure.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-err-code-before-goto
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A function-like name that returns a kernel resource that, on failure,
 * yields NULL (allocators) — failure is detected by `!x` style checks.
 */
predicate allocatorName(string n) {
  n = "kcalloc" or n = "kmalloc" or n = "kzalloc" or n = "kmalloc_array" or
  n = "kvmalloc" or n = "kvzalloc" or n = "kvcalloc" or n = "vmalloc" or
  n = "vzalloc" or n = "devm_kzalloc" or n = "devm_kcalloc" or
  n = "devm_kmalloc" or n = "devm_kmalloc_array" or n = "krealloc" or
  n = "kmemdup" or n = "kstrdup" or n = "kasprintf"
}

/**
 * A function-like name that returns a count / handle / index where
 * failure is encoded as `<= 0` or `== 0` (no items, or negative errno).
 */
predicate countLikeName(string n) {
  n = "of_count_phandle_with_args" or
  n = "of_property_count_u32_elems" or
  n = "of_property_count_u64_elems" or
  n = "of_property_count_strings" or
  n = "of_get_child_count" or
  n = "of_get_available_child_count" or
  n = "platform_irq_count" or
  n = "of_irq_count"
}

/** A call to one of the above helpers. */
class InterestingCall extends FunctionCall {
  InterestingCall() {
    allocatorName(this.getTarget().getName()) or
    countLikeName(this.getTarget().getName())
  }
}

/**
 * A GotoStmt jumping to a label inside a function whose body returns an
 * `int` status variable. We use the goto target as a stand-in for "cleanup
 * path".
 */
class CleanupGoto extends GotoStmt {
  CleanupGoto() {
    exists(string n |
      n = this.getName() and
      (n = "end" or n = "out" or n = "err" or n = "fail" or n = "exit" or
       n = "cleanup" or n.matches("out_%") or n.matches("err_%") or
       n.matches("fail_%") or n.matches("free_%") or n.matches("put_%"))
    )
  }
}

/**
 * The `if (cond) { ... goto L; }` block where `cond` is a failure test
 * derived from one of the interesting calls, and the body of the `then`
 * branch does NOT assign to any local variable of integer type that is
 * (textually) used as a return value via `return ret;` style.
 */
from
  Function f, IfStmt ifs, InterestingCall ic, CleanupGoto g,
  LocalVariable retVar, ReturnStmt rs
where
  ifs.getEnclosingFunction() = f and
  g.getEnclosingFunction() = f and
  ic.getEnclosingFunction() = f and
  // The if-condition mentions the call's result (directly or via a variable
  // assigned from the call).
  (
    ifs.getCondition().getAChild*() = ic
    or
    exists(Variable v, AssignExpr ae |
      ae.getLValue().(VariableAccess).getTarget() = v and
      ae.getRValue() = ic and
      ifs.getCondition().getAChild*().(VariableAccess).getTarget() = v
    )
    or
    exists(Variable v, DeclStmt ds, Initializer init |
      ds.getADeclaration() = v and
      v.getInitializer() = init and
      init.getExpr() = ic and
      ifs.getCondition().getAChild*().(VariableAccess).getTarget() = v
    )
  ) and
  // The then-branch contains the goto to cleanup.
  g.getParent*() = ifs.getThen() and
  // The function has a return statement of an integer variable.
  rs.getEnclosingFunction() = f and
  rs.getExpr().(VariableAccess).getTarget() = retVar and
  retVar.getType().getUnspecifiedType() instanceof IntType and
  // The then-branch does NOT assign to retVar before the goto.
  not exists(AssignExpr ae |
    ae.getEnclosingFunction() = f and
    ae.getLValue().(VariableAccess).getTarget() = retVar and
    ae.getParent*() = ifs.getThen()
  ) and
  // retVar is not the same variable being NULL-checked.
  not ifs.getCondition().getAChild*().(VariableAccess).getTarget() = retVar
select g,
  "Goto to cleanup label '" + g.getName() +
    "' on a failure path of $@, without assigning an error code to return variable '" +
    retVar.getName() + "'.",
  ic, ic.getTarget().getName()
