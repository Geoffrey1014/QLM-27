/**
 * @name Missing error return code on allocation-failure goto
 * @description An allocator call returns NULL, and the failure branch jumps to an error
 *              cleanup label via `goto` without first assigning an error code (e.g. -ENOMEM)
 *              to the function's status/return variable. The cleanup label then returns the
 *              previously-set status, causing the function to wrongly report success or an
 *              unrelated error code.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-err-code-on-alloc-fail-goto
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Names of kernel allocator-like functions whose NULL return indicates failure
 * and which conventionally require -ENOMEM (or similar) to be propagated.
 */
bindingset[n]
predicate isAllocLikeName(string n) {
  n = "kmalloc" or n = "kzalloc" or n = "kcalloc" or n = "krealloc" or
  n = "kmalloc_array" or n = "kmemdup" or n = "kstrdup" or n = "kstrndup" or
  n = "vmalloc" or n = "vzalloc" or n = "vmalloc_array" or
  n = "devm_kmalloc" or n = "devm_kzalloc" or n = "devm_kcalloc" or
  n = "devm_kmemdup" or n = "devm_kstrdup" or
  n = "kmem_cache_alloc" or n = "kmem_cache_zalloc" or
  n = "alloc_skb" or n = "alloc_netdev" or n = "alloc_etherdev" or
  n = "alloc_workqueue" or n = "create_workqueue" or n = "create_singlethread_workqueue" or
  n = "of_get_child_by_name" or n = "of_find_node_by_name" or
  // allocator family from the seed patch and close cousins
  n.matches("%_alloc") or
  n.matches("alloc_%") or
  n.matches("%kzalloc%") or
  n.matches("%kmalloc%")
}

/** A call to an allocator-like function whose result is assigned to a local variable. */
class AllocAssign extends ExprStmt {
  LocalScopeVariable lhsVar;
  FunctionCall allocCall;

  AllocAssign() {
    exists(AssignExpr a |
      a = this.getExpr() and
      a.getLValue() = lhsVar.getAnAccess() and
      allocCall = a.getRValue() and
      isAllocLikeName(allocCall.getTarget().getName())
    )
    or
    exists(Initializer init |
      init.getExpr() = allocCall and
      init.getDeclaration() = lhsVar and
      isAllocLikeName(allocCall.getTarget().getName()) and
      this.getEnclosingFunction() = allocCall.getEnclosingFunction()
    )
  }

  LocalScopeVariable getLhs() { result = lhsVar }

  FunctionCall getAllocCall() { result = allocCall }
}

/** A NULL-check on `v` whose then-branch goto-jumps to a label. */
class NullCheckGoto extends IfStmt {
  LocalScopeVariable v;
  GotoStmt g;

  NullCheckGoto() {
    // condition is essentially `!v` or `v == NULL`
    exists(Expr cond | cond = this.getCondition() |
      cond.(NotExpr).getOperand() = v.getAnAccess()
      or
      exists(EQExpr eq | eq = cond and
        eq.getAnOperand() = v.getAnAccess() and
        eq.getAnOperand().getValue() = "0"
      )
    ) and
    // then-branch contains an unconditional goto, with no preceding assignment to a likely
    // status/error variable inside the then-branch.
    g.getEnclosingStmt+() = this.getThen() and
    not exists(AssignExpr a |
      a.getEnclosingStmt().getParentStmt*() = this.getThen() and
      a.getLValue() instanceof VariableAccess
    )
  }

  LocalScopeVariable getCheckedVar() { result = v }

  GotoStmt getGoto() { result = g }

  Stmt getJumpTarget() { result = g.getTarget() }
}

/**
 * The enclosing function returns `int` (so an error-code convention applies)
 * and has at least one explicit `return <variable>;` somewhere reachable from
 * the goto target — implying the cleanup label propagates a status variable.
 */
predicate functionPropagatesStatus(Function f) {
  f.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr() instanceof VariableAccess
  )
}

from AllocAssign aa, NullCheckGoto nc, Function f
where
  f = aa.getEnclosingFunction() and
  f = nc.getEnclosingFunction() and
  nc.getCheckedVar() = aa.getLhs() and
  // null-check follows the allocation (same basic-block ordering by location)
  aa.getLocation().getStartLine() < nc.getLocation().getStartLine() and
  functionPropagatesStatus(f) and
  // jump target is a label inside the same function (cleanup label)
  nc.getJumpTarget().getEnclosingFunction() = f
select nc, "Possible missing error-code assignment: allocation '" +
  aa.getAllocCall().getTarget().getName() +
  "' returns NULL and control jumps via goto without setting an error status."
