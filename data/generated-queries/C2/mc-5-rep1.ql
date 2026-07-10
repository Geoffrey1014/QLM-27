/**
 * @name  rq3-c2-mc-5-rep1
 * @id    cpp/rq3/c2/mc-5-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects allocation calls (devm_kcalloc / kmalloc family) whose
 *              result is assigned to a variable that is later used without a
 *              NULL check being performed first.
 */

import cpp
import semmle.code.cpp.controlflow.Guards

predicate isAllocCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "devm_kcalloc" or
    n = "devm_kmalloc" or
    n = "devm_kzalloc" or
    n = "kcalloc" or
    n = "kmalloc" or
    n = "kzalloc" or
    n = "kmalloc_array"
  )
}

predicate assignsToVariable(FunctionCall fc, Variable v) {
  exists(Assignment a |
    a.getRValue() = fc and
    a.getLValue() = v.getAnAccess()
  )
  or
  exists(Initializer init |
    init.getExpr() = fc and
    init.getDeclaration() = v
  )
}

predicate hasNullCheck(FunctionCall fc, Variable v) {
  assignsToVariable(fc, v) and
  exists(GuardCondition g, VariableAccess va |
    va = v.getAnAccess() and
    g.controls(va.getBasicBlock(), _) and
    (
      g = va or
      exists(EqualityOperation eq |
        eq = g and
        (eq.getAnOperand() = va or eq.getAnOperand().(VariableAccess).getTarget() = v)
      )
    )
  )
  or
  // simple syntactic form: if (!v) or if (v == NULL) after the assignment
  exists(IfStmt ifs, Expr cond |
    cond = ifs.getCondition() and
    (
      cond.(NotExpr).getOperand().(VariableAccess).getTarget() = v or
      cond.(VariableAccess).getTarget() = v or
      exists(EqualityOperation eq |
        eq = cond and
        eq.getAnOperand().(VariableAccess).getTarget() = v
      )
    ) and
    assignsToVariable(fc, v)
  )
}

predicate isUsedAfter(Variable v, FunctionCall fc) {
  assignsToVariable(fc, v) and
  exists(VariableAccess va |
    va = v.getAnAccess() and
    va != fc.getAChild*() and
    (
      va.getEnclosingFunction() = fc.getEnclosingFunction() and
      va.getLocation().getStartLine() > fc.getLocation().getStartLine()
      or
      va.getEnclosingFunction() != fc.getEnclosingFunction()
    )
  )
}

predicate missingNullCheck(FunctionCall fc, Variable v) {
  isAllocCall(fc) and
  assignsToVariable(fc, v) and
  isUsedAfter(v, fc) and
  not hasNullCheck(fc, v)
}

from FunctionCall fc, Variable v
where missingNullCheck(fc, v)
select fc,
  "Allocation result assigned to '" + v.getName() +
    "' is used later without a NULL check (missing-check pattern)."
