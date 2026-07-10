/**
 * @name  rq3-c2-mc-3-rep2
 * @id    cpp/rq3/c2/mc-3-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects use-before-NULL-check: a pointer variable is dereferenced
 *              earlier in a function than it is checked for NULL.
 */

import cpp

predicate isNullCheckOnVar(Expr check, Variable v) {
  exists(EQExpr eq | eq = check |
    eq.getAnOperand().(VariableAccess).getTarget() = v and
    eq.getAnOperand().getValue() = "0"
  )
  or
  exists(NEExpr ne | ne = check |
    ne.getAnOperand().(VariableAccess).getTarget() = v and
    ne.getAnOperand().getValue() = "0"
  )
  or
  exists(NotExpr n | n = check |
    n.getOperand().(VariableAccess).getTarget() = v
  )
}

predicate isDerefOfVar(Expr deref, Variable v) {
  exists(PointerFieldAccess pfa | pfa = deref |
    pfa.getQualifier().(VariableAccess).getTarget() = v
  )
  or
  exists(PointerDereferenceExpr pde | pde = deref |
    pde.getOperand().(VariableAccess).getTarget() = v
  )
  or
  exists(ArrayExpr ae | ae = deref |
    ae.getArrayBase().(VariableAccess).getTarget() = v
  )
}

predicate paramOrLocal(Variable v, Function f) {
  v.(Parameter).getFunction() = f
  or
  exists(LocalVariable lv | lv = v | lv.getFunction() = f)
}

predicate derefBeforeCheck(Function f, Variable v, Expr deref, Expr check) {
  paramOrLocal(v, f) and
  isDerefOfVar(deref, v) and
  isNullCheckOnVar(check, v) and
  deref.getEnclosingFunction() = f and
  check.getEnclosingFunction() = f and
  exists(Location ld, Location lc | ld = deref.getLocation() and lc = check.getLocation() |
    ld.getStartLine() < lc.getStartLine()
    or
    (ld.getStartLine() = lc.getStartLine() and ld.getStartColumn() < lc.getStartColumn())
  )
}

from Function f, Variable v, Expr deref, Expr check
where derefBeforeCheck(f, v, deref, check)
select deref,
  "Pointer '" + v.getName() + "' is dereferenced here but later NULL-checked at $@ in function " +
    f.getName() + ".", check, check.toString()
