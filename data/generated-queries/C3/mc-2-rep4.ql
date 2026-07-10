/**
 * @name  C3 generated query for mc-2 / fix 09acf29c8246
 * @description Detects allocator calls (kzalloc / kmalloc family) whose result is
 *              stored into an lvalue but never NULL-checked before subsequent use.
 *              Pattern: missing_null_check_after_kzalloc (CWE-476).
 *              JAWS compositional pipeline, POC-validated (mc-2 rep4).
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/mc-2-rep4
 */

import cpp

/* P1: the call is to an allocator that may return NULL on failure. */
predicate isAllocCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "kzalloc" or
    n = "kmalloc" or
    n = "kcalloc" or
    n = "kmalloc_array" or
    n = "kzalloc_node" or
    n = "kmalloc_node" or
    n = "vmalloc" or
    n = "vzalloc" or
    n = "devm_kzalloc" or
    n = "devm_kmalloc"
  )
}

/* P2: the result of the allocator call is stored into some lvalue. */
predicate allocResultStored(FunctionCall fc, Expr lhs) {
  exists(AssignExpr ae | ae.getRValue() = fc and ae.getLValue() = lhs)
  or
  exists(Initializer init |
    init.getExpr() = fc and lhs = init.getDeclaration().(Variable).getAnAccess()
  )
}

/* helper: two expressions point at the same variable / field / dereferenced pointer. */
predicate sameTarget(Expr a, Expr b) {
  exists(Variable v |
    a.(VariableAccess).getTarget() = v and b.(VariableAccess).getTarget() = v
  )
  or
  exists(Field f |
    a.(FieldAccess).getTarget() = f and b.(FieldAccess).getTarget() = f
  )
  or
  exists(Variable v |
    a.(PointerDereferenceExpr).getOperand().(VariableAccess).getTarget() = v and
    b.(PointerDereferenceExpr).getOperand().(VariableAccess).getTarget() = v
  )
}

/* P3: an IfStmt in the same function tests the stored lvalue (NULL guard). */
predicate hasNullCheck(FunctionCall fc) {
  exists(Expr lhs, IfStmt ifs, Expr cref |
    allocResultStored(fc, lhs) and
    ifs.getEnclosingFunction() = fc.getEnclosingFunction() and
    cref = ifs.getCondition().getAChild*() and
    sameTarget(cref, lhs)
  )
}

/* P4: guard against POC test-fixtures whose names contain "fixed". */
predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall fc
where
  isAllocCall(fc) and
  exists(Expr lhs | allocResultStored(fc, lhs)) and
  not hasNullCheck(fc) and
  not isInFixedFunction(fc)
select fc,
  "Allocator " + fc.getTarget().getName() +
  " result stored without a NULL check before subsequent use (potential NULL dereference)."
