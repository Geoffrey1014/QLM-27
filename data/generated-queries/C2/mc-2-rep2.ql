/**
 * @name  rq3-c2-mc-2-rep2
 * @id    cpp/rq3/c2/mc-2-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing NULL check after kzalloc / kmalloc-family allocation,
 *              where the returned pointer is subsequently dereferenced.
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * A call to an allocation function in the kmalloc family that can return NULL.
 */
predicate is_alloc_call(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "kzalloc" or
    n = "kmalloc" or
    n = "kcalloc" or
    n = "kmalloc_array" or
    n = "kvzalloc" or
    n = "kvmalloc" or
    n = "vmalloc" or
    n = "vzalloc"
  )
}

/**
 * The allocation result is assigned to (or initialises) the given expression `lhs`.
 */
predicate alloc_assigned_to(FunctionCall fc, Expr lhs) {
  exists(Assignment a | a.getRValue() = fc and a.getLValue() = lhs)
  or
  exists(Variable v | v.getInitializer().getExpr() = fc and lhs = v.getAnAccess())
}

/**
 * `e` is checked for being NULL (or non-NULL) by a guard.
 */
predicate has_null_check(Expr allocLhs, FunctionCall fc) {
  alloc_assigned_to(fc, allocLhs) and
  exists(Expr checkExpr |
    // Same syntactic form or same underlying variable accessed after the call.
    (
      checkExpr = allocLhs
      or
      exists(Variable v |
        allocLhs = v.getAnAccess() and
        checkExpr = v.getAnAccess()
      )
      or
      exists(Field f, FieldAccess fa1, FieldAccess fa2 |
        allocLhs = fa1 and
        fa1.getTarget() = f and
        checkExpr = fa2 and
        fa2.getTarget() = f
      )
    ) and
    (
      // Explicit comparison with 0 / NULL.
      exists(EqualityOperation eq |
        eq.getAnOperand() = checkExpr and
        eq.getAnOperand().getValue() = "0"
      )
      or
      // Used directly as a boolean condition: if (!p) or if (p).
      exists(IfStmt ifs | ifs.getCondition() = checkExpr.getParent*())
      or
      exists(UnaryLogicalOperation uop | uop.getOperand() = checkExpr)
      or
      exists(GuardCondition g | g = checkExpr or g.(Operation).getAnOperand() = checkExpr)
    )
  )
}

/**
 * `e` (an access to the alloc-target variable/field) is dereferenced.
 */
predicate is_dereferenced_after(Expr allocLhs, FunctionCall fc) {
  alloc_assigned_to(fc, allocLhs) and
  exists(Expr derefAccess |
    (
      exists(Variable v |
        allocLhs = v.getAnAccess() and
        derefAccess = v.getAnAccess()
      )
      or
      exists(Field f, FieldAccess fa1, FieldAccess fa2 |
        allocLhs = fa1 and
        fa1.getTarget() = f and
        derefAccess = fa2 and
        fa2.getTarget() = f
      )
    ) and
    (
      exists(PointerDereferenceExpr d | d.getOperand() = derefAccess)
      or
      exists(PointerFieldAccess pfa | pfa.getQualifier() = derefAccess)
      or
      exists(ArrayExpr ae | ae.getArrayBase() = derefAccess)
      or
      exists(FunctionCall callUse | callUse.getAnArgument() = derefAccess)
    ) and
    derefAccess != allocLhs
  )
}

/**
 * Bug condition: allocation lhs is dereferenced later but never null-checked.
 */
predicate missing_null_check(FunctionCall fc, Expr allocLhs) {
  is_alloc_call(fc) and
  alloc_assigned_to(fc, allocLhs) and
  is_dereferenced_after(allocLhs, fc) and
  not has_null_check(allocLhs, fc)
}

from FunctionCall fc, Expr allocLhs
where missing_null_check(fc, allocLhs)
select fc,
  "Allocation result assigned to " + allocLhs.toString() +
    " is used without a NULL check; allocation can fail and cause a NULL dereference."
