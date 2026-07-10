/**
 * @name Missing NULL check after allocation
 * @description An allocation-style call (devm_kcalloc, kmalloc, kzalloc,
 *              kcalloc, kmalloc_array, devm_kzalloc, devm_kmalloc, ...)
 *              writes its result into an lvalue (variable or struct field)
 *              that is later dereferenced or otherwise used without an
 *              intervening NULL check on that lvalue. Such a missing
 *              check causes a NULL pointer dereference when the
 *              allocation fails.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-5
 */

import cpp

/** A call to an allocation-style function whose return value the caller
 *  must check against NULL. */
predicate isAllocCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "kmalloc" or
    n = "kzalloc" or
    n = "kcalloc" or
    n = "kmalloc_array" or
    n = "kzalloc_node" or
    n = "kmalloc_node" or
    n = "devm_kmalloc" or
    n = "devm_kzalloc" or
    n = "devm_kcalloc" or
    n = "devm_kmalloc_array" or
    n = "vmalloc" or
    n = "vzalloc" or
    n = "malloc" or
    n = "calloc"
  )
}

/** A NULL-test of expression `e`: matches `!e`, `e == NULL`, `e != NULL`,
 *  `e == 0`, `e != 0`, or `e` used as a boolean condition. */
predicate isNullCheckOf(Expr cond, Expr e) {
  cond.(NotExpr).getOperand() = e
  or
  exists(EqualityOperation eq |
    eq = cond and
    eq.getAnOperand() = e and
    eq.getAnOperand().getValue() = "0"
  )
  or
  cond = e and cond.getType().getUnspecifiedType() instanceof PointerType
}

/** An IfStmt whose condition contains a NULL-check of expression `e`. */
predicate guardsNull(IfStmt ifs, Expr e) {
  exists(Expr sub | sub = ifs.getCondition().getAChild*() or sub = ifs.getCondition() |
    isNullCheckOf(sub, e)
  )
}

from FunctionCall alloc, Expr lhs, Function f
where
  isAllocCall(alloc) and
  // The allocation result is assigned to lhs (either a variable or a
  // field access). We capture both `x = alloc(...)` and `obj->f =
  // alloc(...)` forms.
  exists(AssignExpr ae |
    ae.getRValue() = alloc and
    ae.getLValue() = lhs
  ) and
  f = alloc.getEnclosingFunction() and
  // No NULL check on the same syntactic lhs anywhere in the enclosing
  // function. This is intentionally syntactic — we compare the textual
  // form of the access — to keep the monolithic query simple.
  not exists(IfStmt ifs, Expr checked |
    ifs.getEnclosingFunction() = f and
    guardsNull(ifs, checked) and
    checked.toString() = lhs.toString()
  ) and
  // Avoid noise from non-pointer destinations and from allocations whose
  // return is immediately compared (e.g. inside `if ((x = alloc())) `).
  alloc.getType().getUnspecifiedType() instanceof PointerType
select alloc,
  "Allocation result assigned to '" + lhs.toString() +
    "' is not checked for NULL in function '" + f.getName() + "'."
