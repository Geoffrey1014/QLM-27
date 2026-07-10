/**
 * @name Missing NULL check after allocator call
 * @description The return value of an allocation function (kzalloc, kmalloc,
 *              kcalloc, vmalloc, malloc, etc.) is stored into a pointer
 *              target (local variable or struct field) and subsequently used
 *              in the same function without any NULL check on that target.
 *              Allocation can fail and dereferencing the NULL value crashes
 *              the kernel.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-2
 */

import cpp

/** A function whose return value is a freshly-allocated pointer that may be NULL. */
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
    n = "krealloc" or
    n = "malloc" or
    n = "calloc" or
    n = "realloc" or
    n = "devm_kzalloc" or
    n = "devm_kmalloc" or
    n = "devm_kcalloc"
  )
}

/** An expression that is structurally a NULL-ness test on `e`
 *  (e.g. `!e`, `e == NULL`, `e == 0`, `NULL == e`, `e != NULL`, etc.). */
predicate isNullTestOf(Expr test, Expr e) {
  // !e
  exists(NotExpr ne | ne = test and ne.getOperand() = e)
  or
  // e == NULL / e == 0 / NULL == e / 0 == e
  exists(EQExpr eq | eq = test |
    (eq.getLeftOperand() = e and eq.getRightOperand().getValue() = "0") or
    (eq.getRightOperand() = e and eq.getLeftOperand().getValue() = "0")
  )
  or
  // e != NULL / e != 0
  exists(NEExpr ne2 | ne2 = test |
    (ne2.getLeftOperand() = e and ne2.getRightOperand().getValue() = "0") or
    (ne2.getRightOperand() = e and ne2.getLeftOperand().getValue() = "0")
  )
  or
  // bare `if (e)` — e itself used as boolean condition
  e = test
}

/** True if expression `a` and `b` syntactically refer to the same
 *  pointer target (same local variable, or same `obj->field` /
 *  `obj.field` access on syntactically equal qualifiers). */
predicate sameTarget(Expr a, Expr b) {
  exists(LocalVariable lv |
    a = lv.getAnAccess() and b = lv.getAnAccess())
  or
  exists(Parameter p |
    a = p.getAnAccess() and b = p.getAnAccess())
  or
  exists(Field f, FieldAccess fa1, FieldAccess fa2 |
    fa1 = a and fa2 = b and
    fa1.getTarget() = f and fa2.getTarget() = f and
    fa1.getQualifier().(VariableAccess).getTarget() =
      fa2.getQualifier().(VariableAccess).getTarget())
}

from FunctionCall alloc, Expr target, Function fn
where
  isAllocCall(alloc) and
  fn = alloc.getEnclosingFunction() and
  // the alloc result is assigned to `target` (lvalue) in the same function
  exists(AssignExpr ae |
    ae.getEnclosingFunction() = fn and
    ae.getRValue() = alloc and
    ae.getLValue() = target
  ) and
  // `target` is a pointer
  target.getType().getUnspecifiedType() instanceof PointerType and
  // there is NO null-ness test of an expression that names the same target
  // anywhere in the same function
  not exists(IfStmt ifs, Expr cond, Expr testedAccess |
    ifs.getEnclosingFunction() = fn and
    cond = ifs.getCondition() and
    isNullTestOf(cond, testedAccess) and
    sameTarget(target, testedAccess)
  ) and
  // also: not checked via conditional / logical operators outside an if
  not exists(LogicalAndExpr la, Expr testedAccess |
    la.getEnclosingFunction() = fn and
    isNullTestOf(la.getAnOperand(), testedAccess) and
    sameTarget(target, testedAccess)
  ) and
  not exists(LogicalOrExpr lo, Expr testedAccess |
    lo.getEnclosingFunction() = fn and
    isNullTestOf(lo.getAnOperand(), testedAccess) and
    sameTarget(target, testedAccess)
  )
select alloc,
  "Result of '" + alloc.getTarget().getName() +
    "' is stored without a subsequent NULL check on the target in function '" +
    fn.getName() + "'."
