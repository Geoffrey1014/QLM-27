/**
 * @name Missing NULL check on allocator return before dereference
 * @description The result of an allocation-style function (e.g. kzalloc,
 *              kmalloc, kcalloc, vmalloc, kstrdup, ...) is stored into a
 *              pointer and later dereferenced (via field access or array
 *              index) along a control-flow path that does not first test
 *              the pointer against NULL. The allocator can return NULL on
 *              failure, so the dereference may oops the kernel.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-2
 */

import cpp

/** Heuristic: a call whose return value is a freshly-allocated pointer
 *  that the caller must null-check. */
bindingset[n]
predicate isAllocFunctionName(string n) {
  n = "kzalloc" or
  n = "kmalloc" or
  n = "kcalloc" or
  n = "kmalloc_array" or
  n = "kzalloc_node" or
  n = "kmalloc_node" or
  n = "vmalloc" or
  n = "vzalloc" or
  n = "kvmalloc" or
  n = "kvzalloc" or
  n = "kmemdup" or
  n = "kstrdup" or
  n = "kstrndup" or
  n = "devm_kzalloc" or
  n = "devm_kmalloc" or
  n = "devm_kcalloc" or
  n = "malloc" or
  n = "calloc"
}

/** An assignment of an allocator-call result into an l-value (local var,
 *  field access, pointer-deref, etc.). */
class AllocAssign extends AssignExpr {
  FunctionCall acquireCall;
  AllocAssign() {
    acquireCall = this.getRValue() and
    isAllocFunctionName(acquireCall.getTarget().getName()) and
    this.getLValue().getType().getUnspecifiedType() instanceof PointerType
  }
  FunctionCall getAcquireCall() { result = acquireCall }
}

/** Two l-value expressions refer to the "same" pointer location for our
 *  purposes: same local variable, OR same field of the same base. */
predicate sameLocation(Expr a, Expr b) {
  exists(LocalScopeVariable v |
    a = v.getAnAccess() and b = v.getAnAccess()
  )
  or
  exists(Field f, Variable base |
    a.(FieldAccess).getTarget() = f and
    b.(FieldAccess).getTarget() = f and
    a.(FieldAccess).getQualifier() = base.getAnAccess() and
    b.(FieldAccess).getQualifier() = base.getAnAccess()
  )
}

/** A dereference site that consumes the assigned pointer location. */
predicate isDerefOf(Expr useSite, Expr assignedLvalue) {
  // p->field, where p is the same location
  exists(PointerFieldAccess pfa |
    useSite = pfa and
    sameLocation(pfa.getQualifier(), assignedLvalue)
  )
  or
  // *p
  exists(PointerDereferenceExpr d |
    useSite = d and
    sameLocation(d.getOperand(), assignedLvalue)
  )
  or
  // p[i]
  exists(ArrayExpr ax |
    useSite = ax and
    sameLocation(ax.getArrayBase(), assignedLvalue)
  )
}

/** A NULL-check on the assigned pointer location. */
predicate isNullCheckOf(Expr check, Expr assignedLvalue) {
  // if (!p) ...
  exists(NotExpr ne |
    check = ne and
    sameLocation(ne.getOperand(), assignedLvalue)
  )
  or
  // if (p == NULL) / if (p == 0) / if (NULL == p)
  exists(EQExpr eq |
    check = eq and
    (
      sameLocation(eq.getLeftOperand(), assignedLvalue) and
      eq.getRightOperand().getValue() = "0"
      or
      sameLocation(eq.getRightOperand(), assignedLvalue) and
      eq.getLeftOperand().getValue() = "0"
    )
  )
  or
  // if (p != NULL)
  exists(NEExpr ne |
    check = ne and
    (
      sameLocation(ne.getLeftOperand(), assignedLvalue) and
      ne.getRightOperand().getValue() = "0"
      or
      sameLocation(ne.getRightOperand(), assignedLvalue) and
      ne.getLeftOperand().getValue() = "0"
    )
  )
  or
  // if (p) ...  -- a plain truthiness test in a condition position
  exists(IfStmt is |
    is.getCondition() = check and
    sameLocation(check, assignedLvalue)
  )
}

from AllocAssign aa, Expr deref, Function f
where
  f = aa.getEnclosingFunction() and
  isDerefOf(deref, aa.getLValue()) and
  deref.getEnclosingFunction() = f and
  // dereference is reached from the assignment
  aa.getASuccessor+() = deref and
  // and there is no NULL-check between the assignment and the dereference
  not exists(Expr check |
    isNullCheckOf(check, aa.getLValue()) and
    check.getEnclosingFunction() = f and
    aa.getASuccessor+() = check and
    check.getASuccessor+() = deref
  )
select deref,
  "Pointer from allocator '" + aa.getAcquireCall().getTarget().getName() +
    "' is dereferenced here without a prior NULL check (assigned at $@).",
  aa, "allocation"
