/**
 * @name Missing NULL check after allocation
 * @description The pointer returned by an allocation-like function (kmalloc,
 *              kcalloc, devm_kcalloc, kzalloc, kmalloc_array, vmalloc, etc.)
 *              is stored into an lvalue but the lvalue is never tested
 *              against NULL inside the enclosing function. The next use of
 *              that pointer can therefore NULL-dereference on allocation
 *              failure.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-5
 */

import cpp

/** Heuristic: a function whose name suggests it is an allocation
 *  that may return NULL on failure. */
bindingset[n]
predicate isAllocName(string n) {
  n.matches("kmalloc%") or
  n.matches("kzalloc%") or
  n.matches("kcalloc%") or
  n.matches("kmalloc_array%") or
  n.matches("kvmalloc%") or
  n.matches("kvzalloc%") or
  n.matches("kvcalloc%") or
  n.matches("vmalloc%") or
  n.matches("vzalloc%") or
  n.matches("devm_kmalloc%") or
  n.matches("devm_kzalloc%") or
  n.matches("devm_kcalloc%") or
  n.matches("devm_kmalloc_array%") or
  n.matches("krealloc%") or
  n.matches("__kmalloc%")
}

/** True if `e` is syntactically a NULL test of `lvalExpr`'s value:
 *  `!x`, `x == NULL`, `NULL == x`, `x == 0`, `0 == x`, or `x` used
 *  bare as a truthiness test inside a condition. */
predicate isNullTestOf(Expr e, Expr lvalExpr) {
  // !x where x matches lvalExpr by source text
  exists(NotExpr n | n = e and n.getOperand().toString() = lvalExpr.toString())
  or
  // x == 0 or NULL == x (compare text on each side)
  exists(EQExpr eq |
    eq = e and
    (
      (eq.getLeftOperand().toString() = lvalExpr.toString() and
       eq.getRightOperand().getValue() = "0")
      or
      (eq.getRightOperand().toString() = lvalExpr.toString() and
       eq.getLeftOperand().getValue() = "0")
    )
  )
  or
  // x != 0 / x != NULL (positive form, still a check)
  exists(NEExpr ne |
    ne = e and
    (
      (ne.getLeftOperand().toString() = lvalExpr.toString() and
       ne.getRightOperand().getValue() = "0")
      or
      (ne.getRightOperand().toString() = lvalExpr.toString() and
       ne.getLeftOperand().getValue() = "0")
    )
  )
}

/** True if function `f` contains anywhere a NULL test of an expression
 *  whose source-text equals `lvalText`. */
predicate functionChecksNullOf(Function f, string lvalText) {
  exists(Expr testExpr, Expr lvalExpr |
    testExpr.getEnclosingFunction() = f and
    lvalExpr.toString() = lvalText and
    isNullTestOf(testExpr, lvalExpr)
  )
}

from AssignExpr assign, FunctionCall fc, Function callee, Function f,
     Expr lhs, string lhsText
where
  // The RHS is a direct call to an alloc-like function.
  assign.getRValue() = fc and
  fc.getTarget() = callee and
  isAllocName(callee.getName()) and
  // The callee returns a pointer (any pointer type).
  callee.getType().getUnspecifiedType() instanceof PointerType and
  // LHS captured for reporting / matching.
  lhs = assign.getLValue() and
  lhsText = lhs.toString() and
  // Enclosing function.
  f = assign.getEnclosingFunction() and
  // No NULL check on this lvalue anywhere in the function.
  not functionChecksNullOf(f, lhsText)
select assign,
  "Result of allocation '" + callee.getName() +
    "()' stored into '" + lhsText +
    "' but no NULL check on '" + lhsText +
    "' appears in function '" + f.getName() +
    "()'; subsequent use may NULL-dereference on allocation failure."
