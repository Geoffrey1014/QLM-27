/**
 * @name  rq3-c2-mc-5-rep4
 * @id    cpp/rq3/c2/mc-5-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing NULL checks after devm_ / k-alloc-family calls
 *              whose result is stored into a variable and later used.
 */

import cpp

/** Holds if `fc` is a call to an allocator that may return NULL. */
predicate isAllocCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "devm_kcalloc" or
    n = "devm_kmalloc" or
    n = "devm_kzalloc" or
    n = "devm_kmalloc_array" or
    n = "devm_kzalloc_array" or
    n = "kcalloc" or
    n = "kmalloc" or
    n = "kzalloc" or
    n = "kmalloc_array" or
    n = "kzalloc_array" or
    n = "vmalloc" or
    n = "vzalloc"
  )
}

/** Holds if the result of allocation `fc` flows directly into l-value `lhs`
 *  via a top-level assignment. */
predicate assignsAllocResult(Expr lhs, FunctionCall fc) {
  isAllocCall(fc) and
  exists(Assignment a |
    a.getRValue() = fc and
    lhs = a.getLValue()
  )
}

/** Holds if there is some guard later in the enclosing function that compares
 *  an expression structurally equivalent to `lhs` against null. */
predicate hasNullCheck(Expr lhs, FunctionCall fc) {
  assignsAllocResult(lhs, fc) and
  exists(Expr check, Function f |
    f = fc.getEnclosingFunction() and
    check.getEnclosingFunction() = f and
    check.(EqualityOperation).getAnOperand().toString() = lhs.toString() and
    check.(EqualityOperation).getAnOperand() instanceof Literal
  )
  or
  // Logical-not style check:  if (!ptr)
  assignsAllocResult(lhs, fc) and
  exists(NotExpr ne |
    ne.getEnclosingFunction() = fc.getEnclosingFunction() and
    ne.getOperand().toString() = lhs.toString()
  )
}

/** Holds if `lhs` (the alloc result) is subsequently used inside the same
 *  function after the alloc call. */
predicate usedAfterAlloc(Expr lhs, FunctionCall fc) {
  assignsAllocResult(lhs, fc) and
  exists(Expr use |
    use.getEnclosingFunction() = fc.getEnclosingFunction() and
    use.toString() = lhs.toString() and
    use.getLocation().getStartLine() > fc.getLocation().getStartLine() and
    not use = lhs
  )
}

from FunctionCall fc, Expr lhs
where
  isAllocCall(fc) and
  assignsAllocResult(lhs, fc) and
  usedAfterAlloc(lhs, fc) and
  not hasNullCheck(lhs, fc)
select fc,
  "Allocation result assigned to '" + lhs.toString() +
    "' is used without a NULL check in function " + fc.getEnclosingFunction().getName() + "."
