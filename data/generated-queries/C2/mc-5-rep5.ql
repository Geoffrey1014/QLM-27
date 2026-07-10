/**
 * @name  rq3-c2-mc-5-rep5
 * @id    cpp/rq3/c2/mc-5-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 */
import cpp

predicate isAllocCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "devm_kcalloc" or
    n = "devm_kzalloc" or
    n = "devm_kmalloc" or
    n = "kcalloc" or
    n = "kzalloc" or
    n = "kmalloc" or
    n = "kmalloc_array" or
    n = "vmalloc" or
    n = "vzalloc"
  )
}

predicate assignsAllocResult(FunctionCall fc, Expr lhs) {
  isAllocCall(fc) and
  exists(Assignment a |
    a.getRValue() = fc and
    lhs = a.getLValue()
  )
}

predicate hasNullCheck(Expr lhs, FunctionCall fc) {
  assignsAllocResult(fc, lhs) and
  exists(IfStmt ifs, Expr cond |
    cond = ifs.getCondition().getAChild*() or cond = ifs.getCondition() |
    cond.toString() = lhs.toString() and
    ifs.getLocation().getStartLine() > fc.getLocation().getStartLine() and
    ifs.getLocation().getStartLine() < fc.getLocation().getStartLine() + 5
  )
}

predicate usedAfter(Expr lhs, FunctionCall fc) {
  assignsAllocResult(fc, lhs) and
  exists(Expr use |
    use.toString() = lhs.toString() and
    use.getLocation().getStartLine() > fc.getLocation().getStartLine() and
    use.getEnclosingFunction() = fc.getEnclosingFunction() and
    not exists(Assignment a | a.getLValue() = use)
  )
}

predicate missingNullCheck(FunctionCall fc, Expr lhs) {
  assignsAllocResult(fc, lhs) and
  usedAfter(lhs, fc) and
  not hasNullCheck(lhs, fc)
}

from FunctionCall fc, Expr lhs
where missingNullCheck(fc, lhs)
select fc, "Allocation result assigned may be used without NULL check."
