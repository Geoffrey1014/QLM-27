/**
 * @name  rq3-c2-err-5-rep3
 * @id    cpp/rq3/c2/err-5-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing error-code assignment on allocation-failure paths
 *              that goto a cleanup label (pattern of 31d82c2c787d).
 */
import cpp

/** A call to a kernel allocation function that may return NULL. */
predicate isAllocCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "vzalloc" or
    n = "vmalloc" or
    n = "kmalloc" or
    n = "kzalloc" or
    n = "kcalloc" or
    n = "kmalloc_array" or
    n = "kmemdup" or
    n = "kstrdup" or
    n = "krealloc" or
    n = "alloc_pages" or
    n = "__get_free_pages" or
    n = "devm_kzalloc" or
    n = "devm_kmalloc"
  )
}

/** `ifs` is an `if (!e)` or `if (e == NULL)` style null-check of `e`. */
predicate isNullCheckOf(IfStmt ifs, Expr e) {
  exists(NotExpr ne | ne = ifs.getCondition() and ne.getOperand() = e)
  or
  exists(EQExpr eq | eq = ifs.getCondition() |
    eq.getLeftOperand() = e and eq.getRightOperand().getValue() = "0"
    or
    eq.getRightOperand() = e and eq.getLeftOperand().getValue() = "0"
  )
}

/** A goto statement appears (directly or nested) in the then-branch of `ifs`. */
predicate gotoInThen(IfStmt ifs, GotoStmt gs) {
  gs.getParent*() = ifs.getThen()
}

/** `s` assigns a negative integer (an errno) to `retVar`. */
predicate assignsErrorCode(Stmt s, Variable retVar) {
  exists(AssignExpr ae, ExprStmt es |
    es = s and
    ae = es.getExpr() and
    ae.getLValue() = retVar.getAnAccess() and
    (
      ae.getRValue().getValue().toInt() < 0
      or
      exists(UnaryMinusExpr um | um = ae.getRValue())
    )
  )
}

/**
 * In the then-branch containing the goto, there is no assignment of an
 * error code to `retVar` prior to the goto.
 */
predicate missingErrorAssignBeforeGoto(IfStmt ifs, GotoStmt gs, Variable retVar) {
  gotoInThen(ifs, gs) and
  not exists(Stmt s |
    s.getParent*() = ifs.getThen() and
    assignsErrorCode(s, retVar)
  )
}

from FunctionCall fc, Variable v, IfStmt ifs, GotoStmt gs, LocalVariable retVar, Function f
where
  isAllocCall(fc) and
  f = fc.getEnclosingFunction() and
  f.getType().getName() = "int" and
  v.getAnAssignedValue() = fc and
  isNullCheckOf(ifs, v.getAnAccess()) and
  ifs.getEnclosingFunction() = f and
  gotoInThen(ifs, gs) and
  retVar.getFunction() = f and
  retVar.getType().getName() = "int" and
  missingErrorAssignBeforeGoto(ifs, gs, retVar) and
  // retVar is actually returned somewhere in f
  exists(ReturnStmt rs | rs.getEnclosingFunction() = f and rs.getExpr() = retVar.getAnAccess())
select ifs, "Missing error code assignment to $@ before goto on allocation failure.", retVar, retVar.getName()
