/**
 * @name  rq3-c2-err-5-rep5
 * @id    cpp/rq3/c2/err-5-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects the error-return-code pattern: an allocation/acquisition
 *              call returns NULL, the if-block goto's a cleanup label without
 *              first assigning a negative errno to the return variable.
 */

import cpp

/* Allocation/acquisition calls whose NULL result indicates failure. */
predicate is_alloc_call(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "vzalloc" or
    n = "vmalloc" or
    n = "kzalloc" or
    n = "kmalloc" or
    n = "kcalloc" or
    n = "kmalloc_array" or
    n = "kmemdup" or
    n = "kstrdup" or
    n = "alloc_workqueue" or
    n = "alloc_etherdev" or
    n = "devm_kzalloc" or
    n = "devm_kmalloc" or
    n = "of_get_property" or
    n = "of_find_node_by_name" or
    n = "of_parse_phandle" or
    n = "ioremap" or
    n = "request_threaded_irq"
  )
}

/* `ife` is an if-statement whose condition tests `e` for being NULL/zero
 * (covers `if (!e)`, `if (e == NULL)`, `if (NULL == e)`). */
predicate is_null_check_of(IfStmt ife, Expr e) {
  exists(Expr cond | cond = ife.getCondition() |
    cond.(NotExpr).getOperand() = e
    or
    exists(EQExpr eq | eq = cond |
      (eq.getLeftOperand() = e and eq.getRightOperand() instanceof Literal and
        eq.getRightOperand().getValue() = "0")
      or
      (eq.getRightOperand() = e and eq.getLeftOperand() instanceof Literal and
        eq.getLeftOperand().getValue() = "0")
    )
  )
}

/* `s` contains a goto statement (directly, or one nested in its block). */
predicate goto_in_block(Stmt s, GotoStmt g) {
  s = g
  or
  exists(BlockStmt b | b = s |
    g.getEnclosingBlock+() = b
  )
}

/* `s` (the if-then block) contains an assignment to `ret` (any variable
 *  whose name suggests a return/error code) of a negative integer / error
 *  macro before the goto. */
predicate assigns_ret_in_block(Stmt s) {
  exists(AssignExpr a, Variable v |
    a.getLValue() = v.getAnAccess() and
    (v.getName() = "ret" or v.getName() = "err" or v.getName() = "rc" or
     v.getName() = "error" or v.getName() = "status") and
    (
      a.getEnclosingStmt() = s
      or
      a.getEnclosingStmt().getParent*() = s
    )
  )
}

/* The bug: an if-statement that is a NULL-check of an allocation result,
 * whose then-block goto's a cleanup label, but does NOT assign a negative
 * errno value to a ret-like variable before the goto. */
predicate bad_null_handler(IfStmt ife, FunctionCall alloc, GotoStmt g) {
  is_alloc_call(alloc) and
  exists(Variable v |
    // Allocation result is stored into v (directly).
    exists(AssignExpr a |
      a.getRValue() = alloc and a.getLValue() = v.getAnAccess()
    )
    or
    // Or v is initialized at declaration with the alloc call.
    exists(Initializer i | i.getExpr() = alloc and i.getDeclaration() = v)
  |
    is_null_check_of(ife, v.getAnAccess())
  ) and
  goto_in_block(ife.getThen(), g) and
  not assigns_ret_in_block(ife.getThen())
}

from IfStmt ife, FunctionCall alloc, GotoStmt g
where bad_null_handler(ife, alloc, g)
select ife,
  "Missing error-code assignment before goto " + g.getName() +
    " on NULL return from " + alloc.getTarget().getName() + "()."
