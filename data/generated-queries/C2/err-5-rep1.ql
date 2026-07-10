/**
 * @name  rq3-c2-err-5-rep1
 * @id    cpp/rq3/c2/err-5-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing error-code assignment before goto-cleanup
 *              on the NULL-check path of an allocation.
 */

import cpp

/** Holds if `fc` is a call to a common kernel allocator that may return NULL. */
predicate is_alloc_call(FunctionCall fc) {
  fc.getTarget().getName() =
    ["vzalloc", "vmalloc", "kmalloc", "kzalloc", "kcalloc",
     "kmalloc_array", "kvmalloc", "kvzalloc", "kmem_cache_alloc",
     "kmem_cache_zalloc", "alloc_pages", "__get_free_pages"]
}

/** Holds if `v` is assigned the result of an allocator call in `init`. */
predicate alloc_to_var(Variable v, FunctionCall fc, Expr init) {
  is_alloc_call(fc) and
  (
    exists(AssignExpr ae |
      ae = init and
      ae.getLValue() = v.getAnAccess() and
      ae.getRValue() = fc
    )
    or
    exists(Initializer i |
      i = v.getInitializer() and
      i.getExpr() = fc and
      init = fc
    )
  )
}

/** Holds if `ifs` is a NULL check on `v` (e.g. `if (!v)` or `if (v == NULL)`). */
predicate null_check_of(IfStmt ifs, Variable v) {
  exists(Expr cond | cond = ifs.getCondition() |
    cond.(NotExpr).getOperand() = v.getAnAccess()
    or
    exists(EQExpr eq | eq = cond |
      eq.getAnOperand() = v.getAnAccess() and
      eq.getAnOperand().getValue() = "0"
    )
  )
}

/** Holds if `g` is a goto whose target label name suggests a cleanup/free/out path. */
predicate is_cleanup_goto(GotoStmt g) {
  exists(string n | n = g.getName() |
    n.matches("out%") or n.matches("err%") or n.matches("fail%") or
    n.matches("free%") or n.matches("cleanup%") or n.matches("unlock%") or
    n.matches("undo%") or n.matches("release%") or n.matches("exit%")
  )
}

/** Holds if statement `s` (or one of its descendants) assigns a negative integer value to `ret`. */
predicate assigns_error_code(Stmt s, Variable ret) {
  exists(AssignExpr ae |
    ae.getEnclosingStmt().getParentStmt*() = s and
    ae.getLValue() = ret.getAnAccess() and
    (
      ae.getRValue().(UnaryMinusExpr).getOperand().getValue().toInt() > 0
      or
      ae.getRValue().getValue().toInt() < 0
    )
  )
}

/**
 * Holds if `ifs` is a NULL-check on `v` whose then-branch jumps to a cleanup label
 * via `g`, without assigning an error code to `ret` first.
 */
predicate null_goto_missing_errcode(IfStmt ifs, Variable v, Variable ret, GotoStmt g) {
  null_check_of(ifs, v) and
  is_cleanup_goto(g) and
  g.getParentStmt*() = ifs.getThen() and
  not assigns_error_code(ifs.getThen(), ret) and
  // ensure `ret` is a local variable in the same enclosing function as the goto
  ret instanceof LocalVariable and
  ret.(LocalVariable).getFunction() = ifs.getEnclosingFunction() and
  // and ret's name is suggestive of an error return code
  ret.getName() = ["ret", "rc", "err", "error", "status", "r"]
}

from FunctionCall fc, Variable v, Expr init, IfStmt ifs, Variable ret, GotoStmt g
where
  alloc_to_var(v, fc, init) and
  null_goto_missing_errcode(ifs, v, ret, g) and
  // proximity: the NULL check uses the same variable assigned the allocation,
  // and the if-statement is in the same function as the allocation.
  ifs.getEnclosingFunction() = fc.getEnclosingFunction()
select ifs,
  "Missing error code assignment to '" + ret.getName() +
  "' before goto-cleanup on NULL-check of allocation result '" + v.getName() + "'."
