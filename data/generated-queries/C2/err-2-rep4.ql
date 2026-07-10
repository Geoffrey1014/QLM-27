/**
 * @name  rq3-c2-err-2-rep4
 * @id    cpp/rq3/c2/err-2-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects failure-path branches that jump to a cleanup label without
 *              first assigning a negative errno to the function's return-code variable.
 */

import cpp

/**
 * A call expression that conventionally indicates failure via a NULL/zero/negative
 * return value (allocator or of_count_phandle_with_args-like APIs).
 */
predicate is_failable_call(FunctionCall c) {
  exists(string n | n = c.getTarget().getName() |
    n = "kcalloc" or n = "kmalloc" or n = "kzalloc" or
    n = "of_count_phandle_with_args" or
    n = "devm_kcalloc" or n = "devm_kzalloc" or
    n = "devm_kmalloc"
  )
}

/**
 * `ifs` is a failure check on the result of a failable call, and `blk` is the
 * "then" branch executed when the call has failed.
 */
predicate failure_branch_block(IfStmt ifs, BlockStmt blk) {
  exists(FunctionCall c | is_failable_call(c) |
    c = ifs.getCondition().getAChild*() or
    exists(Variable v | v.getAnAssignedValue() = c |
      ifs.getCondition().getAChild*() = v.getAnAccess()
    )
  ) and
  blk = ifs.getThen()
}

/**
 * `blk` contains (directly or in a nested stmt) a `goto` statement.
 */
predicate has_goto(BlockStmt blk) {
  exists(GotoStmt g | g.getParentStmt*() = blk)
}

/**
 * Inside `blk`, the variable `ret` is assigned a negative integer literal
 * (or a unary minus on a positive literal / errno macro expansion thereof).
 */
predicate assigns_negative_errno(BlockStmt blk, Variable ret) {
  exists(AssignExpr a |
    a.getEnclosingStmt().getParentStmt*() = blk and
    a.getLValue() = ret.getAnAccess() and
    (
      a.getRValue().getValue().toInt() < 0
      or
      exists(UnaryMinusExpr um | um = a.getRValue())
    )
  )
}

/**
 * `f` is a function with a local `ret` variable that is used as the final
 * return value (i.e., `return ret;` appears in `f`).
 */
predicate is_error_code_variable(Function f, Variable ret) {
  ret.(LocalVariable).getFunction() = f and
  ret.getName() = "ret" and
  exists(ReturnStmt r | r.getEnclosingFunction() = f and
    r.getExpr() = ret.getAnAccess())
}

from Function f, Variable ret, IfStmt ifs, BlockStmt blk
where
  is_error_code_variable(f, ret) and
  ifs.getEnclosingFunction() = f and
  failure_branch_block(ifs, blk) and
  has_goto(blk) and
  not assigns_negative_errno(blk, ret)
select ifs,
  "Failure branch of a failable call jumps to cleanup without assigning a negative errno to '" +
    ret.getName() + "' (function '" + f.getName() + "')."
