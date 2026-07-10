/**
 * @name Error-return-code: failing-branch goto leaves stale `ret` so caller sees success
 * @description Detects functions that declare an `int ret` return-value variable and
 *              return it at the end, where on at least one error-condition branch the
 *              code performs `goto <cleanup_label>` without first assigning a negative
 *              errno to `ret`. Because an earlier successful call (commonly
 *              `of_property_read_u32` / `of_property_read_string`) may have set ret==0,
 *              this causes the function to silently return success on the failing path
 *              (CWE-252 / CWE-703).
 *
 *              Pattern source: TOTE-Robot kernel bug class; seed commit 45c7eaeb29d6
 *              (thermal: thermal_of: fix error return code of
 *              thermal_of_populate_bind_params).
 *
 * @kind problem
 * @problem.severity warning
 * @id qlm/err-2-rep4-error-return-code
 */

import cpp

predicate returnsRetVar(Function fn, LocalVariable ret) {
  ret.getFunction() = fn and
  ret.getName() = "ret" and
  exists(ReturnStmt r |
    r.getEnclosingFunction() = fn and
    r.getExpr().(VariableAccess).getTarget() = ret
  )
}

predicate isErrorBranchGoto(GotoStmt g, IfStmt ifs) {
  ifs.getThen() = g
  or
  g.getParentStmt+() = ifs.getThen()
}

predicate assignsRetInBranch(IfStmt ifs, LocalVariable ret) {
  exists(AssignExpr ae |
    ae.getLValue().(VariableAccess).getTarget() = ret and
    (
      ae.getEnclosingStmt() = ifs.getThen() or
      ae.getEnclosingStmt().getParentStmt+() = ifs.getThen()
    )
  )
}

predicate errorGotoMissingRetAssign(
  Function fn, IfStmt ifs, GotoStmt g, LocalVariable ret
) {
  returnsRetVar(fn, ret) and
  isErrorBranchGoto(g, ifs) and
  g.getEnclosingFunction() = fn and
  not assignsRetInBranch(ifs, ret)
}

from Function fn, IfStmt ifs, GotoStmt g, LocalVariable ret
where errorGotoMissingRetAssign(fn, ifs, g, ret)
select g,
       "Error-cleanup goto in $@ may return success (ret==0) because the failing branch never assigns ret = -Exxx before jumping.",
       fn, fn.getName()
