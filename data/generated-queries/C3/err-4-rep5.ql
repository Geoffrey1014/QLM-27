/**
 * @name Error-return-code-not-set
 * @description Detects `goto <cleanup_label>` from a NULL/error check whose
 *              `then` branch does not assign a negative errno to the
 *              function's return-code variable, while the cleanup label
 *              ultimately returns that variable unmodified. Pattern from
 *              commit c021e0235770 (usb: gadget: legacy: fix error return
 *              code of multi_bind()).
 * @kind problem
 * @problem.severity warning
 * @id qlm/err-4-rep5
 */

import cpp

predicate isStatusVar(LocalVariable v) {
  v.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt r |
    r.getEnclosingFunction() = v.getFunction() and
    r.getExpr().(VariableAccess).getTarget() = v
  )
}

predicate isNegativeIntConst(Expr e) {
  e.getValue().toInt() < 0
  or
  e.(UnaryMinusExpr).getOperand().getValue().toInt() > 0
}

predicate isBareFailGoto(GotoStmt g, LocalVariable v) {
  isStatusVar(v) and
  g.getEnclosingFunction() = v.getFunction() and
  exists(IfStmt ifs | g.getParentStmt*() = ifs.getThen()) and
  not exists(Assignment a |
    a.getEnclosingFunction() = v.getFunction() and
    a.getLValue().(VariableAccess).getTarget() = v and
    isNegativeIntConst(a.getRValue()) and
    exists(IfStmt ifs2 |
      g.getParentStmt*() = ifs2.getThen() and
      a.getEnclosingStmt().getParentStmt*() = ifs2.getThen()
    )
  )
}

predicate labelPathReturnsVarWithoutNegativeAssign(GotoStmt g, LocalVariable v) {
  isStatusVar(v) and
  g.getEnclosingFunction() = v.getFunction() and
  exists(LabelStmt lbl, ReturnStmt r |
    lbl = g.getTarget() and
    r.getEnclosingFunction() = v.getFunction() and
    r.getExpr().(VariableAccess).getTarget() = v and
    r.getLocation().getStartLine() > lbl.getLocation().getStartLine() and
    not exists(Assignment a |
      a.getEnclosingFunction() = v.getFunction() and
      a.getLValue().(VariableAccess).getTarget() = v and
      isNegativeIntConst(a.getRValue()) and
      a.getLocation().getStartLine() >= lbl.getLocation().getStartLine() and
      a.getLocation().getStartLine() <= r.getLocation().getStartLine()
    )
  )
}

from GotoStmt g, LocalVariable v
where
  isBareFailGoto(g, v) and
  labelPathReturnsVarWithoutNegativeAssign(g, v)
select g,
  "Error-return-code-not-set: goto-to-cleanup-label fires without assigning a negative errno to '"
    + v.getName() + "', and the label path returns it unmodified."
