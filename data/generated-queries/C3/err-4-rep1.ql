/**
 * @name Error-return code not set on failure goto
 * @description An int status variable is returned by the function, but on
 *              an error branch (`if (cond) goto LBL;`) the code does NOT
 *              assign a negative errno to status before the goto, and
 *              the label simply returns the unassigned status. Result:
 *              the function returns 0 (success) despite the failure.
 *              Mirror of commit c021e0235770 ("usb: gadget: legacy: fix
 *              error return code of multi_bind()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/err-4-rep1
 */

import cpp

/* status int variable used as the function's return value */
predicate isStatusVar(LocalVariable v) {
  v.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt r |
    r.getEnclosingFunction() = v.getFunction() and
    r.getExpr().(VariableAccess).getTarget() = v
  )
}

/* negative integer literal (e.g. expansion of -ENOMEM = -12) */
predicate isNegativeConstant(Expr e) {
  e.getValue().toInt() < 0
  or
  e.(UnaryMinusExpr).getOperand().getValue().toInt() > 0
}

/* `goto LBL;` reachable inside an if-then branch */
predicate isFailGoto(GotoStmt g) {
  exists(IfStmt ifs |
    g = ifs.getThen()
    or
    g.getParent+() = ifs.getThen()
  )
}

/* the if-then branch that contains `g` has NO assignment of a negative
 * constant to v before the goto */
predicate missingStatusAssignBeforeGoto(GotoStmt g, LocalVariable v) {
  isFailGoto(g) and
  isStatusVar(v) and
  g.getEnclosingFunction() = v.getFunction() and
  not exists(Assignment a, IfStmt ifs, Stmt s |
    (g = ifs.getThen() or g.getParent+() = ifs.getThen()) and
    s = a.getEnclosingStmt() and
    (s = ifs.getThen() or s.getParent+() = ifs.getThen()) and
    a.getLValue().(VariableAccess).getTarget() = v and
    isNegativeConstant(a.getRValue())
  )
}

/* `g` jumps to a label that leads to `return v;`, and between the
 * label and that return there is no assignment of a negative constant
 * to v (line-number proxy for "no rescue at the label"). */
predicate labelReturnsVarWithoutNegativeAssign(GotoStmt g, LocalVariable v) {
  g.getEnclosingFunction() = v.getFunction() and
  isStatusVar(v) and
  exists(LabelStmt lbl, ReturnStmt r |
    lbl = g.getTarget() and
    r.getEnclosingFunction() = v.getFunction() and
    r.getExpr().(VariableAccess).getTarget() = v and
    r.getLocation().getStartLine() >= lbl.getLocation().getStartLine() and
    not exists(Assignment a |
      a.getEnclosingFunction() = v.getFunction() and
      a.getLValue().(VariableAccess).getTarget() = v and
      isNegativeConstant(a.getRValue()) and
      a.getLocation().getStartLine() >= lbl.getLocation().getStartLine() and
      a.getLocation().getStartLine() <= r.getLocation().getStartLine()
    )
  )
}

from GotoStmt g, LocalVariable v
where
  missingStatusAssignBeforeGoto(g, v) and
  labelReturnsVarWithoutNegativeAssign(g, v)
select g,
  "Error-return-code-not-set: jump to label without assigning negative errno to '" +
  v.getName() + "' before goto, while the label returns it unmodified."
