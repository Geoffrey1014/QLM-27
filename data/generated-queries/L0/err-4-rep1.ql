/**
 * @name Error-return code not set on failure goto
 *       (error-return-code pattern) [L0 zero-shot single-predicate]
 * @description Detects int-returning functions where an if-guarded
 *              `goto CLEANUP;` branch fails to assign a negative errno
 *              to the return-code variable before the goto, while the
 *              cleanup label ultimately returns that variable without
 *              rescuing it. Result: the function silently returns 0
 *              (success) on a failure path — the bug shape fixed by
 *              upstream commit c021e0235770 ("usb: gadget: legacy: fix
 *              error return code of multi_bind()").
 *
 *              L0 constraint: at most one helper predicate. The single
 *              predicate `isStatusVar` captures "int local returned by
 *              the enclosing function". The remaining structural checks
 *              (bare-goto in if-then, label-return without rescue) are
 *              inlined verbatim in the assembly where-clause.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/error-return-code-not-set
 * @tags reliability
 *       error-handling
 *       error-return
 */

import cpp

/* P1 — int local variable v is the return value of its enclosing
 * function (a typical `int status;` / `int err;`-style variable). */
predicate isStatusVar(LocalVariable v) {
  v.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt r |
    r.getEnclosingFunction() = v.getFunction() and
    r.getExpr().(VariableAccess).getTarget() = v
  )
}

from GotoStmt g, LocalVariable v, IfStmt ifs, LabelStmt lbl, ReturnStmt r
where
  isStatusVar(v) and
  g.getEnclosingFunction() = v.getFunction() and
  (g = ifs.getThen() or g.getParent+() = ifs.getThen()) and
  /* No assignment of a negative constant to v in the if-then before the goto. */
  not exists(Assignment a, Stmt s |
    s = a.getEnclosingStmt() and
    (s = ifs.getThen() or s.getParent+() = ifs.getThen()) and
    a.getLValue().(VariableAccess).getTarget() = v and
    (
      a.getRValue().getValue().toInt() < 0 or
      a.getRValue().(UnaryMinusExpr).getOperand().getValue().toInt() > 0
    )
  ) and
  /* The goto's target label has a `return v;` after it (line-number proxy). */
  lbl = g.getTarget() and
  r.getEnclosingFunction() = v.getFunction() and
  r.getExpr().(VariableAccess).getTarget() = v and
  r.getLocation().getStartLine() >= lbl.getLocation().getStartLine() and
  /* Between the label and the return, no rescue assignment to v either. */
  not exists(Assignment a2 |
    a2.getEnclosingFunction() = v.getFunction() and
    a2.getLValue().(VariableAccess).getTarget() = v and
    (
      a2.getRValue().getValue().toInt() < 0 or
      a2.getRValue().(UnaryMinusExpr).getOperand().getValue().toInt() > 0
    ) and
    a2.getLocation().getStartLine() >= lbl.getLocation().getStartLine() and
    a2.getLocation().getStartLine() <= r.getLocation().getStartLine()
  )
select g,
  "Error-return-code-not-set: jump to label without assigning negative errno to '" +
  v.getName() + "' before goto, while the label returns it unmodified."
