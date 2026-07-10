/**
 * @name Missing error-return-code assignment on goto-to-cleanup branch
 * @description Detects a function-local pattern where an error-condition
 *              branch jumps via `goto <cleanup_label>` to a label whose
 *              return is `return <int_var>;`, without first assigning a
 *              negative errno value to that variable. The caller will
 *              receive whatever stale value the variable held (often 0,
 *              wrongly indicating success).
 *
 *              Models commits like 45c7eaeb29d6
 *              (thermal_of_populate_bind_params).
 * @kind problem
 * @problem.severity warning
 * @id qlm/err-return-missing-assignment
 * @tags reliability
 *       correctness
 */

import cpp

/* The function returns an integral local variable from a `return v;` stmt. */
predicate isCleanupReturn(ReturnStmt r, LocalVariable v) {
  exists(VariableAccess va |
    r.getExpr() = va and
    va.getTarget() = v and
    v.getType().getUnspecifiedType() instanceof IntegralType
  )
}

/* A label statement that precedes such a return inside the same function. */
predicate isCleanupLabel(LabelStmt lbl, LocalVariable v) {
  exists(ReturnStmt r |
    isCleanupReturn(r, v) and
    r.getEnclosingFunction() = lbl.getEnclosingFunction() and
    lbl.getLocation().getStartLine() <= r.getLocation().getStartLine()
  )
}

/* A goto whose target is a cleanup label. */
predicate gotoTargetsCleanup(GotoStmt g, LocalVariable v) {
  exists(LabelStmt lbl |
    isCleanupLabel(lbl, v) and
    g.getTarget() = lbl and
    g.getEnclosingFunction() = lbl.getEnclosingFunction()
  )
}

/* The goto sits directly under an `if` guard (i.e. it's a conditional jump). */
predicate gotoUnderErrorGuard(GotoStmt g) {
  exists(IfStmt ifs |
    ifs.getThen() = g
    or
    (ifs.getThen() instanceof BlockStmt and
     ifs.getThen().(BlockStmt).getAStmt() = g)
  )
}

/* An expression that looks like a negative errno literal (e.g. -ENOMEM). */
predicate errnoMacroValue(Expr e) {
  exists(UnaryMinusExpr um, Expr inner |
    um = e and
    inner = um.getOperand() and
    (
      (exists(inner.getValue()) and inner.getValue().toInt() >= 1 and inner.getValue().toInt() <= 4096)
      or
      exists(MacroInvocation mi |
        mi.getExpr() = inner and
        mi.getMacroName().regexpMatch("E[A-Z0-9]+"))
    )
  )
  or
  exists(MacroInvocation mi |
    mi.getExpr() = e and
    mi.getMacroName().regexpMatch("E[A-Z0-9]+"))
}

/* True iff `v = -E<errno>` is assigned in the same function on a line
 * within 3 lines preceding `before`. Used to exclude gotos that DO set
 * ret to an errno just before jumping. */
predicate assignsErrnoToBefore(LocalVariable v, Stmt before) {
  exists(AssignExpr a, VariableAccess lhs, ExprStmt es |
    lhs = a.getLValue() and
    lhs.getTarget() = v and
    errnoMacroValue(a.getRValue()) and
    es.getExpr() = a and
    es.getEnclosingFunction() = before.getEnclosingFunction() and
    es.getLocation().getStartLine() < before.getLocation().getStartLine() and
    es.getLocation().getStartLine() >= before.getLocation().getStartLine() - 3
  )
}

from GotoStmt g, LocalVariable v
where
  gotoTargetsCleanup(g, v) and
  gotoUnderErrorGuard(g) and
  not assignsErrnoToBefore(v, g) and
  not g.getEnclosingFunction().getName().matches("%_fixed%") and
  not g.getEnclosingFunction().getName().matches("%_fp_%")
select g,
  "error-path goto to cleanup label without assigning errno to return variable " +
    v.getName()
