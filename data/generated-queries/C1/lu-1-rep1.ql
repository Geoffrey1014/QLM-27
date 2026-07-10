/**
 * @name C1 lu-1: missing cleanup on early-return after pointer acquire
 * @description Detects a function that obtains a pointer p from a call,
 *              then on a guarded error path (not testing p itself)
 *              returns without passing p to any cleanup helper.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-1
 */

import cpp

/* `v` is a local pointer variable inside `caller` whose value comes from
 * a call (either as initializer or first assignment). */
predicate acquiredPointer(LocalVariable v, Function caller, ControlFlowNode acquireSite) {
  v.getFunction() = caller and
  v.getType().getUnspecifiedType() instanceof PointerType and
  (
    exists(FunctionCall fc |
      fc = v.getInitializer().getExpr() and
      acquireSite = fc
    )
    or
    exists(AssignExpr ae, FunctionCall fc |
      ae.getLValue() = v.getAnAccess() and
      ae.getRValue() = fc and
      acquireSite = ae
    )
  )
}

/* `va` is a variable access of `v` somewhere inside `s` (recursively
 * through statements and expressions). */
predicate accessInStmt(VariableAccess va, LocalVariable v, Stmt s) {
  va.getTarget() = v and
  exists(Stmt host | host = va.getEnclosingStmt() and host.getParentStmt*() = s)
}

/* `fc` is a call inside `s` that takes `v` as an argument. */
predicate callOnVarInStmt(LocalVariable v, Stmt s) {
  exists(FunctionCall fc, VariableAccess va |
    va = fc.getAnArgument() and
    va.getTarget() = v and
    fc.getEnclosingStmt().getParentStmt*() = s
  )
}

/* An if-statement whose condition does not mention `v`, whose then-branch
 * contains a ReturnStmt, and whose then-branch performs no call passing
 * `v`. */
predicate badEarlyReturn(IfStmt ifs, ReturnStmt ret, LocalVariable v, Function caller) {
  ifs.getEnclosingFunction() = caller and
  ret.getEnclosingFunction() = caller and
  ret.getParentStmt*() = ifs.getThen() and
  not exists(VariableAccess va |
    va.getTarget() = v and
    va.getParent+() = ifs.getCondition()
  ) and
  not callOnVarInStmt(v, ifs.getThen())
}

from Function f, LocalVariable v, ControlFlowNode acquireSite, IfStmt ifs, ReturnStmt ret
where
  acquiredPointer(v, f, acquireSite) and
  badEarlyReturn(ifs, ret, v, f) and
  // The if must occur after the acquire (source-line order, fine for a
  // single-TU detector and a useful disambiguator for the kernel scan).
  acquireSite.getLocation().getStartLine() < ifs.getLocation().getStartLine()
select ret,
  "Possible resource leak: local pointer '" + v.getName() +
    "' obtained by a function call may leak on this early-return path of '" +
    f.getName() + "' (no cleanup call on it in the then-branch, and the " +
    "branch condition does not test the pointer itself)."
