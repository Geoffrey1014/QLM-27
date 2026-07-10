/**
 * @name Missing release call on early-return error path after pointer allocation
 * @description A function calls an allocator-style API that returns a
 *              pointer requiring an explicit paired release (e.g.
 *              platform_device_alloc / platform_device_put). The function
 *              has an error-cleanup label whose body calls the matching
 *              release on the allocated pointer (stored in a field or
 *              variable). If a later error check after the allocation
 *              returns directly instead of "goto"ing the cleanup label,
 *              the allocated object leaks (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-4
 */

import cpp

/* Acquirer-style APIs: name ends with "_alloc", "_create", "_get", or
 * "_new" and the call's value is stored somewhere we can track. We keep
 * the pattern generic so it carries over from the POC to the real kernel. */
bindingset[name]
predicate isAcquireCallName(string name) {
  name.matches("%_alloc") or
  name.matches("%_create") or
  name.matches("%_new") or
  name = "platform_device_alloc"
}

/* Release-style API: name matches "<prefix>_put" or "<prefix>_free" or
 * "<prefix>_destroy" — the paired counterpart of the acquirer. */
bindingset[name]
predicate isReleaseCallName(string name) {
  name.matches("%_put") or
  name.matches("%_free") or
  name.matches("%_destroy")
}

/* Get the "stem" of a function name = part before the last underscore.
 * Used to require the release call pair the acquirer (e.g.
 * platform_device_alloc <-> platform_device_put). */
bindingset[name]
string apiStem(string name) {
  result = name.regexpCapture("^(.*)_(alloc|create|new|put|free|destroy)$", 1)
}

/* An acquire call whose return value is written into some Expr (a
 * variable assignment or a field-store), captured as `lhs`. */
predicate acquireAssign(FunctionCall acq, Expr lhs, Function enclosing) {
  isAcquireCallName(acq.getTarget().getName()) and
  acq.getEnclosingFunction() = enclosing and
  acq.getType().getUnspecifiedType() instanceof PointerType and
  exists(AssignExpr a |
    a.getRValue() = acq and
    a.getLValue() = lhs
  )
}

/* Two expressions refer to the "same storage" if they are both
 * VariableAccesses of the same Variable, or both FieldAccesses of the
 * same Field on a VariableAccess of the same Variable. This lets us
 * tie `dwc->dwc3 = platform_device_alloc(...)` to the later
 * `platform_device_put(dwc->dwc3)`. */
predicate sameStorage(Expr a, Expr b) {
  exists(Variable v |
    a.(VariableAccess).getTarget() = v and
    b.(VariableAccess).getTarget() = v
  )
  or
  exists(Field f, Variable v |
    a.(FieldAccess).getTarget() = f and
    b.(FieldAccess).getTarget() = f and
    a.(FieldAccess).getQualifier().(VariableAccess).getTarget() = v and
    b.(FieldAccess).getQualifier().(VariableAccess).getTarget() = v
  )
}

/* A cleanup label `lbl` in `f` whose subsequent code calls a paired
 * release on the same storage as the acquire's lhs. */
predicate cleanupLabelFor(LabelStmt lbl, FunctionCall rel, Expr lhs, Function f) {
  lbl.getEnclosingFunction() = f and
  rel.getEnclosingFunction() = f and
  isReleaseCallName(rel.getTarget().getName()) and
  apiStem(rel.getTarget().getName()) =
    apiStem(any(FunctionCall acq | acquireAssign(acq, lhs, f)).getTarget().getName()) and
  sameStorage(rel.getArgument(0), lhs) and
  rel.getLocation().getStartLine() >= lbl.getLocation().getStartLine()
}

/* A direct `return <expr>;` statement that is a sibling-cousin of an
 * acquire+cleanup-label pair, i.e. it lives lexically after the acquire
 * but before (or after) the cleanup label, and is the body of an `if`
 * that tests an error condition. */
predicate directReturnAfterAcquire(ReturnStmt ret, FunctionCall acq,
                                   Expr lhs, Function f) {
  ret.getEnclosingFunction() = f and
  acq.getEnclosingFunction() = f and
  ret.getLocation().getStartLine() > acq.getLocation().getStartLine() and
  /* The return is guarded by an IfStmt (typical error check). */
  exists(IfStmt ifs |
    ret.getParent*() = ifs.getThen() and
    ifs.getEnclosingFunction() = f and
    /* Exclude the canonical "acquire failed" null-check: the if condition
     * tests the acquire's storage for null/zero. That return is correct
     * because there is nothing yet to release. */
    not exists(Expr cond, Expr testedStorage |
      cond = ifs.getCondition() and
      (
        /* `if (!storage)` */
        testedStorage = cond.(NotExpr).getOperand() or
        /* `if (storage == NULL)` / `if (NULL == storage)` */
        exists(EQExpr eq | eq = cond and
          (testedStorage = eq.getLeftOperand() or testedStorage = eq.getRightOperand())
        ) or
        /* `if (storage)` (rare positive form) */
        testedStorage = cond
      ) and
      sameStorage(testedStorage, lhs)
    )
  )
}

from Function f, FunctionCall acq, Expr lhs, LabelStmt lbl,
     FunctionCall rel, ReturnStmt ret
where
  acquireAssign(acq, lhs, f) and
  cleanupLabelFor(lbl, rel, lhs, f) and
  directReturnAfterAcquire(ret, acq, lhs, f) and
  /* The leaking return precedes the cleanup label (so it doesn't fall
   * through into it) and is not itself a `goto <lbl>`. */
  ret.getLocation().getStartLine() < lbl.getLocation().getStartLine() and
  /* No goto to `lbl` lexically dominates this return inside the same
   * enclosing if. */
  not exists(GotoStmt g |
    g.getEnclosingFunction() = f and
    g.getTarget() = lbl and
    g.getLocation().getStartLine() = ret.getLocation().getStartLine()
  )
select ret,
  "Missing release of '" + lhs.toString() +
    "' acquired by " + acq.getTarget().getName() +
    "() on this error path: function has cleanup label '" + lbl.getName() +
    "' that calls " + rel.getTarget().getName() +
    "(), but this `return` bypasses it (CWE-401 resource leak)."
