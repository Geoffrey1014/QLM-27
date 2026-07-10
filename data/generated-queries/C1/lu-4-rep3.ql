/**
 * @name Missing release of allocated resource on error-return path
 * @description Detects a function that acquires a resource via a call
 *              returning a pointer (assigned to a local/struct field),
 *              uses goto-based cleanup elsewhere on error paths, but
 *              contains at least one error-branch `return` that bypasses
 *              the cleanup and leaks the resource. Pattern derived from
 *              CVE-style "missing put/free on error path" memory leaks
 *              (e.g. dwc3_pci_probe / sctp_sf_do_5_2_4_dupcook).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-4
 * @tags correctness
 *       resource-leak
 */

import cpp

/** Heuristic: a call whose target name looks like resource acquisition
 *  and which returns a pointer. */
predicate acquiringCall(FunctionCall fc) {
  fc.getType().getUnspecifiedType() instanceof PointerType and
  exists(string n | n = fc.getTarget().getName().toLowerCase() |
    n.matches("%alloc%") or
    n.matches("%kmalloc%") or
    n.matches("%kzalloc%") or
    n.matches("%kcalloc%") or
    n.matches("%new%") or
    n.matches("%make%") or
    n.matches("%create%") or
    n.matches("%_get_%") or
    n.matches("get\\_%") or
    n.matches("%acquire%") or
    n.matches("%dup%") or
    n.matches("%build%") or
    n.matches("%open%") or
    n.matches("%register%")
  )
}

/** Heuristic: a release/put/free-style call somewhere in the function,
 *  which acts as the function's cleanup handler. */
predicate releasingCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName().toLowerCase() |
    n.matches("%free%") or
    n.matches("%release%") or
    n.matches("%put%") or
    n.matches("%destroy%") or
    n.matches("%close%") or
    n.matches("%delete%") or
    n.matches("%dispose%") or
    n.matches("%cleanup%") or
    n.matches("%unref%") or
    n = "kfree" or n = "vfree"
  )
}

/** Get a textual name for the lvalue an acquiring call's result is
 *  stored into (variable name or last field name). */
string acqTargetName(FunctionCall acq) {
  exists(AssignExpr a | a.getRValue() = acq |
    result = a.getLValue().(VariableAccess).getTarget().getName()
    or
    result = a.getLValue().(FieldAccess).getTarget().getName()
  )
  or
  exists(Variable v | v.getInitializer().getExpr() = acq | result = v.getName())
}

/** True if `acq` stores into something (var or struct field) that is
 *  also passed as an argument to some releasing call inside `f`. */
predicate hasMatchingRelease(FunctionCall acq, Function f) {
  exists(FunctionCall rel | rel.getEnclosingFunction() = f and releasingCall(rel) |
    // Same variable
    exists(Variable v |
      acq = v.getInitializer().getExpr() and
      rel.getAnArgument().(VariableAccess).getTarget() = v
    )
    or
    exists(AssignExpr a, Variable v |
      a.getRValue() = acq and
      a.getLValue().(VariableAccess).getTarget() = v and
      rel.getAnArgument().(VariableAccess).getTarget() = v
    )
    or
    // Same struct field (e.g. dwc->dwc3)
    exists(AssignExpr a, string fname |
      a.getRValue() = acq and
      fname = a.getLValue().(FieldAccess).getTarget().getName() and
      rel.getAnArgument().(FieldAccess).getTarget().getName() = fname
    )
  )
}

/** Convenience: `if (cond) return <expr>;` style error return. */
predicate isErrorReturnInIf(ReturnStmt ret, IfStmt ifs) {
  ret.getParent*() = ifs.getThen() and
  not exists(GotoStmt g | g.getParent*() = ifs.getThen())
}

from FunctionCall acq, Function f, ReturnStmt errRet, IfStmt errIf, GotoStmt cleanupGoto
where
  f = acq.getEnclosingFunction() and
  acquiringCall(acq) and
  // The function uses a goto-based cleanup idiom: at least one other
  // error path in this function does `goto <label>` to reach release.
  cleanupGoto.getEnclosingFunction() = f and
  // There IS a release for what `acq` produced — i.e. function knows
  // how to free it — so a direct `return` skipping cleanup is suspect.
  hasMatchingRelease(acq, f) and
  // Suspicious return: inside the then-branch of an if, no goto in
  // that branch, no release call in that branch.
  errRet.getEnclosingFunction() = f and
  errIf.getEnclosingFunction() = f and
  isErrorReturnInIf(errRet, errIf) and
  not exists(FunctionCall rel |
    rel.getParent*() = errIf.getThen() and releasingCall(rel)
  ) and
  // Control-flow reachable from acq.
  acq.getASuccessor+() = errRet and
  // The if-condition does NOT mention the acquired storage (otherwise
  // it's a null-check on the acquire result -> not a leak).
  not exists(VariableAccess va |
    va = errIf.getCondition().getAChild*() and
    exists(Variable v |
      acq = v.getInitializer().getExpr() and va.getTarget() = v
      or
      exists(AssignExpr a |
        a.getRValue() = acq and
        a.getLValue().(VariableAccess).getTarget() = v and
        va.getTarget() = v
      )
    )
  ) and
  // Skip the very first if-after-acq that null-checks the acq result.
  errIf != min(IfStmt firstIf |
    firstIf.getEnclosingFunction() = f and acq.getASuccessor+() = firstIf
  |
    firstIf order by firstIf.getLocation().getStartLine()
  )
select errRet,
  "Possible resource leak: $@ acquires a resource that is released elsewhere via goto, but this error-return bypasses the cleanup.",
  acq, acq.getTarget().getName()
