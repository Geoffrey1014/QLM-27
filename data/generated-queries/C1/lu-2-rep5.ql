/**
 * @name Allocated resource leaked on early-return bypassing cleanup label
 * @description A local pointer obtained from an allocation-like call has a
 *              cleanup path (release/free of the same variable reachable from
 *              the allocation), but at least one `return` statement reachable
 *              from the allocation does NOT pass through any release of that
 *              variable. Pattern: missing goto-to-cleanup on a branch.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-2
 */

import cpp

/** A function name that looks like a resource acquisition. */
bindingset[n]
predicate isAllocName(string n) {
  n = "kmalloc" or n = "kzalloc" or n = "kcalloc" or n = "kmalloc_array" or
  n = "vmalloc" or n = "vzalloc" or n = "malloc" or
  n.matches("%_alloc") or n.matches("alloc_%") or
  n.matches("%kmalloc%") or n.matches("%kzalloc%") or
  n.matches("%kcalloc%")
}

/** A function call that looks like a release on variable v. */
predicate isReleaseCall(FunctionCall fc, Variable v) {
  fc.getAnArgument() = v.getAnAccess() and
  exists(string n | n = fc.getTarget().getName() |
    n = "kfree" or n = "vfree" or n = "free" or n = "kvfree" or
    n.matches("%_free") or n.matches("free_%") or
    n.matches("%_put") or n.matches("%_release") or
    n.matches("%_destroy")
  )
}

/** An allocation-style call assigned to local pointer v. */
predicate isAcquisition(Expr acq, LocalVariable v) {
  v.getType().getUnspecifiedType() instanceof PointerType and
  exists(FunctionCall fc | fc = acq |
    isAllocName(fc.getTarget().getName()) and
    (
      // direct assignment: v = alloc(...)
      exists(AssignExpr ae |
        ae.getLValue() = v.getAnAccess() and ae.getRValue() = fc
      )
      or
      // initialiser: T *v = alloc(...)
      v.getInitializer().getExpr() = fc
    )
  )
}

from Function f, LocalVariable v, Expr acq, ReturnStmt leak
where
  isAcquisition(acq, v) and
  acq.getEnclosingFunction() = f and
  leak.getEnclosingFunction() = f and
  // the return is reachable from the acquisition
  acq.getASuccessor+() = leak and
  // at least one release of v is also reachable from the acquisition
  // (so this function DOES have a cleanup path — the bug is on a branch
  //  that bypasses it, not an "always-leaks" simple function).
  exists(FunctionCall rel |
    isReleaseCall(rel, v) and
    acq.getASuccessor+() = rel and
    rel.getEnclosingFunction() = f
  ) and
  // but THIS return path has no intervening release of v
  not exists(FunctionCall rel2 |
    isReleaseCall(rel2, v) and
    acq.getASuccessor+() = rel2 and
    rel2.getASuccessor+() = leak
  ) and
  // and this return is not the "alloc failed" guard (e.g. return -ENOMEM
  // immediately after a null-check). Heuristic: if the only thing between
  // the acquisition and the return is a single null-test on v, skip.
  not exists(IfStmt nullChk |
    nullChk.getEnclosingFunction() = f and
    acq.getASuccessor+() = nullChk and
    nullChk.getASuccessor+() = leak and
    nullChk.getCondition().getAChild*() = v.getAnAccess() and
    // and there is no other statement between acq and leak besides this
    // null check (best-effort filter)
    not exists(Stmt other |
      other.getEnclosingFunction() = f and
      acq.getASuccessor+() = other and
      other.getASuccessor+() = leak and
      other != nullChk and
      not other = nullChk.getThen() and
      not other.getParent*() = nullChk
    )
  )
select leak,
  "Possible leak of '" + v.getName() +
    "' acquired at $@: this return path has no release, " +
    "but another path in the same function does release it.",
  acq, "acquisition"
