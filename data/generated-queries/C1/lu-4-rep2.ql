/**
 * @name Early-return on post-acquisition error check skips established cleanup path
 * @description After acquiring a resource via an alloc/create/get-style call,
 *              other sibling error-check branches in the same function jump
 *              to a cleanup label (`goto err`) that releases the resource,
 *              but one error-check branch returns directly. Because the
 *              direct return skips the cleanup path, the acquired resource
 *              is leaked on that failure path.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-4
 */

import cpp

bindingset[n]
predicate isAcquireName(string n) {
  n.matches("%_alloc") or
  n.matches("%_alloc_%") or
  n.matches("alloc_%") or
  n.matches("%kzalloc%") or
  n.matches("%kmalloc%") or
  n.matches("%_create") or
  n.matches("%_create_%") or
  n.matches("%_get") or
  n.matches("%_get_%") or
  n.matches("%_acquire") or
  n.matches("%_lookup") or
  n.matches("%_find_%") or
  n.matches("%_open") or
  n.matches("%parse_phandle%") or
  n.matches("%_register") or
  n.matches("%_new")
}

bindingset[n]
predicate isReleaseName(string n) {
  n.matches("%_put") or
  n.matches("%_free") or
  n.matches("free_%") or
  n.matches("kfree%") or
  n.matches("%release%") or
  n.matches("%_destroy") or
  n.matches("%_unref") or
  n.matches("%_close")
}

/** Statement `s` is in the then-branch of IfStmt `ifs`. */
predicate isThenBranch(IfStmt ifs, Stmt s) {
  s = ifs.getThen() or
  s.getParent+() = ifs.getThen()
}

/** The condition expression of `ifs` mentions variable `v` (used to filter
 *  out `if (!resource)` post-acquisition null-checks). */
predicate ifCondMentionsVar(IfStmt ifs, Variable v) {
  exists(VariableAccess va |
    va = v.getAnAccess() and
    va.getParent*() = ifs.getCondition()
  )
}

from
  Function f, AssignExpr acq, Variable resVar, FunctionCall acqCall,
  ReturnStmt badRet, IfStmt badIf,
  GotoStmt goodGoto, IfStmt goodIf, FunctionCall relCall
where
  // 1. resource acquisition by assignment inside f
  acq.getEnclosingFunction() = f and
  acq.getLValue() = resVar.getAnAccess() and
  acq.getRValue() = acqCall and
  isAcquireName(acqCall.getTarget().getName()) and
  resVar.getType().getUnspecifiedType() instanceof PointerType and

  // 2. a release-style call exists in f
  relCall.getEnclosingFunction() = f and
  isReleaseName(relCall.getTarget().getName()) and

  // 3. "good" sibling: IfStmt after acquisition whose then-branch is a
  //    goto whose CFG path reaches relCall; condition is not a null
  //    check on resVar
  goodIf.getEnclosingFunction() = f and
  acq.getASuccessor+() = goodIf and
  isThenBranch(goodIf, goodGoto) and
  goodGoto.getASuccessor*() = relCall and
  not ifCondMentionsVar(goodIf, resVar) and

  // 4. "bad" sibling: IfStmt after acquisition whose then-branch is a
  //    direct return that does NOT pass through relCall
  badIf.getEnclosingFunction() = f and
  badIf != goodIf and
  acq.getASuccessor+() = badIf and
  isThenBranch(badIf, badRet) and
  badRet.getEnclosingFunction() = f and
  not badRet.getASuccessor*() = relCall and
  not relCall.getASuccessor*() = badRet and

  // 5. bad-if condition is not a null-check on the acquired resource
  //    (would mean the resource is itself NULL on this branch, so nothing
  //    to leak).
  not ifCondMentionsVar(badIf, resVar) and

  // 6. bad-if condition is not a null-check on ANY pointer variable that
  //    was assigned to immediately before the if (filters out
  //    `x = alloc(); if (!x) return;` shapes where x itself is the failed
  //    acquisition).
  not exists(Variable nv, AssignExpr near |
    near.getEnclosingFunction() = f and
    near.getLValue() = nv.getAnAccess() and
    nv.getType().getUnspecifiedType() instanceof PointerType and
    near.getASuccessor+() = badIf and
    ifCondMentionsVar(badIf, nv) and
    // "immediately before" = no other side-effecting assignment to a
    // distinct pointer in between
    not exists(AssignExpr mid, Variable mv |
      mid.getEnclosingFunction() = f and
      mid.getLValue() = mv.getAnAccess() and
      mv != nv and
      near.getASuccessor+() = mid and
      mid.getASuccessor+() = badIf
    )
  )
select badRet,
  "Resource '" + resVar.getName() + "' acquired by $@ is leaked on this " +
    "early-return path; sibling error checks `goto` the cleanup label " +
    "that calls " + relCall.getTarget().getName() + "().",
  acqCall, acqCall.getTarget().getName()
