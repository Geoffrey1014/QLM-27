/**
 * @name Missing resource release on security hook failure
 * @description When a security_* hook (e.g. security_sctp_assoc_request) is checked
 *              for failure and the function returns/discards on that error path, any
 *              resource allocated earlier in the same function (e.g. via *_new(),
 *              *_alloc(), *_create()) must be released on that error path. Missing the
 *              release leaks memory or refcounts. Pattern source: sctp commit
 *              b6631c6031c7 "sctp: Fix memory leak in sctp_sf_do_5_2_4_dupcook".
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-release-on-security-hook-failure
 * @tags security
 *       reliability
 *       memory-leak
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * A call that looks like a resource allocator: returns a pointer (or assigns one)
 * and has a name matching the conventional kernel allocator families.
 */
class AllocCall extends FunctionCall {
  AllocCall() {
    exists(string n | n = this.getTarget().getName() |
      n.matches("%\\_new") or
      n.matches("%\\_alloc") or
      n.matches("%\\_alloc\\_%") or
      n.matches("%\\_create") or
      n.matches("kmalloc%") or
      n.matches("kzalloc%") or
      n.matches("kcalloc%") or
      n = "vmalloc" or
      n = "vzalloc" or
      n.matches("sctp\\_%\\_new") or
      n.matches("sctp\\_%\\_create") or
      n.matches("of\\_%\\_get\\_%") or
      n.matches("of\\_parse\\_%") or
      n.matches("of\\_find\\_%")
    )
  }
}

/**
 * A call to a security_* LSM hook that returns nonzero on failure.
 */
class SecurityHookCall extends FunctionCall {
  SecurityHookCall() { this.getTarget().getName().matches("security\\_%") }
}

/**
 * A release/cleanup call matching the variable that held the allocated resource.
 */
predicate isReleaseCall(FunctionCall fc, Variable v) {
  exists(string n | n = fc.getTarget().getName() |
    n.matches("%\\_free") or
    n.matches("%\\_free\\_%") or
    n = "kfree" or
    n = "vfree" or
    n.matches("%\\_put") or
    n.matches("%\\_release") or
    n.matches("%\\_destroy") or
    n.matches("%\\_release\\_%") or
    n.matches("%\\_destroy\\_%")
  ) and
  fc.getAnArgument().(VariableAccess).getTarget() = v
}

/**
 * A statement that exits the function: return, goto-out, or pdiscard helpers.
 */
predicate isExitStmt(Stmt s) {
  s instanceof ReturnStmt
  or
  exists(GotoStmt g | g = s and g.getName().matches("%out%"))
  or
  exists(ReturnStmt r, FunctionCall fc |
    r = s and
    fc = r.getExpr().(FunctionCall) and
    fc.getTarget().getName().matches("%pdiscard%")
  )
}

from
  Function f, AllocCall alloc, Variable v, SecurityHookCall sec, IfStmt ifs, Stmt exitStmt
where
  // Allocation result stored into v
  alloc.getEnclosingFunction() = f and
  (
    exists(AssignExpr ae |
      ae.getRValue() = alloc and ae.getLValue().(VariableAccess).getTarget() = v
    )
    or
    exists(Variable vv |
      vv = v and
      vv.getInitializer().getExpr() = alloc
    )
  ) and
  // Security hook called in same function
  sec.getEnclosingFunction() = f and
  // If-statement guarded by the security hook return value
  ifs.getEnclosingFunction() = f and
  (
    ifs.getControllingExpr() = sec
    or
    ifs.getControllingExpr().(UnaryOperation).getOperand() = sec
    or
    exists(Expr cond | cond = ifs.getControllingExpr() |
      cond.getAChild*() = sec
    )
  ) and
  // The then-branch exits the function
  exitStmt = ifs.getThen().(BlockStmt).getStmt(_) and
  isExitStmt(exitStmt) and
  // The allocation precedes the security check (textual order proxy)
  alloc.getLocation().getStartLine() < sec.getLocation().getStartLine() and
  // No release of v on that exit path (within the then-branch)
  not exists(FunctionCall rel |
    rel.getEnclosingFunction() = f and
    isReleaseCall(rel, v) and
    rel.getLocation().getStartLine() >= ifs.getLocation().getStartLine() and
    rel.getLocation().getStartLine() <= exitStmt.getLocation().getEndLine()
  ) and
  // And there is no release between alloc and the if anywhere reachable on this path
  not exists(FunctionCall rel |
    rel.getEnclosingFunction() = f and
    isReleaseCall(rel, v) and
    rel.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    rel.getLocation().getStartLine() < ifs.getLocation().getStartLine()
  )
select ifs,
  "Possible resource leak: '" + v.getName() +
    "' allocated by '" + alloc.getTarget().getName() +
    "' is not released on the failure path of security hook '" +
    sec.getTarget().getName() + "'."
