/**
 * @name Missing kfree on early return after kmalloc (af9005_identify_state pattern, L1)
 * @description Detects a ReturnStmt in a function that previously allocated a
 *              buffer via kmalloc into a local variable, where between the
 *              allocation and this return there is neither a kfree on that
 *              variable nor a goto to a cleanup label. Models the memory-leak
 *              shape fixed in commit 2289adbfa559. L1 compositional variant
 *              using two predicates: an allocation matcher and a cleanup
 *              witness used in negation.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l1-lu2-kmalloc-missing-kfree-on-return
 */
import cpp

predicate isKmallocIntoVar(FunctionCall alloc, Variable v) {
  alloc.getTarget().getName() = "kmalloc" and
  exists(AssignExpr ae |
    ae.getRValue() = alloc and
    ae.getLValue() = v.getAnAccess()
  )
}

predicate hasCleanupBetween(FunctionCall alloc, Variable v, ReturnStmt ret) {
  exists(FunctionCall release |
    release.getTarget().getName() = "kfree" and
    release.getEnclosingFunction() = ret.getEnclosingFunction() and
    release.getAnArgument() = v.getAnAccess() and
    release.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    release.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
  or
  exists(GotoStmt g |
    g.getEnclosingFunction() = ret.getEnclosingFunction() and
    g.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    g.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
}

from FunctionCall alloc, Variable v, ReturnStmt ret, Function enclosing
where isKmallocIntoVar(alloc, v)
  and enclosing = alloc.getEnclosingFunction()
  and ret.getEnclosingFunction() = enclosing
  and ret.getLocation().getStartLine() > alloc.getLocation().getStartLine()
  and not hasCleanupBetween(alloc, v, ret)
select ret,
  "Return in '" + enclosing.getName() + "' after kmalloc into '" + v.getName() +
  "' may leak the buffer (no intervening kfree(v) or goto-cleanup between the allocation and this return)."
