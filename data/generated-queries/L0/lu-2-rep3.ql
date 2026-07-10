/**
 * @name Missing kfree on early return after kmalloc (af9005_identify_state pattern)
 * @description Detects a ReturnStmt in a function that previously allocated a
 *              buffer via kmalloc into a local variable, where between the
 *              allocation and this return there is neither a kfree on that
 *              variable nor a goto to a cleanup label. Models the memory-leak
 *              shape fixed in commit 2289adbfa559.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-lu2-kmalloc-missing-kfree-on-return
 */
import cpp

predicate isKmallocCall(FunctionCall fc) {
  fc.getTarget().getName() = "kmalloc"
}

from FunctionCall acquire, Function enclosing, Variable v, ReturnStmt ret
where isKmallocCall(acquire)
  and enclosing = acquire.getEnclosingFunction()
  and exists(AssignExpr ae |
    ae.getRValue() = acquire and
    ae.getLValue() = v.getAnAccess()
  )
  and ret.getEnclosingFunction() = enclosing
  and ret.getLocation().getStartLine() > acquire.getLocation().getStartLine()
  and not exists(FunctionCall release |
    release.getTarget().getName() = "kfree" and
    release.getEnclosingFunction() = enclosing and
    release.getAnArgument() = v.getAnAccess() and
    release.getLocation().getStartLine() < ret.getLocation().getStartLine() and
    release.getLocation().getStartLine() > acquire.getLocation().getStartLine()
  )
  and not exists(GotoStmt g |
    g.getEnclosingFunction() = enclosing and
    g.getLocation().getStartLine() < ret.getLocation().getStartLine() and
    g.getLocation().getStartLine() > acquire.getLocation().getStartLine()
  )
select ret,
  "Return in '" + enclosing.getName() + "' after kmalloc into '" + v.getName() +
  "' may leak the buffer (no intervening kfree or goto-cleanup between the allocation and this return)."
