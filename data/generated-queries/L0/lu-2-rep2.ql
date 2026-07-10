/**
 * @name Missing kfree on early-return path after kmalloc (buffer memory leak)
 * @description Detects functions that call kmalloc and then, on some
 *              return path that lies textually after the kmalloc, exit
 *              without a preceding kfree cleanup in the function. Motivated
 *              by af9005_identify_state (commit 2289adbfa559) — the
 *              `return -EIO` in the reply-classification else branch skips
 *              the `err: kfree(buf);` label.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-lu2-kmalloc-early-return-leak
 */
import cpp

predicate isKmallocCall(FunctionCall fc) {
  fc.getTarget().getName() = "kmalloc"
}

from FunctionCall acquire, Function enclosing, ReturnStmt earlyRet
where isKmallocCall(acquire)
  and enclosing = acquire.getEnclosingFunction()
  and earlyRet.getEnclosingFunction() = enclosing
  and earlyRet.getLocation().getStartLine() > acquire.getLocation().getStartLine()
  and not exists(FunctionCall release |
    release.getTarget().getName() = "kfree" and
    release.getEnclosingFunction() = enclosing and
    release.getLocation().getStartLine() < earlyRet.getLocation().getStartLine()
  )
select earlyRet,
  "Early return in function '" + enclosing.getName() +
  "' after kmalloc but before any kfree cleanup — possible buffer leak."
