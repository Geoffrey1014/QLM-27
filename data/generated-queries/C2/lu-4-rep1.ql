/**
 * @name  rq3-c2-lu-4-rep1
 * @id    cpp/rq3/c2/lu-4-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *   Detects missing platform_device_put after platform_device_alloc on error paths.
 */

import cpp

/* Predicate 1: a call that acquires a platform_device via platform_device_alloc. */
predicate acquires_pdev(FunctionCall acq) {
  acq.getTarget().getName() = "platform_device_alloc"
}

/* Predicate 2: a call that releases a platform_device via platform_device_put. */
predicate releases_pdev(FunctionCall rel) {
  rel.getTarget().getName() = "platform_device_put"
}

/* Predicate 3: a return statement that returns a non-zero / error value
 * (heuristic: returns a variable named 'ret' or an integer expression that's not literal 0). */
predicate error_return(ReturnStmt r) {
  exists(Expr e | e = r.getExpr() |
    e.(VariableAccess).getTarget().getName() = "ret"
    or
    e instanceof UnaryMinusExpr
    or
    (e.getValue().toInt() != 0 and exists(e.getValue().toInt()))
  )
}

/* Predicate 4: an early-error return that occurs AFTER an acquisition in the same function,
 * with no release call between them on the control flow.
 * Approximation: same function contains acq and r, acq's location precedes r,
 * and no releases_pdev exists in the function lexically between them. */
predicate missing_release_between(FunctionCall acq, ReturnStmt r) {
  exists(Function f |
    acq.getEnclosingFunction() = f and
    r.getEnclosingFunction() = f and
    acquires_pdev(acq) and
    error_return(r) and
    acq.getLocation().getStartLine() < r.getLocation().getStartLine() and
    not exists(FunctionCall rel |
      releases_pdev(rel) and
      rel.getEnclosingFunction() = f and
      rel.getLocation().getStartLine() > acq.getLocation().getStartLine() and
      rel.getLocation().getStartLine() < r.getLocation().getStartLine()
    )
  )
}

/* Predicate 5: bug site — function contains an acquire and an early error return
 * with no intervening release, AND the function does have some release elsewhere
 * (showing the developer knew cleanup was needed, but missed this path). */
predicate bug_site(Function f, FunctionCall acq, ReturnStmt r) {
  acq.getEnclosingFunction() = f and
  r.getEnclosingFunction() = f and
  missing_release_between(acq, r)
}

from Function f, FunctionCall acq, ReturnStmt r
where bug_site(f, acq, r)
select r,
  "Possible missing platform_device_put after platform_device_alloc at $@ on this error return path in function " + f.getName(),
  acq, "acquisition site"
