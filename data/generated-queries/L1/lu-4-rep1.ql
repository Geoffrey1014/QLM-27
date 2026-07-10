/**
 * @name L1 generated query for lu-4 / fix 9bbfceea12a8
 * @description Missing platform_device_put after platform_device_alloc on error path - memory leak (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l1/lu-4-rep1
 */

import cpp

predicate allocatesResource(FunctionCall acquire) {
  acquire.getTarget().getName() = "platform_device_alloc"
}

/**
 * Holds if `acquire` allocates a resource and there is a `ReturnStmt` reachable
 * from `acquire` in the CFG that is NOT preceded by a matching
 * `platform_device_put` release call. This captures the classic pattern where
 * a middle-of-function error path returns directly and skips the trailing
 * cleanup label (as in the dwc3_pci_probe bug fixed by 9bbfceea12a8).
 */
predicate hasMissingRelease(FunctionCall acquire, ReturnStmt leakRet) {
  allocatesResource(acquire) and
  leakRet.getEnclosingFunction() = acquire.getEnclosingFunction() and
  acquire.getASuccessor+() = leakRet and
  not exists(FunctionCall rel |
    rel.getTarget().getName() = "platform_device_put" and
    rel.getEnclosingFunction() = acquire.getEnclosingFunction() and
    acquire.getASuccessor+() = rel and
    rel.getASuccessor+() = leakRet
  ) and
  not acquire.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall acquire, ReturnStmt leakRet
where hasMissingRelease(acquire, leakRet)
select acquire,
  "platform_device_alloc in " + acquire.getEnclosingFunction().getName() +
  "() may leak on $@ (no platform_device_put on this path) - CWE-401",
  leakRet, "return"
