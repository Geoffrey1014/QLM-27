/**
 * @name  rq3-c2-lu-4-rep2
 * @id    cpp/rq3/c2/lu-4-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing platform_device_put on error paths after
 *              a successful platform_device_alloc (pattern from
 *              dwc3_pci_probe leak fix 9bbfceea12a8).
 */

import cpp

/** Holds if `fc` is a call to the resource-acquiring API. */
predicate is_target_alloc(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_alloc"
}

/** Holds if `fc` is a call to the matching release/cleanup function. */
predicate is_release_call(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_put"
}

/**
 * Holds if `assign` stores the result of a platform_device_alloc call
 * into some lvalue (typically a struct field like `dwc->dwc3`).
 */
predicate stores_alloc_result(Assignment assign, FunctionCall alloc) {
  is_target_alloc(alloc) and
  assign.getRValue() = alloc
}

/**
 * Holds if `ret` is a `return ret;` (or `return <expr>;`) statement that
 * lives in the same function as `alloc` and is lexically positioned
 * after the alloc call, and there is no `platform_device_put` call on
 * the storage location between `alloc` and `ret`.
 */
predicate error_return_without_release(FunctionCall alloc, ReturnStmt ret) {
  exists(Function f |
    alloc.getEnclosingFunction() = f and
    ret.getEnclosingFunction() = f and
    alloc.getLocation().getStartLine() < ret.getLocation().getStartLine() and
    not exists(FunctionCall rel |
      is_release_call(rel) and
      rel.getEnclosingFunction() = f and
      rel.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
      rel.getLocation().getStartLine() < ret.getLocation().getStartLine()
    )
  )
}

/**
 * Holds if function `f` has an error-return on a path following an
 * alloc, with no goto to an err-label block that calls release.
 * This captures the pattern in the dwc3_pci_probe leak.
 */
predicate leaky_function(Function f, FunctionCall alloc, ReturnStmt ret) {
  is_target_alloc(alloc) and
  alloc.getEnclosingFunction() = f and
  ret.getEnclosingFunction() = f and
  error_return_without_release(alloc, ret) and
  // Make sure the function has a release label/call somewhere (else
  // it's not the pattern of "forgot to goto err"); we require at least
  // one platform_device_put exists in the function.
  exists(FunctionCall rel |
    is_release_call(rel) and rel.getEnclosingFunction() = f
  )
}

from Function f, FunctionCall alloc, ReturnStmt ret
where leaky_function(f, alloc, ret)
select ret,
  "Possible missing platform_device_put on error return after platform_device_alloc in $@.",
  f, f.getName()
