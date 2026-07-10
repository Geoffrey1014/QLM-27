/**
 * @name Early return bypasses existing error-cleanup goto in probe-like function
 * @description In a function that allocates a resource (e.g. platform_device_alloc,
 *              of_get_child_by_name, kzalloc, etc.) and uses a `goto <err_label>;`
 *              chain to release it on error, a sibling error path that uses `return`
 *              directly instead of `goto <err_label>` will leak the resource. This
 *              query flags such early returns located after the allocation and before
 *              the cleanup label, when the same function already shows the goto-cleanup
 *              idiom for other error checks.
 * @kind problem
 * @problem.severity warning
 * @id cpp/probe-early-return-bypasses-cleanup-goto
 * @tags correctness
 *       memory-leak
 */

import cpp

/**
 * A function call whose return value is an acquired resource that must be
 * released on the error path. We use the common kernel acquire-style APIs
 * that the dwc3-pci leak (commit 9bbfcee) and its siblings exhibit.
 */
predicate acquiresResource(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "platform_device_alloc" or
    n = "platform_device_register" or
    n = "platform_device_register_full" or
    n = "of_get_child_by_name" or
    n = "of_find_node_by_name" or
    n = "of_find_node_by_phandle" or
    n = "of_parse_phandle" or
    n = "of_node_get" or
    n = "of_get_next_child" or
    n = "of_get_parent" or
    n = "kzalloc" or
    n = "kmalloc" or
    n = "kcalloc" or
    n = "kmemdup" or
    n = "devm_kzalloc" or
    n = "usb_alloc_urb" or
    n = "alloc_workqueue" or
    n = "ioremap" or
    n = "request_firmware" or
    n = "clk_get" or
    n = "regulator_get"
  )
}

/**
 * A `goto err_label;` statement, where the label name looks like an error
 * cleanup label (err, err_*, error, fail, fail_*, out, out_*, free_*, put_*,
 * unwind*).
 */
predicate isErrorCleanupGoto(GotoStmt gs) {
  exists(string lbl | lbl = gs.getName().toLowerCase() |
    lbl = "err" or
    lbl.matches("err\\_%") or
    lbl.matches("err%") or
    lbl = "error" or
    lbl.matches("error\\_%") or
    lbl = "fail" or
    lbl.matches("fail\\_%") or
    lbl = "out" or
    lbl.matches("out\\_%") or
    lbl.matches("free\\_%") or
    lbl.matches("put\\_%") or
    lbl.matches("unwind%") or
    lbl.matches("undo\\_%") or
    lbl.matches("release\\_%") or
    lbl.matches("cleanup%")
  )
}

/**
 * A ReturnStmt that returns an error value (a negative literal, or a variable
 * that the surrounding `if (ret < 0)` / `if (ret)` test conditions on). We
 * approximate with: the ReturnStmt is the body (or first stmt) of an
 * IfStmt whose condition mentions a variable, OR the returned expression is
 * a negative integer constant.
 */
predicate looksLikeErrorReturn(ReturnStmt rs) {
  exists(IfStmt is | is.getThen() = rs or is.getThen().(BlockStmt).getStmt(0) = rs) and
  exists(rs.getExpr())
  or
  exists(Expr e | e = rs.getExpr() |
    e.getValue().toInt() < 0
    or
    // return ret;   where ret was checked < 0 in surrounding if
    e instanceof VariableAccess
  )
}

from Function f, FunctionCall acquire, ReturnStmt badRet, GotoStmt goodGoto
where
  // The function acquires a resource.
  acquiresResource(acquire) and
  acquire.getEnclosingFunction() = f and
  // The same function already uses a goto-cleanup idiom.
  goodGoto.getEnclosingFunction() = f and
  isErrorCleanupGoto(goodGoto) and
  // There is some error return in the same function that is NOT a goto.
  badRet.getEnclosingFunction() = f and
  looksLikeErrorReturn(badRet) and
  // The bad return is positioned AFTER the acquire (so resource is live).
  acquire.getLocation().getStartLine() < badRet.getLocation().getStartLine() and
  // And BEFORE the cleanup goto's label sits (so it's bypassing the cleanup
  // that exists in the same function).
  badRet.getLocation().getStartLine() < goodGoto.getEnclosingStmt().getEnclosingBlock()
                                              .getLocation().getEndLine() and
  // Don't flag the goto's own return-equivalent if the function is tiny.
  f.getLocation().getFile() = badRet.getLocation().getFile() and
  // Filter: probe-ish or init-ish functions (where this idiom is dominant).
  (
    f.getName().matches("%probe%") or
    f.getName().matches("%_init") or
    f.getName().matches("%init_%") or
    f.getName().matches("%_register") or
    f.getName().matches("%setup%") or
    f.getName().matches("%create%") or
    f.getName().matches("%add%")
  )
select badRet,
  "This error `return` in function $@ bypasses the in-function cleanup label `" +
    goodGoto.getName() + "` reached at $@, after acquiring a resource via `" +
    acquire.getTarget().getName() + "` at $@. Consider `goto " + goodGoto.getName() +
    ";` instead to avoid leaking the resource.",
  f, f.getName(), goodGoto, "goto " + goodGoto.getName(),
  acquire, acquire.getTarget().getName()
