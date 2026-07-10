/**
 * @name Function returns success (0) on an allocation-failure-branch goto
 *       (error-return-code pattern) [L0 zero-shot single-predicate]
 * @description Detects int-returning functions where:
 *                - a local int variable (e.g. `status`) flows to the return
 *                  expression;
 *                - the function calls an allocator whose name matches
 *                  `%_alloc` (e.g. `usb_otg_descriptor_alloc`); and
 *                - a `goto` to a cleanup label executes without any prior
 *                  negative-literal assignment to the return variable on
 *                  this failure branch.
 *              Under these conditions the function silently returns the
 *              last non-negative status on what is in fact a failure
 *              branch — the bug shape fixed by upstream commit
 *              c021e0235770 ("usb: gadget: legacy: fix error return code
 *              of multi_bind()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/error-return-code-missing-alloc
 * @tags reliability
 *       error-handling
 *       error-return
 */

import cpp

predicate isBuggyGotoWithoutErrAssignment(Function f, LocalVariable statusVar, GotoStmt g) {
  f.fromSource() and
  statusVar.getFunction() = f and
  statusVar.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = statusVar
  ) and
  g.getEnclosingFunction() = f and
  exists(FunctionCall alloc |
    alloc.getEnclosingFunction() = f and
    alloc.getTarget().getName().matches("%_alloc")
  ) and
  not exists(Assignment a |
    a.getEnclosingFunction() = f and
    a.getLValue().(VariableAccess).getTarget() = statusVar and
    a.getRValue().getValue().toInt() < 0 and
    a.getLocation().getStartLine() < g.getLocation().getStartLine()
  )
}

from Function f, LocalVariable statusVar, GotoStmt g
where isBuggyGotoWithoutErrAssignment(f, statusVar, g)
select g,
       "Function `" + f.getName() +
       "` may reach cleanup goto with `" + statusVar.getName() +
       "` still non-negative on an allocation-failure branch — caller may see success."
