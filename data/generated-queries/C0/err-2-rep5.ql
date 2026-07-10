/**
 * @name Missing error code assignment on allocation/lookup failure goto
 * @description A function returning an int error code allocates a resource (kcalloc/
 *              kmalloc/of_count_phandle_with_args/etc.) and on failure jumps to a
 *              cleanup label via goto, but does not assign a negative errno to the
 *              return variable before jumping. The function may then return 0 (success)
 *              on a real failure path, hiding the bug from callers.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-return-on-failure-goto
 * @tags correctness
 *       error-handling
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * The variable used as the function's `ret` (return code). Heuristic: a local
 * `int` variable that is read by a `return` statement in the enclosing function.
 */
predicate isReturnCodeVar(LocalVariable v, Function f) {
  v.getFunction() = f and
  v.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs, VariableAccess va |
    rs.getEnclosingFunction() = f and
    va = rs.getExpr().(VariableAccess) and
    va.getTarget() = v
  )
}

/** Functions that allocate / acquire a resource whose failure must produce errno. */
predicate isAllocCall(FunctionCall fc, string kind) {
  (
    fc.getTarget().hasName("kmalloc") or
    fc.getTarget().hasName("kzalloc") or
    fc.getTarget().hasName("kcalloc") or
    fc.getTarget().hasName("kmalloc_array") or
    fc.getTarget().hasName("kvmalloc") or
    fc.getTarget().hasName("kvzalloc") or
    fc.getTarget().hasName("vmalloc") or
    fc.getTarget().hasName("vzalloc") or
    fc.getTarget().hasName("devm_kmalloc") or
    fc.getTarget().hasName("devm_kzalloc") or
    fc.getTarget().hasName("devm_kcalloc")
  ) and kind = "alloc"
  or
  (
    fc.getTarget().hasName("of_count_phandle_with_args") or
    fc.getTarget().hasName("of_property_count_elems_of_size") or
    fc.getTarget().hasName("of_property_count_strings") or
    fc.getTarget().hasName("of_property_count_u32_elems") or
    fc.getTarget().hasName("of_property_count_u64_elems")
  ) and kind = "of_count"
}

/** A goto statement that targets a cleanup-like label. */
class CleanupGoto extends GotoStmt {
  CleanupGoto() {
    exists(string n | n = this.getName().toLowerCase() |
      n = "end" or n = "out" or n = "err" or n = "fail" or n = "exit" or
      n.matches("out%") or n.matches("err%") or n.matches("fail%") or
      n.matches("cleanup%") or n.matches("free%") or n.matches("unlock%")
    )
  }
}

/**
 * Block (compound or single stmt) is the "failure branch" of an if checking the
 * alloc/count result, containing a cleanup goto but no assignment to `retVar`.
 */
predicate failureBranchMissingRet(IfStmt ifs, FunctionCall alloc, LocalVariable retVar,
                                  CleanupGoto cg, Function f) {
  ifs.getEnclosingFunction() = f and
  alloc.getEnclosingFunction() = f and
  isAllocCall(alloc, _) and
  isReturnCodeVar(retVar, f) and
  // the `if` condition references the alloc result (directly or via the var it was stored in)
  (
    ifs.getCondition().getAChild*() = alloc
    or
    exists(LocalVariable res, VariableAccess defva, VariableAccess useva |
      defva.getTarget() = res and
      defva.getParent().(AssignExpr).getRValue() = alloc and
      useva.getTarget() = res and
      ifs.getCondition().getAChild*() = useva and
      // defining assignment dominates the if
      defva.getLocation().getStartLine() < ifs.getLocation().getStartLine()
    )
  ) and
  // The failure branch (then-branch in `if (!ptr)` / `if (count <= 0)` style) contains the goto
  cg.getParent+() = ifs.getThen() and
  // ... but no assignment to retVar in that branch before the goto
  not exists(AssignExpr ae |
    ae.getEnclosingFunction() = f and
    ae.getLValue().(VariableAccess).getTarget() = retVar and
    ae.getParent+() = ifs.getThen() and
    ae.getLocation().getStartLine() <= cg.getLocation().getStartLine()
  ) and
  // The cleanup label target does NOT itself assign retVar to an error value before return
  not exists(AssignExpr ae2, LabelStmt lbl |
    lbl.getName() = cg.getName() and
    lbl.getEnclosingFunction() = f and
    ae2.getEnclosingFunction() = f and
    ae2.getLValue().(VariableAccess).getTarget() = retVar and
    ae2.getLocation().getStartLine() > lbl.getLocation().getStartLine()
  ) and
  // retVar is declared/initialized to 0 or has a default of 0 (i.e. could be returned as success).
  // We approximate: there exists a path where retVar reaches return without intervening assignment
  // along the failure path. Conservative check: retVar's initializer is 0 or absent.
  (
    not exists(retVar.getInitializer())
    or
    retVar.getInitializer().getExpr().getValue() = "0"
  )
}

from IfStmt ifs, FunctionCall alloc, LocalVariable retVar, CleanupGoto cg, Function f
where failureBranchMissingRet(ifs, alloc, retVar, cg, f)
select ifs, "Failure branch of '" + alloc.getTarget().getName() +
  "' jumps to cleanup label '" + cg.getName() +
  "' without assigning an error code to return variable '" + retVar.getName() +
  "'; function may return 0 on failure."
