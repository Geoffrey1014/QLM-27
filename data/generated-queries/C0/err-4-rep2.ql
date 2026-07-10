/**
 * @name Missing error code assignment before goto on allocation failure
 * @description When an allocation/acquisition function returns NULL and the code
 *              jumps to an error/cleanup label, the function's error-status
 *              variable should be set to a negative errno (e.g. -ENOMEM).
 *              Otherwise the enclosing function may return a stale value
 *              (often 0 = success) and the caller never learns about the failure.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-code-on-alloc-failure
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A function call that is treated by kernel code as "returns NULL on failure"
 * — i.e. allocators / object-constructors whose name encodes "alloc" / "create"
 * / "new" / "get" / "kzalloc"-style and which return a pointer.
 */
predicate isAllocLikeCall(FunctionCall fc) {
  fc.getType().getUnspecifiedType() instanceof PointerType and
  exists(string n | n = fc.getTarget().getName() |
    n.matches("%alloc%") or
    n.matches("%create%") or
    n.matches("kmemdup%") or
    n.matches("kstrdup%") or
    n.matches("kasprintf%") or
    n.matches("kvasprintf%") or
    n.matches("%_new") or
    n = "of_get_child_by_name" or
    n.matches("of_find_%") or
    n.matches("of_parse_phandle%")
  )
}

/**
 * The local variable (or parameter) that the enclosing function uses to carry
 * its int error-status to the final `return status;`.
 */
predicate isStatusLikeVar(Variable v, Function f) {
  v.getType().getUnspecifiedType().(IntegralType).getSize() <= 8 and
  v.(LocalScopeVariable).getFunction() = f and
  exists(string n | n = v.getName() |
    n = "status" or
    n = "ret" or
    n = "rc" or
    n = "err" or
    n = "error" or
    n = "result"
  ) and
  // The function actually returns this variable somewhere.
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = v
  )
}

/**
 * An `if (!ptr) goto LABEL;` style check on the result of an alloc-like call,
 * where the THEN branch (or the if-statement body) goes straight to a goto
 * with no assignment to the status variable in between.
 */
predicate badNullCheckGoto(
  IfStmt ifs, FunctionCall alloc, GotoStmt gs, Variable status, Function f
) {
  f = ifs.getEnclosingFunction() and
  isStatusLikeVar(status, f) and
  isAllocLikeCall(alloc) and
  alloc.getEnclosingFunction() = f and
  // The condition tests the alloc-target for NULL: !p / p == NULL / NULL == p
  exists(Expr cond, VariableAccess va |
    cond = ifs.getCondition() and
    (
      cond.(NotExpr).getOperand() = va
      or
      cond.(EqualityOperation).getAnOperand() = va and
      cond.(EqualityOperation).getAnOperand().getValue() = "0"
    ) and
    // That same variable was assigned the alloc result.
    exists(AssignExpr ae |
      ae.getLValue().(VariableAccess).getTarget() = va.getTarget() and
      ae.getRValue() = alloc
    )
    or
    // Or the alloc result was assigned at declaration.
    exists(Variable p |
      p = va.getTarget() and
      p.getInitializer().getExpr() = alloc
    )
  ) and
  // The then-branch contains a goto (directly or as its only meaningful stmt).
  gs.getEnclosingStmt*() = ifs.getThen() and
  // No assignment to `status` between the alloc call and the goto.
  not exists(AssignExpr setStatus |
    setStatus.getLValue().(VariableAccess).getTarget() = status and
    setStatus.getEnclosingFunction() = f and
    // textually between the alloc call and the goto
    setStatus.getLocation().getStartLine() >= alloc.getLocation().getStartLine() and
    setStatus.getLocation().getStartLine() <= gs.getLocation().getStartLine()
  ) and
  // The goto target is "fail"-ish (cleanup label), not an early "ok" return.
  exists(string lbl | lbl = gs.getName().toLowerCase() |
    lbl.matches("%fail%") or
    lbl.matches("%err%") or
    lbl.matches("%out%") or
    lbl.matches("%free%") or
    lbl.matches("%cleanup%") or
    lbl.matches("%undo%") or
    lbl.matches("%abort%") or
    lbl.matches("%release%")
  )
}

from IfStmt ifs, FunctionCall alloc, GotoStmt gs, Variable status, Function f
where badNullCheckGoto(ifs, alloc, gs, status, f)
select ifs,
  "Allocation '" + alloc.getTarget().getName() +
    "' returned NULL: code jumps to '" + gs.getName() +
    "' without assigning an error code to '" + status.getName() +
    "', so " + f.getName() + "() may return success on failure."
