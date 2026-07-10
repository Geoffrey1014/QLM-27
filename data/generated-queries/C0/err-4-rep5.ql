/**
 * @name Missing error code assignment before goto cleanup on allocation failure
 * @description Detects patterns where an allocation/acquire function returns NULL
 *              (or a failure indicator), the failure branch jumps to a cleanup
 *              label, but no negative error code is assigned to the return-status
 *              variable. The caller therefore returns 0 (success) even though
 *              the operation failed. Models the multi_bind() fix pattern in
 *              drivers/usb/gadget/legacy/multi.c.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-code-before-goto
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph
import semmle.code.cpp.controlflow.Guards

/**
 * Functions whose return value is commonly checked for NULL to indicate
 * allocation/acquire failure (kernel pointer-returning APIs).
 */
predicate isAllocatingFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%alloc%") or
    n.matches("%_create%") or
    n.matches("%_get%") or
    n.matches("%_acquire%") or
    n.matches("%_init") or
    n = "kmalloc" or
    n = "kzalloc" or
    n = "kcalloc" or
    n = "vmalloc" or
    n = "vzalloc" or
    n = "devm_kzalloc" or
    n = "devm_kmalloc" or
    n = "of_find_node_by_name" or
    n = "of_parse_phandle"
  ) and
  f.getType().getUnspecifiedType() instanceof PointerType
}

/** A status/return variable: a local int that is also used as the return value. */
predicate isStatusVariable(LocalVariable v, Function enclosing) {
  v.getFunction() = enclosing and
  v.getType().getUnspecifiedType() instanceof IntegralType and
  exists(ReturnStmt ret, VariableAccess va |
    ret.getEnclosingFunction() = enclosing and
    va = ret.getExpr().(VariableAccess) and
    va.getTarget() = v
  )
}

/**
 * A NULL-check on the result of an allocating call that controls a `goto`
 * to a cleanup label without assigning an error code to the status variable.
 */
predicate missingErrorCodeBeforeGoto(
  FunctionCall alloc, IfStmt ifs, GotoStmt g, LocalVariable status, Function enclosing
) {
  enclosing = alloc.getEnclosingFunction() and
  isAllocatingFunction(alloc.getTarget()) and
  isStatusVariable(status, enclosing) and
  // The if-statement guards on the allocation result being NULL/falsy.
  ifs.getEnclosingFunction() = enclosing and
  exists(Expr cond | cond = ifs.getCondition() |
    // simple `!ptr` form
    cond.(NotExpr).getOperand().(VariableAccess).getTarget() =
      alloc.getParent().(AssignExpr).getLValue().(VariableAccess).getTarget()
    or
    // `ptr == NULL`
    exists(EQExpr eq | eq = cond |
      eq.getAnOperand().(VariableAccess).getTarget() =
        alloc.getParent().(AssignExpr).getLValue().(VariableAccess).getTarget() and
      eq.getAnOperand() instanceof Literal
    )
  ) and
  // The goto is inside the then-branch of the if.
  g.getParentStmt*() = ifs.getThen() and
  // No assignment to `status` happens between the if and the goto inside the
  // then-branch.
  not exists(AssignExpr a |
    a.getEnclosingFunction() = enclosing and
    a.getLValue().(VariableAccess).getTarget() = status and
    a.getParent+() = ifs.getThen()
  ) and
  // status has been set to 0 (or a non-negative) at the entry of the branch
  // — i.e., the implicit value at this point is success. We approximate this
  // by checking that there exists at least one assignment of a literal 0 to
  // status earlier in the function (typical `int status = 0;`).
  exists(AssignExpr init |
    init.getEnclosingFunction() = enclosing and
    init.getLValue().(VariableAccess).getTarget() = status and
    init.getRValue().getValue().toInt() = 0
  )
  or
  // Or status is declared without an initializer that is negative — accept
  // declarations that initialize to 0 OR are uninitialized.
  exists(DeclStmt ds, Variable decl |
    ds.getDeclaration(0) = decl and
    decl = status and
    (
      not exists(status.getInitializer())
      or
      status.getInitializer().getExpr().getValue().toInt() = 0
    )
  )
}

from FunctionCall alloc, IfStmt ifs, GotoStmt g, LocalVariable status, Function f
where missingErrorCodeBeforeGoto(alloc, ifs, g, status, f)
select g,
  "Missing error code assignment to '" + status.getName() +
    "' before 'goto " + g.getName() + "' on failure of '" +
    alloc.getTarget().getName() + "' in function '" + f.getName() + "'."
