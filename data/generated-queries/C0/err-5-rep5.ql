/**
 * @name Missing error code on allocation-failure path
 * @description An allocation function (vzalloc/vmalloc/kmalloc/kzalloc/kcalloc/...)
 *              returns NULL and the failure branch jumps to a cleanup/return label
 *              without first assigning a negative error code to the function's
 *              return-status variable. The enclosing function then returns 0
 *              (success) despite the allocation having failed.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-errno-on-alloc-failure
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/** An allocator that returns NULL on failure. */
class AllocCall extends FunctionCall {
  AllocCall() {
    this.getTarget().getName() in [
      "vzalloc", "vmalloc", "vmalloc_user", "vzalloc_node", "vmalloc_node",
      "kmalloc", "kzalloc", "kcalloc", "kmalloc_array", "krealloc",
      "kmalloc_node", "kzalloc_node", "kmem_cache_alloc", "kmem_cache_zalloc",
      "kstrdup", "kstrndup", "kmemdup",
      "alloc_pages", "__get_free_page", "__get_free_pages",
      "devm_kmalloc", "devm_kzalloc", "devm_kcalloc",
      "dma_alloc_coherent"
    ]
  }
}

/** A goto statement (typical error-handling jump in the kernel). */
class GotoErrorJump extends GotoStmt { }

/**
 * Holds if `v` is assigned a value at statement `s`.
 */
predicate assignsVar(Stmt s, Variable v) {
  exists(AssignExpr ae | ae.getEnclosingStmt() = s and ae.getLValue() = v.getAnAccess())
  or
  exists(DeclStmt ds, Initializer init |
    ds = s and init.getDeclaration() = v and exists(init.getExpr())
  )
}

/**
 * Holds if statement `s` (or any sub-statement) assigns to variable `v`.
 */
predicate stmtAssigns(Stmt s, Variable v) {
  assignsVar(s, v)
  or
  exists(Stmt child | child.getParentStmt*() = s and assignsVar(child, v))
}

/**
 * The local "return status" variable of function `f`: a local int-typed variable
 * that is the operand of a ReturnStmt somewhere in `f`.
 */
predicate retStatusVar(Function f, LocalVariable v) {
  v.getFunction() = f and
  v.getType().getUnspecifiedType() instanceof IntegralType and
  exists(ReturnStmt rs | rs.getEnclosingFunction() = f |
    rs.getExpr() = v.getAnAccess()
  )
}

/**
 * Holds if `if (!alloc)` (or `if (alloc == NULL)`) guards the branch
 * containing `g`, where `alloc` is the result of `ac`.
 */
predicate nullCheckGuardsGoto(AllocCall ac, IfStmt ifs, GotoStmt g) {
  ifs.getThen() = g.getParent*() and
  exists(Expr cond | cond = ifs.getCondition().getFullyConverted().getUnconverted() |
    // !x or x == 0 / x == NULL where x flows from ac
    exists(Variable v |
      ac.getParent*() = v.getInitializer().getExpr() or
      exists(AssignExpr a | a.getLValue() = v.getAnAccess() and a.getRValue() = ac)
    |
      cond.(NotExpr).getOperand() = v.getAnAccess()
      or
      exists(EQExpr eq | eq = cond and
        eq.getAnOperand() = v.getAnAccess() and
        eq.getAnOperand().getValue() = "0"
      )
    )
  )
}

/**
 * Holds if the `then` block of `ifs` jumps via goto `g` to label `lbl`,
 * and the block does NOT assign to status variable `v` before the goto.
 */
predicate gotoMissesAssign(IfStmt ifs, GotoStmt g, Variable v) {
  g.getEnclosingFunction() = ifs.getEnclosingFunction() and
  g.getParent*() = ifs.getThen() and
  not stmtAssigns(ifs.getThen(), v)
}

from
  Function f, AllocCall ac, IfStmt ifs, GotoStmt g, LocalVariable retv
where
  ac.getEnclosingFunction() = f and
  ifs.getEnclosingFunction() = f and
  g.getEnclosingFunction() = f and
  retStatusVar(f, retv) and
  nullCheckGuardsGoto(ac, ifs, g) and
  gotoMissesAssign(ifs, g, retv) and
  // The allocation result is NOT itself the return variable
  not exists(AssignExpr a | a.getLValue() = retv.getAnAccess() and a.getRValue() = ac) and
  // There exists at least one OTHER null-check elsewhere in `f` that DOES set retv
  // (heuristic: function uses retv as its error code on other failure paths)
  exists(IfStmt other, GotoStmt og |
    other != ifs and
    other.getEnclosingFunction() = f and
    og.getParent*() = other.getThen() and
    stmtAssigns(other.getThen(), retv)
  )
select ac,
  "Allocation failure path jumps to '" + g.getName() +
    "' in function $@ without assigning error code to return variable '" +
    retv.getName() + "'.",
  f, f.getName()
