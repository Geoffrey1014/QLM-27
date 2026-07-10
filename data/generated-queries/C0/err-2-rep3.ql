/**
 * @name Missing error return code on failure path
 * @description A function that returns an error code through a local variable
 *              (e.g. `ret`) jumps to a cleanup/return label on a failure
 *              branch without assigning a negative errno to that variable.
 *              The function therefore silently returns the previously
 *              initialized (often 0/success) value to its caller despite the
 *              failure.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-return-code
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph
import semmle.code.cpp.controlflow.Guards

/**
 * A local variable used as the "ret" / error-code return value of its
 * enclosing function: it is `int`, it is read by at least one `return`
 * statement of the function, and it has an initializer or an early
 * assignment giving it 0 (success).
 */
class RetVar extends LocalVariable {
  Function f;

  RetVar() {
    this.getFunction() = f and
    this.getType().getUnspecifiedType() instanceof IntType and
    // Used in a return statement of the enclosing function.
    exists(ReturnStmt r |
      r.getEnclosingFunction() = f and
      this.getAnAccess() = r.getExpr().getAChild*()
    ) and
    // Initialised (or assigned) to 0 somewhere — the "success" sentinel.
    (
      this.getInitializer().getExpr().getValue() = "0"
      or
      exists(AssignExpr a |
        a.getLValue() = this.getAnAccess() and
        a.getRValue().getValue() = "0" and
        a.getEnclosingFunction() = f
      )
    )
  }

  Function getEnclosingFn() { result = f }
}

/**
 * A `goto` statement targeting a label whose body eventually flows into a
 * `return retvar;` of the same function (i.e. a cleanup-then-return label).
 */
predicate gotoToReturnLabel(GotoStmt g, RetVar ret) {
  g.getEnclosingFunction() = ret.getEnclosingFn() and
  exists(ReturnStmt r |
    r.getEnclosingFunction() = ret.getEnclosingFn() and
    r.getExpr() = ret.getAnAccess() and
    // The goto's target label is a predecessor (in the CFG) of this return.
    g.getTarget().getASuccessor*() = r
  )
}

/**
 * Holds if the basic block / statement chain that begins with `g` (a goto
 * to a return label) assigns to `ret` before the goto fires.
 *
 * We approximate: walk up the enclosing `if` body containing the goto
 * and check whether any assignment to `ret` appears in that branch
 * before the goto.
 */
predicate retAssignedInBranchBefore(GotoStmt g, RetVar ret) {
  exists(AssignExpr a, Stmt enclosingIfBranch |
    a.getLValue() = ret.getAnAccess() and
    a.getEnclosingFunction() = ret.getEnclosingFn() and
    // The assignment is in the same lexical "then" branch as the goto.
    enclosingIfBranch = g.getParentStmt+() and
    a.getEnclosingStmt().getParentStmt*() = enclosingIfBranch and
    // And it dominates the goto in the CFG.
    a.getASuccessor*() = g
  )
}

/**
 * Holds if `g` is inside the "then" branch of an `if` statement whose
 * condition tests for failure of a resource-acquisition / counting call
 * (e.g. `if (!p) goto err;`, `if (!count) goto end;`, `if (ret < 0) goto`).
 */
predicate gotoOnFailureBranch(GotoStmt g) {
  exists(IfStmt ifs |
    g.getParentStmt+() = ifs.getThen() and
    (
      // !x   /   x == NULL   /   x == 0
      ifs.getCondition() instanceof NotExpr
      or
      exists(EQExpr eq | eq = ifs.getCondition().getAChild*() |
        eq.getAnOperand().getValue() = "0"
      )
      or
      // x < 0   /   x <= 0
      exists(RelationalOperation rel | rel = ifs.getCondition().getAChild*() |
        rel.getAnOperand().getValue() = "0"
      )
    )
  )
}

from Function f, GotoStmt g, RetVar ret, ReturnStmt r
where
  f = ret.getEnclosingFn() and
  g.getEnclosingFunction() = f and
  gotoToReturnLabel(g, ret) and
  gotoOnFailureBranch(g) and
  // The same `ret` variable is what is returned.
  r.getEnclosingFunction() = f and
  r.getExpr() = ret.getAnAccess() and
  // No assignment to `ret` in this failure branch before the goto.
  not retAssignedInBranchBefore(g, ret) and
  // The function must have at least one OTHER path where it does assign a
  // non-zero error code to `ret` — i.e. the "ret" idiom is used in this fn.
  exists(AssignExpr a2 |
    a2.getEnclosingFunction() = f and
    a2.getLValue() = ret.getAnAccess() and
    not a2.getRValue().getValue() = "0"
  )
select g,
  "Goto to cleanup/return label on a failure branch leaves '" + ret.getName() +
    "' unset, so the function may silently return success."
