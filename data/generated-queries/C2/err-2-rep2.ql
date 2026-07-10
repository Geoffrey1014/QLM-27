/**
 * @name  rq3-c2-err-2-rep2
 * @id    cpp/rq3/c2/err-2-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects functions that goto a cleanup label without setting
 *              an error code in the local return variable, causing the
 *              function to return 0 (success) on an error path.
 */

import cpp

predicate is_error_return_function(Function f) {
  f.getType().getUnspecifiedType() instanceof IntType and
  exists(GotoStmt g | g.getEnclosingFunction() = f)
}

predicate cleanup_label_returns_ret(Function f, LocalVariable ret) {
  ret.getFunction() = f and
  ret.getType().getUnspecifiedType() instanceof IntType and
  exists(LabelStmt lbl, ReturnStmt rs |
    lbl.getEnclosingFunction() = f and
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = ret and
    exists(GotoStmt g | g.getTarget() = lbl)
  )
}

predicate error_check_branch(IfStmt ifstmt, Function f) {
  ifstmt.getEnclosingFunction() = f and
  (
    // !ptr style
    exists(NotExpr ne | ne = ifstmt.getCondition() and
                       ne.getOperand() instanceof VariableAccess)
    or
    // ptr == NULL
    exists(EQExpr eq | eq = ifstmt.getCondition())
    or
    // count <= 0  or  count < 0
    exists(RelationalOperation rel | rel = ifstmt.getCondition())
  )
}

predicate branch_gotos_cleanup(IfStmt ifstmt, GotoStmt gs) {
  gs.getParentStmt*() = ifstmt.getThen() and
  exists(LabelStmt lbl, ReturnStmt rs, Function f |
    gs.getEnclosingFunction() = f and
    lbl.getEnclosingFunction() = f and
    rs.getEnclosingFunction() = f and
    gs.getTarget() = lbl and
    // there is some return-ret reachable; we just require any return after lbl
    exists(ReturnStmt r | r.getEnclosingFunction() = f and r.getExpr() instanceof VariableAccess)
  )
}

predicate branch_does_not_set_ret(IfStmt ifstmt, LocalVariable ret) {
  not exists(AssignExpr ae |
    ae.getEnclosingStmt().getParentStmt*() = ifstmt.getThen() and
    ae.getLValue().(VariableAccess).getTarget() = ret
  )
}

from IfStmt ifstmt, Function f, LocalVariable ret, GotoStmt gs
where
  is_error_return_function(f) and
  cleanup_label_returns_ret(f, ret) and
  ifstmt.getEnclosingFunction() = f and
  error_check_branch(ifstmt, f) and
  branch_gotos_cleanup(ifstmt, gs) and
  branch_does_not_set_ret(ifstmt, ret)
select ifstmt,
  "Error-check branch gotos cleanup label without setting return variable '" +
  ret.getName() + "', so function returns success (0) on failure path."
