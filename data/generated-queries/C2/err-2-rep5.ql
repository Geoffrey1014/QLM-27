/**
 * @name  rq3-c2-err-2-rep5
 * @id    cpp/rq3/c2/err-2-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Detect a goto to an error/cleanup label inside a failure check
 *   where the function's return variable is not assigned a negative errno
 *   constant before the goto. Compositional + POC-OFF generation for RQ3 cell C2.
 */

import cpp

predicate isErrorLabel(LabelStmt l) {
  exists(string n | n = l.getName().toLowerCase() |
    n = "end" or n = "out" or n = "err" or n = "fail" or n = "exit" or n = "cleanup" or
    n.matches("out%") or n.matches("err%") or n.matches("fail%") or n.matches("free%") or
    n.matches("undo%") or n.matches("release%") or n.matches("unlock%") or n.matches("put%")
  )
}

predicate gotoToErrorLabel(GotoStmt g, LabelStmt l) {
  g.getTarget() = l and isErrorLabel(l)
}

predicate isErrnoConstant(Expr e) {
  exists(UnaryMinusExpr um, MacroInvocation mi |
    um = e and
    mi.getExpr() = um.getOperand() and
    mi.getMacroName().regexpMatch("E[A-Z0-9]+")
  )
  or
  e.getValue().toInt() < 0 and e.getValue().toInt() >= -4096
}

predicate failureCheckGuardsGoto(IfStmt ifs, GotoStmt g) {
  gotoToErrorLabel(g, _) and
  (ifs.getThen() = g or g.getParent*() = ifs.getThen())
}

predicate retVarSetToErrnoInThenBranch(LocalVariable ret, IfStmt ifs) {
  exists(AssignExpr ae |
    ae.getEnclosingStmt().getParent*() = ifs.getThen() and
    ae.getLValue().(VariableAccess).getTarget() = ret and
    isErrnoConstant(ae.getRValue())
  )
}

predicate missingErrorCode(IfStmt ifs, GotoStmt g, Function f) {
  failureCheckGuardsGoto(ifs, g) and
  g.getEnclosingFunction() = f and
  // function returns an int (typical errno-returning kernel function)
  f.getType().getUnspecifiedType() instanceof IntType and
  // there exists a candidate local "ret"-like variable in f
  exists(LocalVariable ret |
    ret.getFunction() = f and
    ret.getType().getUnspecifiedType() instanceof IntType and
    (ret.getName() = "ret" or ret.getName() = "err" or ret.getName() = "rc" or ret.getName() = "error") and
    // ret is returned by f somewhere
    exists(ReturnStmt rs |
      rs.getEnclosingFunction() = f and
      rs.getExpr().(VariableAccess).getTarget() = ret
    ) and
    // no errno assignment to ret inside this if-then branch before the goto
    not retVarSetToErrnoInThenBranch(ret, ifs)
  )
}

from IfStmt ifs, GotoStmt g, Function f
where missingErrorCode(ifs, g, f)
select g,
  "Goto to error label '" + g.getTarget().(LabelStmt).getName() +
  "' in function '" + f.getName() +
  "' without assigning a negative errno to the return variable."
