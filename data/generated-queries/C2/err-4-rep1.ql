/**
 * @name  rq3-c2-err-4-rep1
 * @id    cpp/rq3/c2/err-4-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 */
import cpp

/** Heuristic: a function whose name suggests resource allocation/creation. */
predicate isAllocLike(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%alloc%") or
    n.matches("%_create%") or
    n.matches("kmalloc%") or
    n.matches("kzalloc%") or
    n.matches("%_new")
  ) and
  f.getType().getUnspecifiedType() instanceof PointerType
}

/** A call to an alloc-like function whose result is assigned to a local variable. */
predicate allocCallAssigned(FunctionCall fc, LocalScopeVariable v, Function caller) {
  isAllocLike(fc.getTarget()) and
  caller = fc.getEnclosingFunction() and
  (
    exists(AssignExpr a | a.getRValue() = fc and a.getLValue() = v.getAnAccess())
    or
    exists(Initializer init | init.getExpr() = fc and init.getDeclaration() = v)
  )
}

/** An if-statement that tests `!v` (i.e. v is NULL) after an alloc assignment. */
predicate nullCheckOnAlloc(IfStmt ifs, LocalScopeVariable v, Function caller) {
  exists(FunctionCall fc |
    allocCallAssigned(fc, v, caller) and
    ifs.getEnclosingFunction() = caller and
    exists(NotExpr ne |
      ne = ifs.getCondition() and
      ne.getOperand() = v.getAnAccess()
    )
  )
}

/** The then-branch of `ifs` contains a goto, and no assignment of an error code
 *  to a `status`-typed integer local in `caller` occurs before that goto. */
predicate gotoWithoutStatusSet(IfStmt ifs, GotoStmt g, Function caller) {
  nullCheckOnAlloc(ifs, _, caller) and
  g.getParent*() = ifs.getThen() and
  not exists(AssignExpr ae, LocalScopeVariable s |
    ae.getParent*() = ifs.getThen() and
    ae.getLValue() = s.getAnAccess() and
    s.getType().getUnspecifiedType() instanceof IntegralType and
    s.getName().toLowerCase().matches("%status%") and
    ae.getRValue().getValue().toInt() < 0
  )
}

/** Caller has a local integer variable returned at the end (status pattern). */
predicate callerReturnsStatusVar(Function caller) {
  exists(ReturnStmt rs, LocalScopeVariable s |
    rs.getEnclosingFunction() = caller and
    rs.getExpr() = s.getAnAccess() and
    s.getType().getUnspecifiedType() instanceof IntegralType
  )
}

from IfStmt ifs, GotoStmt g, Function caller
where
  gotoWithoutStatusSet(ifs, g, caller) and
  callerReturnsStatusVar(caller)
select ifs, "Missing error status assignment before goto to cleanup label in " + caller.getName() + "()."
