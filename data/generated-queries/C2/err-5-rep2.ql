/**
 * @name  rq3-c2-err-5-rep2
 * @id    cpp/rq3/c2/err-5-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2 - error-return bug pattern.
 */
import cpp

/** A call to a function that may return NULL on allocation failure. */
predicate is_alloc_call(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "vzalloc" or n = "vmalloc" or n = "kmalloc" or n = "kzalloc" or
    n = "kcalloc" or n = "kmemdup" or n = "kstrdup" or n = "kasprintf" or
    n = "alloc_pages" or n = "alloc_page" or n = "kmalloc_array" or
    n = "krealloc" or n = "devm_kzalloc" or n = "devm_kmalloc"
  )
}

/** The variable v is assigned from an allocation call. */
predicate assigned_from_alloc(Variable v, FunctionCall fc) {
  is_alloc_call(fc) and
  exists(Assignment a |
    a.getRValue() = fc and
    a.getLValue() = v.getAnAccess()
  )
  or
  is_alloc_call(fc) and
  exists(Initializer i |
    i.getExpr() = fc and
    i.getDeclaration() = v
  )
}

/** A goto statement that jumps to a cleanup-style label. */
predicate is_cleanup_goto(GotoStmt g) {
  exists(string lbl | lbl = g.getName() |
    lbl.matches("%out%") or lbl.matches("%err%") or
    lbl.matches("%fail%") or lbl.matches("%free%") or
    lbl.matches("%cleanup%") or lbl.matches("%undo%") or
    lbl.matches("%release%")
  )
}

/** IfStmt that tests v is NULL (or !v) and whose then-branch goto's a cleanup label. */
predicate null_check_then_goto(IfStmt ifs, Variable v, GotoStmt g) {
  is_cleanup_goto(g) and
  g.getParent*() = ifs.getThen() and
  (
    // !v form
    exists(NotExpr ne | ne = ifs.getCondition() and ne.getOperand() = v.getAnAccess())
    or
    // v == NULL  or  v == 0
    exists(EQExpr eq | eq = ifs.getCondition() |
      eq.getAnOperand() = v.getAnAccess() and
      eq.getAnOperand().getValue() = "0"
    )
    or
    // plain `if (v)` else-branch unsupported here; covered above.
    none()
  )
}

/** True if some statement in `block` assigns a (likely negative) integer literal to a local `ret`-like int variable. */
predicate assigns_error_to_ret(Stmt block) {
  exists(Assignment a, Variable ret |
    a.getEnclosingStmt().getParent*() = block and
    a.getLValue() = ret.getAnAccess() and
    ret.getType().getUnderlyingType() instanceof IntType and
    (
      ret.getName() = "ret" or ret.getName() = "err" or
      ret.getName() = "rc"  or ret.getName() = "error" or
      ret.getName() = "status"
    ) and
    (
      // -CONST  (e.g. -ENOMEM expands to a negative literal)
      exists(UnaryMinusExpr um | um = a.getRValue())
      or
      // -ENOMEM macro-expanded to a constant int with negative value
      exists(int v | v = a.getRValue().getValue().toInt() and v < 0)
    )
  )
}

/** Bug: alloc -> NULL-check -> goto cleanup, but no error-code assignment to `ret` happens in the then-branch before the goto. */
predicate missing_error_assignment(IfStmt ifs, Variable v, GotoStmt g, FunctionCall alloc) {
  assigned_from_alloc(v, alloc) and
  null_check_then_goto(ifs, v, g) and
  not assigns_error_to_ret(ifs.getThen())
}

from IfStmt ifs, Variable v, GotoStmt g, FunctionCall alloc
where missing_error_assignment(ifs, v, g, alloc)
select ifs, "Possible missing error-code assignment before goto cleanup after NULL check of allocation result for $@.",
  v, v.getName()
