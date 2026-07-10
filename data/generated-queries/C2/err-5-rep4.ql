/**
 * @name rq3-c2-err-5-rep4
 * @id   cpp/rq3/c2/err-5-rep4
 * @kind problem
 * @problem.severity warning
 * @description Detects missing error-code assignment on allocator NULL-check
 *              failure branches that goto a cleanup label. Compositional +
 *              POC-OFF generation for RQ3 cell C2.
 */
import cpp

/** Function calls to common kernel allocator APIs that may return NULL. */
predicate is_alloc_call(FunctionCall fc) {
  fc.getTarget().getName() in [
    "vzalloc", "vmalloc", "kmalloc", "kzalloc", "kcalloc",
    "kmalloc_array", "kvzalloc", "kvmalloc", "kmemdup",
    "kstrdup", "kstrndup", "krealloc", "kmalloc_node",
    "kzalloc_node", "vmalloc_node", "alloc_pages"
  ]
}

/** `v = alloc(...)` style assignment where `fc` is an allocator call. */
predicate assigns_alloc_to_var(AssignExpr ae, Variable v, FunctionCall fc) {
  is_alloc_call(fc) and
  ae.getRValue() = fc and
  ae.getLValue() = v.getAnAccess()
}

/** Like above, but for declarators: `T *v = alloc(...);` */
predicate decl_init_alloc(LocalVariable v, FunctionCall fc) {
  is_alloc_call(fc) and
  v.getInitializer().getExpr() = fc
}

/** `v` was assigned an allocator result earlier in the same function. */
predicate var_holds_alloc(Variable v, Function f) {
  exists(AssignExpr ae, FunctionCall fc |
    assigns_alloc_to_var(ae, v, fc) and ae.getEnclosingFunction() = f
  )
  or
  exists(LocalVariable lv, FunctionCall fc |
    lv = v and decl_init_alloc(lv, fc) and fc.getEnclosingFunction() = f
  )
}

/** `if (!v) goto label;` (or `if (v == NULL) goto label;`) — the then-branch
 *  is a (possibly braced) goto with no other side-effects we care about. */
predicate null_check_goto(IfStmt is, Variable v, GotoStmt gs) {
  // condition tests v for NULL
  (
    is.getCondition().(NotExpr).getOperand() = v.getAnAccess()
    or
    exists(EQExpr eq | eq = is.getCondition() |
      eq.getAnOperand() = v.getAnAccess() and
      eq.getAnOperand().(Literal).getValue() = "0"
    )
  ) and
  // then-branch ultimately performs a goto
  gs.getParentStmt*() = is.getThen()
}

/** The then-branch of `is` contains an assignment of a negative integer
 *  literal to `ret` somewhere before the goto. */
predicate then_sets_neg_errno(IfStmt is, Variable ret) {
  exists(AssignExpr ae |
    ae.getEnclosingStmt().getParentStmt*() = is.getThen() and
    ae.getLValue() = ret.getAnAccess() and
    (
      ae.getRValue().(UnaryMinusExpr).getOperand() instanceof Literal
      or
      exists(Literal l | l = ae.getRValue() and l.getValue().toInt() < 0)
      or
      // covers `ret = -ENOMEM` after macro expansion to a negative int constant
      ae.getRValue().getValue().toInt() < 0
    )
  )
}

/** `ret` is an int-typed local variable in `f` that flows to a return. */
predicate is_return_code_var(LocalVariable ret, Function f) {
  ret.getFunction() = f and
  ret.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr() = ret.getAnAccess()
  )
}

/** Composite: an allocator null-check branch that gotos cleanup without
 *  setting `ret` to a negative errno first. */
predicate buggy_null_check(
  IfStmt is, Variable v, GotoStmt gs, LocalVariable ret, Function f
) {
  is.getEnclosingFunction() = f and
  var_holds_alloc(v, f) and
  null_check_goto(is, v, gs) and
  is_return_code_var(ret, f) and
  not then_sets_neg_errno(is, ret)
}

from IfStmt is, Variable v, GotoStmt gs, LocalVariable ret, Function f
where buggy_null_check(is, v, gs, ret, f)
select is,
  "Allocator NULL-check on '$@' gotos '" + gs.getName() +
  "' without assigning a negative errno to return-code variable '$@' in function $@.",
  v, v.getName(),
  ret, ret.getName(),
  f, f.getName()
