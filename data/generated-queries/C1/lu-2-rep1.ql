/**
 * @name Missing kfree on early-return path after kmalloc
 * @description A function allocates a buffer with kmalloc (or another
 *              kmalloc-family allocator), stores the pointer in a local
 *              variable, and establishes a cleanup epilogue that calls
 *              kfree() on that variable. If the function also contains
 *              a `return` statement that lexically appears after the
 *              allocation but before the kfree epilogue, and that
 *              return is not itself a `goto` into the cleanup label,
 *              then this exit path bypasses the cleanup and the
 *              allocated buffer leaks (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-2
 */

import cpp

/** Names of kmalloc-family heap allocators whose return value the
 *  caller owns and must release via kfree-family functions. */
predicate isHeapAcquireApi(string name) {
  name = "kmalloc" or
  name = "kzalloc" or
  name = "kcalloc" or
  name = "kmalloc_array" or
  name = "kvmalloc" or
  name = "kvzalloc" or
  name = "kvcalloc" or
  name = "krealloc" or
  name = "kmemdup" or
  name = "kstrdup" or
  name = "kstrndup"
}

/** True if `c` is a kfree-family release call. */
predicate isHeapReleaseCall(FunctionCall c) {
  c.getTarget().getName() = "kfree" or
  c.getTarget().getName() = "kvfree" or
  c.getTarget().getName() = "kfree_sensitive"
}

/** The variable that captures the value of `call`, via initializer
 *  (`T *v = call(...)`) or assignment (`v = call(...)`). */
Variable acquiredInto(FunctionCall call) {
  exists(Variable v |
    v.getInitializer().getExpr() = call and
    result = v
  )
  or
  exists(AssignExpr a, VariableAccess lhs |
    a.getRValue() = call and
    lhs = a.getLValue() and
    result = lhs.getTarget()
  )
}

/** A kfree-family call inside `f` whose first argument reads `v`. */
FunctionCall releaseOfVar(Function f, Variable v) {
  isHeapReleaseCall(result) and
  result.getEnclosingFunction() = f and
  exists(VariableAccess arg |
    arg = result.getArgument(0) and
    arg.getTarget() = v
  )
}

/** Earliest source line of any release of `v` in `f`. */
int firstReleaseLine(Function f, Variable v) {
  result = min(int ln | ln = releaseOfVar(f, v).getLocation().getStartLine())
}

/** True iff `ret` is the body of a `goto` (i.e. flows into the cleanup
 *  via a jump) -- we approximate by checking whether a `GotoStmt` to
 *  some label appears on the immediately preceding source line. */
predicate returnIsAfterGoto(Function f, ReturnStmt ret) {
  exists(GotoStmt g |
    g.getEnclosingFunction() = f and
    g.getLocation().getEndLine() = ret.getLocation().getStartLine() - 1
  )
}

/** True iff `ret` is a "guard return" that fires when the allocation
 *  itself failed: it is dominated by an `if (!v)` (or `if (v == NULL)`)
 *  check that gates the post-allocation usage. Such returns do not
 *  leak because `v` is NULL at the return point. */
predicate returnGuardsNullAcquisition(ReturnStmt ret, Variable v) {
  exists(IfStmt ifs |
    ret.getParentStmt*() = ifs.getThen() and
    (
      // if (!v)
      exists(NotExpr ne, VariableAccess va |
        ne = ifs.getCondition() and
        va = ne.getOperand() and
        va.getTarget() = v
      )
      or
      // if (v == NULL) or if (NULL == v) or if (v == 0)
      exists(EQExpr eq, VariableAccess va |
        eq = ifs.getCondition() and
        (va = eq.getLeftOperand() or va = eq.getRightOperand()) and
        va.getTarget() = v
      )
    )
  )
}

from FunctionCall acquire, Variable buf, Function f, ReturnStmt badRet, int relLine
where
  isHeapAcquireApi(acquire.getTarget().getName()) and
  buf = acquiredInto(acquire) and
  f = acquire.getEnclosingFunction() and
  badRet.getEnclosingFunction() = f and
  // Function has a kfree(buf) cleanup epilogue.
  relLine = firstReleaseLine(f, buf) and
  // The return appears between the allocation and the cleanup -- it
  // exits before the cleanup runs.
  acquire.getLocation().getStartLine() < badRet.getLocation().getStartLine() and
  badRet.getLocation().getStartLine() < relLine and
  // Exclude returns reached by goto into the cleanup label.
  not returnIsAfterGoto(f, badRet) and
  // Exclude guard returns that fire when the allocation itself failed
  // (e.g. `if (!buf) return -ENOMEM;`); buf is NULL there, no leak.
  not returnGuardsNullAcquisition(badRet, buf)
select badRet,
  "This `return` in '" + f.getName() +
    "' leaks the buffer '" + buf.getName() +
    "' acquired by " + acquire.getTarget().getName() +
    "() at line " + acquire.getLocation().getStartLine() +
    " -- a kfree epilogue exists at line " + relLine +
    " but this exit path bypasses it."
