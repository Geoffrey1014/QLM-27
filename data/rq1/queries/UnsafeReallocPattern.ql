/**
 * @name Unsafe realloc pattern causing potential memory leak
 * @description Detects cases where ptr = realloc(ptr, size) directly overwrites
 *              the original pointer. If realloc fails and returns NULL, the
 *              original memory becomes unreachable, causing a memory leak.
 *              Pattern from Linux commit c42458fcf54b3d0bc2ac06667c98dceb43831889.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/unsafe-realloc-pattern
 * @tags reliability
 *       security
 *       external/cwe/cwe-401
 */

import cpp

/**
 * A call to realloc-like functions that may return NULL on failure
 * without freeing the original buffer.
 */
class ReallocCall extends FunctionCall {
  ReallocCall() {
    this.getTarget().hasName([
      "realloc",
      "reallocarray",
      "krealloc",
      "kvrealloc",
      "devm_krealloc",
      "__krealloc",
      "krealloc_noprof",
      "kvrealloc_noprof"
    ])
  }

  /** Gets the pointer argument being reallocated (first argument). */
  Expr getPointerArg() {
    result = this.getArgument(0)
  }
}

/**
 * Holds if the function terminates the program on failure (exit-on-failure pattern).
 * Functions like xrealloc, xmalloc that call exit/abort on NULL are safe
 * because the program terminates and OS reclaims memory.
 */
predicate isExitOnFailureFunction(Function f) {
  // Function name starts with 'x' (common convention for exit-on-failure wrappers)
  f.getName().matches("x%alloc%")
  or
  f.getName().matches("x%realloc%")
  or
  // Function contains a call to exit/abort after checking NULL
  exists(FunctionCall exitCall |
    exitCall.getEnclosingFunction() = f and
    exitCall.getTarget().hasName(["exit", "_exit", "_Exit", "abort", "panic", "BUG"])
  )
}

/**
 * Holds if the variable `v` is a local copy of another pointer value.
 * This detects the safe pattern where:
 *   const char **array = *vals;  // local copy via initializer
 *   array = *vals;               // or via assignment
 *   array = realloc(array, size);  // realloc on local
 *   if (array) *vals = array;      // only update original on success
 *
 * In this case, the original pointer (*vals) is preserved if realloc fails.
 */
predicate isLocalCopyOfPointer(LocalVariable localVar, Function f) {
  localVar.getFunction() = f and
  (
    // Case 1: Initialized from another pointer via declaration initializer
    // e.g., const char **array = *vals;
    exists(Expr initExpr |
      initExpr = localVar.getInitializer().getExpr() and
      (
        initExpr instanceof PointerDereferenceExpr
        or
        initExpr.(VariableAccess).getTarget() instanceof Parameter
        or
        initExpr.(VariableAccess).getTarget() != localVar
      )
    )
    or
    // Case 2: Assigned from another pointer via assignment
    // e.g., array = *vals;
    exists(AssignExpr initAssign, Expr source |
      initAssign.getLValue().(VariableAccess).getTarget() = localVar and
      initAssign.getRValue() = source and
      (
        source instanceof PointerDereferenceExpr
        or
        source.(VariableAccess).getTarget() instanceof Parameter
        or
        source.(VariableAccess).getTarget() != localVar
      )
    )
  )
}

/**
 * Holds if `assign` is an assignment where a realloc call result is
 * assigned directly back to the same variable that was passed as
 * the first argument to realloc.
 *
 * Pattern: ptr = realloc(ptr, size)
 */
predicate isUnsafeReallocAssignment(AssignExpr assign, ReallocCall reallocCall, Variable v) {
  // The RHS is a realloc call
  assign.getRValue() = reallocCall and
  // The LHS is a variable access
  assign.getLValue().(VariableAccess).getTarget() = v and
  // The first argument to realloc is the same variable
  reallocCall.getPointerArg().(VariableAccess).getTarget() = v
}

// Main query: Find unsafe realloc patterns where the original pointer
// would be lost if realloc fails.
from ReallocCall reallocCall, AssignExpr assign, Variable v, Function f
where
  f = reallocCall.getEnclosingFunction() and
  isUnsafeReallocAssignment(assign, reallocCall, v) and
  // Exclude cases where realloc's first argument is NULL (initial allocation)
  not reallocCall.getPointerArg() instanceof NullValue and
  not reallocCall.getPointerArg().(Literal).getValue() = "0" and
  // Exclude exit-on-failure wrapper functions (xrealloc, etc.)
  // These functions terminate the program on failure, so the leak is irrelevant
  not isExitOnFailureFunction(f) and
  // Exclude cases where the variable is a local copy of another pointer
  // In this pattern, the original pointer is preserved if realloc fails:
  //   array = *vals;
  //   array = realloc(array, size);
  //   if (array) *vals = array;  // original preserved on failure
  not (v instanceof LocalVariable and isLocalCopyOfPointer(v, f))
select reallocCall,
  "Potential memory leak: " + reallocCall.getTarget().getName() + "() result is assigned " +
  "directly to '" + v.getName() + "' which was passed as the first argument. " +
  "If " + reallocCall.getTarget().getName() + "() fails and returns NULL, the original " +
  "memory is leaked. Use a temporary variable instead in function '" + f.getName() + "'."
