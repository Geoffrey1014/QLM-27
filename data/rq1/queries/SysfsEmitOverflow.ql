/**
 * @name sysfs show() unbounded concatenation into buf (should use sysfs_emit_at)
 * @description A sysfs `show()` callback (signature `ssize_t f(struct device*,
 *              struct device_attribute*, char *buf)` or the kobject/kobj_attribute
 *              variant) concatenates into `buf` inside a loop with a raw
 *              `sprintf(buf + off, ...)` / `strcat(buf, ...)` and provides NO
 *              `PAGE_SIZE - off` remaining-space cap. The sysfs read() handler hands the
 *              callback a single PAGE_SIZE buffer; an unbounded loop concat can walk off
 *              the page (CWE-787), as in the mlxbf-pmc overflow (80ccd40568bcd). The
 *              preferred fix is `sysfs_emit_at()`, which enforces the bound.
 *
 *              Discriminator (only the dangerous shape, not the ~1978 cleanup mass):
 *                * destination is `buf + <off>` (pointer arithmetic on the sysfs buf
 *                  param) OR `strcat(buf, ...)`, AND
 *                * that write is inside a loop, AND
 *                * the call is a RAW formatter (sprintf/snprintf/scnprintf/strcat) whose
 *                  size argument (if any) is NOT a `PAGE_SIZE - off` remaining-space cap.
 *              Excludes: single bounded write; `sysfs_emit`/`sysfs_emit_at`; capped
 *              `scnprintf(buf+off, PAGE_SIZE-off, ...)`; mutually-exclusive single-write
 *              branches (those are not loop concatenation).
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id cpp/sysfs-emit-overflow
 * @tags security
 *       external/cwe/cwe-787
 *       external/cwe/cwe-120
 */

import cpp

/** Non-shippable build/host tooling and test code. */
predicate excludedFile(File f) {
  f.getRelativePath().regexpMatch("^(scripts|tools|samples)/.*")
  or
  f.getRelativePath().regexpMatch("(?i).*(/test|_test|/kunit|/selftest|/tests/).*")
}

/**
 * A sysfs `show()` callback: returns ssize_t-ish, last parameter is `char *buf`, and at
 * least one parameter is a `struct device_attribute *` or `struct kobj_attribute *`
 * (the registered show()-pointer signature).
 */
class SysfsShowFunction extends Function {
  Parameter bufParam;

  SysfsShowFunction() {
    not excludedFile(this.getFile()) and
    // last param is `char *buf`
    bufParam = this.getParameter(this.getNumberOfParameters() - 1) and
    bufParam.getType().getUnspecifiedType() instanceof PointerType and
    bufParam.getType().getUnspecifiedType().(PointerType).getBaseType().getUnspecifiedType()
        instanceof CharType and
    bufParam.getName() = "buf" and
    // some parameter is device_attribute* / kobj_attribute*
    exists(Parameter p, string tn |
      p = this.getAParameter() and
      tn = p.getType().getUnspecifiedType().(PointerType).getBaseType().getUnspecifiedType().getName()
    |
      tn.regexpMatch("(?i)(device_attribute|kobj_attribute)")
    )
  }

  Parameter getBufParam() { result = bufParam }
}

/** An access to the sysfs show() `buf` parameter. */
predicate isBufAccess(SysfsShowFunction f, Expr e) {
  e = f.getBufParam().getAnAccess()
}

/**
 * A write `buf + <off>`: pointer arithmetic whose base operand is the `buf` parameter
 * (covers `buf + len`, `&buf[len]`, etc.). Returns the destination expression used as the
 * formatter's first argument.
 */
predicate bufOffsetDest(SysfsShowFunction f, Expr dest) {
  exists(PointerArithmeticOperation pa |
    dest = pa and
    isBufAccess(f, pa.getAnOperand())
  )
  or
  // &buf[len]
  exists(AddressOfExpr ao, ArrayExpr ae |
    dest = ao and
    ao.getOperand() = ae and
    isBufAccess(f, ae.getArrayBase())
  )
}

/**
 * Holds if the size argument of a bounded-formatter call is a real remaining-space cap,
 * i.e. it mentions `PAGE_SIZE` (typically `PAGE_SIZE - off`, or `max(PAGE_SIZE - off, 0)`
 * which expands to a `__careful_cmp` statement-expression so the SubExpr is not a direct
 * child). Detect it by looking for a `PAGE_SIZE` macro reference whose expansion overlaps
 * the size-argument location, plus the plain direct-subtraction form.
 */
predicate isPageSizeCap(Expr sizeArg) {
  // direct `PAGE_SIZE - off` (and similar) as a child of the size arg
  exists(SubExpr se | se = sizeArg.getAChild*())
  or
  // the size arg (or its statement-expression expansion, e.g. max()/min() macro) mentions
  // a PAGE_SIZE macro invocation at the same source line.
  exists(MacroInvocation mi |
    mi.getMacroName() = "PAGE_SIZE" and
    mi.getLocation().getFile() = sizeArg.getLocation().getFile() and
    mi.getLocation().getStartLine() = sizeArg.getLocation().getStartLine()
  )
}

/**
 * A bounded write into buf+off whose size argument is a `PAGE_SIZE - off` style cap
 * (scnprintf/snprintf with a remaining-space cap). Safe by construction; must NOT flag.
 */
predicate isBoundedConcat(SysfsShowFunction f, FunctionCall fc) {
  fc.getTarget().getName().regexpMatch("scnprintf|snprintf") and
  bufOffsetDest(f, fc.getArgument(0)) and
  isPageSizeCap(fc.getArgument(1))
}

/**
 * A raw unbounded concatenation into buf, inside a loop:
 *   - sprintf(buf+off, ...)                         (no size arg at all), or
 *   - snprintf/scnprintf(buf+off, <not a cap>, ...) (size arg has no subtraction), or
 *   - strcat(buf, ...) / strncat(buf, ...)
 * AND the call is enclosed by a loop in the same function.
 */
predicate unboundedConcat(SysfsShowFunction f, FunctionCall fc) {
  fc.getEnclosingFunction() = f and
  exists(Loop l | l.getEnclosingFunction() = f and fc.getEnclosingStmt().getParentStmt*() = l.getStmt())
  and
  (
    // sprintf(buf+off, ...)  -- no size argument, definitionally unbounded
    fc.getTarget().getName() = "sprintf" and bufOffsetDest(f, fc.getArgument(0))
    or
    // snprintf/scnprintf(buf+off, sz, ...) where sz is NOT a PAGE_SIZE-off cap
    fc.getTarget().getName().regexpMatch("scnprintf|snprintf") and
    bufOffsetDest(f, fc.getArgument(0)) and
    not isPageSizeCap(fc.getArgument(1))
    or
    // strcat/strncat into the raw buf
    fc.getTarget().getName().regexpMatch("strcat|strncat") and
    isBufAccess(f, fc.getArgument(0))
  )
}

from SysfsShowFunction f, FunctionCall fc
where
  unboundedConcat(f, fc) and
  // The whole function must NOT be doing the bounded thing instead (defensive: if the
  // body's concat writes are all PAGE_SIZE-capped, the unbounded matcher won't fire, but
  // guard against a body that mixes a stray bounded write).
  not isBoundedConcat(f, fc)
select fc,
  "sysfs show() '" + f.getName() + "' concatenates into buf via '" +
    fc.getTarget().getName() + "' in a loop with no PAGE_SIZE-len cap (CWE-787); " +
    "use sysfs_emit_at(). $@",
  f, f.getName()
