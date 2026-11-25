/**
 * @name USB descriptor blob-walk OOB (device-controlled length used without remainder check)
 * @description A USB device supplies a raw descriptor blob (the `extra`/`extralen` field of a
 *              `usb_host_{interface,config,endpoint}`, or the buffer returned by
 *              `usb_get_extra_descriptor`). Driver code casts a position in the blob to a typed
 *              descriptor struct, reads a DEVICE-CONTROLLED length/count field (`bLength`,
 *              `bNrInPins`/`bNrInputPins`, `bNumDescriptors`, `bNrEntities`, `bNrChannels`,
 *              `bControlSize`, `wLength`, `wTotalLength`, ...), then uses it to index, advance a
 *              pointer, or size a memcpy — WITHOUT first comparing it against the bytes actually
 *              remaining in the blob (`extralen`/`buflen`/`rest`/`size`/an `end` pointer/...).
 *              Comparing the field against ANOTHER descriptor field (e.g. `bLength`) is NOT a real
 *              bound because that field is also attacker-controlled.
 *
 *              v2: taint now flows through the pointer-returning descriptor-walk HELPERS
 *              (`snd_usb_find_desc`, `snd_usb_find_csint_desc`, `__usb_get_extra_descriptor`),
 *              so descriptor fields fetched via those helpers stay tainted. The source is also
 *              broadened to length/count fields read off ANY cast of a tainted blob walk pointer.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id cpp/usb-descriptor-oob
 * @tags security
 *       external/cwe/cwe-125
 *       external/cwe/cwe-787
 */

import cpp
import semmle.code.cpp.dataflow.new.TaintTracking
import semmle.code.cpp.dataflow.new.DataFlow
import semmle.code.cpp.controlflow.IRGuards

/** USB-relevant files only (keeps the global taint run to minutes). */
predicate relevantFile(File f) {
  f.getRelativePath()
      .regexpMatch("^(sound/usb|drivers/usb|drivers/media/usb|drivers/hid|drivers/net/usb)/.*")
}

/** Non-shippable build/host tooling and test code. */
predicate excludedFile(File f) {
  f.getRelativePath().regexpMatch("^(scripts|tools|samples)/.*")
  or
  f.getRelativePath().regexpMatch("(?i).*(/test|_test|/kunit|/selftest|/tests/).*")
}

/** Regex matching DEVICE-CONTROLLED descriptor length/count field names. */
string descriptorFieldRegex() {
  result =
    "(?i)^(bLength|bNrInPins|bNrInputPins|bNumDescriptors|bNrEntities|bNrChannels|" +
      "bControlSize|wLength|wTotalLength|bNumEndpoints|bNumConfigurations|bNumInterfaces|" +
      "bNumFormats|bNrModes|bNrBands|bSubframeSize|bInCollection)$"
}

/** Holds for a buffer-REMAINDER / total-available-bytes name (a real bound), not a descriptor field. */
bindingset[n]
predicate remainderName(string n) {
  n.regexpMatch("(?i).*(extralen|buflen|buf_len|datalen|maxlen|remaining|remain|rest|" +
      "_len|^len$|_size|^size$|^bytes$|nbytes|desclen|^end$|_end$).*") and
  not n.regexpMatch(descriptorFieldRegex())
}

/** The descriptor-walk POINTER-RETURNING helpers whose return value points INTO the blob. */
predicate isBlobWalkHelper(Function fn) {
  fn.getName().regexpMatch("(?i)^(snd_usb_find_desc|snd_usb_find_csint_desc)$")
}

/**
 * Source: the raw descriptor blob root, so any length/count derived from it is tainted.
 * Taint flows through `p = extra; p += n; ((T*)p)->bLength` and through helper-call arguments.
 * Restricted to relevant files for performance.
 */
predicate isBlobSource(DataFlow::Node node) {
  relevantFile(node.getLocation().getFile()) and
  not excludedFile(node.getLocation().getFile()) and
  (
    // FieldAccess to an `extra` field of a usb_host_{interface,config,endpoint}.
    exists(FieldAccess fa, Field f |
      fa = node.asExpr() and f = fa.getTarget() and f.getName() = "extra" and
      f.getDeclaringType().getName().regexpMatch("(?i)usb_host_(interface|config|endpoint)")
    )
    or
    // Return value of the usb_get_extra_descriptor family (the descriptor pointer it locates).
    exists(Call c |
      c.getTarget().getName().regexpMatch("(?i)__?usb_get_extra_descriptor") and
      node.asExpr() = c
    )
  )
}

/**
 * Sink categories — the tainted operand used unsafely.
 * (a) array offset, (b) the offset operand of pointer arithmetic, (c) the size argument of a
 *     mem* / copy_* call. Restricted to relevant, non-test files.
 */
predicate isUnsafeUse(DataFlow::Node node) {
  relevantFile(node.getLocation().getFile()) and
  not excludedFile(node.getLocation().getFile()) and
  (
    // (a) array index
    exists(ArrayExpr ae | node.asExpr() = ae.getArrayOffset())
    or
    // (b) the (non-pointer) offset operand of pointer arithmetic that advances a blob position.
    exists(PointerArithmeticOperation pa |
      node.asExpr() = pa.getAnOperand() and
      node.asExpr().getUnspecifiedType() instanceof IntegralType
    )
    or
    // (c) size (last) argument of a copy/move/set.
    exists(Call c, int i |
      c.getTarget().getName().regexpMatch("(?i)(mem(cpy|move|set)|.*copy_.*|__builtin_mem.*)") and
      i = c.getTarget().getNumberOfParameters() - 1 and
      node.asExpr() = c.getArgument(i)
    )
  )
}

/**
 * VALUE-SENSITIVE safe guard.
 * `checked` is the operand whose value is bounded on branch `b`, when the relational op compares
 * it against the buffer REMAINDER:
 *   - the OTHER operand refers to a remainder-named variable/field (`extralen`, `buflen`, `rest`,
 *     `size`, `end`, ...), OR
 *   - this is a pointer comparison (`p < end`, `next > end`) where `checked` is the position
 *     pointer and the other side is the blob-end pointer / pointer-arith.
 * A comparison purely between descriptor fields (`bLength < sz`) is NOT safe (both attacker-set):
 * neither operand is remainder-named, so it never matches here.
 * Note: this is value-sensitive — it only blocks flow of the SPECIFIC expression that is checked,
 * so an unrelated loop guard like `while (extralen > 4)` (which does not check `sz`) does not
 * suppress a `sz`-derived sink.
 */
predicate isSafeGuard(IRGuardCondition g, Expr checked, boolean b) {
  exists(RelationalOperation rel, Expr other |
    rel = g.getUnconvertedResultExpression() and
    checked = rel.getAnOperand() and
    other = rel.getAnOperand() and
    other != checked and
    (b = true or b = false)
  |
    // remainder named on the other side
    exists(VariableAccess va |
      va = other.getAChild*() and remainderName(va.getTarget().getName())
    )
    or
    // pointer position vs pointer end
    checked.getUnspecifiedType() instanceof PointerType and
    other.getUnspecifiedType() instanceof PointerType
  )
}

/**
 * Additional taint step: the blob's BYTES are attacker-controlled, so a value LOADED through a
 * tainted blob pointer is itself tainted. Standard taint already covers `p[i]`, but a field read
 * through a (possibly cast) tainted pointer — `((T*)p)->bNrInputPins`, `sel->v2.baCSourceID` — is
 * not a default step. Model: tainted qualifier/base/operand  ->  the load expression.
 */
predicate blobLoadStep(DataFlow::Node pred, DataFlow::Node succ) {
  // field read through tainted pointer/struct: `q->f` / `q.f`
  exists(FieldAccess fa |
    pred.asExpr() = fa.getQualifier() and
    succ.asExpr() = fa
  )
  or
  // pointer dereference `*q`
  exists(PointerDereferenceExpr d |
    pred.asExpr() = d.getOperand() and
    succ.asExpr() = d
  )
  or
  // C++/cast position in the blob keeps the taint: `(T*)q`
  exists(Cast c |
    pred.asExpr() = c.getExpr() and
    succ.asExpr() = c
  )
}

/**
 * Additional taint step through the POINTER-RETURNING blob-walk helpers.
 * `snd_usb_find_desc(descstart, ...)` / `snd_usb_find_csint_desc(buffer, ...)` return a pointer
 * INTO their first argument's blob, advancing the walk. If that blob argument is tainted, the
 * call's return value is tainted too — so a descriptor located via the helper stays tainted.
 * We taint from ANY pointer-typed argument (the blob is always passed as a pointer arg) to the
 * call return, which is intra-helper sound: the helper only returns positions inside `descstart`.
 */
predicate helperReturnStep(DataFlow::Node pred, DataFlow::Node succ) {
  exists(Call c, Expr arg |
    isBlobWalkHelper(c.getTarget()) and
    arg = c.getAnArgument() and
    arg.getUnspecifiedType() instanceof PointerType and
    pred.asExpr() = arg and
    succ.asExpr() = c
  )
}

module Cfg implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) { isBlobSource(node) }

  predicate isSink(DataFlow::Node node) { isUnsafeUse(node) }

  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    blobLoadStep(pred, succ) or
    helperReturnStep(pred, succ)
  }

  predicate isBarrier(DataFlow::Node node) {
    node = DataFlow::BarrierGuard<isSafeGuard/3>::getABarrierNode()
  }
}

module Flow = TaintTracking::Global<Cfg>;

from DataFlow::Node source, DataFlow::Node sink
where Flow::flow(source, sink)
select sink,
  sink.getLocation().getFile().getRelativePath() + ":" +
    sink.getLocation().getStartLine().toString() +
    " USB descriptor blob length/count from " +
    source.getLocation().getFile().getRelativePath() + ":" +
    source.getLocation().getStartLine().toString() +
    " used (index/ptr-arith/copy-size) without a buffer-remainder check."
