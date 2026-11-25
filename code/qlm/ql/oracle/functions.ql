/**
 * @name PoC function spans
 * @description Name and line span of every function defined in the PoC database; used to
 *              attribute query results to `_buggy` / `_fixed` / variant functions.
 * @kind table
 * @id qlm/poc-function-spans
 */

import cpp

from Function f, BlockStmt b
where b = f.getBlock() and f.fromSource()
select f.getName(), b.getLocation().getFile().getBaseName(), f.getLocation().getStartLine(),
  b.getLocation().getEndLine()
