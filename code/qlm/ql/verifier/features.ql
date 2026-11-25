/**
 * @name QLM fidelity-check features
 * @description Per-function structural feature counts for the seed slice and the PoC.
 *              The verdict (which dimensions must agree) is computed by verifier.py.
 * @kind table
 * @id qlm/verifier-features
 */

import Features

from string file, string fn, string role, string dim, int n
where subject(file, fn, role) and feature(file, fn, dim, n)
select role, file, fn, dim, n
