/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.Sieve.DataBminus_p1459
import Fermat433.Sieve.DataCplus_p1459

/-!
# The sieves of the rerun at `p = 1459`, checked by the kernel

The whole quadratic Chabauty computation was repeated at `p = 1459` as an independent check
(PROOF.md, "Second prime"). Its candidates (1546 on `B⁻`, 1426 on `C⁺`) are sieved at the primes of
`L` above 2917 and 26261, in the 1459-parts of `E₁(𝔽_q)`, `E₂(𝔽_q)`, and only the four known points
survive on each curve. On `C⁺` the two disks `x ≡ 103` use the vectors recomputed at higher
precision (`second_prime/cands103_Cplus.gp`), as in the record.
-/

namespace Fermat433.Sieve

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem sieve_B_minus_p1459 :
    run Bminus_p1459.inputs Bminus_p1459.certs =
      some [(1, 0), (1458, 0), (0, 1), (0, 1458)] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem sieve_C_plus_p1459 :
    run Cplus_p1459.inputs Cplus_p1459.certs =
      some [(0, 1), (0, 1458), (1458, 0), (1, 0)] := by
  decide +kernel

end Fermat433.Sieve
