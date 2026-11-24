import OddZetaSix.SixConfluentGate
import OddZetaSix.SixPeriodicRate
import OddZetaSix.SixHighWalls

/-!
# Stage 2B Arithmetic Rate Closure (`C_bound = 194 / 25 = 7.76`)

Assembles the three prime bands into the unconditional arithmetic rate theorem
`sixArithRate_proved : SixArithRateHypothesis ((194 : ℝ) / 25)`:
- Tiny primes `p ≤ (1/10000) * n`: rate `≤ (18 / 50) * (1 / 10000) = 0.000036` (`SixPNTBridge`).
- Periodic small primes `(1/10000) * n < p ≤ (7/2) * n`: rate `≤ 552 / 1000 = 0.552` (`SixPeriodicRate`).
- Middle/high primes `(7/2) * n < p ≤ 55 * n`: rate `≤ 7206 / 1000 = 7.206` (`SixHighWalls`).
- Total: `0.000036 + 0.552 + 7.206 = 7.758036 < 7.76 = 194 / 25`.

Instantiates `sixZeta_irrational_of_arith_and_analytic` to reduce
`SixZetaIrrationalityStatement` purely to `SixAnalyticRateHypothesis R_bound`
with `R_bound + 194 / 25 < 0` (Stage 3 handoff).

Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

noncomputable section
set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix

/-- **Stage 2B Main Arithmetic Theorem**: `SixArithRateHypothesis (194 / 25)` (`C_bound = 7.76`)
is unconditionally proved. -/
theorem sixArithRate_proved : SixArithRateHypothesis ((194 : ℝ) / 25) :=
  sixArithRate_of_three_bands ((1 : ℝ) / 10000) ((7 : ℝ) / 2) ((552 : ℝ) / 1000)
    ((7206 : ℝ) / 1000) ((194 : ℝ) / 25)
    (by norm_num) (by norm_num) (by norm_num)
    sixPeriodicBand_rate_le sixHighBand_rate_le (by norm_num)

/-- **Stage 2B Endgame Reduction**: both the confluent gate (`SixGateHypothesis`) and the
arithmetic rate (`SixArithRateHypothesis (194 / 25)`) are now discharged, so proving
`SixZetaIrrationalityStatement` requires only `SixAnalyticRateHypothesis R_bound`
with `R_bound < -194 / 25 = -7.76`. -/
theorem sixZeta_irrational_of_analytic
    (R_bound : ℝ) (hsum : R_bound + (194 : ℝ) / 25 < 0)
    (hanal : SixAnalyticRateHypothesis R_bound) :
    SixZetaIrrationalityStatement :=
  sixZeta_irrational_of_arith_and_analytic R_bound ((194 : ℝ) / 25) hsum sixArithRate_proved hanal

end OddZetaSix
