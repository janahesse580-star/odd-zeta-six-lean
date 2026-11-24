import OddZetaSix.SixArithRate
import OddZetaSix.SixAnalyticRate

/-!
# Unconditional Irrationality of at Least One of `ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17)`

Combines the three unconditionally proved hypotheses:
1. `sixGate_proved : SixGateHypothesis` (`SixConfluentGate.lean`)
2. `sixArithRate_proved : SixArithRateHypothesis (194 / 25)` (`SixArithRate.lean`, `C_bound = 7.76`)
3. `sixAnalyticRate_proved : SixAnalyticRateHypothesis (-779 / 100)` (`SixAnalyticRate.lean`, `R_bound = -7.79`)

Since `R_bound + C_bound = -779 / 100 + 194 / 25 = -3 / 100 < 0`, the master assembly
closes unconditionally:
`∃ s ∈ ({7, 9, 11, 13, 15, 17} : Finset ℕ), Irrational ((riemannZeta (s : ℂ)).re)`.

Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

noncomputable section
set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix

/-- Unconditional proof of `SixZetaIrrationalityStatement`. -/
theorem sixZeta_irrational : SixZetaIrrationalityStatement :=
  sixZeta_irrational_of_analytic (-(779 : ℝ) / 100) (by norm_num) sixAnalyticRate_proved

/-- Unconditional main theorem in explicit Mathlib `riemannZeta` form:
at least one of `ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17)` is irrational. -/
theorem exists_irrational_riemannZeta_seven_to_seventeen :
    ∃ s ∈ ({7, 9, 11, 13, 15, 17} : Finset ℕ), Irrational ((riemannZeta (s : ℂ)).re) :=
  sixZeta_irrational

end OddZetaSix
