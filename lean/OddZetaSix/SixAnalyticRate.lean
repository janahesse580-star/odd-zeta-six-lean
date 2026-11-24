import OddZetaSix.AnalyticData.Shard0
import OddZetaSix.AnalyticData.Shard1
import OddZetaSix.AnalyticData.Shard2
import OddZetaSix.AnalyticData.Shard3

/-!
# Stage 3 Analytic Rate Closure (`R_bound = -779 / 100 = -7.79`)

Assembles the four certified compact-phase shards covering `[0, 2]` (58 cells total,
all verified by `decide +kernel`, zero `native_decide`), bounds `log (5 / 3)` via
`RationalLogBounds.checkRounded`, and invokes `sixAnalyticRate_of_four_bin_endpoints`
to discharge `SixAnalyticRateHypothesis (-(779 : ℝ) / 100)`:
- Basis normalization rate: `9 / 10 + 3 / 5 * log (5 / 3) ≤ 9 / 10 + 3 / 5 * (51083 / 100000) = 1.206498`.
- Average of 8 certified endpoint ceilings: `-9.009375`.
- Combined analytic rate: `1.206498 - 9.009375 = -7.802877 < -7.79 = -779 / 100`.

Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix

open OddZetaSix.AnalyticData

theorem log_five_thirds_le : Real.log ((5 : ℝ) / 3) ≤ (51083 : ℝ) / 100000 := by
  have h := (RationalLogBounds.unit_sound (5 / 3) 5 (by norm_num)).2
  have hq : RationalLogBounds.unitUpper (5 / 3) 5 ≤ 51083 / 100000 := by
    norm_num [RationalLogBounds.unitUpper, RationalLogBounds.atanhUpper,
      RationalLogBounds.atanhLower, RationalLogBounds.atanhError,
      RationalLogBounds.argument, Finset.sum_range_succ]
  have hqR : (RationalLogBounds.unitUpper (5 / 3) 5 : ℝ) ≤ (51083 : ℝ) / 100000 := by
    have h1 := Rat.cast_le (K := ℝ).mpr hq
    push_cast at h1
    exact h1
  push_cast at h
  exact h.trans hqR

/-- Certified compact `[0, 2]` off-root ceilings for all 4 bins and both endpoints. -/
theorem sixSlimCompact_certified (b : Fin 4) (side : Fin 2) (y : ℝ)
    (hy0 : 0 ≤ y) (hy2 : y ≤ 2)
    (hpos : ∀ j : Fin 2, 0 < sixAdaptivePairModulus (69 / 50) (sixSlimRoots b j : ℝ) y) :
    sixPhasePotential (fun j => (sixSlimRoots b j : ℝ)) (sixBinKnot b side) y ≤
      (sixSlimCaps b side : ℝ) := by
  by_cases h1 : y ≤ ((7 / 32 : ℚ) : ℝ)
  · exact checkCellChain_sound 0 (7 / 32) shard0Cells shard0_ok b side (by simpa using hy0) h1 hpos
  · by_cases h2 : y ≤ ((83 / 256 : ℚ) : ℝ)
    · exact checkCellChain_sound (7 / 32) (83 / 256) shard1Cells shard1_ok b side
        (le_of_not_ge h1) h2 hpos
    · by_cases h3 : y ≤ ((103 / 256 : ℚ) : ℝ)
      · exact checkCellChain_sound (83 / 256) (103 / 256) shard2Cells shard2_ok b side
          (le_of_not_ge h2) h3 hpos
      · exact checkCellChain_sound (103 / 256) 2 shard3Cells shard3_ok b side
          (le_of_not_ge h3) (by simpa using hy2) hpos

/-- **Stage 3 Main Analytic Theorem**: `SixAnalyticRateHypothesis (-779 / 100)` (`R_bound = -7.79`)
is unconditionally proved. -/
theorem sixAnalyticRate_proved : SixAnalyticRateHypothesis (-(779 : ℝ) / 100) := by
  apply sixAnalyticRate_of_four_bin_endpoints sixSlimRoots sixSlimRoots_bounds
    sixSlimCaps sixSlimCompact_certified (-(779 : ℝ) / 100)
  have hlog := log_five_thirds_le
  have havgQ : (∑ b : Fin 4, (sixSlimCaps b 0 + sixSlimCaps b 1)) / 8 = -(72075 : ℚ) / 8000 := by
    decide +kernel
  have havg : (∑ b : Fin 4, ((sixSlimCaps b 0 : ℝ) + (sixSlimCaps b 1 : ℝ))) / 8 =
      -(72075 : ℝ) / 8000 := by
    have h := congrArg (Rat.cast : ℚ → ℝ) havgQ
    push_cast at h
    exact h
  linarith

end OddZetaSix
