import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Actual zeta series and exact finite cutoffs

Adapted from `OddZetaMixed.ZetaTail` for the six-value window
`ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17)` and summation cutoff `s = 40`.
All zeta identifications use Mathlib's standard `riemannZeta`.
-/

set_option autoImplicit false

namespace OddZetaSix

open scoped BigOperators

/-- The real Dirichlet series at a natural exponent, starting at one. -/
noncomputable def zetaNat (s : ℕ) : ℝ :=
  ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ s

/-- The exact rational finite sum `H_m^(s) = ∑_{v=1}^m 1/v^s`. -/
def harmonicCutoff (s m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range m, 1 / ((k : ℚ) + 1) ^ s

/-- The shifted real series `T_s(q) = ∑_{v=q}^∞ 1/v^s` for positive `q`. -/
noncomputable def zetaTail (s q : ℕ) : ℝ :=
  ∑' k : ℕ, 1 / ((k : ℝ) + (q : ℝ)) ^ s

theorem summable_zetaNat {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1 < s))

theorem hasSum_zetaNat {s : ℕ} (hs : 2 ≤ s) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) (zetaNat s) :=
  (summable_zetaNat hs).hasSum

/-- Full complex equality with Mathlib's `riemannZeta`. -/
theorem riemannZeta_nat_eq_ofReal {s : ℕ} (hs : 2 ≤ s) :
    riemannZeta (s : ℂ) = (zetaNat s : ℂ) := by
  have hsC : 1 < (s : ℂ).re := by
    simpa using (show (1 : ℝ) < s by exact_mod_cast (show 1 < s by omega))
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hsC, zetaNat, Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  simp

theorem zetaNat_eq_re_riemannZeta {s : ℕ} (hs : 2 ≤ s) :
    zetaNat s = (riemannZeta (s : ℂ)).re := by
  rw [riemannZeta_nat_eq_ofReal hs]
  rfl

theorem riemannZeta_nat_im_eq_zero {s : ℕ} (hs : 2 ≤ s) :
    (riemannZeta (s : ℂ)).im = 0 := by
  rw [riemannZeta_nat_eq_ofReal hs]
  rfl

@[simp] theorem harmonicCutoff_zero (s : ℕ) : harmonicCutoff s 0 = 0 := by
  simp [harmonicCutoff]

theorem harmonicCutoff_succ (s m : ℕ) :
    harmonicCutoff s (m + 1) = harmonicCutoff s m + 1 / ((m : ℚ) + 1) ^ s := by
  simp [harmonicCutoff, Finset.sum_range_succ]

theorem harmonicCutoff_cast_real (s m : ℕ) :
    (harmonicCutoff s m : ℝ) = ∑ k ∈ Finset.range m, 1 / ((k : ℝ) + 1) ^ s := by
  simp [harmonicCutoff]

theorem summable_zetaTail {s : ℕ} (hs : 2 ≤ s) (q : ℕ) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + (q : ℝ)) ^ s) := by
  simpa only [Nat.cast_add] using
    (summable_nat_add_iff q).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1 < s))

theorem hasSum_zetaTail {s : ℕ} (hs : 2 ≤ s) (q : ℕ) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + (q : ℝ)) ^ s) (zetaTail s q) :=
  (summable_zetaTail hs q).hasSum

theorem harmonicCutoff_add_zetaTail {s : ℕ} (hs : 2 ≤ s) (m : ℕ) :
    (harmonicCutoff s m : ℝ) + zetaTail s (m + 1) = zetaNat s := by
  simpa only [harmonicCutoff_cast_real, zetaTail, zetaNat, Nat.cast_add,
    Nat.cast_one, add_assoc] using (summable_zetaNat hs).sum_add_tsum_nat_add m

theorem zetaTail_eq_zetaNat_sub_harmonicCutoff {s q : ℕ} (hs : 2 ≤ s) (hq : 0 < q) :
    zetaTail s q = zetaNat s - (harmonicCutoff s (q - 1) : ℝ) := by
  have h := harmonicCutoff_add_zetaTail hs (q - 1)
  rw [Nat.sub_add_cancel hq] at h
  linarith

theorem hasSum_shifted_inv_pow {s q : ℕ} (hs : 2 ≤ s) (hq : 0 < q) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + (q : ℝ)) ^ s)
      (zetaNat s - (harmonicCutoff s (q - 1) : ℝ)) := by
  rw [← zetaTail_eq_zetaNat_sub_harmonicCutoff hs hq]
  exact hasSum_zetaTail hs q

/-- The shifted inverse-power sum for the `local50-45-209` summation variable
`t = v - 40 * n` (where `s = min_a z_a = 40`). -/
theorem hasSum_six_shifted_inv_pow (n k i : ℕ) (hk : 40 * n < k) :
    HasSum (fun v : ℕ => 1 / ((v : ℝ) - 40 * (n : ℝ) + (k : ℝ)) ^ (i + 4))
      (zetaNat (i + 4) - (harmonicCutoff (i + 4) (k - 40 * n - 1) : ℝ)) := by
  have hq : 0 < k - 40 * n := Nat.sub_pos_of_lt hk
  have hden (v : ℕ) : (v : ℝ) - 40 * (n : ℝ) + (k : ℝ) =
      (v : ℝ) + ((k - 40 * n : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk.le]
    push_cast
    ring
  simp_rw [hden]
  exact hasSum_shifted_inv_pow (by omega) hq

/-- The six target odd zeta values, in the order `7, 9, 11, 13, 15, 17`. -/
noncomputable def sixZetaValues (j : Fin 6) : ℝ :=
  zetaNat (7 + 2 * (j : ℕ))

theorem sixZetaValues_eq_re_riemannZeta (j : Fin 6) :
    sixZetaValues j = (riemannZeta ((7 + 2 * (j : ℕ) : ℕ) : ℂ)).re :=
  zetaNat_eq_re_riemannZeta (by omega)

theorem sixZetaValues_ofReal (j : Fin 6) :
    (sixZetaValues j : ℂ) = riemannZeta ((7 + 2 * (j : ℕ) : ℕ) : ℂ) :=
  (riemannZeta_nat_eq_ofReal (by omega)).symm

end OddZetaSix
