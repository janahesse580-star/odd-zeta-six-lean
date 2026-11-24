import OddZetaSix.Statement
import OddZetaSix.SixIdentity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Endgame Irrationality Skeleton and Locked Proof Contracts

Locks the three explicit `Prop` interfaces (no custom axioms, no `sorry`) needed
to complete the proof of `SixZetaIrrationalityStatement`:
1. `SixGateHypothesis` (closed live in `SixConfluentGate.lean`);
2. `SixArithRateHypothesis C_bound` (multiplicative exponential bound, avoiding `log 0`);
3. `SixAnalyticRateHypothesis R_bound` (multiplicative exponential bound, avoiding `log 0`).

All rates are normalized by `sixNorm n = n * (15 * n) * 50 = 750 * n^2` (`n * h * L`).
-/

noncomputable section
set_option autoImplicit false

namespace OddZetaSix

open scoped BigOperators

/-- Common asymptotic normalization `n * h * L = n * (15 * n) * 50 = 750 * n^2`. -/
def sixNorm (n : ℕ) : ℝ :=
  (n : ℝ) * (rank n : ℝ) * (paramL : ℝ)

theorem sixNorm_eq (n : ℕ) : sixNorm n = 750 * (n : ℝ) ^ 2 := by
  unfold sixNorm rank paramL
  push_cast
  ring

theorem sixNorm_nonneg (n : ℕ) : 0 ≤ sixNorm n := by
  rw [sixNorm_eq]
  positivity

/-! ## Locked three-input interfaces -/

/-- Auxiliary-prime nonvanishing contract: for every positive denominator `Q` and
threshold `N₀`, there is `n ≥ N₀` such that `P_n(q) ≠ 0` for every rational
6-tuple `q` whose denominators divide `Q`. -/
def SixGateHypothesis : Prop :=
  ∀ (Q : ℤ), 0 < Q → ∀ (N₀ : ℕ), ∃ n : ℕ, N₀ ≤ n ∧
    ∀ (q : Fin 6 → ℚ), (∀ k : Fin 6, ∃ a : ℤ, (Q : ℚ) * q k = (a : ℚ)) →
      (sixPrimitivePolynomial n).eval₂ (Int.castRingHom ℚ) q ≠ 0

/-- Arithmetic upper rate contract in multiplicative exponential form
`|γ_n|⁻¹ ≤ exp(C_bound * n h L)` eventually, avoiding `log 0` side conditions. -/
def SixArithRateHypothesis (C_bound : ℝ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop,
    |(sixPrimitiveScalar n : ℝ)|⁻¹ ≤ Real.exp (C_bound * sixNorm n)

/-- Analytic upper rate contract in multiplicative exponential form
`|det 𝓗_n(ζ)| ≤ exp(R_bound * n h L)` eventually, avoiding `log 0` side conditions. -/
def SixAnalyticRateHypothesis (R_bound : ℝ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop,
    |Matrix.det (sixFunctional n)| ≤ Real.exp (R_bound * sixNorm n)

/-! ## Denominator clearing for integer multivariate polynomials -/

theorem common_denominator_exists {ι : Type*} [Finite ι] (z : ι → ℚ) :
    ∃ Q : ℤ, 0 < Q ∧ ∀ i, ∃ a : ℤ, (Q : ℚ) * z i = (a : ℚ) := by
  obtain ⟨Q, hQ⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (Submonoid.pos ℤ) z
  refine ⟨Q, Q.property, ?_⟩
  intro i
  obtain ⟨a, ha⟩ := hQ i
  refine ⟨a, ?_⟩
  simpa only [Algebra.smul_def, eq_intCast] using ha.symm

theorem clear_denominators {σ : Type*} (P : MvPolynomial σ ℤ) (z : σ → ℚ)
    (Q : ℤ) (d : ℕ) (hdegree : P.totalDegree ≤ d)
    (hz : ∀ i, ∃ a : ℤ, (Q : ℚ) * z i = (a : ℚ)) :
    ∃ a : ℤ, (Q : ℚ) ^ d * P.eval₂ (Int.castRingHom ℚ) z = (a : ℚ) := by
  classical
  choose a ha using hz
  refine ⟨∑ m ∈ P.support,
    P.coeff m * Q ^ (d - m.sum (fun _ e => e)) * ∏ i ∈ m.support, a i ^ m i, ?_⟩
  rw [MvPolynomial.eval₂_eq, Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_prod]
  apply Finset.sum_congr rfl
  intro m hm
  have hmdegree : (∑ i ∈ m.support, m i) ≤ d :=
    (MvPolynomial.le_totalDegree hm).trans hdegree
  have hprod : (∏ i ∈ m.support, (a i : ℚ) ^ m i) =
      (Q : ℚ) ^ (∑ i ∈ m.support, m i) * ∏ i ∈ m.support, z i ^ m i := by
    simp_rw [← ha, mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hprod]
  change (Q : ℚ) ^ d * ((P.coeff m : ℚ) * ∏ i ∈ m.support, z i ^ m i) =
    (P.coeff m : ℚ) * (Q : ℚ) ^ (d - ∑ i ∈ m.support, m i) *
      ((Q : ℚ) ^ (∑ i ∈ m.support, m i) * ∏ i ∈ m.support, z i ^ m i)
  have hpow : (Q : ℚ) ^ (d - ∑ i ∈ m.support, m i) *
      (Q : ℚ) ^ (∑ i ∈ m.support, m i) = (Q : ℚ) ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hmdegree]
  calc
    _ = (P.coeff m : ℚ) *
        ((Q : ℚ) ^ (d - ∑ i ∈ m.support, m i) *
          (Q : ℚ) ^ (∑ i ∈ m.support, m i)) * ∏ i ∈ m.support, z i ^ m i := by
      rw [hpow]
      ring
    _ = _ := by ring

theorem clear_denominators_nonzero {σ : Type*} (P : MvPolynomial σ ℤ)
    (z : σ → ℚ) (Q : ℤ) (d : ℕ) (hQ : Q ≠ 0)
    (hdegree : P.totalDegree ≤ d)
    (hz : ∀ i, ∃ a : ℤ, (Q : ℚ) * z i = (a : ℚ))
    (hne : P.eval₂ (Int.castRingHom ℚ) z ≠ 0) :
    ∃ a : ℤ, a ≠ 0 ∧ (Q : ℚ) ^ d * P.eval₂ (Int.castRingHom ℚ) z = (a : ℚ) := by
  obtain ⟨a, ha⟩ := clear_denominators P z Q d hdegree hz
  refine ⟨a, ?_, ha⟩
  intro hzero
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ
  have : (Q : ℚ) ^ d * P.eval₂ (Int.castRingHom ℚ) z ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hQ') hne
  apply this
  simpa [hzero] using ha

theorem one_le_abs_cleared_evaluation {σ : Type*} (P : MvPolynomial σ ℤ)
    (z : σ → ℚ) (Q : ℤ) (d : ℕ) (hQ : Q ≠ 0)
    (hdegree : P.totalDegree ≤ d)
    (hz : ∀ i, ∃ a : ℤ, (Q : ℚ) * z i = (a : ℚ))
    (hne : P.eval₂ (Int.castRingHom ℚ) z ≠ 0) :
    1 ≤ |(Q : ℚ) ^ d * P.eval₂ (Int.castRingHom ℚ) z| := by
  obtain ⟨a, hane, ha⟩ := clear_denominators_nonzero P z Q d hQ hdegree hz hne
  rw [ha]
  have habs : (1 : ℤ) ≤ |a| := by
    have : (0 : ℤ) < |a| := abs_pos.mpr hane
    omega
  exact_mod_cast habs

/-! ## Main endgame assembly theorem -/

private theorem eval₂_rat_cast_real {σ : Type*} (P : MvPolynomial σ ℤ) (q : σ → ℚ) :
    ((P.eval₂ (Int.castRingHom ℚ) q : ℚ) : ℝ) =
      P.eval₂ (Int.castRingHom ℝ) (fun k => (q k : ℝ)) := by
  have h := MvPolynomial.hom_eval₂ P (Int.castRingHom ℚ) (Rat.castHom ℝ) q
  have hcomp : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ :=
    RingHom.ext fun z => by simp
  simpa only [hcomp, Rat.coe_castHom] using h

theorem sixPrimitivePolynomial_eventually_bound
    (R_bound C_bound : ℝ)
    (harith : SixArithRateHypothesis C_bound)
    (hanal : SixAnalyticRateHypothesis R_bound) :
    ∀ᶠ n : ℕ in Filter.atTop,
      |(sixPrimitivePolynomial n).eval₂ (Int.castRingHom ℝ) sixZetaValues| ≤
        Real.exp ((R_bound + C_bound) * sixNorm n) := by
  filter_upwards [harith, hanal] with n hC hR
  have hγ : (sixPrimitiveScalar n : ℝ) ≠ 0 := by
    exact_mod_cast sixPrimitiveScalar_ne_zero n
  have heval : (sixPrimitivePolynomial n).eval₂ (Int.castRingHom ℝ) sixZetaValues =
      (sixPrimitiveScalar n : ℝ)⁻¹ * Matrix.det (sixFunctional n) := by
    have h := sixPrimitivePolynomial_eval_actual n
    rw [← h, inv_mul_cancel_left₀ hγ]
  rw [heval, abs_mul, abs_inv]
  calc
    |(sixPrimitiveScalar n : ℝ)|⁻¹ * |Matrix.det (sixFunctional n)|
        ≤ Real.exp (C_bound * sixNorm n) * Real.exp (R_bound * sixNorm n) :=
      mul_le_mul hC hR (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((R_bound + C_bound) * sixNorm n) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Master contradiction assembly: once `R_bound + C_bound < 0`, the three
contracts imply `SixZetaIrrationalityStatement`. -/
theorem sixZeta_irrational_of_hypotheses
    (R_bound C_bound : ℝ) (hsum : R_bound + C_bound < 0)
    (hgate : SixGateHypothesis)
    (harith : SixArithRateHypothesis C_bound)
    (hanal : SixAnalyticRateHypothesis R_bound) :
    SixZetaIrrationalityStatement := by
  rw [← sixZeta_irrational_iff_standard]
  by_contra hall
  push Not at hall
  have hrat : ∀ i : Fin 6, ∃ q : ℚ, (q : ℝ) = sixZetaValues i := by
    intro i
    have hni := hall i
    unfold Irrational at hni
    push Not at hni
    exact hni
  choose q hq using hrat
  obtain ⟨Q, hQpos, hQint⟩ := common_denominator_exists q
  have hbound := sixPrimitivePolynomial_eventually_bound R_bound C_bound harith hanal
  rw [Filter.eventually_atTop] at hbound
  obtain ⟨N₁, hN₁⟩ := hbound
  let δ : ℝ := -(R_bound + C_bound)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQpos
  have hQposR : (0 : ℝ) < (Q : ℝ) := by linarith
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (15 * Real.log (Q : ℝ) / (750 * δ))
  let N₀ : ℕ := max (max N₁ N₂) 1
  obtain ⟨n, hn, hPne⟩ := hgate Q hQpos N₀
  have hn1 : N₁ ≤ n := (le_max_left N₁ N₂).trans ((le_max_left _ 1).trans hn)
  have hn2 : N₂ ≤ n := (le_max_right N₁ N₂).trans ((le_max_left _ 1).trans hn)
  have hnPos : 0 < n := (le_max_right (max N₁ N₂) 1).trans hn
  have hne := hPne q hQint
  have hlowerQ := one_le_abs_cleared_evaluation (sixPrimitivePolynomial n) q Q (rank n)
    hQpos.ne' (sixPrimitivePolynomial_totalDegree_le n) hQint hne
  have hlowerR : (1 : ℝ) ≤ ((Q : ℝ) ^ (rank n)) *
      |(sixPrimitivePolynomial n).eval₂ (Int.castRingHom ℝ) sixZetaValues| := by
    have hcast : (1 : ℝ) ≤
        ((|(Q : ℚ) ^ rank n * (sixPrimitivePolynomial n).eval₂ (Int.castRingHom ℚ) q| : ℚ) : ℝ) := by
      exact_mod_cast hlowerQ
    rw [Rat.cast_abs, Rat.cast_mul, Rat.cast_pow, Rat.cast_intCast, eval₂_rat_cast_real,
      abs_mul, abs_pow, abs_of_pos hQposR] at hcast
    have hqfun : (fun k => (q k : ℝ)) = sixZetaValues := funext hq
    rwa [hqfun] at hcast
  have hupperR := hN₁ n hn1
  have hcomb : (1 : ℝ) ≤ (Q : ℝ) ^ (rank n) * Real.exp ((R_bound + C_bound) * sixNorm n) :=
    hlowerR.trans (mul_le_mul_of_nonneg_left hupperR (pow_nonneg hQposR.le _))
  have hQpow : (Q : ℝ) ^ (rank n) = Real.exp ((rank n : ℝ) * Real.log (Q : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hQposR, mul_comm]
  rw [hQpow, ← Real.exp_add] at hcomb
  have hexp_neg : (rank n : ℝ) * Real.log (Q : ℝ) + (R_bound + C_bound) * sixNorm n < 0 := by
    rw [sixNorm_eq]
    have hrank : (rank n : ℝ) = 15 * (n : ℝ) := by unfold rank; push_cast; ring
    rw [hrank]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnPos
    have hN2n : 15 * Real.log (Q : ℝ) / (750 * δ) < (n : ℝ) :=
      lt_of_lt_of_le hN₂ (by exact_mod_cast hn2)
    have h750 : 0 < 750 * δ := by positivity
    have hmul : 15 * Real.log (Q : ℝ) < (n : ℝ) * (750 * δ) := (div_lt_iff₀ h750).mp hN2n
    have hmul2 : 15 * (n : ℝ) * Real.log (Q : ℝ) < 750 * δ * (n : ℝ) ^ 2 := by
      nlinarith
    have hsum_eq : R_bound + C_bound = -δ := by dsimp [δ]; ring
    rw [hsum_eq]
    linarith
  have hlt1 : Real.exp ((rank n : ℝ) * Real.log (Q : ℝ) + (R_bound + C_bound) * sixNorm n) < 1 :=
    Real.exp_lt_one_iff.mpr hexp_neg
  linarith

end OddZetaSix
