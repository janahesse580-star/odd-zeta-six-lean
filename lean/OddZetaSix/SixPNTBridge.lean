import PNTDependency
import OddZetaSix.SixAssembly
import OddZetaSix.SixSmallPrimes
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# PNT Bridge for `SixArithRateHypothesis`

Connects the per-prime valuation bounds from Stage 2A (`SixSmallPrimes`,
`SixLocalSlots`) to the vendored Prime Number Theorem package (`PNTDependency`)
and the locked endgame arithmetic contract `SixArithRateHypothesis C_bound`
(normalized by `sixNorm n = 750 * n^2`).

Main components:
1. Exact unconditional exponential bridge
   `|(sixPrimitiveScalar n : ℝ)|⁻¹ ≤ Real.exp (sixPrimeCost n)`.
2. Sharp universal bound for `p^2 > 140n + 2`: `Nat.log p (55 * n) ≤ 1`,
   hence `-v_p(γ_n) ≤ 270 * n`.
3. Tiny prime band (`p ≤ ε * n`): split at `p^2 ≤ 140n + 2` (`o(n^2)`) and
   `√(140n + 2) < p ≤ ε * n` (rate `≤ (18 / 50) * ε`).
4. Exceptional prime vanishing: any `O(1)` wall-adjacent primes (and divisors
   of `n`) contribute `o(n^2)` to `sixPrimeCost n`.
5. Band-splitting & PNT continuous/perturbed rate wrappers culminating in
   `sixArithRate_of_three_bands`.

Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

noncomputable section
set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix

open Finset Filter MeasureTheory
open scoped BigOperators

/-! ## Prime cost definitions and exponential bridge -/

/-- All primes up to the sharp integrality cutoff `55 * n`. -/
def sixCutoffPrimes (n : ℕ) : Finset ℕ :=
  Nat.primesLE (55 * n)

/-- Nonnegative `p`-adic denominator exponent `max 0 (-v_p(γ_n))` as a real number. -/
def sixPrimeExpReal (n p : ℕ) : ℝ :=
  (max (0 : ℤ) (-padicValRat p (sixPrimitiveScalar n)) : ℝ)

theorem sixPrimeExpReal_nonneg (n p : ℕ) : 0 ≤ sixPrimeExpReal n p := by
  unfold sixPrimeExpReal
  exact_mod_cast le_max_left (0 : ℤ) (-padicValRat p (sixPrimitiveScalar n))

/-- Total logarithmic denominator cost `∑_{p ≤ 55n} max(0, -v_p(γ_n)) log p`. -/
def sixPrimeCost (n : ℕ) : ℝ :=
  ∑ p ∈ sixCutoffPrimes n, sixPrimeExpReal n p * Real.log (p : ℝ)

/-- Band-restricted prime cost on `a * n < p ≤ b * n`. -/
def sixBandPrimeCost (n : ℕ) (a b : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ (Nat.primesLE ⌊b * (n : ℝ)⌋₊).filter (fun p : ℕ => a * (n : ℝ) < (p : ℝ)),
    sixPrimeExpReal n p * Real.log (p : ℝ)

theorem sixPrimeCost_nonneg (n : ℕ) : 0 ≤ sixPrimeCost n := by
  apply Finset.sum_nonneg
  intro p hp
  have hpr : p.Prime := (Nat.mem_primesLE.mp hp).2
  exact mul_nonneg (sixPrimeExpReal_nonneg n p)
    (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))

theorem sixBandPrimeCost_nonneg (n : ℕ) (a b : ℝ) : 0 ≤ sixBandPrimeCost n a b := by
  classical
  unfold sixBandPrimeCost
  apply Finset.sum_nonneg
  intro p hp
  have hpr : p.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  exact mul_nonneg (sixPrimeExpReal_nonneg n p)
    (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))

/-- For any rational `q ≠ 0` and prime `p ∣ q.den`, `padicValRat p q = -padicValNat p q.den`. -/
private theorem padicValRat_eq_neg_den_of_dvd (q : ℚ) (p : ℕ) [Fact p.Prime]
    (hdvd : p ∣ q.den) :
    padicValRat p q = -(padicValNat p q.den : ℤ) := by
  have hp : p.Prime := Fact.out
  have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
  have hndvd_num : ¬ p ∣ q.num.natAbs := by
    intro hnum
    have h1 : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hnum hdvd
    rw [hcop.gcd_eq_one] at h1
    exact hp.not_dvd_one h1
  have hnum0 : q.num ≠ 0 := by
    intro h0
    rw [h0] at hndvd_num
    exact hndvd_num (dvd_zero p)
  have hq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
  conv_lhs => rw [hq]
  rw [padicValRat.div (by exact_mod_cast hnum0) (by exact_mod_cast q.den_nz),
    padicValRat.of_int, padicValInt, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd hndvd_num]
  simp

/-- Unconditional exponential bridge: `|γ_n|⁻¹ ≤ exp(sixPrimeCost n)` for every `n : ℕ`. -/
theorem abs_inv_sixPrimitiveScalar_le_exp_primeCost (n : ℕ) :
    |(sixPrimitiveScalar n : ℝ)|⁻¹ ≤ Real.exp (sixPrimeCost n) := by
  let q : ℚ := sixPrimitiveScalar n
  have hqne : q ≠ 0 := sixPrimitiveScalar_ne_zero n
  have hnum_ne : q.num ≠ 0 := Rat.num_ne_zero.mpr hqne
  have hden_pos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have habs_inv : |(q : ℝ)|⁻¹ ≤ (q.den : ℝ) := by
    have hqR : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    rw [hqR, abs_div, inv_div, abs_of_pos hden_pos]
    have h1 : (1 : ℝ) ≤ |(q.num : ℝ)| := by
      have : (1 : ℤ) ≤ |q.num| := by
        have := abs_pos.mpr hnum_ne
        omega
      exact_mod_cast this
    exact div_le_self hden_pos.le h1
  have hlog_den : Real.log (q.den : ℝ) ≤ sixPrimeCost n := by
    have hfac : (∏ p ∈ q.den.primeFactors, p ^ q.den.factorization p) = q.den :=
      Nat.prod_factorization_pow_eq_self q.den_nz
    have hlog_eq : Real.log (q.den : ℝ) =
        ∑ p ∈ q.den.primeFactors, (padicValNat p q.den : ℝ) * Real.log (p : ℝ) := by
      conv_lhs => rw [← hfac]
      push_cast
      rw [Real.log_prod (fun p hp => by
        have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
        exact pow_ne_zero _ (by exact_mod_cast hpr.ne_zero))]
      apply Finset.sum_congr rfl
      intro p hp
      have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
      have : Fact p.Prime := ⟨hpr⟩
      rw [Real.log_pow, Nat.factorization_def q.den hpr]
    rw [hlog_eq]
    unfold sixPrimeCost
    have hsub : q.den.primeFactors ⊆ sixCutoffPrimes n := by
      intro p hp
      have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hdvd : p ∣ q.den := Nat.dvd_of_mem_primeFactors hp
      have : Fact p.Prime := ⟨hpr⟩
      have hv_pos : 0 < padicValNat p q.den :=
        lt_of_lt_of_le Nat.zero_lt_one (one_le_padicValNat_of_dvd q.den_nz hdvd)
      have hv_eq : padicValRat p q = -(padicValNat p q.den : ℤ) :=
        padicValRat_eq_neg_den_of_dvd q p hdvd
      have hp55 : p ≤ 55 * n := by
        by_contra hgt
        push Not at hgt
        have hle0 := sixPrimitiveScalar_large_prime_integral n p hgt
        change -padicValRat p q ≤ 0 at hle0
        omega
      exact Nat.mem_primesLE.mpr ⟨hp55, hpr⟩
    refine (Finset.sum_le_sum (fun p hp => ?_)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by
        have hpr : p.Prime := (Nat.mem_primesLE.mp hp).2
        exact mul_nonneg (sixPrimeExpReal_nonneg n p)
          (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))))
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ q.den := Nat.dvd_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpr⟩
    have hv_eq : padicValRat p q = -(padicValNat p q.den : ℤ) :=
      padicValRat_eq_neg_den_of_dvd q p hdvd
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
    unfold sixPrimeExpReal
    change (padicValNat p q.den : ℝ) ≤ max ((0 : ℤ) : ℝ) (-((padicValRat p q : ℤ) : ℝ))
    rw [hv_eq, Int.cast_neg, neg_neg, Int.cast_zero, Int.cast_natCast]
    exact le_max_right (0 : ℝ) (padicValNat p q.den : ℝ)
  calc
    |(q : ℝ)|⁻¹ ≤ (q.den : ℝ) := habs_inv
    _ = Real.exp (Real.log (q.den : ℝ)) := (Real.exp_log hden_pos).symm
    _ ≤ Real.exp (sixPrimeCost n) := Real.exp_le_exp.mpr hlog_den

/-- Sufficient condition for `SixArithRateHypothesis C_bound` via `sixPrimeCost`. -/
theorem sixArithRate_of_eventually_primeCost_div (C_bound : ℝ)
    (h : ∀ᶠ n : ℕ in atTop, sixPrimeCost n / sixNorm n ≤ C_bound) :
    SixArithRateHypothesis C_bound := by
  filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with n hdiv hn
  have hnorm_pos : 0 < sixNorm n := by
    rw [sixNorm_eq]
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hle : sixPrimeCost n ≤ C_bound * sixNorm n := (div_le_iff₀ hnorm_pos).mp hdiv
  exact (abs_inv_sixPrimitiveScalar_le_exp_primeCost n).trans (Real.exp_le_exp.mpr hle)

/-! ## Sharp universal bound `270 * n` for `p^2 > 140n + 2` -/

theorem sixPrimitiveScalar_padic_le_270n (n p : ℕ) [Fact p.Prime]
    (hsq : 140 * n + 2 < p ^ 2) :
    -padicValRat p (sixPrimitiveScalar n) ≤ 270 * (n : ℤ) := by
  have hp : p.Prime := Fact.out
  have hlog_le : Nat.log p (55 * n) ≤ 1 := by
    by_cases h55 : 55 * n = 0
    · simp [h55]
    · have hlt : 55 * n < p ^ 2 := by omega
      have := (Nat.log_lt_iff_lt_pow hp.one_lt h55).mpr hlt
      omega
  have hub := sixPrimitiveScalar_universal_bound_55 n p
  have hlogZ : (Nat.log p (55 * n) : ℤ) ≤ 1 := by exact_mod_cast hlog_le
  nlinarith

theorem sixPrimeExpReal_le_270n (n p : ℕ) [Fact p.Prime]
    (hsq : 140 * n + 2 < p ^ 2) :
    sixPrimeExpReal n p ≤ 270 * (n : ℝ) := by
  unfold sixPrimeExpReal
  have h := sixPrimitiveScalar_padic_le_270n n p hsq
  have hle : max (0 : ℤ) (-padicValRat p (sixPrimitiveScalar n)) ≤ 270 * (n : ℤ) :=
    max_le (by positivity) h
  exact_mod_cast hle

theorem sixPrimeExpReal_mul_log_le_universal (n p : ℕ) [Fact p.Prime] (hn : 0 < n) :
    sixPrimeExpReal n p * Real.log (p : ℝ) ≤ 270 * (n : ℝ) * Real.log (55 * (n : ℝ)) := by
  have hp : p.Prime := Fact.out
  have hub := sixPrimitiveScalar_universal_bound_55 n p
  have hexp_le : sixPrimeExpReal n p ≤ 270 * (n : ℝ) * (Nat.log p (55 * n) : ℝ) := by
    unfold sixPrimeExpReal
    have hZ : max (0 : ℤ) (-padicValRat p (sixPrimitiveScalar n)) ≤
        18 * (15 * (n : ℤ)) * (Nat.log p (55 * n) : ℤ) :=
      max_le (by positivity) hub
    have hR : (max (0 : ℤ) (-padicValRat p (sixPrimitiveScalar n)) : ℝ) ≤
        18 * (15 * (n : ℝ)) * (Nat.log p (55 * n) : ℝ) := by exact_mod_cast hZ
    linarith
  have hpow_le : (p : ℝ) ^ (Nat.log p (55 * n)) ≤ 55 * (n : ℝ) := by
    have hnat : p ^ (Nat.log p (55 * n)) ≤ 55 * n := Nat.pow_log_le_self p (by omega)
    exact_mod_cast hnat
  have hlog_mul : (Nat.log p (55 * n) : ℝ) * Real.log (p : ℝ) ≤ Real.log (55 * (n : ℝ)) := by
    have hppos : (0 : ℝ) < (p : ℝ) ^ (Nat.log p (55 * n)) := by
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
      positivity
    rw [← Real.log_pow]
    exact Real.log_le_log hppos hpow_le
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  calc
    sixPrimeExpReal n p * Real.log (p : ℝ)
        ≤ (270 * (n : ℝ) * (Nat.log p (55 * n) : ℝ)) * Real.log (p : ℝ) :=
      mul_le_mul_of_nonneg_right hexp_le hlogp
    _ = 270 * (n : ℝ) * ((Nat.log p (55 * n) : ℝ) * Real.log (p : ℝ)) := by ring
    _ ≤ 270 * (n : ℝ) * Real.log (55 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_mul (by positivity)

/-! ## Elementary asymptotic decay helpers (`o(n^2)`) -/

/-- Elementary bound `log x ≤ 4 * x^(1/4)` for all `x > 0`. -/
private theorem log_le_four_mul_rpow_quarter {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 4 * x ^ ((1 : ℝ) / 4) := by
  have h4 : 0 < x ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hx _
  have hlog : Real.log (x ^ ((1 : ℝ) / 4)) = ((1 : ℝ) / 4) * Real.log x :=
    Real.log_rpow hx _
  have hle : Real.log (x ^ ((1 : ℝ) / 4)) ≤ x ^ ((1 : ℝ) / 4) - 1 :=
    Real.log_le_sub_one_of_pos h4
  linarith

/-- `log(55 n) / √n → 0` as `n → ∞`, hence `√(140n + 2) * log(55 n) / n → 0`. -/
theorem sqrt_mul_log_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ => ((Nat.sqrt (140 * n + 2) + 1 : ℕ) : ℝ) * Real.log (55 * (n : ℝ)) / (n : ℝ))
      atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => (1000 : ℝ) * ((n : ℝ) ^ (-(1 : ℝ) / 4))) atTop (nhds 0) := by
    have hr := tendsto_rpow_neg_atTop (show (0 : ℝ) < (1 : ℝ) / 4 by norm_num)
    have hcomp := (hr.comp tendsto_natCast_atTop_atTop).const_mul (1000 : ℝ)
    simpa [neg_div] using hcomp
  refine squeeze_zero' ?_ ?_ hinv
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have h55 : (1 : ℝ) ≤ 55 * (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hlog : 0 ≤ Real.log (55 * (n : ℝ)) := Real.log_nonneg h55
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnPos : (0 : ℝ) < (n : ℝ) := by linarith
    have hsqrt_le : ((Nat.sqrt (140 * n + 2) + 1 : ℕ) : ℝ) ≤ 14 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
      have hsq : (Nat.sqrt (140 * n + 2)) ^ 2 ≤ 140 * n + 2 := by
        rw [sq]; exact Nat.sqrt_le _
      have h142 : (140 * n + 2 : ℝ) ≤ 144 * (n : ℝ) := by linarith
      have hsqR : ((Nat.sqrt (140 * n + 2) : ℕ) : ℝ) ^ 2 ≤ (12 * Real.sqrt (n : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hnPos.le]
        have : ((Nat.sqrt (140 * n + 2) : ℕ) : ℝ) ^ 2 ≤ (140 * n + 2 : ℝ) := by exact_mod_cast hsq
        linarith
      have hs1 : ((Nat.sqrt (140 * n + 2) : ℕ) : ℝ) ≤ 12 * Real.sqrt (n : ℝ) := by
        nlinarith [Real.sqrt_nonneg (n : ℝ)]
      have h1le : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
        rw [Real.le_sqrt (by norm_num) hnPos.le]; linarith
      rw [Real.sqrt_eq_rpow] at hs1 h1le
      push_cast
      linarith
    have hlog_le : Real.log (55 * (n : ℝ)) ≤ 16 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
      have h1 := log_le_four_mul_rpow_quarter (show 0 < 55 * (n : ℝ) by positivity)
      rw [Real.mul_rpow (by norm_num) hnPos.le] at h1
      have h55_4 : (55 : ℝ) ^ ((1 : ℝ) / 4) ≤ 4 := by
        have h4 : (55 : ℝ) ≤ (4 : ℝ) ^ (4 : ℝ) := by norm_num
        calc
          (55 : ℝ) ^ ((1 : ℝ) / 4) ≤ ((4 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow (by norm_num) h4 (by norm_num)
          _ = (4 : ℝ) ^ ((4 : ℝ) * ((1 : ℝ) / 4)) := (Real.rpow_mul (by norm_num) _ _).symm
          _ = 4 := by norm_num
      have hn4 : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by positivity
      nlinarith
    have hlog_nn : 0 ≤ Real.log (55 * (n : ℝ)) :=
      Real.log_nonneg (by linarith)
    have hnum : ((Nat.sqrt (140 * n + 2) + 1 : ℕ) : ℝ) * Real.log (55 * (n : ℝ)) ≤
        224 * ((n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 4)) := by
      have := mul_le_mul hsqrt_le hlog_le hlog_nn (by positivity)
      linarith
    have hrpow_comb : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 4) / (n : ℝ) =
        (n : ℝ) ^ (-(1 : ℝ) / 4) := by
      rw [← Real.rpow_add hnPos]
      conv_lhs => rhs; rw [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_sub hnPos]
      congr 1; norm_num
    have hdiv : ((Nat.sqrt (140 * n + 2) + 1 : ℕ) : ℝ) * Real.log (55 * (n : ℝ)) / (n : ℝ) ≤
        224 * (n : ℝ) ^ (-(1 : ℝ) / 4) := by
      rw [div_le_iff₀ hnPos]
      have hmul : 224 * (n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) =
          224 * ((n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 4)) := by
        rw [← hrpow_comb]
        field_simp [hnPos.ne']
      linarith
    have hnneg : 0 ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) := by positivity
    linarith

/-- Any sub-range of `p^2 ≤ 140n + 2` contributes `0` to the `sixNorm n` rate. -/
theorem sixSqrtPrimes_rate_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (∑ p ∈ (sixCutoffPrimes n).filter (fun p => p ^ 2 ≤ 140 * n + 2),
        sixPrimeExpReal n p * Real.log (p : ℝ)) / sixNorm n) atTop (nhds 0) := by
  have htop : Tendsto (fun n : ℕ =>
      (270 / 750 : ℝ) * (((Nat.sqrt (140 * n + 2) + 1 : ℕ) : ℝ) * Real.log (55 * (n : ℝ)) / (n : ℝ)))
      atTop (nhds 0) := by
    simpa using sqrt_mul_log_div_nat_tendsto_zero.const_mul (270 / 750 : ℝ)
  refine squeeze_zero' ?_ ?_ htop
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n _
    apply div_nonneg _ (sixNorm_nonneg n)
    apply Finset.sum_nonneg
    intro p hp
    have hpr : p.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
    exact mul_nonneg (sixPrimeExpReal_nonneg n p)
      (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hcard : ((sixCutoffPrimes n).filter (fun p => p ^ 2 ≤ 140 * n + 2)).card ≤
        Nat.sqrt (140 * n + 2) + 1 := by
      have hsub : (sixCutoffPrimes n).filter (fun p => p ^ 2 ≤ 140 * n + 2) ⊆
          Finset.range (Nat.sqrt (140 * n + 2) + 1) := by
        intro p hp
        have hsq : p ^ 2 ≤ 140 * n + 2 := (Finset.mem_filter.mp hp).2
        have hle : p ≤ Nat.sqrt (140 * n + 2) := Nat.le_sqrt.mpr (by simpa [sq] using hsq)
        exact Finset.mem_range.mpr (by omega)
      exact (Finset.card_le_card hsub).trans (by rw [Finset.card_range])
    have hsum : (∑ p ∈ (sixCutoffPrimes n).filter (fun p => p ^ 2 ≤ 140 * n + 2),
        sixPrimeExpReal n p * Real.log (p : ℝ)) ≤
        ((Nat.sqrt (140 * n + 2) + 1 : ℕ) : ℝ) * (270 * (n : ℝ) * Real.log (55 * (n : ℝ))) := by
      calc
        _ ≤ ∑ _p ∈ (sixCutoffPrimes n).filter (fun p => p ^ 2 ≤ 140 * n + 2),
              (270 * (n : ℝ) * Real.log (55 * (n : ℝ))) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpr : p.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
          have : Fact p.Prime := ⟨hpr⟩
          exact sixPrimeExpReal_mul_log_le_universal n p hn
        _ = (((sixCutoffPrimes n).filter (fun p => p ^ 2 ≤ 140 * n + 2)).card : ℝ) *
              (270 * (n : ℝ) * Real.log (55 * (n : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((Nat.sqrt (140 * n + 2) + 1 : ℕ) : ℝ) *
              (270 * (n : ℝ) * Real.log (55 * (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
          have : (1 : ℝ) ≤ 55 * (n : ℝ) := by
            have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            linarith
          have := Real.log_nonneg this
          positivity
    rw [sixNorm_eq]
    have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h750 : 0 < 750 * (n : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ h750]
    calc
      _ ≤ ((Nat.sqrt (140 * n + 2) + 1 : ℕ) : ℝ) * (270 * (n : ℝ) * Real.log (55 * (n : ℝ))) := hsum
      _ = (270 / 750 : ℝ) * (((Nat.sqrt (140 * n + 2) + 1 : ℕ) : ℝ) *
            Real.log (55 * (n : ℝ)) / (n : ℝ)) * (750 * (n : ℝ) ^ 2) := by
        field_simp [hnPos.ne']

/-- Any bounded-cardinality family of exceptional primes (`card ≤ M`) with `p^2 > 140n + 2`
contributes `0` to the `sixNorm n` rate. -/
theorem sixExceptionalPrimes_rate_tendsto_zero (E : ℕ → Finset ℕ) (M : ℕ)
    (hsub : ∀ n, E n ⊆ sixCutoffPrimes n)
    (hcard : ∀ᶠ n : ℕ in atTop, (E n).card ≤ M) :
    Tendsto (fun n : ℕ =>
      (∑ p ∈ E n, sixPrimeExpReal n p * Real.log (p : ℝ)) / sixNorm n) atTop (nhds 0) := by
  have hlog_div : Tendsto (fun n : ℕ =>
      (270 * (M : ℝ) / 750 : ℝ) * (Real.log (55 * (n : ℝ)) / (n : ℝ))) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.log (55 * (n : ℝ)) / (n : ℝ)) atTop (nhds 0) := by
      refine squeeze_zero' ?_ ?_ sqrt_mul_log_div_nat_tendsto_zero
      · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
        have : (1 : ℝ) ≤ 55 * (n : ℝ) := by
          have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith
        have := Real.log_nonneg this
        positivity
      · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
        have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have h1 : (1 : ℝ) ≤ ((Nat.sqrt (140 * n + 2) + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_pos _
        have hlog : 0 ≤ Real.log (55 * (n : ℝ)) := by
          apply Real.log_nonneg
          have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith
        exact div_le_div_of_nonneg_right (by nlinarith) hnPos.le
    simpa using h1.const_mul (270 * (M : ℝ) / 750 : ℝ)
  refine squeeze_zero' ?_ ?_ hlog_div
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n _
    apply div_nonneg _ (sixNorm_nonneg n)
    apply Finset.sum_nonneg
    intro p hp
    have hpr : p.Prime := (Nat.mem_primesLE.mp (hsub n hp)).2
    exact mul_nonneg (sixPrimeExpReal_nonneg n p)
      (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
  · filter_upwards [hcard, eventually_ge_atTop (1 : ℕ)] with n hc hn
    have hsum : (∑ p ∈ E n, sixPrimeExpReal n p * Real.log (p : ℝ)) ≤
        (M : ℝ) * (270 * (n : ℝ) * Real.log (55 * (n : ℝ))) := by
      calc
        _ ≤ ∑ _p ∈ E n, (270 * (n : ℝ) * Real.log (55 * (n : ℝ))) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpr : p.Prime := (Nat.mem_primesLE.mp (hsub n hp)).2
          have : Fact p.Prime := ⟨hpr⟩
          exact sixPrimeExpReal_mul_log_le_universal n p hn
        _ = ((E n).card : ℝ) * (270 * (n : ℝ) * Real.log (55 * (n : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (M : ℝ) * (270 * (n : ℝ) * Real.log (55 * (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
          have : (1 : ℝ) ≤ 55 * (n : ℝ) := by
            have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            linarith
          have := Real.log_nonneg this
          positivity
    rw [sixNorm_eq]
    have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h750 : 0 < 750 * (n : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ h750]
    calc
      _ ≤ (M : ℝ) * (270 * (n : ℝ) * Real.log (55 * (n : ℝ))) := hsum
      _ = (270 * (M : ℝ) / 750 : ℝ) * (Real.log (55 * (n : ℝ)) / (n : ℝ)) *
            (750 * (n : ℝ) ^ 2) := by
        field_simp [hnPos.ne']

/-- Number of primes `p` within distance `K` of `r * n` for a finite set of rational walls `W`
is bounded by `(2 * K + 1) * W.card`. -/
theorem wallWindow_card_le (W : Finset ℚ) (K n : ℕ) :
    ((sixCutoffPrimes n).filter (fun p : ℕ => ∃ r ∈ W, |(p : ℚ) - r * (n : ℚ)| ≤ (K : ℚ))).card ≤
      (2 * K + 1) * W.card := by
  classical
  let win : ℚ → Finset ℕ := fun r =>
    Finset.Icc (⌊r * (n : ℚ)⌋.toNat - K) (⌈r * (n : ℚ)⌉.toNat + K)
  have hsub : (sixCutoffPrimes n).filter
      (fun p : ℕ => ∃ r ∈ W, |(p : ℚ) - r * (n : ℚ)| ≤ (K : ℚ)) ⊆
      W.biUnion (fun r => Finset.Icc (⌊r * (n : ℚ) - (K : ℚ)⌋.toNat) (⌊r * (n : ℚ) + (K : ℚ)⌋.toNat)) := by
    intro p hp
    obtain ⟨r, hrW, hdist⟩ := (Finset.mem_filter.mp hp).2
    rw [Finset.mem_biUnion]
    refine ⟨r, hrW, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · rw [abs_sub_le_iff] at hdist
      have h1 : r * (n : ℚ) - (K : ℚ) ≤ (p : ℚ) := by linarith
      have h2 : ⌊r * (n : ℚ) - (K : ℚ)⌋ ≤ (p : ℤ) := Int.floor_le_iff.mpr (by
        have : (p : ℚ) < ((p : ℤ) + 1 : ℚ) := by push_cast; linarith
        exact h1.trans_lt this)
      omega
    · rw [abs_sub_le_iff] at hdist
      have h1 : (p : ℚ) ≤ r * (n : ℚ) + (K : ℚ) := by linarith
      have h2 : (p : ℤ) ≤ ⌊r * (n : ℚ) + (K : ℚ)⌋ := Int.le_floor.mpr (by exact_mod_cast h1)
      omega
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  calc
    ∑ r ∈ W, (Finset.Icc (⌊r * (n : ℚ) - (K : ℚ)⌋.toNat) (⌊r * (n : ℚ) + (K : ℚ)⌋.toNat)).card
        ≤ ∑ _r ∈ W, (2 * K + 1) := by
      apply Finset.sum_le_sum
      intro r _
      rw [Nat.card_Icc]
      have hdiff : ⌊r * (n : ℚ) + (K : ℚ)⌋ = ⌊r * (n : ℚ) - (K : ℚ)⌋ + (2 * (K : ℤ)) := by
        have heq : r * (n : ℚ) + (K : ℚ) = (r * (n : ℚ) - (K : ℚ)) + ((2 * (K : ℤ) : ℤ) : ℚ) := by
          push_cast; ring
        rw [heq, Int.floor_add_intCast]
      omega
    _ = (2 * K + 1) * W.card := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## Tiny prime band (`p ≤ ε * n`) rate bound `(18 / 50) * ε` -/

/-- The tiny prime band `p ≤ ε * n` contributes at most `(18 / 50) * ε + o(1)` to `sixNorm n`. -/
theorem sixTinyPrimes_rate_eventually_le (ε : ℝ) (hε : 0 < ε) (_hε55 : ε ≤ 55) :
    ∀ δ > 0, ∀ᶠ n : ℕ in atTop,
      (∑ p ∈ (sixCutoffPrimes n).filter (fun p : ℕ => (p : ℝ) ≤ ε * (n : ℝ)),
        sixPrimeExpReal n p * Real.log (p : ℝ)) / sixNorm n ≤ (18 / 50 : ℝ) * ε + δ := by
  intro δ hδ
  have hsqrt := Metric.tendsto_nhds.mp sixSqrtPrimes_rate_tendsto_zero (δ / 2) (by positivity)
  have htheta : Tendsto (fun n : ℕ => (270 / 750 : ℝ) * (Chebyshev.theta (ε * (n : ℝ)) / (n : ℝ)))
      atTop (nhds ((18 / 50 : ℝ) * ε)) := by
    have h1 := (OddZetaPNT.scaled_theta_div_nat_limit ε hε).const_mul (270 / 750 : ℝ)
    convert h1 using 1
    congr 1; ring
  have hth := Metric.tendsto_nhds.mp htheta (δ / 2) (by positivity)
  filter_upwards [hsqrt, hth, eventually_ge_atTop (1 : ℕ)] with n hsq_ev hth_ev hn
  have hsplit : (∑ p ∈ (sixCutoffPrimes n).filter (fun p : ℕ => (p : ℝ) ≤ ε * (n : ℝ)),
      sixPrimeExpReal n p * Real.log (p : ℝ)) ≤
      (∑ p ∈ (sixCutoffPrimes n).filter (fun p => p ^ 2 ≤ 140 * n + 2),
        sixPrimeExpReal n p * Real.log (p : ℝ)) +
      (∑ p ∈ ((sixCutoffPrimes n).filter (fun p : ℕ => (p : ℝ) ≤ ε * (n : ℝ))).filter
          (fun p => 140 * n + 2 < p ^ 2),
        sixPrimeExpReal n p * Real.log (p : ℝ)) := by
    have hpart := (Finset.sum_filter_add_sum_filter_not
      ((sixCutoffPrimes n).filter (fun p : ℕ => (p : ℝ) ≤ ε * (n : ℝ)))
      (fun p => p ^ 2 ≤ 140 * n + 2)
      (fun p => sixPrimeExpReal n p * Real.log (p : ℝ))).symm
    rw [hpart]
    apply add_le_add
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Finset.mem_filter] at hp ⊢
        exact ⟨(Finset.mem_filter.mp hp.1).1, hp.2⟩
      · intro p hp _
        have hpr : p.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
        exact mul_nonneg (sixPrimeExpReal_nonneg n p)
          (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
    · apply le_of_eq
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext p; simp only [Finset.mem_filter, not_le]
  have hmid : (∑ p ∈ ((sixCutoffPrimes n).filter (fun p : ℕ => (p : ℝ) ≤ ε * (n : ℝ))).filter
      (fun p => 140 * n + 2 < p ^ 2),
      sixPrimeExpReal n p * Real.log (p : ℝ)) ≤
      270 * (n : ℝ) * Chebyshev.theta (ε * (n : ℝ)) := by
    have hsub : ((sixCutoffPrimes n).filter (fun p : ℕ => (p : ℝ) ≤ ε * (n : ℝ))).filter
        (fun p => 140 * n + 2 < p ^ 2) ⊆ Nat.primesLE ⌊ε * (n : ℝ)⌋₊ := by
      intro p hp
      have hp1 := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
      have hpr : p.Prime := (Nat.mem_primesLE.mp hp1.1).2
      exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (by positivity)).mpr hp1.2, hpr⟩
    calc
      _ ≤ ∑ p ∈ ((sixCutoffPrimes n).filter (fun p : ℕ => (p : ℝ) ≤ ε * (n : ℝ))).filter
            (fun p => 140 * n + 2 < p ^ 2),
            (270 * (n : ℝ)) * Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hsq' : 140 * n + 2 < p ^ 2 := (Finset.mem_filter.mp hp).2
        have hpr : p.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2
        have : Fact p.Prime := ⟨hpr⟩
        exact mul_le_mul_of_nonneg_right (sixPrimeExpReal_le_270n n p hsq')
          (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
      _ ≤ ∑ p ∈ Nat.primesLE ⌊ε * (n : ℝ)⌋₊, (270 * (n : ℝ)) * Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp _
        have hpr : p.Prime := (Nat.mem_primesLE.mp hp).2
        exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
      _ = 270 * (n : ℝ) * ∑ p ∈ Nat.primesLE ⌊ε * (n : ℝ)⌋₊, Real.log (p : ℝ) := by
        rw [Finset.mul_sum]
      _ = 270 * (n : ℝ) * Chebyshev.theta (ε * (n : ℝ)) := by
        rw [Chebyshev.theta_eq_sum_primesLE]
  have hnorm_pos : 0 < sixNorm n := by
    rw [sixNorm_eq]
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hmid_div : 270 * (n : ℝ) * Chebyshev.theta (ε * (n : ℝ)) / sixNorm n =
      (270 / 750 : ℝ) * (Chebyshev.theta (ε * (n : ℝ)) / (n : ℝ)) := by
    rw [sixNorm_eq]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp [hnR]
  rw [Real.dist_eq, sub_zero] at hsq_ev
  rw [Real.dist_eq] at hth_ev
  have hsq_le : (∑ p ∈ (sixCutoffPrimes n).filter (fun p => p ^ 2 ≤ 140 * n + 2),
      sixPrimeExpReal n p * Real.log (p : ℝ)) / sixNorm n ≤ δ / 2 :=
    (le_abs_self _).trans hsq_ev.le
  have hth_le : (270 / 750 : ℝ) * (Chebyshev.theta (ε * (n : ℝ)) / (n : ℝ)) ≤
      (18 / 50 : ℝ) * ε + δ / 2 := by
    have := (le_abs_self _).trans hth_ev.le
    linarith
  have hdiv_all : (∑ p ∈ (sixCutoffPrimes n).filter (fun p : ℕ => (p : ℝ) ≤ ε * (n : ℝ)),
      sixPrimeExpReal n p * Real.log (p : ℝ)) / sixNorm n ≤
      (∑ p ∈ (sixCutoffPrimes n).filter (fun p => p ^ 2 ≤ 140 * n + 2),
        sixPrimeExpReal n p * Real.log (p : ℝ)) / sixNorm n +
      270 * (n : ℝ) * Chebyshev.theta (ε * (n : ℝ)) / sixNorm n := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (hsplit.trans (add_le_add le_rfl hmid)) hnorm_pos.le
  rw [hmid_div] at hdiv_all
  linarith

/-! ## Band-splitting identities and PNT continuous/perturbed wrappers -/

/-- Exact partition of `sixPrimeCost n` into prefix `[0, ε]` + periodic `(ε, cut]` + high `(cut, 55]`. -/
theorem sixPrimeCost_eq_three_bands (n : ℕ) {ε cut : ℝ}
    (hε : 0 ≤ ε) (hεcut : ε ≤ cut) (hcut55 : cut ≤ 55) :
    sixPrimeCost n =
      (∑ p ∈ (sixCutoffPrimes n).filter (fun p : ℕ => (p : ℝ) ≤ ε * (n : ℝ)),
        sixPrimeExpReal n p * Real.log (p : ℝ)) +
      sixBandPrimeCost n ε cut +
      sixBandPrimeCost n cut 55 := by
  classical
  have h1 : (sixCutoffPrimes n).filter (fun p : ℕ => ε * (n : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ cut * (n : ℝ)) =
      (Nat.primesLE ⌊cut * (n : ℝ)⌋₊).filter (fun p : ℕ => ε * (n : ℝ) < (p : ℝ)) := by
    ext p
    simp only [Finset.mem_filter, sixCutoffPrimes, Nat.mem_primesLE,
      Nat.le_floor_iff (mul_nonneg (hε.trans hεcut) (Nat.cast_nonneg n))]
    constructor
    · rintro ⟨⟨_, hpr⟩, hlo, hhi⟩; exact ⟨⟨hhi, hpr⟩, hlo⟩
    · rintro ⟨⟨hhi, hpr⟩, hlo⟩
      refine ⟨⟨?_, hpr⟩, hlo, hhi⟩
      have : (p : ℝ) ≤ 55 * (n : ℝ) := hhi.trans (mul_le_mul_of_nonneg_right hcut55 (Nat.cast_nonneg n))
      exact_mod_cast this
  have h2 : (sixCutoffPrimes n).filter (fun p : ℕ => cut * (n : ℝ) < (p : ℝ)) =
      (Nat.primesLE ⌊(55 : ℝ) * (n : ℝ)⌋₊).filter (fun p : ℕ => cut * (n : ℝ) < (p : ℝ)) := by
    ext p
    simp only [Finset.mem_filter, sixCutoffPrimes, Nat.mem_primesLE,
      Nat.le_floor_iff (mul_nonneg (by norm_num : (0 : ℝ) ≤ 55) (Nat.cast_nonneg n))]
    constructor
    · rintro ⟨⟨h55, hpr⟩, hlo⟩; exact ⟨⟨by exact_mod_cast h55, hpr⟩, hlo⟩
    · rintro ⟨⟨h55, hpr⟩, hlo⟩; exact ⟨⟨by exact_mod_cast h55, hpr⟩, hlo⟩
  unfold sixPrimeCost sixBandPrimeCost
  rw [← h1, ← h2]
  have hsplit1 := (Finset.sum_filter_add_sum_filter_not (sixCutoffPrimes n)
    (fun p : ℕ => (p : ℝ) ≤ ε * (n : ℝ))
    (fun p => sixPrimeExpReal n p * Real.log (p : ℝ))).symm
  rw [hsplit1, add_assoc]
  congr 1
  have hsplit2 := (Finset.sum_filter_add_sum_filter_not
    ((sixCutoffPrimes n).filter (fun p : ℕ => ¬(p : ℝ) ≤ ε * (n : ℝ)))
    (fun p : ℕ => (p : ℝ) ≤ cut * (n : ℝ))
    (fun p => sixPrimeExpReal n p * Real.log (p : ℝ))).symm
  rw [hsplit2]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p; simp only [Finset.mem_filter, not_le]; tauto
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p; simp only [Finset.mem_filter, not_le]
    constructor
    · rintro ⟨⟨hp, _⟩, hcut⟩; exact ⟨hp, hcut⟩
    · rintro ⟨hp, hcut⟩
      refine ⟨⟨hp, ?_⟩, hcut⟩
      exact (mul_le_mul_of_nonneg_right hεcut (Nat.cast_nonneg n)).trans_lt hcut

/-- Additivity of `sixBandPrimeCost` on adjacent intervals `(a, b]` and `(b, c]`. -/
theorem sixBandPrimeCost_add (n : ℕ) {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    sixBandPrimeCost n a c = sixBandPrimeCost n a b + sixBandPrimeCost n b c := by
  classical
  unfold sixBandPrimeCost
  have hsplit := (Finset.sum_filter_add_sum_filter_not
    ((Nat.primesLE ⌊c * (n : ℝ)⌋₊).filter (fun p : ℕ => a * (n : ℝ) < (p : ℝ)))
    (fun p : ℕ => (p : ℝ) ≤ b * (n : ℝ))
    (fun p => sixPrimeExpReal n p * Real.log (p : ℝ))).symm
  rw [hsplit]
  have hb0 : 0 ≤ b * (n : ℝ) := mul_nonneg (ha.trans hab) (Nat.cast_nonneg n)
  have hc0 : 0 ≤ c * (n : ℝ) := mul_nonneg ((ha.trans hab).trans hbc) (Nat.cast_nonneg n)
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.le_floor_iff hb0, Nat.le_floor_iff hc0]
    constructor
    · rintro ⟨⟨⟨_, hpr⟩, ha'⟩, hb'⟩; exact ⟨⟨hb', hpr⟩, ha'⟩
    · rintro ⟨⟨hb', hpr⟩, ha'⟩
      exact ⟨⟨⟨hb'.trans (mul_le_mul_of_nonneg_right hbc (Nat.cast_nonneg n)), hpr⟩, ha'⟩, hb'⟩
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.le_floor_iff hc0, not_le]
    constructor
    · rintro ⟨⟨⟨hc', hpr⟩, _⟩, hb'⟩; exact ⟨⟨hc', hpr⟩, hb'⟩
    · rintro ⟨⟨hc', hpr⟩, hb'⟩
      exact ⟨⟨⟨hc', hpr⟩, (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n)).trans_lt hb'⟩, hb'⟩

/-- Bridge from `OddZetaPNT.primeBandCost_bounded_perturbation_limit` + continuous nonnegative
weight + bounded exceptional primes to an asymptotic upper rate on `sixBandPrimeCost n a b / sixNorm n`. -/
theorem sixBandPrimeCost_rate_of_continuous_majorant
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (_hb55 : b ≤ 55)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
    (hf0 : ∀ x ∈ Set.Icc a b, 0 ≤ f x)
    (C : ℝ) (hC0 : 0 ≤ C) (E : ℕ → Finset ℕ) (M : ℕ)
    (hEsub : ∀ n, E n ⊆ sixCutoffPrimes n)
    (hEcard : ∀ᶠ n : ℕ in atTop, (E n).card ≤ M)
    (hdom : ∀ᶠ n : ℕ in atTop,
      ∀ p ∈ (Nat.primesLE ⌊b * (n : ℝ)⌋₊).filter (fun p : ℕ => a * (n : ℝ) < (p : ℝ)),
        p ∉ E n →
        sixPrimeExpReal n p ≤ (n : ℝ) * f ((p : ℝ) / (n : ℝ)) + C) :
    ∀ δ > 0, ∀ᶠ n : ℕ in atTop,
      sixBandPrimeCost n a b / sixNorm n ≤ (∫ x in a..b, f x) / 750 + δ := by
  intro δ hδ
  classical
  let L : ℝ := ∫ x in a..b, f x
  let w : ℕ → ℕ → ℝ := fun n p => (n : ℝ) * f ((p : ℝ) / (n : ℝ)) + C
  have hw_lim : Tendsto (fun n : ℕ => OddZetaPNT.primeBandCost w n a b / 750)
      atTop (nhds (L / 750)) := by
    have hcont : Tendsto (fun n : ℕ => OddZetaPNT.primeWeightedInterval n f a b)
        atTop (nhds L) :=
      OddZetaPNT.primeWeightedInterval_continuous_limit f a b ha hab hf
    have hpert : Tendsto (fun n : ℕ => OddZetaPNT.primeBandCost w n a b) atTop (nhds L) := by
      apply OddZetaPNT.primeBandCost_bounded_perturbation_limit w f a b |C| L ha hab hcont
      filter_upwards with n p _
      dsimp [w]; simp
    exact hpert.div_const 750
  have hexc_lim := sixExceptionalPrimes_rate_tendsto_zero E M hEsub hEcard
  have hw_ev := Metric.tendsto_nhds.mp hw_lim (δ / 2) (by positivity)
  have hexc_ev := Metric.tendsto_nhds.mp hexc_lim (δ / 2) (by positivity)
  filter_upwards [hdom, hw_ev, hexc_ev, eventually_ge_atTop (1 : ℕ)] with n hdn hwe hee hn
  have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnorm_pos : 0 < sixNorm n := by rw [sixNorm_eq]; positivity
  let S := (Nat.primesLE ⌊b * (n : ℝ)⌋₊).filter (fun p : ℕ => a * (n : ℝ) < (p : ℝ))
  have hw_nonneg : ∀ p ∈ S, 0 ≤ w n p * Real.log (p : ℝ) := by
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    have hpr : p.Prime := (Nat.mem_primesLE.mp hmem.1).2
    have hbp : (p : ℝ) ≤ b * (n : ℝ) :=
      (Nat.le_floor_iff (mul_nonneg (ha.le.trans hab) hnPos.le)).mp (Nat.mem_primesLE.mp hmem.1).1
    have hx : (p : ℝ) / (n : ℝ) ∈ Set.Icc a b :=
      ⟨((lt_div_iff₀ hnPos).mpr hmem.2).le, (div_le_iff₀ hnPos).mpr hbp⟩
    have hfval : 0 ≤ f ((p : ℝ) / (n : ℝ)) := hf0 _ hx
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
    dsimp [w]
    positivity
  have hsum_le : sixBandPrimeCost n a b ≤
      (∑ p ∈ S, w n p * Real.log (p : ℝ)) +
      (∑ p ∈ E n, sixPrimeExpReal n p * Real.log (p : ℝ)) := by
    unfold sixBandPrimeCost
    have hpart := (Finset.sum_filter_add_sum_filter_not S (fun p => p ∈ E n)
      (fun p => sixPrimeExpReal n p * Real.log (p : ℝ))).symm
    rw [hpart, add_comm]
    apply add_le_add
    · refine (Finset.sum_le_sum (fun p hp => ?_)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ S) (fun p hp _ => hw_nonneg p hp))
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      have hpE : p ∉ E n := (Finset.mem_filter.mp hp).2
      have hpr : p.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hpS).1).2
      exact mul_le_mul_of_nonneg_right (hdn p hpS hpE)
        (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
    · apply Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).2)
      intro p hp _
      have hpr : p.Prime := (Nat.mem_primesLE.mp (hEsub n hp)).2
      exact mul_nonneg (sixPrimeExpReal_nonneg n p)
        (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
  have hdiv_w : (∑ p ∈ S, w n p * Real.log (p : ℝ)) / sixNorm n =
      OddZetaPNT.primeBandCost w n a b / 750 := by
    rw [sixNorm_eq]
    unfold OddZetaPNT.primeBandCost
    have hn2 : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hnPos.ne'
    dsimp [S]
    field_simp [hn2]
  rw [Real.dist_eq] at hwe hee
  rw [sub_zero] at hee
  have hwe' : OddZetaPNT.primeBandCost w n a b / 750 ≤ L / 750 + δ / 2 := by
    have := (le_abs_self _).trans hwe.le
    linarith
  have hee' : (∑ p ∈ E n, sixPrimeExpReal n p * Real.log (p : ℝ)) / sixNorm n ≤ δ / 2 :=
    (le_abs_self _).trans hee.le
  calc
    sixBandPrimeCost n a b / sixNorm n
        ≤ ((∑ p ∈ S, w n p * Real.log (p : ℝ)) +
            (∑ p ∈ E n, sixPrimeExpReal n p * Real.log (p : ℝ))) / sixNorm n :=
      div_le_div_of_nonneg_right hsum_le hnorm_pos.le
    _ = (∑ p ∈ S, w n p * Real.log (p : ℝ)) / sixNorm n +
        (∑ p ∈ E n, sixPrimeExpReal n p * Real.log (p : ℝ)) / sixNorm n := add_div _ _ _
    _ = OddZetaPNT.primeBandCost w n a b / 750 +
        (∑ p ∈ E n, sixPrimeExpReal n p * Real.log (p : ℝ)) / sixNorm n := by rw [hdiv_w]
    _ ≤ L / 750 + δ := by linarith

/-- Finite piecewise tile sum bound: if `(a, b]` is partitioned by finitely many tiles `i ∈ s`
each admitting a continuous nonnegative majorant `f i`, then `sixBandPrimeCost n a b / sixNorm n`
has asymptotic upper rate `≤ (∑ i ∈ s, ∫ x in a_i..b_i, f_i x) / 750`. -/
theorem sixBandPrimeCost_rate_of_piecewise_majorant {ι : Type*} (s : Finset ι)
    (a b : ℝ) (_ha : 0 < a) (_hab : a ≤ b)
    (lo hi : ι → ℝ) (f : ι → ℝ → ℝ)
    (hlo : ∀ i ∈ s, 0 < lo i) (hlohi : ∀ i ∈ s, lo i ≤ hi i) (_hhi55 : ∀ i ∈ s, hi i ≤ 55)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (Set.Icc (lo i) (hi i)))
    (hf0 : ∀ i ∈ s, ∀ x ∈ Set.Icc (lo i) (hi i), 0 ≤ f i x)
    (C : ℝ) (hC0 : 0 ≤ C) (E : ℕ → Finset ℕ) (M : ℕ)
    (hEsub : ∀ n, E n ⊆ sixCutoffPrimes n)
    (hEcard : ∀ᶠ n : ℕ in atTop, (E n).card ≤ M)
    (hcover : ∀ n : ℕ, 0 < n →
      ∀ p ∈ (Nat.primesLE ⌊b * (n : ℝ)⌋₊).filter (fun p : ℕ => a * (n : ℝ) < (p : ℝ)),
        p ∉ E n →
        ∃ i ∈ s, lo i * (n : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ hi i * (n : ℝ) ∧
          sixPrimeExpReal n p ≤ (n : ℝ) * f i ((p : ℝ) / (n : ℝ)) + C) :
    ∀ δ > 0, ∀ᶠ n : ℕ in atTop,
      sixBandPrimeCost n a b / sixNorm n ≤ (∑ i ∈ s, ∫ x in lo i..hi i, f i x) / 750 + δ := by
  intro δ hδ
  classical
  let w : ι → ℕ → ℕ → ℝ := fun i n p => (n : ℝ) * f i ((p : ℝ) / (n : ℝ)) + C
  have hsum_lim : Tendsto (fun n : ℕ =>
      (∑ i ∈ s, OddZetaPNT.primeBandCost (w i) n (lo i) (hi i)) / 750)
      atTop (nhds ((∑ i ∈ s, ∫ x in lo i..hi i, f i x) / 750)) := by
    apply Tendsto.div_const
    apply tendsto_finsetSum
    intro i hi'
    have hcont := OddZetaPNT.primeWeightedInterval_continuous_limit (f i) (lo i) (hi i)
      (hlo i hi') (hlohi i hi') (hf i hi')
    apply OddZetaPNT.primeBandCost_bounded_perturbation_limit (w i) (f i) (lo i) (hi i) |C| _
      (hlo i hi') (hlohi i hi') hcont
    filter_upwards with n p _
    dsimp [w]; simp
  have hexc_lim := sixExceptionalPrimes_rate_tendsto_zero E M hEsub hEcard
  have hw_ev := Metric.tendsto_nhds.mp hsum_lim (δ / 2) (by positivity)
  have hexc_ev := Metric.tendsto_nhds.mp hexc_lim (δ / 2) (by positivity)
  filter_upwards [hw_ev, hexc_ev, eventually_ge_atTop (1 : ℕ)] with n hwe hee hn
  have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnorm_pos : 0 < sixNorm n := by rw [sixNorm_eq]; positivity
  let S := (Nat.primesLE ⌊b * (n : ℝ)⌋₊).filter (fun p : ℕ => a * (n : ℝ) < (p : ℝ))
  let Si : ι → Finset ℕ := fun i =>
    (Nat.primesLE ⌊hi i * (n : ℝ)⌋₊).filter (fun p : ℕ => lo i * (n : ℝ) < (p : ℝ))
  have hw_nonneg : ∀ i ∈ s, ∀ p ∈ Si i, 0 ≤ w i n p * Real.log (p : ℝ) := by
    intro i hi' p hp
    have hmem := Finset.mem_filter.mp hp
    have hpr : p.Prime := (Nat.mem_primesLE.mp hmem.1).2
    have hbp : (p : ℝ) ≤ hi i * (n : ℝ) :=
      (Nat.le_floor_iff (mul_nonneg ((hlo i hi').le.trans (hlohi i hi')) hnPos.le)).mp
        (Nat.mem_primesLE.mp hmem.1).1
    have hx : (p : ℝ) / (n : ℝ) ∈ Set.Icc (lo i) (hi i) :=
      ⟨((lt_div_iff₀ hnPos).mpr hmem.2).le, (div_le_iff₀ hnPos).mpr hbp⟩
    have hfval : 0 ≤ f i ((p : ℝ) / (n : ℝ)) := hf0 i hi' _ hx
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
    dsimp [w]; positivity
  have hsum_le : sixBandPrimeCost n a b ≤
      (∑ i ∈ s, ∑ p ∈ Si i, w i n p * Real.log (p : ℝ)) +
      (∑ p ∈ E n, sixPrimeExpReal n p * Real.log (p : ℝ)) := by
    unfold sixBandPrimeCost
    have hpart := (Finset.sum_filter_add_sum_filter_not S (fun p => p ∈ E n)
      (fun p => sixPrimeExpReal n p * Real.log (p : ℝ))).symm
    rw [hpart, add_comm]
    apply add_le_add
    · calc
        ∑ p ∈ S.filter (fun p => p ∉ E n), sixPrimeExpReal n p * Real.log (p : ℝ)
            ≤ ∑ p ∈ S.filter (fun p => p ∉ E n),
                ∑ i ∈ s, if p ∈ Si i then w i n p * Real.log (p : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro p hp
          have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
          have hpE : p ∉ E n := (Finset.mem_filter.mp hp).2
          have hpr : p.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hpS).1).2
          obtain ⟨i₀, hi₀, hlo', hhi', hdom'⟩ := hcover n hn p hpS hpE
          have hpSi : p ∈ Si i₀ := by
            rw [Finset.mem_filter, Nat.mem_primesLE]
            exact ⟨⟨(Nat.le_floor_iff (mul_nonneg ((hlo i₀ hi₀).le.trans (hlohi i₀ hi₀)) hnPos.le)).mpr hhi',
              hpr⟩, hlo'⟩
          have h1 : sixPrimeExpReal n p * Real.log (p : ℝ) ≤
              (if p ∈ Si i₀ then w i₀ n p * Real.log (p : ℝ) else 0) := by
            simp only [hpSi, ite_true]
            exact mul_le_mul_of_nonneg_right hdom'
              (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
          have h2 : (if p ∈ Si i₀ then w i₀ n p * Real.log (p : ℝ) else 0) ≤
              ∑ i ∈ s, if p ∈ Si i then w i n p * Real.log (p : ℝ) else 0 :=
            Finset.single_le_sum
              (f := fun i => if p ∈ Si i then w i n p * Real.log (p : ℝ) else 0)
              (fun i hi' => by
                split_ifs with hmem
                · exact hw_nonneg i hi' p hmem
                · exact le_rfl)
              hi₀
          exact h1.trans h2
        _ = ∑ i ∈ s, ∑ p ∈ S.filter (fun p => p ∉ E n),
              if p ∈ Si i then w i n p * Real.log (p : ℝ) else 0 := Finset.sum_comm
        _ ≤ ∑ i ∈ s, ∑ p ∈ Si i, w i n p * Real.log (p : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi'
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp; exact (Finset.mem_filter.mp hp).2
          · intro p hp _; exact hw_nonneg i hi' p hp
    · apply Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).2)
      intro p hp _
      have hpr : p.Prime := (Nat.mem_primesLE.mp (hEsub n hp)).2
      exact mul_nonneg (sixPrimeExpReal_nonneg n p)
        (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
  have hdiv_w : (∑ i ∈ s, ∑ p ∈ Si i, w i n p * Real.log (p : ℝ)) / sixNorm n =
      (∑ i ∈ s, OddZetaPNT.primeBandCost (w i) n (lo i) (hi i)) / 750 := by
    rw [sixNorm_eq, Finset.sum_div]
    unfold OddZetaPNT.primeBandCost
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    have hn2 : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hnPos.ne'
    dsimp [Si]
    field_simp [hn2]
  rw [Real.dist_eq] at hwe hee
  rw [sub_zero] at hee
  have hwe' : (∑ i ∈ s, OddZetaPNT.primeBandCost (w i) n (lo i) (hi i)) / 750 ≤
      (∑ i ∈ s, ∫ x in lo i..hi i, f i x) / 750 + δ / 2 := by
    have := (le_abs_self _).trans hwe.le
    linarith
  have hee' : (∑ p ∈ E n, sixPrimeExpReal n p * Real.log (p : ℝ)) / sixNorm n ≤ δ / 2 :=
    (le_abs_self _).trans hee.le
  calc
    sixBandPrimeCost n a b / sixNorm n
        ≤ ((∑ i ∈ s, ∑ p ∈ Si i, w i n p * Real.log (p : ℝ)) +
            (∑ p ∈ E n, sixPrimeExpReal n p * Real.log (p : ℝ))) / sixNorm n :=
      div_le_div_of_nonneg_right hsum_le hnorm_pos.le
    _ = (∑ i ∈ s, ∑ p ∈ Si i, w i n p * Real.log (p : ℝ)) / sixNorm n +
        (∑ p ∈ E n, sixPrimeExpReal n p * Real.log (p : ℝ)) / sixNorm n := add_div _ _ _
    _ = (∑ i ∈ s, OddZetaPNT.primeBandCost (w i) n (lo i) (hi i)) / 750 +
        (∑ p ∈ E n, sixPrimeExpReal n p * Real.log (p : ℝ)) / sixNorm n := by rw [hdiv_w]
    _ ≤ (∑ i ∈ s, ∫ x in lo i..hi i, f i x) / 750 + δ := by linarith

/-! ## Master 3-band assembly into `SixArithRateHypothesis` -/

/-- Master arithmetic rate assembly: combines the tiny prime band `p ≤ ε * n`,
the periodic band `ε * n < p ≤ cut * n`, and the middle/high band `cut * n < p ≤ 55 * n`. -/
theorem sixArithRate_of_three_bands
    (ε cut C₀ C₁ C_bound : ℝ)
    (hε : 0 < ε) (hεcut : ε ≤ cut) (hcut55 : cut ≤ 55)
    (hper : ∀ δ > 0, ∀ᶠ n : ℕ in atTop, sixBandPrimeCost n ε cut / sixNorm n ≤ C₀ + δ)
    (hhigh : ∀ δ > 0, ∀ᶠ n : ℕ in atTop, sixBandPrimeCost n cut 55 / sixNorm n ≤ C₁ + δ)
    (hsum : (18 / 50 : ℝ) * ε + C₀ + C₁ < C_bound) :
    SixArithRateHypothesis C_bound := by
  let δ : ℝ := (C_bound - ((18 / 50 : ℝ) * ε + C₀ + C₁)) / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  apply sixArithRate_of_eventually_primeCost_div C_bound
  filter_upwards [sixTinyPrimes_rate_eventually_le ε hε (hεcut.trans hcut55) δ hδ,
    hper δ hδ, hhigh δ hδ] with n h0 h1 h2
  rw [sixPrimeCost_eq_three_bands n hε.le hεcut hcut55, add_div, add_div]
  dsimp [δ] at h0 h1 h2
  linarith

end OddZetaSix
