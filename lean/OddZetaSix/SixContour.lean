import OddZetaSix.SixAssembly
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Half-Integer Vertical Contour Representation, Basis Change, and Normalization Rate

Establishes the analytic bridge for `local50-45-209` (`L = 50`, `h = 15 n`, `c = 1 / 50`,
abscissa `σ₀ = -n - 1/2`):
1. Complex evaluation `sixEntryComplex n i j`, analyticity on `{Re z > -(45 n + 1)}`,
   complex partial fractions, and vanishing of the divided fourth derivative at the
   protected integers `-40 n, ..., -1`.
2. Fifth cotangent kernel `sixContourKernel z = (π cot (π z))⁽⁴⁾ / 24`, exact closed form
   `π⁵ (cos³(π z) + 2 cos(π z)) / (3 sin⁵(π z))`, and uniform bounds on half-integer
   vertical and nonzero horizontal edges.
3. Clockwise rectangle residue theorem on `[σ₀, q + 1/2] × [-q, q]` and closing-edge
   vanishing as `q → ∞`, yielding the exact vertical line integral representation:
   `sixVerticalIntegral n i j = -(2 π i) * (sixFunctional n i j : ℂ)`.
4. Unit lower-triangular basis change `sixUnitBasisChange` to any even polynomial basis
   preserving `det (sixFunctional n)`, Cauchy–Schwarz + Leibniz determinant majorant by
   positive diagonal modulus moments, and scaling to monic polynomials in `((t + c_n) / (50 n))²`.
5. Exact quadratic normalization rate:
   `log (sixBasisNormalization n) / sixNorm n → 9 / 10 + 3 / 5 * log (5 / 3)`.

Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

noncomputable section
set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix

open Polynomial Finset Filter MeasureTheory Set Complex
open scoped BigOperators Topology Interval

/-! ## Section 1: Complex entry evaluation and protected fourth-derivative zeros -/

/-- Complex evaluation of `R_n(z) E_i(z + c_n) E_j(z + c_n)`. -/
def sixEntryComplex (n i j : ℕ) (z : ℂ) : ℂ :=
  aeval z (C (sixNormalization n) * sixNumerator n * centeredMultiplier n i j) /
    aeval z (sixDenominator n)

/-- Open pole-free half-plane `{z : ℂ | -(45 n + 1) < Re z}`. -/
def sixComplexHalfPlane (n : ℕ) : Set ℂ :=
  {z | -(45 * (n : ℝ) + 1) < z.re}

theorem isOpen_sixComplexHalfPlane (n : ℕ) : IsOpen (sixComplexHalfPlane n) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem six_pole_translate_complex_ne_zero (n k : ℕ) (hk : k ∈ sixPoleSet n)
    (z : ℂ) (hz : -(45 * (n : ℝ) + 1) < z.re) : z + (k : ℂ) ≠ 0 := by
  have hp : 0 < (z + (k : ℂ)).re := by
    simpa using six_pole_translate_pos n k hk z.re hz
  intro h
  simp [h] at hp

theorem six_denominator_complex_eval_ne_zero (n : ℕ) (z : ℂ)
    (hz : -(45 * (n : ℝ) + 1) < z.re) : aeval z (sixDenominator n) ≠ 0 := by
  rw [six_denominator_powers]
  simp only [map_prod, map_pow, map_add, aeval_X, map_natCast]
  exact Finset.prod_ne_zero_iff.mpr fun k hk =>
    pow_ne_zero _ (six_pole_translate_complex_ne_zero n k hk z hz)

theorem sixEntryComplex_analyticAt (n i j : ℕ) (z : ℂ)
    (hz : -(45 * (n : ℝ) + 1) < z.re) : AnalyticAt ℂ (sixEntryComplex n i j) z :=
  (analyticAt_id.aeval_polynomial
    (C (sixNormalization n) * sixNumerator n * centeredMultiplier n i j)).div
    (analyticAt_id.aeval_polynomial (sixDenominator n))
    (six_denominator_complex_eval_ne_zero n z hz)

private theorem aeval_complex_ofReal (P : ℚ[X]) (x : ℝ) :
    aeval (x : ℂ) P = ((aeval x P : ℝ) : ℂ) :=
  aeval_algHom_apply (Complex.ofRealAm.restrictScalars ℚ) x P

theorem sixEntryComplex_ofReal (n i j : ℕ) (x : ℝ) :
    sixEntryComplex n i j (x : ℂ) = (sixEntryReal n i j x : ℂ) := by
  simp only [sixEntryComplex, sixEntryReal, aeval_complex_ofReal, Complex.ofReal_div]

theorem sixPoleComplement_complex_eval (n k l : ℕ) (hk : k ∈ sixPoleSet n)
    (hl : l < sixPoleOrder n k) (z : ℂ) (hz : -(45 * (n : ℝ) + 1) < z.re) :
    aeval z (sixPoleComplement n k l) =
      aeval z (sixDenominator n) / (z + (k : ℂ)) ^ (l + 1) := by
  have h := congrArg (fun P : ℚ[X] => aeval z P) (sixPoleComplement_mul n k l hk hl)
  simp only [map_mul, map_pow, map_add, aeval_X, map_natCast] at h
  exact (eq_div_iff (pow_ne_zero _ (six_pole_translate_complex_ne_zero n k hk z hz))).mpr
    (by simpa only [mul_comm] using h)

theorem sixEntryComplex_partial_fractions (n : ℕ) (i j : Fin (rank n))
    (z : ℂ) (hz : -(45 * (n : ℝ) + 1) < z.re) :
    sixEntryComplex n i j z = ∑ k ∈ sixPoleSet n, ∑ l,
      (sixPrincipalCoefficients n i j k l : ℂ) / (z + (k : ℂ)) ^ (l.val + 1) := by
  unfold sixEntryComplex
  rw [six_cleared_partial_fractions]
  simp only [map_sum, map_mul, aeval_C, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l _
  rw [sixPoleComplement_complex_eval n k l.val hk l.isLt z hz]
  have hd := six_denominator_complex_eval_ne_zero n z hz
  have hp := pow_ne_zero (l.val + 1) (six_pole_translate_complex_ne_zero n k hk z hz)
  field_simp
  simp

theorem sixEntryComplex_eventuallyEq_partial_fractions (n : ℕ) (i j : Fin (rank n))
    (z : ℂ) (hz : -(45 * (n : ℝ) + 1) < z.re) :
    sixEntryComplex n i j =ᶠ[𝓝 z]
      (fun w : ℂ => ∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
        (sixPrincipalCoefficients n i j k l : ℂ) / (w + (k : ℂ)) ^ (l.val + 1)) := by
  filter_upwards [(isOpen_sixComplexHalfPlane n).mem_nhds hz] with w hw
  exact sixEntryComplex_partial_fractions n i j w hw

private theorem complex_iteratedDeriv_shifted_zpow (r : ℕ) (m : ℤ) (z a : ℂ) :
    iteratedDeriv r (fun w : ℂ => (w + a) ^ m) z =
      (∏ s ∈ range r, ((m : ℂ) - (s : ℂ))) * (z + a) ^ (m - (r : ℤ)) := by
  rw [iteratedDeriv_comp_add_const r (fun w : ℂ => w ^ m) a, iteratedDeriv_eq_iterate]
  exact iter_deriv_zpow m (z + a) r

private theorem complex_fourthDerivative_inv_pow_add (m : ℕ) (hm : 1 ≤ m)
    (z a : ℂ) (hz : z + a ≠ 0) :
    iteratedDeriv 4 (fun w : ℂ => 1 / (w + a) ^ m) z / 24 =
      ((m + 3).choose 4 : ℂ) / (z + a) ^ (m + 4) := by
  have hfun : (fun w : ℂ => 1 / (w + a) ^ m) =
      (fun w : ℂ => (w + a) ^ (-(m : ℤ))) := by
    funext w; simp [zpow_neg, one_div]
  rw [hfun, complex_iteratedDeriv_shifted_zpow]
  have hexp : -(m : ℤ) - (4 : ℕ) = -((m + 4 : ℕ) : ℤ) := by push_cast; ring
  rw [hexp, zpow_neg, zpow_natCast]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) (fourthDerivative_coefficient m hm)
  push_cast at hc
  norm_num [Finset.prod_range_succ]
  field_simp [pow_ne_zero (m + 4) hz]
  linear_combination -hc

private theorem complex_fourthDerivative_const_div_pow_add (m : ℕ) (hm : 1 ≤ m)
    (c z a : ℂ) (hz : z + a ≠ 0) :
    iteratedDeriv 4 (fun w : ℂ => c / (w + a) ^ m) z / 24 =
      c * ((m + 3).choose 4 : ℂ) / (z + a) ^ (m + 4) := by
  have hfun : (fun w : ℂ => c / (w + a) ^ m) =
      (fun w : ℂ => c * (1 / (w + a) ^ m)) := by funext w; ring
  rw [hfun, iteratedDeriv_const_mul_field, mul_div_assoc,
    complex_fourthDerivative_inv_pow_add m hm z a hz]
  ring

private theorem complex_contDiffAt_const_div_pow_add (r m : ℕ) (c z a : ℂ)
    (hz : z + a ≠ 0) : ContDiffAt ℂ r (fun w : ℂ => c / (w + a) ^ m) z :=
  contDiffAt_const.div ((contDiffAt_id.add contDiffAt_const).pow m) (pow_ne_zero m hz)

theorem sixEntryComplex_fourthDerivative (n : ℕ) (i j : Fin (rank n))
    (z : ℂ) (hz : -(45 * (n : ℝ) + 1) < z.re) :
    iteratedDeriv 4 (sixEntryComplex n i j) z / 24 =
      ∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
        (sixPrincipalCoefficients n i j k l : ℂ) * ((l.val + 4).choose 4 : ℂ) /
          (z + (k : ℂ)) ^ (l.val + 5) := by
  have hsmooth (k : ℕ) (hk : k ∈ sixPoleSet n) :
      ContDiffAt ℂ 4 (fun w : ℂ => ∑ l : Fin (sixPoleOrder n k),
        (sixPrincipalCoefficients n i j k l : ℂ) / (w + (k : ℂ)) ^ (l.val + 1)) z := by
    apply ContDiffAt.sum
    intro l _
    exact complex_contDiffAt_const_div_pow_add 4 (l.val + 1)
      (sixPrincipalCoefficients n i j k l : ℂ) z (k : ℂ)
      (six_pole_translate_complex_ne_zero n k hk z hz)
  rw [Filter.EventuallyEq.iteratedDeriv_eq 4
    (sixEntryComplex_eventuallyEq_partial_fractions n i j z hz)]
  rw [iteratedDeriv_fun_sum hsmooth, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDeriv_fun_sum (fun l _ =>
    complex_contDiffAt_const_div_pow_add 4 (l.val + 1)
      (sixPrincipalCoefficients n i j k l : ℂ) z (k : ℂ)
      (six_pole_translate_complex_ne_zero n k hk z hz)), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l _
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    complex_fourthDerivative_const_div_pow_add (l.val + 1) (by omega)
      (sixPrincipalCoefficients n i j k l : ℂ) z (k : ℂ)
      (six_pole_translate_complex_ne_zero n k hk z hz)

theorem sixEntryComplex_dividedFourthDerivative_ofReal (n : ℕ) (i j : Fin (rank n))
    (x : ℝ) (hx : -(45 * (n : ℝ) + 1) < x) :
    iteratedDeriv 4 (sixEntryComplex n i j) (x : ℂ) / 24 =
      ((iteratedDeriv 4 (sixEntryReal n i j) x / 24 : ℝ) : ℂ) := by
  rw [sixEntryComplex_fourthDerivative n i j (x : ℂ) (by simpa using hx),
    sixEntryReal_fourthDerivative n i j x hx]
  push_cast
  rfl

/-- Successive analytic divided differences at a point `c`. -/
def sixPoleTaylorTail (f : ℂ → ℂ) (c : ℂ) (k : ℕ) : ℂ → ℂ :=
  (Function.swap dslope c)^[k] f

theorem sixPoleTaylorTail_analytic {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (k : ℕ) : AnalyticAt ℂ (sixPoleTaylorTail f c k) c := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨_, hp.has_fpower_series_iterate_dslope_fslope k⟩

theorem sixPoleTaylorTail_at_center {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (k : ℕ) :
    sixPoleTaylorTail f c k c = iteratedDeriv k f c / k.factorial := by
  have hh := (hf.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope k).coeff_zero 1
  rw [← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope,
    zero_add, FormalMultilinearSeries.coeff_ofScalars] at hh
  exact hh.symm

private theorem dslope_sub_mul (c : ℂ) (g : ℂ → ℂ) (hg : ContinuousAt g c) :
    dslope (fun z => (z - c) * g z) c = g := by
  funext z
  by_cases hz : z = c
  · subst z
    rw [dslope_same]
    have hd : HasDerivAt (fun w => (w - c) * g w) (g c) c := by
      rw [hasDerivAt_iff_tendsto_slope_zero]
      have hev : (fun t : ℂ => t⁻¹ • (((c + t - c) * g (c + t)) - ((c - c) * g c))) =ᶠ[𝓝[≠] 0]
          (fun t : ℂ => g (c + t)) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [smul_eq_mul, add_sub_cancel_left, sub_self, zero_mul, sub_zero]
        rw [← mul_assoc, inv_mul_cancel₀ ht, one_mul]
      have hlim : Tendsto (fun t : ℂ => g (c + t)) (𝓝[≠] 0) (𝓝 (g c)) := by
        have hcont : Tendsto (fun t : ℂ => c + t) (𝓝 0) (𝓝 c) := by
          have hc : Continuous (fun t : ℂ => c + t) := by fun_prop
          have h := hc.tendsto (0 : ℂ)
          rwa [add_zero] at h
        exact (hg.tendsto.comp hcont).mono_left nhdsWithin_le_nhds
      exact hlim.congr' hev.symm
    exact hd.deriv
  · rw [dslope_of_ne _ hz, slope_def_field]
    simp only [sub_self, zero_mul, sub_zero]
    rw [mul_div_cancel_left₀ _ (sub_ne_zero.mpr hz)]

private theorem sixPoleTaylorTail_pow_mul (c : ℂ) (m : ℕ) (h : ℂ → ℂ)
    (hh : AnalyticAt ℂ h c) :
    sixPoleTaylorTail (fun z => (z - c) ^ (m + 1) * h z) c m =
      fun z => (z - c) * h z := by
  induction m generalizing h with
  | zero => simp [sixPoleTaylorTail]
  | succ m ih =>
    change sixPoleTaylorTail (dslope (fun z => (z - c) ^ (m + 2) * h z) c) c m = _
    have hrew : (fun z => (z - c) ^ (m + 2) * h z) =
        (fun z => (z - c) * ((z - c) ^ (m + 1) * h z)) := by
      funext z; ring
    have hcont : ContinuousAt (fun z => (z - c) ^ (m + 1) * h z) c :=
      (((analyticAt_id.sub analyticAt_const).pow (m + 1)).mul hh).continuousAt
    rw [hrew, dslope_sub_mul c (fun z => (z - c) ^ (m + 1) * h z) hcont]
    exact ih h hh

/-- Complex fourth derivative vanishes at every protected integer `-40 n, ..., -1`. -/
theorem sixEntryComplex_dividedFourthDerivative_protected (n : ℕ) (i j : Fin (rank n))
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ 40 * n) :
    iteratedDeriv 4 (sixEntryComplex n i j) (-(k : ℂ)) / 24 = 0 := by
  obtain ⟨Q, hQ⟩ := protected_fifth_power_dvd n k hk hkn
  have hhp : -(45 * (n : ℝ) + 1) < (-(k : ℂ)).re := by
    simp only [neg_re, natCast_re]
    have hkR : (k : ℝ) ≤ 40 * (n : ℝ) := by exact_mod_cast hkn
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  let h : ℂ → ℂ := fun z =>
    aeval z (C (sixNormalization n) * Q * centeredMultiplier n i j) /
      aeval z (sixDenominator n)
  have hh : AnalyticAt ℂ h (-(k : ℂ)) :=
    (analyticAt_id.aeval_polynomial _).div
      (analyticAt_id.aeval_polynomial _)
      (six_denominator_complex_eval_ne_zero n (-(k : ℂ)) hhp)
  have hEq : sixEntryComplex n i j = fun z => (z - (-(k : ℂ))) ^ 5 * h z := by
    funext z
    simp only [sixEntryComplex, h, hQ, map_mul, map_pow, map_add, aeval_X, aeval_C, sub_neg_eq_add]
    have hrat : (algebraMap ℚ ℂ) (k : ℚ) = (k : ℂ) := by simp
    rw [hrat]
    ring
  have hf : AnalyticAt ℂ (sixEntryComplex n i j) (-(k : ℂ)) :=
    sixEntryComplex_analyticAt n i j (-(k : ℂ)) hhp
  have ht := sixPoleTaylorTail_at_center hf 4
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat] at ht
  rw [← ht, hEq, sixPoleTaylorTail_pow_mul (-(k : ℂ)) 4 h hh]
  simp

/-- Shifting the real functional series from `-40 n` to `-n` drops only `39 n` zero terms. -/
theorem hasSum_sixContour_residue_series (n : ℕ) (i j : Fin (rank n)) :
    HasSum (fun v : ℕ =>
      iteratedDeriv 4 (sixEntryComplex n i j) ((v : ℂ) - (n : ℂ)) / 24)
      (sixFunctional n i j : ℂ) := by
  have horig : HasSum (fun v : ℕ =>
      iteratedDeriv 4 (sixEntryComplex n i j) ((v : ℂ) - 40 * (n : ℂ)) / 24)
      (sixFunctional n i j : ℂ) := by
    have hreal : HasSum (fun v : ℕ =>
        iteratedDeriv 4 (sixEntryReal n i j) ((v : ℝ) - 40 * (n : ℝ)) / 24)
        (sixFunctional n i j) := (summable_sixEntryReal_fourthDerivative n i j).hasSum
    apply (Complex.hasSum_ofReal.mpr hreal).congr_fun
    intro v
    simpa only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast,
      Complex.ofReal_ofNat] using
      sixEntryComplex_dividedFourthDerivative_ofReal n i j
        ((v : ℝ) - 40 * (n : ℝ)) (six_summation_point_in_halfline n v)
  have hshift := (hasSum_nat_add_iff' (39 * n) (f := fun v : ℕ =>
      iteratedDeriv 4 (sixEntryComplex n i j) ((v : ℂ) - 40 * (n : ℂ)) / 24)).mpr horig
  have hzero : (∑ v ∈ range (39 * n),
      iteratedDeriv 4 (sixEntryComplex n i j) ((v : ℂ) - 40 * (n : ℂ)) / 24) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    have hv' : v < 39 * n := mem_range.mp hv
    have hx : (v : ℂ) - 40 * (n : ℂ) = -((40 * n - v : ℕ) : ℂ) := by
      rw [Nat.cast_sub (by omega : v ≤ 40 * n)]; push_cast; ring
    rw [hx]
    exact sixEntryComplex_dividedFourthDerivative_protected n i j (40 * n - v)
      (by omega) (by omega)
  rw [hzero, sub_zero] at hshift
  refine hshift.congr_fun ?_
  intro v
  congr 2
  push_cast
  ring

/-! ## Section 2: Half-integer vertical contour `σ₀ = -n - 1/2` and fifth cotangent kernel -/

/-- Exact half-integer vertical contour abscissa `σ₀ = -n - 1/2` (`c = 1/50`, `c L_n = n`). -/
def sixContourAbscissa (n : ℕ) : ℝ := -(n : ℝ) - 1 / 2

/-- Point on the vertical contour at height `y`. -/
def sixContourPoint (n : ℕ) (y : ℝ) : ℂ :=
  (sixContourAbscissa n : ℂ) + (y : ℂ) * Complex.I

@[simp] theorem sixContourPoint_re (n : ℕ) (y : ℝ) :
    (sixContourPoint n y).re = sixContourAbscissa n := by
  simp [sixContourPoint]

@[simp] theorem sixContourPoint_im (n : ℕ) (y : ℝ) :
    (sixContourPoint n y).im = y := by
  simp [sixContourPoint]

theorem sixContourAbscissa_in_halfplane (n : ℕ) :
    -(45 * (n : ℝ) + 1) < sixContourAbscissa n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  dsimp [sixContourAbscissa]
  linarith

theorem sixContourAbscissa_ne_int (n : ℕ) (m : ℤ) :
    sixContourAbscissa n ≠ (m : ℝ) := by
  intro h
  have he : (2 * m + 2 * (n : ℤ) : ℤ) = -1 := by
    have he' : 2 * (m : ℝ) + 2 * (n : ℝ) = -1 := by
      dsimp [sixContourAbscissa] at h; linarith
    exact_mod_cast he'
  omega

private theorem sin_pi_ne_zero_of_re_ne_int (z : ℂ)
    (hz : ∀ m : ℤ, z.re ≠ (m : ℝ)) : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp h
  have he : z = (m : ℂ) := by
    apply mul_left_cancel₀ (show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero)
    simpa only [mul_comm] using hm
  exact hz m (by simp [he])

theorem six_sin_ne_zero_on_contour (n : ℕ) (y : ℝ) :
    Complex.sin ((Real.pi : ℂ) * sixContourPoint n y) ≠ 0 :=
  sin_pi_ne_zero_of_re_ne_int _ fun m => by
    simpa only [sixContourPoint_re] using sixContourAbscissa_ne_int n m

theorem six_sin_ne_zero_on_half_integer (q : ℤ) (z : ℂ)
    (hz : z.re = (q : ℝ) + 1 / 2) : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  apply sin_pi_ne_zero_of_re_ne_int
  intro m hm
  have he : (2 * m - 2 * q : ℤ) = 1 := by
    have he' : 2 * (m : ℝ) - 2 * (q : ℝ) = 1 := by linarith
    exact_mod_cast he'
  omega

theorem six_sin_ne_zero_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp h
  have he : z = (m : ℂ) := by
    apply mul_left_cancel₀ (show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero)
    simpa only [mul_comm] using hm
  exact hz (by simp [he])

def sixCotKernel (z : ℂ) : ℂ := (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z)

def sixContourKernel (z : ℂ) : ℂ :=
  iteratedDeriv 4 sixCotKernel z / 24

private def cotJet (r : ℕ) (z : ℂ) : ℂ :=
  let p : ℂ := Real.pi
  let s := Complex.sin (p * z)
  let c := Complex.cos (p * z)
  match r with
  | 0 => p * c / s
  | 1 => -p ^ 2 / s ^ 2
  | 2 => 2 * p ^ 3 * c / s ^ 3
  | 3 => -2 * p ^ 4 * (1 + 2 * c ^ 2) / s ^ 4
  | _ => 8 * p ^ 5 * (c ^ 3 + 2 * c) / s ^ 5

private theorem hasDerivAt_cotJet (r : Fin 4) (z : ℂ)
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    HasDerivAt (cotJet r.val) (cotJet (r.val + 1) z) z := by
  let p : ℂ := Real.pi
  have hs := ((hasDerivAt_id z).const_mul p).csin
  have hc := ((hasDerivAt_id z).const_mul p).ccos
  have ht := Complex.sin_sq_add_cos_sq (p * z)
  fin_cases r
  · convert! ((hc.const_mul p).div hs hz) using 1
    dsimp [cotJet, p] at *
    field_simp [hz]; try field_simp [hz]
    linear_combination ht
  · convert! (hasDerivAt_const z (-p ^ 2)).div (hs.pow 2) (pow_ne_zero 2 hz) using 1
    dsimp [cotJet, p]
    field_simp [hz]; try field_simp [hz]
    ring
  · convert! ((hc.const_mul (2 * p ^ 3)).div (hs.pow 3) (pow_ne_zero 3 hz)) using 1
    dsimp [cotJet, p] at *
    field_simp [hz]; try field_simp [hz]
    linear_combination ht
  · convert! ((((hc.pow 2).const_mul 2).const_add 1).const_mul (-2 * p ^ 4)).div
      (hs.pow 4) (pow_ne_zero 4 hz) using 1
    dsimp [cotJet, p] at *
    field_simp [hz]; try field_simp [hz]
    linear_combination -8 * Complex.cos ((Real.pi : ℂ) * z) * ht

private theorem iteratedDeriv_cotJet (r : ℕ) (hr : r ≤ 4) (z : ℂ)
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    iteratedDeriv r sixCotKernel z = cotJet r z := by
  induction r generalizing z with
  | zero => simp [sixCotKernel, Complex.cot, cotJet, mul_div_assoc]
  | succ r ih =>
    have he : iteratedDeriv r sixCotKernel =ᶠ[𝓝 z] cotJet r := by
      have hcont : ContinuousAt (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) z := by fun_prop
      filter_upwards [hcont.eventually_ne hz] with w hw
      exact ih (by omega) w hw
    rw [iteratedDeriv_succ, he.deriv_eq]
    exact (hasDerivAt_cotJet ⟨r, by omega⟩ z hz).deriv

/-- Exact closed form of the normalized fourth cotangent derivative kernel. -/
theorem sixContourKernel_eq (z : ℂ) (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    sixContourKernel z = (Real.pi : ℂ) ^ 5 *
      (Complex.cos ((Real.pi : ℂ) * z) ^ 3 + 2 * Complex.cos ((Real.pi : ℂ) * z)) /
        (3 * Complex.sin ((Real.pi : ℂ) * z) ^ 5) := by
  rw [sixContourKernel, iteratedDeriv_cotJet 4 (by omega) z hz]
  dsimp [cotJet]
  field_simp [hz]; try field_simp [hz]
  ring

theorem sixContourKernel_analyticAt (z : ℂ)
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) : AnalyticAt ℂ sixContourKernel z := by
  have hc : AnalyticAt ℂ sixCotKernel z := by
    unfold sixCotKernel Complex.cot
    exact analyticAt_const.mul
      ((Complex.analyticAt_cos.comp (analyticAt_const.mul analyticAt_id)).div
        (Complex.analyticAt_sin.comp (analyticAt_const.mul analyticAt_id)) hz)
  unfold sixContourKernel
  simp_rw [iteratedDeriv_eq_iterate]
  exact (hc.iterated_deriv 4).div analyticAt_const (by norm_num : (24 : ℂ) ≠ 0)

def sixContourIntegrand (n i j : ℕ) (z : ℂ) : ℂ :=
  sixEntryComplex n i j z * sixContourKernel z

theorem sixContourIntegrand_analyticAt (n i j : ℕ) (z : ℂ)
    (hz : sixContourAbscissa n ≤ z.re)
    (hs : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    AnalyticAt ℂ (sixContourIntegrand n i j) z :=
  (sixEntryComplex_analyticAt n i j z
    (lt_of_lt_of_le (sixContourAbscissa_in_halfplane n) hz)).mul
    (sixContourKernel_analyticAt z hs)

private theorem cotKernel_logDeriv (z : ℂ) :
    sixCotKernel z = logDeriv (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) z := by
  have hd := ((hasDerivAt_id z).const_mul (Real.pi : ℂ)).csin
  simp only [id_eq, mul_one] at hd
  rw [logDeriv_apply, hd.deriv]
  simp only [sixCotKernel, Complex.cot]
  ring

theorem sixCotKernel_principal_part (m : ℤ) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A (m : ℂ) ∧
      sixCotKernel =ᶠ[𝓝[≠] (m : ℂ)] (fun z => 1 / (z - (m : ℂ)) + A z) := by
  let f : ℂ → ℂ := fun z => Complex.sin ((Real.pi : ℂ) * z)
  have hf : AnalyticAt ℂ f (m : ℂ) :=
    Complex.analyticAt_sin.comp (analyticAt_const.mul analyticAt_id)
  have hf0 : f (m : ℂ) = 0 := by simpa only [f, mul_comm] using Complex.sin_int_mul_pi m
  let g := dslope f (m : ℂ)
  have hg : AnalyticAt ℂ g (m : ℂ) := by
    obtain ⟨p, hp⟩ := hf
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  have hg0 : g (m : ℂ) ≠ 0 := by
    have hd := ((hasDerivAt_id (m : ℂ)).const_mul (Real.pi : ℂ)).csin
    change dslope f (m : ℂ) (m : ℂ) ≠ 0
    rw [dslope_same, show deriv f (m : ℂ) =
      Complex.cos ((Real.pi : ℂ) * m) * (Real.pi : ℂ) by simpa [f] using hd.deriv]
    apply mul_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
    intro hc
    have h := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * m)
    change Complex.sin ((Real.pi : ℂ) * m) = 0 at hf0
    simp [hf0, hc] at h
  have hfactor : f = fun z => (z - (m : ℂ)) * g z := by
    funext z
    simpa only [smul_eq_mul, hf0, sub_zero] using (sub_smul_dslope f (m : ℂ) z).symm
  refine ⟨logDeriv g, hg.deriv.div hg hg0, ?_⟩
  filter_upwards [hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hga hgn hz
  have hzm : z - (m : ℂ) ≠ 0 := sub_ne_zero.mpr hz
  rw [cotKernel_logDeriv]
  change logDeriv f z = _
  rw [hfactor, logDeriv_fun_mul z hzm hgn (by fun_prop) hga.differentiableAt]
  simp [logDeriv_apply]

private theorem iteratedDeriv_eventuallyEq_nhdsNE {f g : ℂ → ℂ} {c : ℂ}
    (h : f =ᶠ[𝓝[≠] c] g) (r : ℕ) :
    iteratedDeriv r f =ᶠ[𝓝[≠] c] iteratedDeriv r g := by
  induction r with
  | zero => simpa using h
  | succ r ih => simpa only [iteratedDeriv_succ] using ih.nhdsNE_deriv

private theorem fourthDeriv_inv_sub (c z : ℂ) :
    iteratedDeriv 4 (fun w : ℂ => 1 / (w - c)) z / 24 = 1 / (z - c) ^ 5 := by
  have h := congrFun (iter_deriv_inv_linear_sub 4 (1 : ℂ) c) z
  norm_num [one_div, iteratedDeriv_eq_iterate, zpow_neg, zpow_natCast] at h ⊢
  rw [h]; ring

theorem sixContourKernel_principal_part (m : ℤ) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A (m : ℂ) ∧
      sixContourKernel =ᶠ[𝓝[≠] (m : ℂ)] (fun z => 1 / (z - (m : ℂ)) ^ 5 + A z) := by
  obtain ⟨A, hA, hcot⟩ := sixCotKernel_principal_part m
  refine ⟨fun z => iteratedDeriv 4 A z / 24, ?_, ?_⟩
  · simp_rw [iteratedDeriv_eq_iterate]
    exact (hA.iterated_deriv 4).div analyticAt_const (by norm_num : (24 : ℂ) ≠ 0)
  · filter_upwards [iteratedDeriv_eventuallyEq_nhdsNE hcot 4,
      hA.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hAz hzm
    have hi : ContDiffAt ℂ 4 (fun w : ℂ => 1 / (w - (m : ℂ))) z :=
      contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.mpr hzm)
    rw [sixContourKernel, hz, iteratedDeriv_fun_add hi hAz.contDiffAt,
      add_div, fourthDeriv_inv_sub]

/-! ## Section 3: Fixed-index decay, exponential cotangent bound, and vertical integral -/

def sixPolynomialCoefficientNorm (P : ℚ[X]) : ℝ :=
  ∑ r ∈ range (P.natDegree + 1), ‖(P.coeff r : ℂ)‖

def sixEntryCoefficientNorm (n i j : ℕ) : ℝ :=
  sixPolynomialCoefficientNorm
    (C (sixNormalization n) * sixNumerator n * centeredMultiplier n i j)

def sixContourDecayRadius (n : ℕ) : ℝ := 2 * (95 * (n : ℝ) + 1)

def sixContourDecayConstant (n : ℕ) : ℝ :=
  2 ^ (582 * n + 14) *
    (1 + ∑ i : Fin (rank n), ∑ j : Fin (rank n), sixEntryCoefficientNorm n i j)

theorem sixContourDecayRadius_ge_two (n : ℕ) : 2 ≤ sixContourDecayRadius n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  dsimp [sixContourDecayRadius]; linarith

private theorem sixEntryCoefficientNorm_nonneg (n i j : ℕ) :
    0 ≤ sixEntryCoefficientNorm n i j := by
  unfold sixEntryCoefficientNorm sixPolynomialCoefficientNorm
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem sixContourDecayConstant_pos (n : ℕ) : 0 < sixContourDecayConstant n := by
  unfold sixContourDecayConstant
  apply mul_pos (by positivity)
  have h : 0 ≤ ∑ i : Fin (rank n), ∑ j : Fin (rank n), sixEntryCoefficientNorm n i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      sixEntryCoefficientNorm_nonneg n i j
  linarith

private theorem norm_aeval_le_coefficientNorm (P : ℚ[X]) (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖aeval z P‖ ≤ sixPolynomialCoefficientNorm P * ‖z‖ ^ P.natDegree := by
  rw [aeval_eq_sum_range]
  calc
    _ ≤ ∑ r ∈ range (P.natDegree + 1), ‖(P.coeff r : ℂ)‖ * ‖z‖ ^ r := by
      simpa [Algebra.smul_def, norm_mul, norm_pow] using
        norm_sum_le (range (P.natDegree + 1)) (fun r => P.coeff r • z ^ r)
    _ ≤ ∑ r ∈ range (P.natDegree + 1), ‖(P.coeff r : ℂ)‖ * ‖z‖ ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hz (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hr))
        (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; rfl

private theorem six_sum_pole_orders (n : ℕ) :
    (∑ k ∈ sixPoleSet n, sixPoleOrder n k) = 582 * n + 14 := by
  have h := congrArg Polynomial.natDegree (six_denominator_powers n)
  rw [sixDenominator_degree,
    natDegree_prod_of_monic _ _ (fun (k : ℕ) _ =>
      (monic_X_add_C (k : ℚ)).pow (sixPoleOrder n k))] at h
  simpa only [natDegree_pow, natDegree_X_add_C, mul_one] using h.symm

private theorem six_denominator_norm_lower (n : ℕ) (z : ℂ)
    (hz : sixContourDecayRadius n ≤ ‖z‖) :
    (‖z‖ / 2) ^ (582 * n + 14) ≤ ‖aeval z (sixDenominator n)‖ := by
  rw [six_denominator_powers]
  simp only [map_prod, map_pow, map_add, aeval_X, map_natCast, norm_prod, norm_pow]
  rw [← six_sum_pole_orders n, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (by positivity) _)
  intro k hk
  apply pow_le_pow_left₀ (by positivity)
  have hk' : (k : ℝ) ≤ 95 * (n : ℝ) + 1 := by exact_mod_cast (six_pole_address_bounds n k hk).2
  have ht : ‖z‖ ≤ ‖z + (k : ℂ)‖ + (k : ℝ) := by
    simpa only [add_sub_cancel_right, Complex.norm_natCast] using norm_sub_le (z + (k : ℂ)) k
  dsimp [sixContourDecayRadius] at hz
  linarith

private theorem six_entry_numerator_degree_decay (n : ℕ) (i j : Fin (rank n)) :
    (C (sixNormalization n) * sixNumerator n * centeredMultiplier n i j).natDegree +
      (114 * n + 17) ≤ 582 * n + 14 := by
  rw [natDegree_mul
    (mul_ne_zero (by simpa using sixNormalization_ne_zero n) (sixNumerator_monic n).ne_zero)
    (centeredMultiplier_ne_zero n i j), natDegree_C_mul (sixNormalization_ne_zero n),
    sixNumerator_degree, centeredMultiplier_degree]
  have hi : i.val < 15 * n := i.isLt
  have hj : j.val < 15 * n := j.isLt
  omega

theorem sixEntryComplex_norm_le_decay (n : ℕ) (i j : Fin (rank n)) (z : ℂ)
    (hz : sixContourDecayRadius n ≤ ‖z‖) :
    ‖sixEntryComplex n i j z‖ ≤ sixContourDecayConstant n / ‖z‖ ^ (114 * n + 17) := by
  let P := C (sixNormalization n) * sixNumerator n * centeredMultiplier n i j
  let A := sixEntryCoefficientNorm n i j
  have hx : 1 ≤ ‖z‖ := le_trans (by norm_num : (1 : ℝ) ≤ 2)
    ((sixContourDecayRadius_ge_two n).trans hz)
  have hxpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hx
  have hA : 0 ≤ A := sixEntryCoefficientNorm_nonneg n i j
  have hN : ‖aeval z P‖ ≤ A * ‖z‖ ^ P.natDegree := norm_aeval_le_coefficientNorm P z hx
  have hd := six_entry_numerator_degree_decay n i j
  have hDlow := six_denominator_norm_lower n z hz
  have hDpos : 0 < ‖aeval z (sixDenominator n)‖ :=
    lt_of_lt_of_le (pow_pos (by positivity) _) hDlow
  have hAtot : A ≤ 1 + ∑ a : Fin (rank n), ∑ b : Fin (rank n), sixEntryCoefficientNorm n a b := by
    have h1 : A ≤ ∑ b : Fin (rank n), sixEntryCoefficientNorm n i b :=
      Finset.single_le_sum (f := fun b : Fin (rank n) => sixEntryCoefficientNorm n i b)
        (fun b _ => sixEntryCoefficientNorm_nonneg n i b) (Finset.mem_univ j)
    have h2 : (∑ b : Fin (rank n), sixEntryCoefficientNorm n i b) ≤
        ∑ a : Fin (rank n), ∑ b : Fin (rank n), sixEntryCoefficientNorm n a b :=
      Finset.single_le_sum
        (f := fun a : Fin (rank n) => ∑ b : Fin (rank n), sixEntryCoefficientNorm n a b)
        (fun a _ => Finset.sum_nonneg fun b _ => sixEntryCoefficientNorm_nonneg n a b) (Finset.mem_univ i)
    linarith
  rw [sixEntryComplex, norm_div]
  apply (div_le_div_iff₀ hDpos (pow_pos hxpos _)).mpr
  change ‖aeval z P‖ * ‖z‖ ^ (114 * n + 17) ≤ _
  calc
    _ ≤ (A * ‖z‖ ^ P.natDegree) * ‖z‖ ^ (114 * n + 17) :=
      mul_le_mul_of_nonneg_right hN (pow_nonneg (norm_nonneg _) _)
    _ = A * ‖z‖ ^ (P.natDegree + (114 * n + 17)) := by rw [pow_add]; ring
    _ ≤ A * ‖z‖ ^ (582 * n + 14) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hd) hA
    _ = (2 ^ (582 * n + 14) * A) * (‖z‖ / 2) ^ (582 * n + 14) := by rw [div_pow]; field_simp
    _ ≤ sixContourDecayConstant n * (‖z‖ / 2) ^ (582 * n + 14) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAtot (by positivity))
        (pow_nonneg (by positivity) _)
    _ ≤ sixContourDecayConstant n * ‖aeval z (sixDenominator n)‖ :=
      mul_le_mul_of_nonneg_left hDlow (sixContourDecayConstant_pos n).le

private theorem sin_norm_sq (w : ℂ) :
    ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  have hre : (Complex.sin w).re = Real.sin w.re * Real.cosh w.im := by
    rw [Complex.sin_eq]
    simp [← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  have him : (Complex.sin w).im = Real.cos w.re * Real.sinh w.im := by
    rw [Complex.sin_eq]
    simp [← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  have hh := Real.cosh_sq w.im
  have ht := Real.sin_sq_add_cos_sq w.re
  linear_combination Real.sin w.re ^ 2 * hh + Real.sinh w.im ^ 2 * ht

theorem six_sin_norm_ge_one_half_integer (q : ℤ) (z : ℂ)
    (hz : z.re = (q : ℝ) + 1 / 2) : 1 ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
  have hre : ((Real.pi : ℂ) * z).re = (q : ℝ) * Real.pi + Real.pi / 2 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hz]; ring
  have hsin : Real.sin (((Real.pi : ℂ) * z).re) ^ 2 = 1 := by
    rw [hre, Real.sin_add_pi_div_two, ← sq_abs, Real.abs_cos_int_mul_pi]; norm_num
  have h := sin_norm_sq ((Real.pi : ℂ) * z)
  rw [hsin] at h
  nlinarith [sq_nonneg (Real.sinh (((Real.pi : ℂ) * z).im)),
    norm_nonneg (Complex.sin ((Real.pi : ℂ) * z))]

theorem six_sin_norm_ge_one_of_im (z : ℂ) (hz : 1 ≤ |z.im|) :
    1 ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
  have him : |((Real.pi : ℂ) * z).im| = Real.pi * |z.im| := by
    simp [Complex.mul_im, abs_mul, Real.pi_pos.le]
  have hpi : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
  have hw : 1 ≤ |((Real.pi : ℂ) * z).im| := by rw [him]; nlinarith
  have hs : 1 ≤ |Real.sinh (((Real.pi : ℂ) * z).im)| := by
    rw [Real.abs_sinh]
    exact hw.trans (Real.self_le_sinh_iff.mpr (abs_nonneg _))
  have h := sin_norm_sq ((Real.pi : ℂ) * z)
  have hs2 : 1 ≤ Real.sinh (((Real.pi : ℂ) * z).im) ^ 2 := by
    nlinarith [sq_abs (Real.sinh (((Real.pi : ℂ) * z).im))]
  nlinarith [sq_nonneg (Real.sin (((Real.pi : ℂ) * z).re)),
    norm_nonneg (Complex.sin ((Real.pi : ℂ) * z))]

theorem sixContourKernel_norm_le (z : ℂ)
    (hz : 1 ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖) :
    ‖sixContourKernel z‖ ≤ 4 * Real.pi ^ 5 := by
  let s := ‖Complex.sin ((Real.pi : ℂ) * z)‖
  let c := ‖Complex.cos ((Real.pi : ℂ) * z)‖
  have hs : 1 ≤ s := hz
  have hc : 0 ≤ c := norm_nonneg _
  have hcs : c ≤ 2 * s := by
    have he : Complex.cos ((Real.pi : ℂ) * z) ^ 2 =
        1 - Complex.sin ((Real.pi : ℂ) * z) ^ 2 := by
      linear_combination Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * z)
    have hb : c ^ 2 ≤ 1 + s ^ 2 := by
      change ‖Complex.cos ((Real.pi : ℂ) * z)‖ ^ 2 ≤ 1 + ‖Complex.sin ((Real.pi : ℂ) * z)‖ ^ 2
      rw [← norm_pow, he]
      have h := norm_sub_le (1 : ℂ) (Complex.sin ((Real.pi : ℂ) * z) ^ 2)
      rw [norm_one, Complex.norm_pow] at h
      exact h
    nlinarith
  have hs0 : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hz)
  rw [sixContourKernel_eq z hs0, norm_div, norm_mul, norm_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    norm_mul, norm_pow, Complex.norm_ofNat]
  have hn : ‖Complex.cos ((Real.pi : ℂ) * z) ^ 3 +
      2 * Complex.cos ((Real.pi : ℂ) * z)‖ ≤ c ^ 3 + 2 * c := by
    have h := norm_add_le (Complex.cos ((Real.pi : ℂ) * z) ^ 3)
      (2 * Complex.cos ((Real.pi : ℂ) * z))
    rw [Complex.norm_pow, norm_mul] at h; norm_num at h; exact h
  apply (div_le_iff₀ (show 0 < 3 * s ^ 5 by positivity)).mpr
  calc
    _ ≤ Real.pi ^ 5 * (c ^ 3 + 2 * c) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ ≤ Real.pi ^ 5 * ((2 * s) ^ 3 + 2 * (2 * s)) := by gcongr
    _ ≤ Real.pi ^ 5 * (12 * s ^ 5) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h3 : s ^ 3 ≤ s ^ 5 := pow_le_pow_right₀ hs (by omega)
      have h1 : s ≤ s ^ 5 := by simpa using pow_le_pow_right₀ hs (show 1 ≤ 5 by omega)
      nlinarith
    _ = _ := by ring

/-- Exponential cotangent kernel bound on the half-integer vertical line:
`‖sixContourKernel (σ₀ + i y)‖ ≤ 32 * π^5 * exp (-2 * π * |y|)`. -/
theorem sixContourKernel_norm_le_exp_half_integer (n : ℕ) (y : ℝ) :
    ‖sixContourKernel (sixContourPoint n y)‖ ≤ 32 * Real.pi ^ 5 * Real.exp (-2 * Real.pi * |y|) := by
  let z := (Real.pi : ℂ) * sixContourPoint n y
  have him : z.im = Real.pi * y := by simp [z, sixContourPoint]
  have hre : z.re = (-(n : ℝ) - 1) * Real.pi + Real.pi / 2 := by
    simp [z, sixContourPoint, sixContourAbscissa]; ring
  have hsin_sq : ‖Complex.sin z‖ ^ 2 = Real.cosh (Real.pi * y) ^ 2 := by
    rw [sin_norm_sq, hre, him]
    have h1 : Real.sin ((-(n : ℝ) - 1) * Real.pi + Real.pi / 2) ^ 2 = 1 := by
      rw [Real.sin_add_pi_div_two, ← sq_abs]
      have hq : (-(n : ℝ) - 1) * Real.pi = ((-(n : ℤ) - 1 : ℤ) : ℝ) * Real.pi := by push_cast; ring
      rw [hq, Real.abs_cos_int_mul_pi]; norm_num
    rw [h1, Real.cosh_sq']
  have hsin_eq : ‖Complex.sin z‖ = Real.cosh (Real.pi * y) := by
    have hnn1 : 0 ≤ ‖Complex.sin z‖ := norm_nonneg _
    have hnn2 : 0 ≤ Real.cosh (Real.pi * y) := (Real.cosh_pos _).le
    nlinarith
  have hsin_low : Real.exp (Real.pi * |y|) / 2 ≤ ‖Complex.sin z‖ := by
    rw [hsin_eq, ← Real.cosh_abs, abs_mul, abs_of_pos Real.pi_pos, Real.cosh_eq]
    linarith [Real.exp_pos (-(Real.pi * |y|))]
  have hcos_le : ‖Complex.cos z‖ ≤ Real.exp (Real.pi * |y|) := by
    rw [Complex.cos, norm_div]
    norm_num only [Complex.norm_ofNat]
    have h := norm_add_le (Complex.exp (z * I)) (Complex.exp (-z * I))
    simp only [Complex.norm_exp, mul_re, I_re, I_im, mul_zero, mul_one,
      zero_sub, neg_im, neg_neg, him] at h
    have h1 := Real.exp_le_exp.mpr (show Real.pi * y ≤ Real.pi * |y| by
      exact mul_le_mul_of_nonneg_left (le_abs_self y) Real.pi_pos.le)
    have h2 := Real.exp_le_exp.mpr (show -(Real.pi * y) ≤ Real.pi * |y| by
      have := neg_le_abs y; nlinarith [Real.pi_pos])
    linarith
  have hs0 : Complex.sin z ≠ 0 := six_sin_ne_zero_on_contour n y
  rw [sixContourKernel_eq _ hs0, norm_div, norm_mul, norm_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    norm_mul, norm_pow, Complex.norm_ofNat]
  change Real.pi ^ 5 * ‖Complex.cos z ^ 3 + 2 * Complex.cos z‖ / (3 * ‖Complex.sin z‖ ^ 5) ≤ _
  have hnum : ‖Complex.cos z ^ 3 + 2 * Complex.cos z‖ ≤ 3 * Real.exp (Real.pi * |y|) ^ 3 := by
    have htri := norm_add_le (Complex.cos z ^ 3) (2 * Complex.cos z)
    rw [Complex.norm_pow, norm_mul] at htri; norm_num only [Complex.norm_ofNat] at htri
    have he1 : 1 ≤ Real.exp (Real.pi * |y|) := Real.one_le_exp (by positivity)
    have h13 : Real.exp (Real.pi * |y|) ≤ Real.exp (Real.pi * |y|) ^ 3 := by
      simpa using pow_le_pow_right₀ he1 (show 1 ≤ 3 by omega)
    have hc3 : ‖Complex.cos z‖ ^ 3 ≤ Real.exp (Real.pi * |y|) ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg _) hcos_le 3
    linarith
  have hden : (Real.exp (Real.pi * |y|) / 2) ^ 5 ≤ ‖Complex.sin z‖ ^ 5 :=
    pow_le_pow_left₀ (by positivity) hsin_low 5
  have hspos : 0 < 3 * ‖Complex.sin z‖ ^ 5 := by positivity
  rw [div_le_iff₀ hspos]
  have hexp_eq : Real.exp (-2 * Real.pi * |y|) * Real.exp (Real.pi * |y|) ^ 5 =
      Real.exp (Real.pi * |y|) ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  calc
    Real.pi ^ 5 * ‖Complex.cos z ^ 3 + 2 * Complex.cos z‖
        ≤ Real.pi ^ 5 * (3 * Real.exp (Real.pi * |y|) ^ 3) :=
      mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = 32 * Real.pi ^ 5 * Real.exp (-2 * Real.pi * |y|) *
          (3 * (Real.exp (Real.pi * |y|) / 2) ^ 5) := by
      rw [div_pow]
      have h32 : (32 : ℝ) * (3 * (Real.exp (Real.pi * |y|) ^ 5 / 2 ^ 5)) =
          3 * Real.exp (Real.pi * |y|) ^ 5 := by ring
      calc
        Real.pi ^ 5 * (3 * Real.exp (Real.pi * |y|) ^ 3)
            = 3 * Real.pi ^ 5 * (Real.exp (-2 * Real.pi * |y|) * Real.exp (Real.pi * |y|) ^ 5) := by
              rw [hexp_eq]; ring
        _ = 32 * Real.pi ^ 5 * Real.exp (-2 * Real.pi * |y|) *
              (3 * (Real.exp (Real.pi * |y|) ^ 5 / 2 ^ 5)) := by ring
    _ ≤ 32 * Real.pi ^ 5 * Real.exp (-2 * Real.pi * |y|) * (3 * ‖Complex.sin z‖ ^ 5) := by
      gcongr

def sixContourIntegrandDecayConstant (n : ℕ) : ℝ :=
  4 * Real.pi ^ 5 * sixContourDecayConstant n

theorem sixContourIntegrandDecayConstant_pos (n : ℕ) :
    0 < sixContourIntegrandDecayConstant n :=
  mul_pos (by positivity) (sixContourDecayConstant_pos n)

theorem sixContourIntegrand_norm_le_decay (n : ℕ) (i j : Fin (rank n)) (z : ℂ)
    (hz : sixContourDecayRadius n ≤ ‖z‖)
    (hs : 1 ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖) :
    ‖sixContourIntegrand n i j z‖ ≤
      sixContourIntegrandDecayConstant n / ‖z‖ ^ (114 * n + 17) := by
  rw [sixContourIntegrand, norm_mul]
  calc
    _ ≤ (sixContourDecayConstant n / ‖z‖ ^ (114 * n + 17)) * (4 * Real.pi ^ 5) :=
      mul_le_mul (sixEntryComplex_norm_le_decay n i j z hz)
        (sixContourKernel_norm_le z hs) (norm_nonneg _)
        (div_nonneg (sixContourDecayConstant_pos n).le (pow_nonneg (norm_nonneg _) _))
    _ = _ := by unfold sixContourIntegrandDecayConstant; ring

/-- Upward-oriented vertical contour integrand on `Re z = -n - 1/2`. -/
def sixVerticalIntegrand (n i j : ℕ) (y : ℝ) : ℂ :=
  sixContourIntegrand n i j (sixContourPoint n y) * Complex.I

theorem sixVerticalIntegrand_continuous (n i j : ℕ) :
    Continuous (sixVerticalIntegrand n i j) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have ha := sixContourIntegrand_analyticAt n i j (sixContourPoint n y)
    (by simp) (six_sin_ne_zero_on_contour n y)
  exact (ha.continuousAt.comp (by unfold sixContourPoint; fun_prop)).mul continuousAt_const

theorem sixVerticalIntegrand_integrable (n : ℕ) (i j : Fin (rank n)) :
    Integrable (sixVerticalIntegrand n i j) := by
  let g : ℝ → ℝ := fun y => (1 + y ^ 2)⁻¹
  have hbound : ∀ y : ℝ, sixContourDecayRadius n ≤ |y| →
      ‖sixVerticalIntegrand n i j y‖ ≤ (2 * sixContourIntegrandDecayConstant n) * ‖g y‖ := by
    intro y hy
    have hy1 : 1 ≤ |y| := (by norm_num : (1 : ℝ) ≤ 2).trans ((sixContourDecayRadius_ge_two n).trans hy)
    have hr : |y| ≤ ‖sixContourPoint n y‖ := by
      simpa [sixContourPoint] using Complex.abs_im_le_norm (sixContourPoint n y)
    have hs : 1 ≤ ‖Complex.sin ((Real.pi : ℂ) * sixContourPoint n y)‖ := by
      apply six_sin_norm_ge_one_half_integer (-(n : ℤ) - 1)
      simp only [sixContourPoint_re, sixContourAbscissa]; push_cast; ring
    have hdec : ‖sixVerticalIntegrand n i j y‖ ≤
        sixContourIntegrandDecayConstant n / |y| ^ (114 * n + 17) := by
      rw [sixVerticalIntegrand, norm_mul, Complex.norm_I, mul_one]
      exact (sixContourIntegrand_norm_le_decay n i j _ (hy.trans hr) hs).trans
        (div_le_div_of_nonneg_left (sixContourIntegrandDecayConstant_pos n).le
          (pow_pos (by linarith) _) (pow_le_pow_left₀ (by linarith) hr _))
    have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_abs y]
    have hp : y ^ 2 ≤ |y| ^ (114 * n + 17) := by
      rw [← sq_abs y]; exact pow_le_pow_right₀ hy1 (by omega)
    have hden : 0 < 1 + y ^ 2 := by positivity
    calc
      ‖sixVerticalIntegrand n i j y‖
          ≤ sixContourIntegrandDecayConstant n / |y| ^ (114 * n + 17) := hdec
      _ ≤ (2 * sixContourIntegrandDecayConstant n) / (1 + y ^ 2) := by
        rw [div_le_div_iff₀ (pow_pos (by linarith) _) hden]
        have hC := (sixContourIntegrandDecayConstant_pos n).le
        nlinarith
      _ = (2 * sixContourIntegrandDecayConstant n) * ‖g y‖ := by
        simp only [g, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden), div_eq_mul_inv]
  have htop : sixVerticalIntegrand n i j =O[atTop] g :=
    Asymptotics.isBigO_iff.mpr ⟨2 * sixContourIntegrandDecayConstant n,
      (eventually_ge_atTop (sixContourDecayRadius n)).mono fun y hy =>
        hbound y (hy.trans (le_abs_self y))⟩
  have hbot : sixVerticalIntegrand n i j =O[atBot] g :=
    Asymptotics.isBigO_iff.mpr ⟨2 * sixContourIntegrandDecayConstant n,
      (eventually_le_atBot (-sixContourDecayRadius n)).mono fun y hy =>
        hbound y (by linarith [neg_le_abs y])⟩
  exact (sixVerticalIntegrand_continuous n i j).locallyIntegrable
    |>.integrable_of_isBigO_atBot_atTop hbot (integrable_inv_one_add_sq.integrableAtFilter _)
      htop (integrable_inv_one_add_sq.integrableAtFilter _)

def sixVerticalIntegral (n i j : ℕ) : ℂ := ∫ y : ℝ, sixVerticalIntegrand n i j y

def sixVerticalTruncation (n i j : ℕ) (q : ℝ) : ℂ :=
  ∫ y in -q..q, sixVerticalIntegrand n i j y

def sixHorizontalClosingIntegral (n i j q : ℕ) (y : ℝ) : ℂ :=
  ∫ x in sixContourAbscissa n..((q : ℝ) + 1 / 2),
    sixContourIntegrand n i j ((x : ℂ) + (y : ℂ) * Complex.I)

def sixRightClosingIntegral (n i j q : ℕ) : ℂ :=
  ∫ y in -(q : ℝ)..(q : ℝ),
    sixContourIntegrand n i j (((q : ℂ) + 1 / 2) + (y : ℂ) * Complex.I) * Complex.I

def sixClockwiseRectangleIntegral (n i j q : ℕ) : ℂ :=
  sixVerticalTruncation n i j q +
    sixHorizontalClosingIntegral n i j q q -
    sixRightClosingIntegral n i j q -
    sixHorizontalClosingIntegral n i j q (-q)

private theorem edge_bound_simplify (n : ℕ) (r : ℝ) (hr : 0 < r) :
    sixContourIntegrandDecayConstant n / r ^ (114 * n + 17) * (2 * r) =
      2 * sixContourIntegrandDecayConstant n / r ^ (114 * n + 16) := by
  rw [show 114 * n + 17 = (114 * n + 16) + 1 by omega, pow_succ]
  field_simp

private theorem integrand_norm_le_of_radius (n : ℕ) (i j : Fin (rank n))
    (z : ℂ) (r : ℝ) (hr : sixContourDecayRadius n ≤ r) (hz : r ≤ ‖z‖)
    (hs : 1 ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖) :
    ‖sixContourIntegrand n i j z‖ ≤
      sixContourIntegrandDecayConstant n / r ^ (114 * n + 17) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    ((sixContourDecayRadius_ge_two n).trans hr)
  exact (sixContourIntegrand_norm_le_decay n i j z (hr.trans hz) hs).trans
    (div_le_div_of_nonneg_left (sixContourIntegrandDecayConstant_pos n).le
      (pow_pos hr0 _) (pow_le_pow_left₀ hr0.le hz _))

theorem sixClockwiseRectangleIntegral_tendsto (n : ℕ) (i j : Fin (rank n)) :
    Tendsto (fun q : ℕ => sixClockwiseRectangleIntegral n i j q) atTop
      (𝓝 (sixVerticalIntegral n i j)) := by
  have hvert : Tendsto (fun q : ℕ => sixVerticalTruncation n i j q) atTop
      (𝓝 (sixVerticalIntegral n i j)) :=
    (intervalIntegral_tendsto_integral (sixVerticalIntegrand_integrable n i j)
      tendsto_neg_atTop_atBot tendsto_id).comp tendsto_natCast_atTop_atTop
  have hhor : ∀ (y : ℕ → ℝ), (∀ q, |y q| = q) →
      Tendsto (fun q : ℕ => sixHorizontalClosingIntegral n i j q (y q)) atTop (𝓝 0) := by
    intro y hy
    apply squeeze_zero_norm' (a := fun q : ℕ =>
      2 * sixContourIntegrandDecayConstant n / (q : ℝ) ^ (114 * n + 16))
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop (sixContourDecayRadius n))] with q hq
      have hq2 : (2 : ℝ) ≤ q := (sixContourDecayRadius_ge_two n).trans hq
      have hq0 : (0 : ℝ) < q := by linarith
      have hlen : |((q : ℝ) + 1 / 2) - sixContourAbscissa n| ≤ 2 * (q : ℝ) := by
        dsimp [sixContourAbscissa, sixContourDecayRadius] at *
        rw [abs_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])]
        linarith [Nat.cast_nonneg (α := ℝ) n]
      calc
        ‖sixHorizontalClosingIntegral n i j q (y q)‖
            ≤ (sixContourIntegrandDecayConstant n / (q : ℝ) ^ (114 * n + 17)) *
                |((q : ℝ) + 1 / 2) - sixContourAbscissa n| := by
              apply intervalIntegral.norm_integral_le_of_norm_le_const
              intro x _
              apply integrand_norm_le_of_radius n i j _ (q : ℝ) hq
              · simpa [hy q] using Complex.abs_im_le_norm ((x : ℂ) + (y q : ℂ) * Complex.I)
              · apply six_sin_norm_ge_one_of_im
                simpa [hy q] using (show (1 : ℝ) ≤ q by linarith)
        _ ≤ (sixContourIntegrandDecayConstant n / (q : ℝ) ^ (114 * n + 17)) * (2 * (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hlen
            (div_nonneg (sixContourIntegrandDecayConstant_pos n).le (pow_nonneg (Nat.cast_nonneg q) _))
        _ = _ := edge_bound_simplify n q hq0
    · exact tendsto_const_div_pow _ _ (by omega)
  have hright : Tendsto (fun q : ℕ => sixRightClosingIntegral n i j q) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun q : ℕ =>
      2 * sixContourIntegrandDecayConstant n / (q : ℝ) ^ (114 * n + 16))
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop (sixContourDecayRadius n))] with q hq
      have hq2 : (2 : ℝ) ≤ q := (sixContourDecayRadius_ge_two n).trans hq
      have hq0 : (0 : ℝ) < q := by linarith
      calc
        ‖sixRightClosingIntegral n i j q‖
            ≤ (sixContourIntegrandDecayConstant n / (q : ℝ) ^ (114 * n + 17)) *
                |(q : ℝ) - -(q : ℝ)| := by
              apply intervalIntegral.norm_integral_le_of_norm_le_const
              intro y _
              rw [norm_mul, Complex.norm_I, mul_one]
              apply integrand_norm_le_of_radius n i j _ (q : ℝ) hq
              · have h : (q : ℝ) + 1 / 2 ≤ ‖((q : ℂ) + 1 / 2) + (y : ℂ) * Complex.I‖ := by
                  simpa using Complex.re_le_norm (((q : ℂ) + 1 / 2) + (y : ℂ) * Complex.I)
                linarith
              · exact six_sin_norm_ge_one_half_integer (q : ℤ) _ (by simp)
        _ = _ := by
          rw [show |(q : ℝ) - -(q : ℝ)| = 2 * (q : ℝ) by
            rw [sub_neg_eq_add, abs_of_nonneg (by positivity)]; ring]
          exact edge_bound_simplify n q hq0
    · exact tendsto_const_div_pow _ _ (by omega)
  have htop := hhor (fun q => (q : ℝ)) (fun q => by simp)
  have hbot := hhor (fun q => -(q : ℝ)) (fun q => by simp)
  simpa only [sixClockwiseRectangleIntegral, add_zero, sub_zero] using
    ((hvert.add htop).sub hright).sub hbot

/-! ## Section 4: Rectangle residue identity and exact vertical contour theorem -/

private def sixRectBoundary (a b h : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x in a..b, f ((x : ℂ) + (-h : ℝ) * I)) -
    (∫ x in a..b, f ((x : ℂ) + (h : ℂ) * I)) +
    (∫ y in -h..h, f ((b : ℂ) + (y : ℂ) * I) * I) -
    (∫ y in -h..h, f ((a : ℂ) + (y : ℂ) * I) * I)

private theorem horizontal_primitive (F f : ℂ → ℂ) (a b y : ℝ)
    (hd : ∀ x ∈ uIcc a b, HasDerivAt F (f ((x : ℂ) + (y : ℂ) * I))
      ((x : ℂ) + (y : ℂ) * I))
    (hi : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) volume a b) :
    (∫ x in a..b, f ((x : ℂ) + (y : ℂ) * I)) =
      F ((b : ℂ) + (y : ℂ) * I) - F ((a : ℂ) + (y : ℂ) * I) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro x hx
  simpa using ((hd x hx).comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I))).comp_ofReal

private theorem vertical_primitive (F f : ℂ → ℂ) (a h : ℝ)
    (hd : ∀ y ∈ uIcc (-h) h, HasDerivAt F (f ((a : ℂ) + (y : ℂ) * I))
      ((a : ℂ) + (y : ℂ) * I))
    (hi : IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I) * I) volume (-h) h) :
    (∫ y in -h..h, f ((a : ℂ) + (y : ℂ) * I) * I) =
      F ((a : ℂ) + (h : ℂ) * I) - F ((a : ℂ) + (-h : ℝ) * I) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro y hy
  simpa using ((hd y hy).comp (y : ℂ)
    (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (a : ℂ))).comp_ofReal

private theorem sixRectBoundary_eq_zero_of_analytic (a b h : ℝ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (uIcc a b ×ℂ uIcc (-h) h)) :
    sixRectBoundary a b h f = 0 := by
  have ht := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) + (-h : ℝ) * I) ((b : ℂ) + (h : ℂ) * I)
    (by simpa using hf.differentiableOn)
  simpa only [sixRectBoundary, add_re, ofReal_re, mul_re, ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, add_im, mul_im,
    mul_one, zero_add, smul_eq_mul, intervalIntegral.integral_mul_const,
    mul_comm I] using ht

private theorem log_neg_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - (Real.pi : ℂ) * I := by
  simp only [Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hz, ofReal_sub]; ring

private theorem log_neg_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi : ℂ) * I := by
  simp only [Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hz, ofReal_add]; ring

private theorem sixRectBoundary_simplePole (a b h c : ℝ)
    (hac : a < c) (hcb : c < b) (hh : 0 < h) :
    sixRectBoundary a b h (fun z => (z - (c : ℂ))⁻¹) = 2 * (Real.pi : ℂ) * I := by
  have hhor (y : ℝ) (hy : y ≠ 0) :
      (∫ x in a..b, (((x : ℂ) + (y : ℂ) * I) - (c : ℂ))⁻¹) =
        Complex.log ((b : ℂ) + (y : ℂ) * I - c) -
          Complex.log ((a : ℂ) + (y : ℂ) * I - c) := by
    apply horizontal_primitive (fun z => Complex.log (z - c)) (fun z => (z - c)⁻¹) a b y
    · intro x _
      have hs : (x : ℂ) + (y : ℂ) * I - c ∈ slitPlane :=
        mem_slitPlane_iff.mpr (Or.inr (by simpa using hy))
      simpa [Function.comp_def] using! (Complex.hasDerivAt_log hs).comp ((x : ℂ) + (y : ℂ) * I)
        ((hasDerivAt_id _).sub_const (c : ℂ))
    · apply Continuous.intervalIntegrable
      apply continuous_iff_continuousAt.mpr
      intro x
      have hz : (x : ℂ) + (y : ℂ) * I - c ≠ 0 := by
        intro he; have := congrArg Complex.im he; simp at this; exact hy this
      exact ContinuousAt.inv₀ (by fun_prop) hz
  have hvright : (∫ y in -h..h, (((b : ℂ) + (y : ℂ) * I) - (c : ℂ))⁻¹ * I) =
      Complex.log ((b : ℂ) + (h : ℂ) * I - c) -
        Complex.log ((b : ℂ) + (-h : ℝ) * I - c) := by
    apply vertical_primitive (fun z => Complex.log (z - c)) (fun z => (z - c)⁻¹) b h
    · intro y _
      have hs : (b : ℂ) + (y : ℂ) * I - c ∈ slitPlane :=
        mem_slitPlane_iff.mpr (Or.inl (by simpa using sub_pos.mpr hcb))
      simpa [Function.comp_def] using! (Complex.hasDerivAt_log hs).comp ((b : ℂ) + (y : ℂ) * I)
        ((hasDerivAt_id _).sub_const (c : ℂ))
    · apply Continuous.intervalIntegrable
      apply continuous_iff_continuousAt.mpr
      intro y
      apply ContinuousAt.mul _ continuousAt_const
      apply ContinuousAt.inv₀ (by fun_prop)
      intro he; have := congrArg Complex.re he; exact (sub_pos.mpr hcb).ne' (by simpa using this)
  have hvleft : (∫ y in -h..h, (((a : ℂ) + (y : ℂ) * I) - (c : ℂ))⁻¹ * I) =
      Complex.log (-((a : ℂ) + (h : ℂ) * I - c)) -
        Complex.log (-((a : ℂ) + (-h : ℝ) * I - c)) := by
    apply vertical_primitive (fun z => Complex.log (-(z - c))) (fun z => (z - c)⁻¹) a h
    · intro y _
      have hs : -((a : ℂ) + (y : ℂ) * I - c) ∈ slitPlane :=
        mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
      simpa only [Function.comp_def, id_eq, neg_inv, mul_neg, neg_mul, neg_neg, mul_one] using!
        (Complex.hasDerivAt_log hs).comp ((a : ℂ) + (y : ℂ) * I)
        (((hasDerivAt_id _).sub_const (c : ℂ)).neg)
    · apply Continuous.intervalIntegrable
      apply continuous_iff_continuousAt.mpr
      intro y
      apply ContinuousAt.mul _ continuousAt_const
      apply ContinuousAt.inv₀ (by fun_prop)
      intro he; have := congrArg Complex.re he; exact (sub_neg.mpr hac).ne (by simpa using this)
  unfold sixRectBoundary
  rw [hhor (-h) (neg_ne_zero.mpr hh.ne'), hhor h hh.ne', hvright, hvleft,
    log_neg_im_pos (by simpa using hh : 0 < ((a : ℂ) + (h : ℂ) * I - c).im),
    log_neg_im_neg (by simpa using neg_neg_of_pos hh : ((a : ℂ) + (-h : ℝ) * I - c).im < 0)]
  ring

private theorem horizontal_ne_real (x y c : ℝ) (hy : y ≠ 0) :
    (x : ℂ) + (y : ℂ) * I ≠ (c : ℂ) := by
  intro he; exact hy (by simpa using congrArg Complex.im he)

private theorem vertical_ne_real (x y c : ℝ) (hx : x ≠ c) :
    (x : ℂ) + (y : ℂ) * I ≠ (c : ℂ) := by
  intro he; exact hx (by simpa using congrArg Complex.re he)

private theorem sixRectBoundary_higherPole (a b h c : ℝ) (ha : a ≠ c) (hb : b ≠ c)
    (hh : h ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    sixRectBoundary a b h (fun z => ((z - (c : ℂ)) ^ (k + 1))⁻¹) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ t : ℕ, k = t + 1 := ⟨k - 1, by omega⟩
  let F : ℂ → ℂ := fun z => -((z - (c : ℂ)) ^ (k + 1))⁻¹ / ((k + 1 : ℕ) : ℂ)
  let f : ℂ → ℂ := fun z => ((z - (c : ℂ)) ^ (k + 1 + 1))⁻¹
  have hd : ∀ z ≠ (c : ℂ), HasDerivAt F (f z) z := by
    intro z hz
    have hz0 : z - (c : ℂ) ≠ 0 := sub_ne_zero.mpr hz
    have hk0 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show k + 1 ≠ 0 by omega)
    have h1 := ((((hasDerivAt_id z).sub_const (c : ℂ)).pow (k + 1)).inv
      (pow_ne_zero (k + 1) hz0)).neg.div_const ((k + 1 : ℕ) : ℂ)
    convert! h1 using 1
    simp only [f, id_eq, Pi.pow_apply, mul_one, Nat.add_sub_cancel]
    field_simp; simp only [pow_succ]; ring
  have hc : ∀ z ≠ (c : ℂ), ContinuousAt f z := fun z hz =>
    ContinuousAt.inv₀ (by fun_prop) (pow_ne_zero _ (sub_ne_zero.mpr hz))
  have hhori (y : ℝ) (hy : y ≠ 0) :
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) volume a b :=
    (continuous_iff_continuousAt.mpr fun x =>
      (hc _ (horizontal_ne_real x y c hy)).comp
        (f := fun x : ℝ => (x : ℂ) + (y : ℂ) * I) (by fun_prop)).intervalIntegrable a b
  have hvert (x : ℝ) (hx : x ≠ c) :
      IntervalIntegrable (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I) * I) volume (-h) h :=
    (continuous_iff_continuousAt.mpr fun y =>
      ((hc _ (vertical_ne_real x y c hx)).comp
        (f := fun y : ℝ => (x : ℂ) + (y : ℂ) * I) (by fun_prop)).mul
        continuousAt_const).intervalIntegrable (-h) h
  unfold sixRectBoundary
  rw [horizontal_primitive F f a b (-h)
        (fun x _ => hd _ (horizontal_ne_real x (-h) c (neg_ne_zero.mpr hh)))
        (hhori (-h) (neg_ne_zero.mpr hh)),
      horizontal_primitive F f a b h
        (fun x _ => hd _ (horizontal_ne_real x h c hh)) (hhori h hh),
      vertical_primitive F f b h (fun y _ => hd _ (vertical_ne_real b y c hb)) (hvert b hb),
      vertical_primitive F f a h (fun y _ => hd _ (vertical_ne_real a y c ha)) (hvert a ha)]
  ring

private def sixPolePrincipal (f : ℂ → ℂ) (c z : ℂ) : ℂ :=
  sixPoleTaylorTail f c 0 c / (z - c) ^ 5 +
  sixPoleTaylorTail f c 1 c / (z - c) ^ 4 +
  sixPoleTaylorTail f c 2 c / (z - c) ^ 3 +
  sixPoleTaylorTail f c 3 c / (z - c) ^ 2 +
  sixPoleTaylorTail f c 4 c / (z - c)

private theorem taylor_step (f : ℂ → ℂ) (c z : ℂ) (k : ℕ) :
    (z - c) * sixPoleTaylorTail f c (k + 1) z =
      sixPoleTaylorTail f c k z - sixPoleTaylorTail f c k c := by
  simpa only [sixPoleTaylorTail, Function.iterate_succ_apply', Function.swap,
    smul_eq_mul] using sub_smul_dslope (sixPoleTaylorTail f c k) c z

private theorem sixPolePrincipal_exact (f : ℂ → ℂ) (c z : ℂ) (hz : z ≠ c) :
    f z / (z - c) ^ 5 = sixPolePrincipal f c z + sixPoleTaylorTail f c 5 z := by
  have h0 := taylor_step f c z 0; have h1 := taylor_step f c z 1
  have h2 := taylor_step f c z 2; have h3 := taylor_step f c z 3
  have h4 := taylor_step f c z 4
  have hz0 := sub_ne_zero.mpr hz
  unfold sixPolePrincipal
  apply (div_eq_iff (pow_ne_zero 5 hz0)).mpr
  field_simp
  change (z - c) * sixPoleTaylorTail f c 1 z = f z - f c at h0
  rw [show sixPoleTaylorTail f c 0 c = f c from rfl]
  linear_combination -h0 - (z - c) * h1 - (z - c) ^ 2 * h2 - (z - c) ^ 3 * h3 - (z - c) ^ 4 * h4

private theorem sixPolePrincipal_analyticAt (f : ℂ → ℂ) (c z : ℂ) (hz : z ≠ c) :
    AnalyticAt ℂ (sixPolePrincipal f c) z := by
  have hd : AnalyticAt ℂ (fun w : ℂ => w - c) z := analyticAt_id.sub analyticAt_const
  have hz0 := sub_ne_zero.mpr hz
  exact ((((analyticAt_const.div (hd.pow 5) (pow_ne_zero 5 hz0)).add
    (analyticAt_const.div (hd.pow 4) (pow_ne_zero 4 hz0))).add
    (analyticAt_const.div (hd.pow 3) (pow_ne_zero 3 hz0))).add
    (analyticAt_const.div (hd.pow 2) (pow_ne_zero 2 hz0))).add
    (analyticAt_const.div hd hz0)

private structure SixRectIntegrable (a b h : ℝ) (f : ℂ → ℂ) : Prop where
  bottom : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (-h : ℝ) * I)) volume a b
  top : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (h : ℂ) * I)) volume a b
  right : IntervalIntegrable (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * I) * I) volume (-h) h
  left : IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I) * I) volume (-h) h

private theorem sixRectIntegrable_of_edges (a b h : ℝ) (f : ℂ → ℂ)
    (hbot : ∀ x ∈ uIcc a b, ContinuousAt f ((x : ℂ) + (-h : ℝ) * I))
    (htop : ∀ x ∈ uIcc a b, ContinuousAt f ((x : ℂ) + (h : ℂ) * I))
    (hr : ∀ y ∈ uIcc (-h) h, ContinuousAt f ((b : ℂ) + (y : ℂ) * I))
    (hl : ∀ y ∈ uIcc (-h) h, ContinuousAt f ((a : ℂ) + (y : ℂ) * I)) :
    SixRectIntegrable a b h f :=
  ⟨ContinuousOn.intervalIntegrable fun x hx =>
      ((hbot x hx).comp (f := fun x : ℝ => (x : ℂ) + (-h : ℝ) * I) (by fun_prop)).continuousWithinAt,
   ContinuousOn.intervalIntegrable fun x hx =>
      ((htop x hx).comp (f := fun x : ℝ => (x : ℂ) + (h : ℂ) * I) (by fun_prop)).continuousWithinAt,
   ContinuousOn.intervalIntegrable fun y hy =>
      (((hr y hy).comp (f := fun y : ℝ => (b : ℂ) + (y : ℂ) * I) (by fun_prop)).mul
        continuousAt_const).continuousWithinAt,
   ContinuousOn.intervalIntegrable fun y hy =>
      (((hl y hy).comp (f := fun y : ℝ => (a : ℂ) + (y : ℂ) * I) (by fun_prop)).mul
        continuousAt_const).continuousWithinAt⟩

private theorem SixRectIntegrable.add {a b h : ℝ} {f g : ℂ → ℂ}
    (hf : SixRectIntegrable a b h f) (hg : SixRectIntegrable a b h g) :
    SixRectIntegrable a b h (fun z => f z + g z) :=
  ⟨hf.bottom.add hg.bottom, hf.top.add hg.top,
   by simpa only [add_mul] using hf.right.add hg.right,
   by simpa only [add_mul] using hf.left.add hg.left⟩

private theorem SixRectIntegrable.const_mul {a b h : ℝ} {f : ℂ → ℂ}
    (hf : SixRectIntegrable a b h f) (c : ℂ) :
    SixRectIntegrable a b h (fun z => c * f z) :=
  ⟨hf.bottom.const_mul c, hf.top.const_mul c,
   by simpa only [mul_assoc] using hf.right.const_mul c,
   by simpa only [mul_assoc] using hf.left.const_mul c⟩

private theorem sixRectBoundary_add {a b h : ℝ} {f g : ℂ → ℂ}
    (hf : SixRectIntegrable a b h f) (hg : SixRectIntegrable a b h g) :
    sixRectBoundary a b h (fun z => f z + g z) =
      sixRectBoundary a b h f + sixRectBoundary a b h g := by
  unfold sixRectBoundary
  simp only [add_mul, intervalIntegral.integral_add hf.bottom hg.bottom,
    intervalIntegral.integral_add hf.top hg.top,
    intervalIntegral.integral_add hf.right hg.right,
    intervalIntegral.integral_add hf.left hg.left]
  ring

private theorem sixRectBoundary_const_mul (a b h : ℝ) (f : ℂ → ℂ) (c : ℂ) :
    sixRectBoundary a b h (fun z => c * f z) = c * sixRectBoundary a b h f := by
  unfold sixRectBoundary
  simp only [mul_assoc, intervalIntegral.integral_const_mul]
  ring

private theorem sixRectIntegrable_purePole (a b h c : ℝ) (ha : a ≠ c) (hb : b ≠ c)
    (hh : h ≠ 0) (k : ℕ) :
    SixRectIntegrable a b h (fun z => ((z - (c : ℂ)) ^ k)⁻¹) := by
  have hf (z : ℂ) (hz : z ≠ c) : ContinuousAt (fun w : ℂ => ((w - c) ^ k)⁻¹) z :=
    ContinuousAt.inv₀ (by fun_prop) (pow_ne_zero k (sub_ne_zero.mpr hz))
  exact sixRectIntegrable_of_edges a b h _
    (fun x _ => hf _ (horizontal_ne_real x (-h) c (neg_ne_zero.mpr hh)))
    (fun x _ => hf _ (horizontal_ne_real x h c hh))
    (fun y _ => hf _ (vertical_ne_real b y c hb))
    (fun y _ => hf _ (vertical_ne_real a y c ha))

private theorem sixRectIntegrable_principal (a b h c : ℝ) (ha : a ≠ c) (hb : b ≠ c)
    (hh : h ≠ 0) (f : ℂ → ℂ) : SixRectIntegrable a b h (sixPolePrincipal f c) := by
  have hi (k : ℕ) := sixRectIntegrable_purePole a b h c ha hb hh k
  unfold sixPolePrincipal
  simpa only [div_eq_mul_inv, pow_one] using
    ((((hi 5).const_mul (sixPoleTaylorTail f c 0 c)).add
      ((hi 4).const_mul (sixPoleTaylorTail f c 1 c))).add
      ((hi 3).const_mul (sixPoleTaylorTail f c 2 c))).add
      ((hi 2).const_mul (sixPoleTaylorTail f c 3 c)) |>.add
      ((hi 1).const_mul (sixPoleTaylorTail f c 4 c))

private theorem sixRectBoundary_principal (a b h c : ℝ) (hac : a < c) (hcb : c < b)
    (hh : 0 < h) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f (c : ℂ)) :
    sixRectBoundary a b h (sixPolePrincipal f c) =
      (2 * (Real.pi : ℂ) * I) * (iteratedDeriv 4 f c / 24) := by
  have hi (k : ℕ) := sixRectIntegrable_purePole a b h c hac.ne hcb.ne.symm hh.ne' k
  have hc (k r : ℕ) := (hi k).const_mul (sixPoleTaylorTail f c r c)
  unfold sixPolePrincipal
  simp only [div_eq_mul_inv]
  rw [sixRectBoundary_add (((hc 5 0).add (hc 4 1)).add (hc 3 2) |>.add (hc 2 3))
      (by simpa only [pow_one] using hc 1 4),
    sixRectBoundary_add (((hc 5 0).add (hc 4 1)).add (hc 3 2)) (hc 2 3),
    sixRectBoundary_add ((hc 5 0).add (hc 4 1)) (hc 3 2),
    sixRectBoundary_add (hc 5 0) (hc 4 1)]
  simp only [sixRectBoundary_const_mul]
  rw [sixRectBoundary_higherPole a b h c hac.ne hcb.ne.symm hh.ne' 4 (by norm_num),
    sixRectBoundary_higherPole a b h c hac.ne hcb.ne.symm hh.ne' 3 (by norm_num),
    sixRectBoundary_higherPole a b h c hac.ne hcb.ne.symm hh.ne' 2 (by norm_num),
    sixRectBoundary_higherPole a b h c hac.ne hcb.ne.symm hh.ne' 1 (by norm_num),
    sixRectBoundary_simplePole a b h c hac hcb hh,
    sixPoleTaylorTail_at_center hf 4]
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat]
  ring

private theorem fill_finite_analytic (S : Finset ℂ) (U : Set ℂ) (f : ℂ → ℂ)
    (hf : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z)
    (hloc : ∀ c ∈ S, ∃ A : ℂ → ℂ, AnalyticAt ℂ A c ∧ f =ᶠ[𝓝[≠] c] A) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧ ∀ z ∉ S, G z = f z := by
  classical
  let A : ℂ → ℂ → ℂ := fun c => if hc : c ∈ S then (hloc c hc).choose else f
  have hA (c : ℂ) (hc : c ∈ S) : AnalyticAt ℂ (A c) c ∧ f =ᶠ[𝓝[≠] c] A c := by
    simpa only [A, dite_eq_left hc] using (hloc c hc).choose_spec
  let G : ℂ → ℂ := fun z => if z ∈ S then A z z else f z
  refine ⟨G, ?_, fun z hz => by simp only [G, ite_eq_right hz]⟩
  intro c hcU
  by_cases hc : c ∈ S
  · apply (hA c hc).1.congr
    have he : ∀ᶠ z in 𝓝 c, z ∉ S.erase c :=
      (S.erase c).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [he, eventually_nhdsWithin_iff.mp (hA c hc).2] with z hz hzg
    by_cases hzc : z = c
    · subst z; simp only [G, ite_eq_left hc]
    · have hzs : z ∉ S := fun hzs => hz (Finset.mem_erase.mpr ⟨hzc, hzs⟩)
      simpa only [G, ite_eq_right hzs] using (hzg hzc).symm
  · apply (hf c hcU hc).congr
    filter_upwards [S.finite_toSet.isClosed.isOpen_compl.mem_nhds hc] with z hz
    have hz' : z ∉ S := hz
    simp only [G, ite_eq_right hz']

private theorem finite_principal_removal (S : Finset ℂ) (U : Set ℂ)
    (f g : ℂ → ℂ) (hf : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z)
    (hloc : ∀ c ∈ S, ∃ A : ℂ → ℂ, AnalyticAt ℂ A c ∧
      f =ᶠ[𝓝[≠] c] (fun z => sixPolePrincipal g c z + A z)) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      ∀ z ∉ S, f z = G z + ∑ c ∈ S, sixPolePrincipal g c z := by
  classical
  let R : ℂ → ℂ := fun z => f z - ∑ c ∈ S, sixPolePrincipal g c z
  obtain ⟨G, hG, he⟩ := fill_finite_analytic S U R
    (fun z hz hzs => (hf z hz hzs).sub (by
      convert! S.analyticAt_sum
        (fun c hc => sixPolePrincipal_analyticAt g c z (fun he => hzs (he ▸ hc))) using 1
      funext w; simp only [Finset.sum_apply]))
    (fun c hc => by
      obtain ⟨A, hA, he⟩ := hloc c hc
      refine ⟨fun z => A z - ∑ d ∈ S.erase c, sixPolePrincipal g d z, ?_, ?_⟩
      · apply hA.sub
        convert! (S.erase c).analyticAt_sum
          (fun d hd => sixPolePrincipal_analyticAt g d c (Finset.mem_erase.mp hd).1.symm) using 1
        funext w; simp only [Finset.sum_apply]
      · filter_upwards [he] with z hz
        dsimp only [R]; rw [← Finset.add_sum_erase _ _ hc, hz]; ring)
  refine ⟨G, hG, fun z hz => ?_⟩
  have ht := he z hz; dsimp only [R] at ht; linear_combination -ht

private def sixRectanglePoleSet (n q : ℕ) : Finset ℂ :=
  (Finset.Icc (-(n : ℤ)) (q : ℤ)).image (fun m : ℤ => (m : ℂ))

private theorem sixRectanglePoleSet_mem (n q : ℕ) (z : ℂ) :
    z ∈ sixRectanglePoleSet n q ↔
      ∃ m : ℤ, -(n : ℤ) ≤ m ∧ m ≤ (q : ℤ) ∧ (m : ℂ) = z := by
  simp only [sixRectanglePoleSet, Finset.mem_image, Finset.mem_Icc]; aesop

/-- **Main Vertical Contour Identity**: for every `n` and `i, j < 15 n`, the complete
upward vertical line integral along `Re z = -n - 1/2` equals `-(2 π i) * sixFunctional n i j`. -/
theorem sixVerticalIntegral_eq_functional (n : ℕ) (i j : Fin (rank n)) :
    sixVerticalIntegral n i j =
      -(2 * (Real.pi : ℂ) * I) * (sixFunctional n i j : ℂ) := by
  classical
  have hrect : ∀ q : ℕ, 1 ≤ q →
      sixClockwiseRectangleIntegral n i j q =
        -(2 * (Real.pi : ℂ) * I) *
          ∑ v ∈ Finset.range (q + n + 1),
            iteratedDeriv 4 (sixEntryComplex n i j) ((v : ℂ) - (n : ℂ)) / 24 := by
    intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hab : sixContourAbscissa n ≤ (q : ℝ) + 1 / 2 := by
      dsimp [sixContourAbscissa]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hclock : sixClockwiseRectangleIntegral n i j q =
        -sixRectBoundary (sixContourAbscissa n) ((q : ℝ) + 1 / 2) q
          (sixContourIntegrand n i j) := by
      unfold sixClockwiseRectangleIntegral sixRectBoundary sixHorizontalClosingIntegral
        sixRightClosingIntegral sixVerticalTruncation sixVerticalIntegrand sixContourPoint
      simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_natCast,
        Complex.ofReal_one, Complex.ofReal_ofNat]
      ring
    rw [hclock]
    obtain ⟨G, hG, he⟩ := finite_principal_removal (sixRectanglePoleSet n q)
      (Icc (sixContourAbscissa n) ((q : ℝ) + 1 / 2) ×ℂ Icc (-(q : ℝ)) q)
      (sixContourIntegrand n i j) (sixEntryComplex n i j)
      (fun z hz hzs => by
        apply sixContourIntegrand_analyticAt n i j z hz.1.1
        intro hs
        obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp hs
        have hzm : z = (m : ℂ) := by
          apply mul_left_cancel₀ (show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero)
          simpa only [mul_comm] using hm
        have hmlo : -(n : ℤ) ≤ m := by
          have hb := hz.1.1; rw [hzm] at hb
          simp only [intCast_re, sixContourAbscissa] at hb
          have : -(n : ℝ) - 1 < (m : ℝ) := by linarith
          have : -(n : ℤ) - 1 < m := by exact_mod_cast this
          omega
        have hmhi : m ≤ (q : ℤ) := by
          have hb := hz.1.2; rw [hzm] at hb; simp only [intCast_re] at hb
          have : (m : ℝ) < (q : ℝ) + 1 := by linarith
          have : m < (q : ℤ) + 1 := by exact_mod_cast this
          omega
        exact hzs ((sixRectanglePoleSet_mem n q z).mpr ⟨m, hmlo, hmhi, hzm.symm⟩))
      (fun c hc => by
        obtain ⟨m, hmlo, _, rfl⟩ := (sixRectanglePoleSet_mem n q c).mp hc
        have hm : sixContourAbscissa n < (m : ℝ) := by
          have : -(n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmlo
          dsimp [sixContourAbscissa]; linarith
        have hf : AnalyticAt ℂ (sixEntryComplex n i j) (m : ℂ) :=
          sixEntryComplex_analyticAt n i j _ (by
            simpa using (lt_trans (sixContourAbscissa_in_halfplane n) hm))
        obtain ⟨A, hA, hK⟩ := sixContourKernel_principal_part m
        refine ⟨fun z => sixPoleTaylorTail (sixEntryComplex n i j) m 5 z +
          sixEntryComplex n i j z * A z, (sixPoleTaylorTail_analytic hf 5).add (hf.mul hA), ?_⟩
        filter_upwards [hK, self_mem_nhdsWithin] with z hz hzm
        rw [sixContourIntegrand, hz, mul_add, mul_one_div, sixPolePrincipal_exact _ _ _ hzm]; ring)
    have hG' : AnalyticOnNhd ℂ G
        (uIcc (sixContourAbscissa n) ((q : ℝ) + 1 / 2) ×ℂ uIcc (-(q : ℝ)) q) := by
      simpa only [uIcc_of_le hab, uIcc_of_le (by linarith : -(q : ℝ) ≤ q)] using hG
    have hGint : SixRectIntegrable (sixContourAbscissa n) ((q : ℝ) + 1 / 2) q G :=
      sixRectIntegrable_of_edges _ _ _ _
        (fun x hx => (hG' _ (by simpa [mem_reProdIm] using And.intro hx (left_mem_uIcc : -(q : ℝ) ∈ uIcc (-(q : ℝ)) q))).continuousAt)
        (fun x hx => (hG' _ (by simpa [mem_reProdIm] using And.intro hx (right_mem_uIcc : (q : ℝ) ∈ uIcc (-(q : ℝ)) q))).continuousAt)
        (fun y hy => (hG' _ (by simpa [mem_reProdIm] using And.intro (right_mem_uIcc : (q : ℝ) + 1 / 2 ∈ uIcc (sixContourAbscissa n) ((q : ℝ) + 1 / 2)) hy)).continuousAt)
        (fun y hy => (hG' _ (by simpa [mem_reProdIm] using And.intro (left_mem_uIcc : sixContourAbscissa n ∈ uIcc (sixContourAbscissa n) ((q : ℝ) + 1 / 2)) hy)).continuousAt)
    have hpb : ∀ c ∈ sixRectanglePoleSet n q,
        c.im = 0 ∧ sixContourAbscissa n < c.re ∧ c.re < (q : ℝ) + 1 / 2 := by
      intro c hc
      obtain ⟨m, hmlo, hmhi, rfl⟩ := (sixRectanglePoleSet_mem n q c).mp hc
      have hlo : -(n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmlo
      have hhi : (m : ℝ) ≤ (q : ℝ) := by exact_mod_cast hmhi
      simp only [intCast_im, intCast_re, sixContourAbscissa, true_and]
      exact ⟨by linarith, by linarith⟩
    have hpi (c : ℂ) (hc : c ∈ sixRectanglePoleSet n q) :
        SixRectIntegrable (sixContourAbscissa n) ((q : ℝ) + 1 / 2) q
          (sixPolePrincipal (sixEntryComplex n i j) c) := by
      have hb := hpb c hc
      have hec : (c.re : ℂ) = c := by apply Complex.ext <;> simp [hb.1]
      rw [← hec]
      exact sixRectIntegrable_principal _ _ _ _ hb.2.1.ne hb.2.2.ne.symm hq0.ne' _
    have hsumInt : SixRectIntegrable (sixContourAbscissa n) ((q : ℝ) + 1 / 2) q
        (fun z => ∑ c ∈ sixRectanglePoleSet n q, sixPolePrincipal (sixEntryComplex n i j) c z) :=
      ⟨by convert! IntervalIntegrable.sum _ (fun c hc => (hpi c hc).bottom) using 1; funext x; simp,
       by convert! IntervalIntegrable.sum _ (fun c hc => (hpi c hc).top) using 1; funext x; simp,
       by convert! IntervalIntegrable.sum _ (fun c hc => (hpi c hc).right) using 1; funext y; simp [Finset.sum_mul],
       by convert! IntervalIntegrable.sum _ (fun c hc => (hpi c hc).left) using 1; funext y; simp [Finset.sum_mul]⟩
    have hbd_eq : sixRectBoundary (sixContourAbscissa n) ((q : ℝ) + 1 / 2) q
        (sixContourIntegrand n i j) =
        (2 * (Real.pi : ℂ) * I) *
          ∑ c ∈ sixRectanglePoleSet n q, iteratedDeriv 4 (sixEntryComplex n i j) c / 24 := by
      have hhor (x y : ℝ) (hy : y ≠ 0) : (x : ℂ) + (y : ℂ) * I ∉ sixRectanglePoleSet n q := fun hc =>
        hy (by simpa using (hpb _ hc).1)
      have hver (y x : ℝ) (hx : x = sixContourAbscissa n ∨ x = (q : ℝ) + 1 / 2) :
          (x : ℂ) + (y : ℂ) * I ∉ sixRectanglePoleSet n q := fun hc => by
        have hb := (hpb _ hc).2
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, zero_mul, sub_zero, add_zero] at hb
        rcases hx with rfl | rfl <;> linarith
      have hcongr : sixRectBoundary (sixContourAbscissa n) ((q : ℝ) + 1 / 2) q
          (sixContourIntegrand n i j) =
          sixRectBoundary (sixContourAbscissa n) ((q : ℝ) + 1 / 2) q
            (fun z => G z + ∑ c ∈ sixRectanglePoleSet n q,
              sixPolePrincipal (sixEntryComplex n i j) c z) := by
        unfold sixRectBoundary
        rw [intervalIntegral.integral_congr (fun x _ => he _ (hhor x (-q) (neg_ne_zero.mpr hq0.ne'))),
            intervalIntegral.integral_congr (fun x _ => he _ (hhor x q hq0.ne')),
            intervalIntegral.integral_congr (fun y _ => congrArg (· * I) (he _ (hver y _ (Or.inr rfl)))),
            intervalIntegral.integral_congr (fun y _ => congrArg (· * I) (he _ (hver y _ (Or.inl rfl))))]
      rw [hcongr, sixRectBoundary_add hGint hsumInt,
        sixRectBoundary_eq_zero_of_analytic _ _ _ _ hG', zero_add]
      have hsum_bd : sixRectBoundary (sixContourAbscissa n) ((q : ℝ) + 1 / 2) q
          (fun z => ∑ c ∈ sixRectanglePoleSet n q, sixPolePrincipal (sixEntryComplex n i j) c z) =
          ∑ c ∈ sixRectanglePoleSet n q,
            sixRectBoundary (sixContourAbscissa n) ((q : ℝ) + 1 / 2) q
              (sixPolePrincipal (sixEntryComplex n i j) c) := by
        unfold sixRectBoundary
        simp only [Finset.sum_mul]
        rw [intervalIntegral.integral_finsetSum (fun c hc => (hpi c hc).bottom),
            intervalIntegral.integral_finsetSum (fun c hc => (hpi c hc).top),
            intervalIntegral.integral_finsetSum (fun c hc => (hpi c hc).right),
            intervalIntegral.integral_finsetSum (fun c hc => (hpi c hc).left)]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hsum_bd, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have hb := hpb c hc
      have hec : (c.re : ℂ) = c := by apply Complex.ext <;> simp [hb.1]
      have hf := sixEntryComplex_analyticAt n i j c
        ((sixContourAbscissa_in_halfplane n).trans hb.2.1)
      simpa only [hec] using sixRectBoundary_principal
        (sixContourAbscissa n) ((q : ℝ) + 1 / 2) q c.re hb.2.1 hb.2.2 hq0
        (sixEntryComplex n i j) (by simpa only [hec] using hf)
    rw [hbd_eq, ← neg_mul]
    congr 1
    have hset : sixRectanglePoleSet n q =
        (Finset.range (q + n + 1)).image (fun v : ℕ => (v : ℂ) - (n : ℂ)) := by
      ext z
      rw [sixRectanglePoleSet_mem, Finset.mem_image]
      constructor
      · rintro ⟨m, hmlo, hmhi, rfl⟩
        have hm0 : 0 ≤ m + (n : ℤ) := by omega
        refine ⟨(m + (n : ℤ)).toNat, Finset.mem_range.mpr (by omega), ?_⟩
        have hv : (((m + (n : ℤ)).toNat : ℕ) : ℤ) = m + (n : ℤ) := Int.toNat_of_nonneg hm0
        have hvC : ((m + (n : ℤ)).toNat : ℂ) = (m : ℂ) + (n : ℂ) := by exact_mod_cast hv
        rw [hvC]; ring
      · rintro ⟨v, hv, rfl⟩
        have hv' := Finset.mem_range.mp hv
        exact ⟨(v : ℤ) - (n : ℤ), by omega, by omega, by push_cast; rfl⟩
    rw [hset, Finset.sum_image]
    intro a _ b _ h1
    have h2 : (a : ℂ) = b := by linear_combination h1
    exact_mod_cast h2
  have hlim : Tendsto (fun q : ℕ => ∑ v ∈ Finset.range (q + n + 1),
      iteratedDeriv 4 (sixEntryComplex n i j) ((v : ℂ) - (n : ℂ)) / 24)
      atTop (𝓝 (sixFunctional n i j : ℂ)) :=
    (hasSum_sixContour_residue_series n i j).tendsto_sum_nat.comp
      (tendsto_atTop.mpr fun b => eventually_atTop.2 ⟨b, fun q hq => by omega⟩)
  have hr := hlim.const_mul (-(2 * (Real.pi : ℂ) * I))
  have he : (fun q : ℕ => sixClockwiseRectangleIntegral n i j q) =ᶠ[atTop]
      (fun q : ℕ => -(2 * (Real.pi : ℂ) * I) *
        ∑ v ∈ Finset.range (q + n + 1),
          iteratedDeriv 4 (sixEntryComplex n i j) ((v : ℂ) - (n : ℂ)) / 24) :=
    (eventually_ge_atTop 1).mono hrect
  exact tendsto_nhds_unique (sixClockwiseRectangleIntegral_tendsto n i j) (hr.congr' he.symm)

/-! ## Section 5: Even polynomial basis change & Cauchy–Schwarz / Leibniz determinant bound -/

/-- Matrix of even-power coefficients `(f i).coeff (2 * j)`. -/
def sixEvenCoefficientMatrix {d : ℕ} (f : Fin d → ℚ[X]) : Matrix (Fin d) (Fin d) ℚ :=
  fun i j => (f i).coeff (2 * j.val)

def sixOriginalCoefficientMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℚ :=
  sixEvenCoefficientMatrix (fun i => evenBasis i.val)

private theorem sixEvenCoefficientMatrix_lower {d : ℕ} (f : Fin d → ℚ[X])
    (hdeg : ∀ i, (f i).natDegree ≤ 2 * i.val) :
    (sixEvenCoefficientMatrix f).IsLowerTriangular := fun i j hij =>
  coeff_eq_zero_of_natDegree_lt ((hdeg i).trans_lt (by simpa using hij))

private theorem sixOriginalCoefficientMatrix_lower (d : ℕ) :
    (sixOriginalCoefficientMatrix d).IsLowerTriangular :=
  sixEvenCoefficientMatrix_lower _ (fun i => (evenBasis_natDegree i.val).le)

private theorem sixOriginalCoefficientMatrix_diag (d : ℕ) (i : Fin d) :
    sixOriginalCoefficientMatrix d i i = (evenBasis i.val).leadingCoeff := by
  change (evenBasis i.val).coeff (2 * i.val) = _
  rw [← evenBasis_natDegree, coeff_natDegree]

private theorem sixOriginalCoefficientMatrix_det_ne_zero (d : ℕ) :
    (sixOriginalCoefficientMatrix d).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular _ (sixOriginalCoefficientMatrix_lower d)]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by
    rw [sixOriginalCoefficientMatrix_diag]
    exact ne_of_gt (evenBasis_leadingCoeff_pos i.val)

/-- Unique row transformation expressing an even polynomial basis `f` in terms of `evenBasis`. -/
def sixUnitBasisChange {d : ℕ} (f : Fin d → ℚ[X]) : Matrix (Fin d) (Fin d) ℚ :=
  sixEvenCoefficientMatrix f * (sixOriginalCoefficientMatrix d)⁻¹

theorem sixUnitBasisChange_det {d : ℕ} (f : Fin d → ℚ[X])
    (hdeg : ∀ i, (f i).natDegree = 2 * i.val)
    (hlead : ∀ i, (f i).leadingCoeff = (evenBasis i.val).leadingCoeff) :
    (sixUnitBasisChange f).det = 1 := by
  have hmul : sixUnitBasisChange f * sixOriginalCoefficientMatrix d =
      sixEvenCoefficientMatrix f :=
    Matrix.nonsing_inv_mul_cancel_right _ _
      (isUnit_iff_ne_zero.mpr (sixOriginalCoefficientMatrix_det_ne_zero d))
  have hlow : (sixUnitBasisChange f).IsLowerTriangular := by
    let := Matrix.invertibleOfIsUnitDet (sixOriginalCoefficientMatrix d)
      (isUnit_iff_ne_zero.mpr (sixOriginalCoefficientMatrix_det_ne_zero d))
    exact (sixEvenCoefficientMatrix_lower f (fun k => (hdeg k).le)).mul
      (Matrix.blockTriangular_inv_of_blockTriangular (sixOriginalCoefficientMatrix_lower d))
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  apply Finset.prod_eq_one
  intro i _
  have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℚ => M i i) hmul
  have hdiag : (sixUnitBasisChange f * sixOriginalCoefficientMatrix d) i i =
      sixUnitBasisChange f i i * sixOriginalCoefficientMatrix d i i := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hj | hj
      · rw [sixOriginalCoefficientMatrix_lower d hj, mul_zero]
      · rw [hlow hj, zero_mul]
    · simp
  rw [hdiag, sixOriginalCoefficientMatrix_diag] at he
  change _ = (f i).coeff (2 * i.val) at he
  rw [← hdeg i, coeff_natDegree, hlead i] at he
  exact (mul_eq_right₀ (ne_of_gt (evenBasis_leadingCoeff_pos i.val))).mp he

private theorem odd_coeff_zero_of_even (P : ℚ[X])
    (heven : P.comp (-X) = P) (q : ℕ) (hq : Odd q) : P.coeff q = 0 := by
  have h := congrArg (fun Q : ℚ[X] => Q.coeff q) heven
  have hc : (P.comp (-X)).coeff q = P.coeff q * (-1 : ℚ) ^ q := by
    simpa only [map_neg, map_one, neg_one_mul] using
      (Polynomial.comp_C_mul_X_coeff (p := P) (r := (-1 : ℚ)) (n := q))
  rw [hc, hq.neg_one_pow] at h
  linarith

theorem sixUnitBasisChange_polynomial {d : ℕ} (f : Fin d → ℚ[X])
    (heven : ∀ i, (f i).comp (-X) = f i)
    (hdeg : ∀ i, (f i).natDegree ≤ 2 * i.val) (i : Fin d) :
    f i = ∑ j : Fin d, C (sixUnitBasisChange f i j) * evenBasis j.val := by
  have hmul : sixUnitBasisChange f * sixOriginalCoefficientMatrix d =
      sixEvenCoefficientMatrix f :=
    Matrix.nonsing_inv_mul_cancel_right _ _
      (isUnit_iff_ne_zero.mpr (sixOriginalCoefficientMatrix_det_ne_zero d))
  apply Polynomial.ext
  intro q
  simp only [finsetSum_coeff, coeff_C_mul]
  rcases Nat.even_or_odd q with hq | hq
  · obtain ⟨k, hk⟩ := hq
    have hkq : q = 2 * k := by omega
    subst q
    by_cases hkd : k < d
    · have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℚ => M i ⟨k, hkd⟩) hmul
      simpa only [sixEvenCoefficientMatrix, sixOriginalCoefficientMatrix,
        Matrix.mul_apply, two_mul] using he.symm
    · rw [coeff_eq_zero_of_natDegree_lt (by have := i.isLt; have := hdeg i; omega)]
      symm
      exact Finset.sum_eq_zero fun j _ => by
        rw [coeff_eq_zero_of_natDegree_lt (by rw [evenBasis_natDegree]; have := j.isLt; omega),
          mul_zero]
  · rw [odd_coeff_zero_of_even (f i) (heven i) q hq]
    symm
    exact Finset.sum_eq_zero fun j _ => by
      rw [odd_coeff_zero_of_even _ (evenBasis_comp_neg_X j.val) q hq, mul_zero]

/-- Centered polynomial evaluated along the vertical contour `Re z = -n - 1/2`. -/
def sixBasisContourValue (n : ℕ) (P : ℚ[X]) (y : ℝ) : ℂ :=
  aeval (sixContourPoint n y) (P.comp (X + C (70 * (n : ℚ) + 1)))

/-- Nonnegative base modulus weight on the vertical contour, including `1 / (2 π)`. -/
def sixModulusWeight (n : ℕ) (y : ℝ) : ℝ :=
  ‖sixVerticalIntegrand n 0 0 y‖ / (2 * Real.pi)

theorem sixModulusWeight_nonneg (n : ℕ) (y : ℝ) : 0 ≤ sixModulusWeight n y := by
  unfold sixModulusWeight; positivity

/-- Positive diagonal modulus moment of a centered polynomial `P` along the contour. -/
def sixBasisModulusMoment (n : ℕ) (P : ℚ[X]) : ℝ :=
  ∫ y : ℝ, sixModulusWeight n y * ‖sixBasisContourValue n P y‖ ^ 2

theorem sixBasisModulusMoment_nonneg (n : ℕ) (P : ℚ[X]) : 0 ≤ sixBasisModulusMoment n P :=
  integral_nonneg fun y => mul_nonneg (sixModulusWeight_nonneg n y) (sq_nonneg _)

theorem sixBasisContourValue_scale (n : ℕ) (c : ℚ) (P : ℚ[X]) (y : ℝ) :
    sixBasisContourValue n (C c * P) y = (c : ℂ) * sixBasisContourValue n P y := by
  simp [sixBasisContourValue, mul_comp]

theorem sixBasisModulusMoment_scale (n : ℕ) (c : ℚ) (P : ℚ[X]) :
    sixBasisModulusMoment n (C c * P) = (c : ℝ) ^ 2 * sixBasisModulusMoment n P := by
  unfold sixBasisModulusMoment
  simp_rw [sixBasisContourValue_scale, norm_mul, mul_pow, Complex.norm_ratCast, sq_abs]
  rw [← integral_const_mul]
  congr 1; funext y; ring

private theorem sixVerticalIntegrand_factorization (n i j : ℕ) (y : ℝ) :
    sixVerticalIntegrand n i j y = sixVerticalIntegrand n 0 0 y *
      sixBasisContourValue n (evenBasis i) y * sixBasisContourValue n (evenBasis j) y := by
  simp only [sixVerticalIntegrand, sixContourIntegrand, sixEntryComplex,
    centeredMultiplier, evenBasis, mul_comp, map_mul, one_comp, mul_one, sixBasisContourValue]
  ring

private theorem det_abs_le_factorized {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (b : Fin k → ℝ) (hA : ∀ i j, |A i j| ≤ b i * b j) :
    |A.det| ≤ (k.factorial : ℝ) * ∏ i, (b i) ^ 2 := by
  let abv : AbsoluteValue ℝ ℝ := AbsoluteValue.abs
  change abv A.det ≤ _
  calc
    abv A.det = abv (∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • ∏ i, A (σ i) i) :=
      congrArg abv (Matrix.det_apply A)
    _ ≤ ∑ σ : Equiv.Perm (Fin k), abv (Equiv.Perm.sign σ • ∏ i, A (σ i) i) := abv.sum_le _ _
    _ = ∑ σ : Equiv.Perm (Fin k), ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl; intro σ _
      rw [abv.map_units_int_smul, abv.map_prod]; rfl
    _ ≤ ∑ σ : Equiv.Perm (Fin k), ∏ i, (b (σ i) * b i) :=
      Finset.sum_le_sum fun σ _ =>
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hA (σ i) i)
    _ = ∑ _σ : Equiv.Perm (Fin k), ∏ i, (b i) ^ 2 := by
      apply Finset.sum_congr rfl; intro σ _
      rw [Finset.prod_mul_distrib, Equiv.prod_comp σ, ← Finset.prod_mul_distrib]
      simp only [← sq]
    _ = _ := by simp [Fintype.card_perm, nsmul_eq_mul]

/-- **Changed-Basis Determinant Majorant**: for any even polynomial basis `f` matching the
degrees and leading coefficients of `evenBasis`, `|det (sixFunctional n)|` is bounded by
`(rank n)! * ∏ i, sixBasisModulusMoment n (f i)`. -/
theorem sixFunctional_det_abs_le_basisModulusMoments (n : ℕ)
    (f : Fin (rank n) → ℚ[X])
    (heven : ∀ i, (f i).comp (-X) = f i)
    (hdeg : ∀ i, (f i).natDegree = 2 * i.val)
    (hlead : ∀ i, (f i).leadingCoeff = (evenBasis i.val).leadingCoeff) :
    |Matrix.det (sixFunctional n)| ≤
      ((rank n).factorial : ℝ) * ∏ i : Fin (rank n), sixBasisModulusMoment n (f i) := by
  let UQ : Matrix (Fin (rank n)) (Fin (rank n)) ℚ := sixUnitBasisChange f
  let UR : Matrix (Fin (rank n)) (Fin (rank n)) ℝ := UQ.map (Rat.cast : ℚ → ℝ)
  let HM : Matrix (Fin (rank n)) (Fin (rank n)) ℝ := Matrix.of (sixFunctional n)
  let H' : Matrix (Fin (rank n)) (Fin (rank n)) ℝ := UR * HM * UR.transpose
  have hdetU : UR.det = 1 := by
    have h := (Rat.castHom ℝ).map_det UQ
    rw [sixUnitBasisChange_det f hdeg hlead, map_one] at h
    exact h.symm
  have hdet_eq : H'.det = Matrix.det (sixFunctional n) := by
    simp only [H', HM, Matrix.det_mul, Matrix.det_transpose, hdetU, one_mul, mul_one]; rfl
  rw [← hdet_eq]
  have hval (i : Fin (rank n)) (y : ℝ) :
      sixBasisContourValue n (f i) y =
        ∑ a : Fin (rank n), (UQ i a : ℂ) * sixBasisContourValue n (evenBasis a.val) y := by
    rw [sixBasisContourValue, sixUnitBasisChange_polynomial f heven (fun k => (hdeg k).le) i]
    simp only [Polynomial.sum_comp, mul_comp, C_comp, map_sum, map_mul, aeval_C,
      sixBasisContourValue]
    simp [UQ]
  let g (i j : Fin (rank n)) (y : ℝ) : ℂ :=
    sixVerticalIntegrand n 0 0 y * sixBasisContourValue n (f i) y * sixBasisContourValue n (f j) y
  have hg_exp (i j : Fin (rank n)) (y : ℝ) :
      g i j y = ∑ a : Fin (rank n), ∑ b : Fin (rank n),
        (UQ i a : ℂ) * sixVerticalIntegrand n a b y * (UQ j b : ℂ) := by
    simp only [g, hval i y, hval j y, mul_sum, sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [sixVerticalIntegrand_factorization n a b y]; ring
  have hg_int (i j : Fin (rank n)) : Integrable (g i j) := by
    change Integrable (fun y => g i j y)
    simp_rw [hg_exp i j]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      ((sixVerticalIntegrand_integrable n a b).const_mul _).mul_const _
  have hg_cont (i j : Fin (rank n)) : Continuous (g i j) := by
    change Continuous (fun y => g i j y)
    simp_rw [hg_exp i j]
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((sixVerticalIntegrand_continuous n a b).const_mul _).mul_const _
  have hg_eq (i j : Fin (rank n)) :
      (∫ y : ℝ, g i j y) = -(2 * (Real.pi : ℂ) * I) * (H' i j : ℂ) := by
    have hint (a b : Fin (rank n)) : Integrable (fun y : ℝ =>
        (UQ i a : ℂ) * sixVerticalIntegrand n a b y * (UQ j b : ℂ)) :=
      ((sixVerticalIntegrand_integrable n a b).const_mul _).mul_const _
    calc
      (∫ y : ℝ, g i j y)
          = ∑ a : Fin (rank n), ∑ b : Fin (rank n),
              ∫ y : ℝ, (UQ i a : ℂ) * sixVerticalIntegrand n a b y * (UQ j b : ℂ) := by
            simp_rw [hg_exp i j]
            rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hint a b))]
            exact Finset.sum_congr rfl fun a _ => integral_finsetSum _ (fun b _ => hint a b)
      _ = ∑ a : Fin (rank n), ∑ b : Fin (rank n),
            (UQ i a : ℂ) * sixVerticalIntegral n a b * (UQ j b : ℂ) := by
            simp only [integral_mul_const, integral_const_mul, sixVerticalIntegral]
      _ = -(2 * (Real.pi : ℂ) * I) * (H' i j : ℂ) := by
            simp only [H', HM, UR, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
              Matrix.of_apply, Finset.sum_mul, Complex.ofReal_sum, Complex.ofReal_mul,
              Complex.ofReal_ratCast]
            rw [Finset.sum_comm]
            simp_rw [sixVerticalIntegral_eq_functional, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro b _
            ring
  have hentry (i j : Fin (rank n)) :
      |H' i j| ≤ Real.sqrt (sixBasisModulusMoment n (f i)) *
        Real.sqrt (sixBasisModulusMoment n (f j)) := by
    have h1 : |H' i j| ≤ (∫ y : ℝ, ‖g i j y‖) / (2 * Real.pi) := by
      have h := norm_integral_le_integral_norm (μ := volume) (g i j)
      rw [hg_eq i j] at h
      simp only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, mul_one] at h
      norm_num at h
      exact (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr (by nlinarith [h])
    let amp (k : Fin (rank n)) (y : ℝ) : ℝ :=
      Real.sqrt (sixModulusWeight n y) * ‖sixBasisContourValue n (f k) y‖
    have hamp_sq (k : Fin (rank n)) (y : ℝ) :
        amp k y ^ 2 = sixModulusWeight n y * ‖sixBasisContourValue n (f k) y‖ ^ 2 := by
      dsimp only [amp]; rw [mul_pow, Real.sq_sqrt (sixModulusWeight_nonneg n y)]
    have hamp_diag (k : Fin (rank n)) (y : ℝ) :
        amp k y = Real.sqrt (‖g k k y‖ / (2 * Real.pi)) := by
      dsimp only [amp, g, sixModulusWeight]
      rw [norm_mul, norm_mul, mul_assoc (‖sixVerticalIntegrand n 0 0 y‖),
        mul_div_right_comm, Real.sqrt_mul (by positivity),
        Real.sqrt_mul_self (norm_nonneg _)]
    have hamp_mem (k : Fin (rank n)) : MemLp (amp k) 2 volume := by
      apply (memLp_two_iff_integrable_sq ?_).mpr
      · simp_rw [hamp_sq k]
        have heq : (fun y => sixModulusWeight n y * ‖sixBasisContourValue n (f k) y‖ ^ 2) =
            (fun y => ‖g k k y‖ / (2 * Real.pi)) := by
          funext y; simp only [g, sixModulusWeight, norm_mul]; ring
        rw [heq]; exact (hg_int k k).norm.div_const _
      · have hc : Continuous (fun y => amp k y) := by
          simp_rw [hamp_diag k]
          exact ((hg_cont k k).norm.div_const _).sqrt
        exact hc.aestronglyMeasurable
    have hprod (y : ℝ) : ‖g i j y‖ / (2 * Real.pi) = amp i y * amp j y := by
      dsimp only [amp, g, sixModulusWeight]
      rw [norm_mul, norm_mul]
      have hs := Real.sq_sqrt (show 0 ≤ ‖sixVerticalIntegrand n 0 0 y‖ / (2 * Real.pi) by positivity)
      linear_combination -(‖sixBasisContourValue n (f i) y‖ * ‖sixBasisContourValue n (f j) y‖) * hs
    have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) (f := amp i) (g := amp j)
      (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
      (Filter.Eventually.of_forall fun y =>
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _) : 0 ≤ amp i y))
      (Filter.Eventually.of_forall fun y =>
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _) : 0 ≤ amp j y))
      (by rw [ENNReal.ofReal_ofNat]; exact hamp_mem i)
      (by rw [ENNReal.ofReal_ofNat]; exact hamp_mem j)
    have hI (k : Fin (rank n)) : (∫ a, amp k a ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
        Real.sqrt (sixBasisModulusMoment n (f k)) := by
      rw [Real.sqrt_eq_rpow]
      congr 1
      unfold sixBasisModulusMoment
      congr 1
      funext a
      rw [Real.rpow_two, hamp_sq]
    rw [hI i, hI j] at hcs
    have h2 : (∫ y : ℝ, ‖g i j y‖) / (2 * Real.pi) ≤
        Real.sqrt (sixBasisModulusMoment n (f i)) * Real.sqrt (sixBasisModulusMoment n (f j)) := by
      rw [← integral_div]
      calc (∫ y : ℝ, ‖g i j y‖ / (2 * Real.pi)) = ∫ y : ℝ, amp i y * amp j y := by
            congr 1; funext y; exact hprod y
        _ ≤ _ := hcs
    exact h1.trans h2
  have hle := det_abs_le_factorized H' (fun i => Real.sqrt (sixBasisModulusMoment n (f i))) hentry
  simpa only [Real.sq_sqrt (sixBasisModulusMoment_nonneg n _)] using hle

/-- Scaled monic polynomial `((evenBasis i).leadingCoeff) * (50 n)^(2i) * Q((X/(50 n))²)`. -/
def sixScaledMonicEven (n i : ℕ) (Q : ℚ[X]) : ℚ[X] :=
  C ((evenBasis i).leadingCoeff * (50 * (n : ℚ)) ^ (2 * i)) *
    Q.comp (C ((50 * (n : ℚ))⁻¹ ^ 2) * X ^ 2)

/-- Basis normalization product `∏_{i < 15 n} ((evenBasis i).leadingCoeff)^2 * (50 n)^(4i)`. -/
def sixBasisNormalization (n : ℕ) : ℝ :=
  ∏ i : Fin (rank n), ((evenBasis i.val).leadingCoeff : ℝ) ^ 2 * (50 * (n : ℝ)) ^ (4 * i.val)

theorem sixBasisNormalization_pos (n : ℕ) (hn : 0 < n) : 0 < sixBasisNormalization n := by
  apply Finset.prod_pos
  intro i _
  have he : (0 : ℝ) < (evenBasis i.val).leadingCoeff := by exact_mod_cast evenBasis_leadingCoeff_pos i.val
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  positivity

theorem sixScaledMonicEven_even (n i : ℕ) (Q : ℚ[X]) :
    (sixScaledMonicEven n i Q).comp (-X) = sixScaledMonicEven n i Q := by
  unfold sixScaledMonicEven
  rw [mul_comp, C_comp, comp_assoc, mul_comp, C_comp, pow_comp, X_comp]
  simp

theorem sixScaledMonicEven_degree_and_lead (n i : ℕ) (hn : 0 < n) (Q : ℚ[X])
    (hmonic : Q.Monic) (hdeg : Q.natDegree = i) :
    (sixScaledMonicEven n i Q).natDegree = 2 * i ∧
      (sixScaledMonicEven n i Q).leadingCoeff = (evenBasis i).leadingCoeff := by
  have h50 : (50 * (n : ℚ)) ≠ 0 := by positivity
  have hc2 : (50 * (n : ℚ))⁻¹ ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero h50)
  let R : ℚ[X] := C ((50 * (n : ℚ))⁻¹ ^ 2) * X ^ 2
  have hRdeg : R.natDegree = 2 := by
    dsimp [R]; rw [natDegree_C_mul hc2, natDegree_X_pow]
  have hRlead : R.leadingCoeff = (50 * (n : ℚ))⁻¹ ^ 2 := by
    dsimp [R]; rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_pow, mul_one]
  have hcomp_deg : (Q.comp R).natDegree = 2 * i := by
    rw [natDegree_comp, hdeg, hRdeg]; ring
  have hcomp_lead : (Q.comp R).leadingCoeff = ((50 * (n : ℚ))⁻¹ ^ 2) ^ i := by
    rw [leadingCoeff_comp (by omega : R.natDegree ≠ 0), hmonic.leadingCoeff, one_mul, hdeg, hRlead]
  have hscale_ne : (evenBasis i).leadingCoeff * (50 * (n : ℚ)) ^ (2 * i) ≠ 0 :=
    mul_ne_zero (evenBasis_leadingCoeff_pos i).ne' (pow_ne_zero _ h50)
  have hprod_lead : ((evenBasis i).leadingCoeff * (50 * (n : ℚ)) ^ (2 * i)) *
      ((50 * (n : ℚ))⁻¹ ^ 2) ^ i = (evenBasis i).leadingCoeff := by
    rw [← pow_mul, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ h50), mul_one]
  constructor
  · unfold sixScaledMonicEven
    change (C _ * Q.comp R).natDegree = 2 * i
    rw [natDegree_C_mul hscale_ne, hcomp_deg]
  · unfold sixScaledMonicEven
    change (C _ * Q.comp R).leadingCoeff = (evenBasis i).leadingCoeff
    rw [leadingCoeff_mul, leadingCoeff_C, hcomp_lead, hprod_lead]

/-- **Scaled Monic Determinant Bound**: for any family of monic polynomials `Q : Fin (15n) → ℚ[X]`
with `deg (Q i) = i`, `|det (sixFunctional n)|` is bounded by `(15n)! * sixBasisNormalization n`
times the product of the normalized diagonal moments of `Q i ((X / (50 n))²)`. -/
theorem sixFunctional_det_abs_le_monicMoments (n : ℕ) (hn : 0 < n)
    (Q : Fin (rank n) → ℚ[X])
    (hmonic : ∀ i, (Q i).Monic) (hdeg : ∀ i, (Q i).natDegree = i.val) :
    |Matrix.det (sixFunctional n)| ≤
      ((rank n).factorial : ℝ) * sixBasisNormalization n *
        ∏ i : Fin (rank n), sixBasisModulusMoment n
          ((Q i).comp (C ((50 * (n : ℚ))⁻¹ ^ 2) * X ^ 2)) := by
  let f : Fin (rank n) → ℚ[X] := fun i => sixScaledMonicEven n i.val (Q i)
  have hdet := sixFunctional_det_abs_le_basisModulusMoments n f
    (fun i => sixScaledMonicEven_even n i.val (Q i))
    (fun i => (sixScaledMonicEven_degree_and_lead n i.val hn (Q i) (hmonic i) (hdeg i)).1)
    (fun i => (sixScaledMonicEven_degree_and_lead n i.val hn (Q i) (hmonic i) (hdeg i)).2)
  have hprod : (∏ i : Fin (rank n), sixBasisModulusMoment n (f i)) =
      sixBasisNormalization n *
        ∏ i : Fin (rank n), sixBasisModulusMoment n
          ((Q i).comp (C ((50 * (n : ℚ))⁻¹ ^ 2) * X ^ 2)) := by
    simp only [f, sixScaledMonicEven, sixBasisModulusMoment_scale, sixBasisNormalization]
    rw [Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl; intro i _
    push_cast; rw [mul_pow, ← pow_mul]; congr 2; omega
  rw [hprod, ← mul_assoc] at hdet
  exact hdet

/-! ## Section 6: Exact quadratic normalization rate `9/10 + (3/5) log (5/3)` -/

private def factorialLogError (m : ℕ) : ℝ :=
  Real.log (m.factorial : ℝ) - ((m : ℝ) * Real.log (m : ℝ) - (m : ℝ))

private theorem factorialLogError_bounds (m : ℕ) :
    0 ≤ factorialLogError m ∧ factorialLogError m ≤ 1 + Real.log (m : ℝ) := by
  rcases m with _ | m
  · norm_num [factorialLogError]
  have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hm1 : (1 : ℝ) ≤ (m + 1 : ℕ) := by norm_num
  have hl := Stirling.le_log_factorial_stirling (Nat.succ_ne_zero m)
  have hlog := Real.log_nonneg hm1
  have hpi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hu := Stirling.log_stirlingSeq'_antitone (Nat.zero_le m)
  dsimp only [Function.comp_def, Nat.succ_eq_add_one] at hu
  have hs : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
    rw [Stirling.stirlingSeq_one, Real.log_div (by positivity) (by positivity),
      Real.log_exp, Real.log_sqrt (by positivity)]
  rw [hs] at hu
  have hf := Stirling.log_stirlingSeq_formula (m + 1)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hm.ne',
    Real.log_div hm.ne' (Real.exp_ne_zero 1), Real.log_exp] at hf
  dsimp only [factorialLogError]
  constructor <;> linarith

private def weightedLogSum (m : ℕ) : ℝ :=
  ∑ i ∈ range m, (i : ℝ) * Real.log (i : ℝ)

private def weightedLogIntegral (x : ℝ) : ℝ :=
  x ^ 2 / 2 * Real.log x - x ^ 2 / 4 + 1 / 4

private theorem weightedLog_integral (m : ℕ) (hm : 1 ≤ m) :
    (∫ x : ℝ in 1..(m : ℝ), x * Real.log x) = weightedLogIntegral (m : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd (x : ℝ) (hx : x ∈ uIcc (1 : ℝ) (m : ℝ)) :
      HasDerivAt (fun t : ℝ => t ^ 2 / 2 * Real.log t - t ^ 2 / 4) (x * Real.log x) x := by
    rw [uIcc_of_le hmR] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h := ((((hasDerivAt_id x).pow 2).div_const 2).mul
      (Real.hasDerivAt_log hx0)).sub (((hasDerivAt_id x).pow 2).div_const 4)
    convert! h using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, Pi.pow_apply]
    field_simp; ring
  simpa [weightedLogIntegral] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (Real.continuous_mul_log.intervalIntegrable _ _)

private theorem weightedLogSum_bounds (m : ℕ) (hm : 1 ≤ m) :
    weightedLogIntegral (m : ℝ) - (m : ℝ) * Real.log (m : ℝ) ≤ weightedLogSum m ∧
      weightedLogSum m ≤ weightedLogIntegral (m : ℝ) := by
  have hmono : MonotoneOn (fun x : ℝ => x * Real.log x) (Icc (1 : ℝ) (m : ℝ)) := by
    intro x hx y hy hxy
    exact mul_le_mul hxy (Real.log_le_log (by linarith [hx.1]) hxy)
      (Real.log_nonneg hx.1) (by linarith [hy.1])
  have hmono' : MonotoneOn (fun x : ℝ => x * Real.log x) (Icc (↑(1 : ℕ)) (m : ℝ)) := by
    simpa only [Nat.cast_one] using hmono
  have hl := hmono'.sum_le_integral_Ico hm
  have hu := hmono'.integral_le_sum_Ico hm
  norm_num only [Nat.cast_one] at hl hu
  rw [weightedLog_integral m hm, Finset.sum_Ico_eq_sub _ hm] at hl hu
  simp only [sum_range_one, Nat.cast_zero, Real.log_zero, sub_zero, mul_zero,
    Nat.zero_add, Nat.cast_one, Real.log_one] at hl hu
  have hshift : (∑ i ∈ range m, ((i + 1 : ℕ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ)) =
      weightedLogSum m + (m : ℝ) * Real.log (m : ℝ) := by
    have h := Finset.sum_range_succ' (fun i : ℕ => (i : ℝ) * Real.log (i : ℝ)) m
    rw [Finset.sum_range_succ] at h
    simpa [weightedLogSum] using h.symm
  rw [hshift] at hu
  exact ⟨by linarith, hl⟩

private theorem sum_natCast (m : ℕ) :
    (∑ i ∈ range m, (i : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

private theorem leadingCoeff_log (i : ℕ) :
    Real.log ((evenBasis i).leadingCoeff : ℝ) =
      Real.log 2 - Real.log ((2 * i).factorial : ℝ) - (if i = 0 then Real.log 2 else 0) := by
  cases i with
  | zero => simp
  | succ i =>
    rw [evenBasis_leadingCoeff_succ]; push_cast
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]; simp

/-- Exact quadratic normalization rate limit `θ(3 - 2 log(2θ)) = 9/10 + 3/5 * log(5/3)`. -/
theorem sixBasisNormalization_log_rate :
    Tendsto (fun n : ℕ => Real.log (sixBasisNormalization n) / sixNorm n)
      atTop (𝓝 ((9 : ℝ) / 10 + 3 / 5 * Real.log (5 / 3))) := by
  let main (n : ℕ) : ℝ :=
    (675 + 450 * Real.log (5 / 3)) * (n : ℝ) ^ 2 -
      30 * (n : ℝ) * Real.log (25 * (n : ℝ)) - 30 * (n : ℝ) - 1 + (30 * (n : ℝ) - 2) * Real.log 2
  have hbounds : ∀ n : ℕ, 1 ≤ n →
      main n - 30 * (n : ℝ) * (1 + Real.log (30 * (n : ℝ))) ≤
          Real.log (sixBasisNormalization n) ∧
        Real.log (sixBasisNormalization n) ≤
          main n + 60 * (n : ℝ) * Real.log (15 * (n : ℝ)) := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h50n : (0 : ℝ) < 50 * n := by positivity
    have he (i : ℕ) : (0 : ℝ) < (evenBasis i).leadingCoeff := by
      exact_mod_cast evenBasis_leadingCoeff_pos i
    have hlog_sum : Real.log (sixBasisNormalization n) =
        (30 * (n : ℝ) - 2) * Real.log 2 -
          2 * (∑ i ∈ range (15 * n), Real.log ((2 * i).factorial : ℝ)) +
          30 * (n : ℝ) * (15 * (n : ℝ) - 1) * Real.log (50 * (n : ℝ)) := by
      rw [sixBasisNormalization, Real.log_prod (fun i _ =>
        mul_ne_zero (pow_ne_zero 2 (he i.val).ne') (pow_ne_zero _ h50n.ne'))]
      have hrow (i : ℕ) :
          Real.log (((evenBasis i).leadingCoeff : ℝ) ^ 2 * (50 * (n : ℝ)) ^ (4 * i)) =
            2 * Real.log ((evenBasis i).leadingCoeff : ℝ) + (4 * Real.log (50 * (n : ℝ))) * (i : ℝ) := by
        rw [Real.log_mul (pow_ne_zero 2 (he i).ne') (pow_ne_zero _ h50n.ne'),
          Real.log_pow, Real.log_pow]; push_cast; ring
      simp_rw [hrow]
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
        2 * Real.log ((evenBasis i).leadingCoeff : ℝ) + (4 * Real.log (50 * (n : ℝ))) * (i : ℝ)) (rank n)]
      unfold rank
      simp_rw [leadingCoeff_log]
      have hif : (∑ i ∈ range (15 * n), if i = 0 then Real.log 2 else 0) = Real.log 2 := by
        simp [show 0 < 15 * n by omega]
      simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hif, sum_natCast]
      push_cast; ring
    let fErr : ℝ := ∑ i ∈ range (15 * n), factorialLogError (2 * i)
    have hfErr_bnds : 0 ≤ fErr ∧ fErr ≤ 15 * (n : ℝ) * (1 + Real.log (30 * (n : ℝ))) := by
      constructor
      · exact Finset.sum_nonneg fun i _ => (factorialLogError_bounds (2 * i)).1
      · calc
          fErr ≤ ∑ _i ∈ range (15 * n), (1 + Real.log (30 * (n : ℝ))) := by
            apply Finset.sum_le_sum; intro i hi
            by_cases hi0 : i = 0
            · subst i
              simp only [Nat.mul_zero, factorialLogError, Nat.factorial_zero, Nat.cast_one,
                Real.log_one, Nat.cast_zero, Real.log_zero, zero_mul, sub_zero]
              have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
              linarith [Real.log_nonneg (show (1 : ℝ) ≤ 30 * (n : ℝ) by linarith)]
            · have hip : (0 : ℝ) < (2 * i : ℕ) := by
                exact_mod_cast Nat.mul_pos (by omega : 0 < 2) (Nat.pos_of_ne_zero hi0)
              have hiR : (i : ℝ) < 15 * (n : ℝ) := by exact_mod_cast Finset.mem_range.mp hi
              have hlog := Real.log_le_log hip (show ((2 * i : ℕ) : ℝ) ≤ 30 * (n : ℝ) by
                push_cast; linarith)
              linarith [(factorialLogError_bounds (2 * i)).2]
          _ = _ := by simp; ring
    have hdecomp : Real.log (sixBasisNormalization n) =
        main n + 4 * (weightedLogIntegral (15 * (n : ℝ)) - weightedLogSum (15 * n)) - 2 * fErr := by
      have hterm (i : ℕ) : Real.log ((2 * i).factorial : ℝ) =
          (2 * Real.log 2) * (i : ℝ) + 2 * ((i : ℝ) * Real.log (i : ℝ)) - 2 * (i : ℝ) +
            factorialLogError (2 * i) := by
        rcases eq_or_ne i 0 with rfl | hi
        · simp [factorialLogError]
        · unfold factorialLogError
          rw [Nat.cast_mul, Nat.cast_ofNat,
            Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hi)]
          ring
      have hlog50 : Real.log (50 * (n : ℝ)) = Real.log 2 + Real.log (25 * (n : ℝ)) := by
        rw [show 50 * (n : ℝ) = 2 * (25 * (n : ℝ)) by ring,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
      have hlog_ratio : Real.log (25 * (n : ℝ)) - Real.log (15 * (n : ℝ)) = Real.log (5 / 3) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        congr 1; field_simp; ring
      rw [hlog_sum]
      simp_rw [hterm]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_natCast]
      change (30 * (n : ℝ) - 2) * Real.log 2 -
          2 * (2 * Real.log 2 * ((15 * n : ℕ) * ((15 * n : ℕ) - 1) / 2) +
            2 * weightedLogSum (15 * n) - 2 * ((15 * n : ℕ) * ((15 * n : ℕ) - 1) / 2) + fErr) +
          30 * (n : ℝ) * (15 * (n : ℝ) - 1) * Real.log (50 * (n : ℝ)) = _
      dsimp only [main, weightedLogIntegral]
      rw [hlog50]
      push_cast
      linear_combination 450 * (n : ℝ) ^ 2 * hlog_ratio
    have hws := weightedLogSum_bounds (15 * n) (by omega)
    push_cast at hws
    constructor <;> linarith
  have hlog_div : ∀ c : ℝ, c ≠ 0 →
      Tendsto (fun n : ℕ => Real.log (c * (n : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
    intro c hc
    have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq] using!
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.log c)).add h1
    simp only [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [Real.log_mul hc (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)), add_div]
  have hi : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hmain_lim : Tendsto (fun n : ℕ => main n / sixNorm n)
      atTop (𝓝 ((9 : ℝ) / 10 + 3 / 5 * Real.log (5 / 3))) := by
    have hc : Tendsto (fun _ : ℕ => (9 : ℝ) / 10 + 3 / 5 * Real.log (5 / 3))
        atTop (𝓝 ((9 : ℝ) / 10 + 3 / 5 * Real.log (5 / 3))) := tendsto_const_nhds
    have h := (((hc.sub ((hlog_div 25 (by norm_num)).const_mul (30 / 750))).sub
      (hi.const_mul (30 / 750))).sub ((hi.pow 2).const_mul (1 / 750))).add
      (((hi.const_mul (30 / 750)).sub ((hi.pow 2).const_mul (2 / 750))).mul_const (Real.log 2))
    norm_num only [mul_zero, sub_zero, zero_pow, zero_sub, zero_mul, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    rw [sixNorm_eq]; dsimp only [main]; field_simp; ring
  have hlo_err : Tendsto (fun n : ℕ => 30 * (n : ℝ) * (1 + Real.log (30 * (n : ℝ))) / sixNorm n)
      atTop (𝓝 0) := by
    have h := (hi.add (hlog_div 30 (by norm_num))).const_mul (30 / 750)
    simp only [add_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    rw [sixNorm_eq]; field_simp
  have hhi_err : Tendsto (fun n : ℕ => 60 * (n : ℝ) * Real.log (15 * (n : ℝ)) / sixNorm n)
      atTop (𝓝 0) := by
    have h := (hlog_div 15 (by norm_num)).const_mul (60 / 750)
    simp only [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    rw [sixNorm_eq]; field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using hmain_lim.sub hlo_err)
    (by simpa only [add_zero] using hmain_lim.add hhi_err)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simpa only [sub_div] using div_le_div_of_nonneg_right (hbounds n hn).1 (sixNorm_nonneg n)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simpa only [add_div] using div_le_div_of_nonneg_right (hbounds n hn).2 (sixNorm_nonneg n)

theorem sixBasisNormalization_eventually_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      sixBasisNormalization n ≤
        Real.exp (((9 : ℝ) / 10 + 3 / 5 * Real.log (5 / 3) + ε) * sixNorm n) := by
  have hu := sixBasisNormalization_log_rate.eventually_lt_const
    (show (9 : ℝ) / 10 + 3 / 5 * Real.log (5 / 3) <
      (9 : ℝ) / 10 + 3 / 5 * Real.log (5 / 3) + ε by linarith)
  filter_upwards [hu, eventually_gt_atTop (0 : ℕ)] with n hup hn
  have hnorm_pos : 0 < sixNorm n := by
    rw [sixNorm_eq]; have : (0 : ℝ) < n := Nat.cast_pos.mpr hn; positivity
  exact Real.le_exp_of_log_le ((div_lt_iff₀ hnorm_pos).mp hup).le

theorem rank_factorial_subquadratic (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((rank n).factorial : ℝ) ≤ Real.exp (ε * sixNorm n) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (15 * (n : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq] using!
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.log 15)).add h1
    simp only [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)), add_div]
  have hlt := hlog.eventually_lt_const (show (0 : ℝ) < 50 * ε by positivity)
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with n hln hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hfac_le : ((rank n).factorial : ℝ) ≤ (15 * (n : ℝ)) ^ (15 * n) := by
    unfold rank
    have hnat : (15 * n).factorial ≤ (15 * n) ^ (15 * n) := Nat.factorial_le_pow (15 * n)
    exact_mod_cast hnat
  apply hfac_le.trans
  apply (Real.log_le_iff_le_exp (pow_pos (by positivity) _)).mp
  rw [Real.log_pow, sixNorm_eq]
  have hmul : Real.log (15 * (n : ℝ)) < 50 * ε * (n : ℝ) := (div_lt_iff₀ hnR).mp hln
  push_cast
  nlinarith

end OddZetaSix
