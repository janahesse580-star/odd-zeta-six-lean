import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic

/-!
# Uniform half-integer Gamma estimates (self-contained port)

Ported verbatim (namespace `OddZetaSix`) from the upstream reference modules
`LogQuadraticMidpoint`, `HalfIntegerGamma` and `HalfIntegerGammaEstimate` of
`odd-zeta-seven-lean` at commit `7a7e3a2`. All bounds are finite and uniform in the
height, including height zero. Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

noncomputable section
set_option autoImplicit false

namespace OddZetaSix

section
open Finset MeasureTheory




/-- The real logarithm of the modulus of `x + I*y`. -/
def logQuadratic (y x : ℝ) : ℝ := Real.log (x^2+y^2)/2

/-- The finite midpoint sum minus its integral, with unit cell width. -/
def logQuadraticMidpointError (m : ℕ) (y : ℝ) : ℝ :=
  (∑ j ∈ range m, logQuadratic y ((j : ℝ)+1/2)) -
    ∫ x : ℝ in 0..(m : ℝ), logQuadratic y x

@[simp] theorem logQuadratic_zero (x : ℝ) : logQuadratic 0 x = Real.log x := by
  simp [logQuadratic, Real.log_pow]

theorem logQuadratic_continuous (y : ℝ) (hy : y ≠ 0) :
    Continuous (logQuadratic y) := by
  unfold logQuadratic
  apply Continuous.div_const
  apply Continuous.log ((continuous_id.pow 2).add continuous_const)
  intro x
  change x^2+y^2 ≠ 0
  have hy2 : 0 < y^2 := sq_pos_of_ne_zero hy
  positivity

/-- Integrability includes height zero, where the integrand is `log x`. -/
theorem logQuadratic_intervalIntegrable (y a b : ℝ) :
    IntervalIntegrable (logQuadratic y) volume a b := by
  by_cases hy : y = 0
  · subst y
    simpa only [show logQuadratic 0 = Real.log from funext logQuadratic_zero] using
      (intervalIntegral.intervalIntegrable_log' (a := a) (b := b))
  · exact (logQuadratic_continuous y hy).intervalIntegrable a b

theorem logQuadratic_monotoneOn (y : ℝ) :
    MonotoneOn (logQuadratic y) (Set.Ioi 0) := by
  intro x hx z hz hxz
  change 0 < x at hx
  change 0 < z at hz
  unfold logQuadratic
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.log_le_log (by positivity)
  nlinarith

/-- A comparison valid on the first cell, excluding only the singular endpoint. -/
theorem logQuadratic_firstCell_lower (y x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    logQuadratic y 1+Real.log x ≤ logQuadratic y x := by
  have hx2 : (x : ℝ)^2 ≠ 0 := pow_ne_zero _ hx.ne'
  have hy2 : (1 : ℝ)+y^2 ≠ 0 := by positivity
  have h := Real.log_le_log (show 0 < x^2*(1+y^2) by positivity)
    (show x^2*(1+y^2) ≤ x^2+y^2 by
      have hxs : x^2 ≤ 1 := by nlinarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hxs) (sq_nonneg y)])
  rw [Real.log_mul hx2 hy2, Real.log_pow] at h
  norm_num only [logQuadratic, one_pow, Nat.cast_ofNat] at h ⊢
  linarith

theorem logQuadratic_firstCell_integral_bounds (y : ℝ) :
    logQuadratic y 1-1 ≤ (∫ x : ℝ in 0..1, logQuadratic y x) ∧
      (∫ x : ℝ in 0..1, logQuadratic y x) ≤ logQuadratic y 1 := by
  have hlog : IntervalIntegrable Real.log volume (0 : ℝ) 1 :=
    intervalIntegral.intervalIntegrable_log'
  have hl := intervalIntegral.integral_mono_on_of_le_Ioo
    (by norm_num : (0 : ℝ) ≤ 1) (intervalIntegrable_const.add hlog)
    (logQuadratic_intervalIntegrable y 0 1)
    (fun x hx => logQuadratic_firstCell_lower y x hx.1 hx.2.le)
  have hu := intervalIntegral.integral_mono_on_of_le_Ioo
    (by norm_num : (0 : ℝ) ≤ 1) (logQuadratic_intervalIntegrable y 0 1)
    (intervalIntegrable_const (c := logQuadratic y 1))
    (fun x hx => logQuadratic_monotoneOn y hx.1 (by norm_num) hx.2.le)
  rw [intervalIntegral.integral_add intervalIntegrable_const hlog] at hl
  simp only [intervalIntegral.integral_const, sub_zero, one_smul,
    integral_log, Real.log_one, Real.log_zero, mul_zero, sub_self, zero_sub,
    add_zero] at hl hu
  constructor <;> linarith

theorem logQuadraticMidpointError_one (y : ℝ) :
    |logQuadraticMidpointError 1 y| ≤ 1 := by
  have hi := logQuadratic_firstCell_integral_bounds y
  have hl := logQuadratic_firstCell_lower y (1/2) (by norm_num) (by norm_num)
  have hu := logQuadratic_monotoneOn y (a := 1/2) (b := 1)
    (by norm_num) (by norm_num) (by norm_num)
  have hlog : -(1 : ℝ) ≤ Real.log (1/2) := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  simp only [logQuadraticMidpointError, sum_range_one, Nat.cast_zero, zero_add,
    Nat.cast_one]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Each positive unit cell costs no more than its endpoint increment. -/
theorem logQuadratic_cell_error (y a : ℝ) (ha : 0 < a) :
    |logQuadratic y (a+1/2)-(∫ x : ℝ in a..a+1, logQuadratic y x)| ≤
      logQuadratic y (a+1)-logQuadratic y a := by
  have hf := logQuadratic_intervalIntegrable y a (a+1)
  have hl := intervalIntegral.integral_mono_on (by linarith : a ≤ a+1)
    (intervalIntegrable_const (c := logQuadratic y a)) hf
    (fun x hx => logQuadratic_monotoneOn y ha
      (show 0 < x by linarith [hx.1]) hx.1)
  have hu := intervalIntegral.integral_mono_on (by linarith : a ≤ a+1) hf
    (intervalIntegrable_const (c := logQuadratic y (a+1)))
    (fun x hx => logQuadratic_monotoneOn y (show 0 < x by linarith [hx.1])
      (show 0 < a+1 by linarith) hx.2)
  simp only [intervalIntegral.integral_const, add_sub_cancel_left, one_smul] at hl hu
  have hml := logQuadratic_monotoneOn y ha (by linarith : 0 < a+1/2)
    (by linarith : a ≤ a+1/2)
  have hmu := logQuadratic_monotoneOn y (by linarith : 0 < a+1/2)
    (by linarith : 0 < a+1) (by linarith : a+1/2 ≤ a+1)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem logQuadraticMidpointError_succ (m : ℕ) (y : ℝ) :
    logQuadraticMidpointError (m+1) y = logQuadraticMidpointError m y +
      (logQuadratic y ((m : ℝ)+1/2)-
        ∫ x : ℝ in (m : ℝ)..(m : ℝ)+1, logQuadratic y x) := by
  unfold logQuadraticMidpointError
  rw [sum_range_succ, Nat.cast_add, Nat.cast_one,
    ← intervalIntegral.integral_add_adjacent_intervals
      (logQuadratic_intervalIntegrable y 0 m)
      (logQuadratic_intervalIntegrable y m (m+1))]
  ring

theorem logQuadraticMidpointError_le_variation (m : ℕ) (hm : 1 ≤ m) (y : ℝ) :
    |logQuadraticMidpointError m y| ≤ 1+logQuadratic y m-logQuadratic y 1 := by
  induction m, hm using Nat.le_induction with
  | base => simpa using logQuadraticMidpointError_one y
  | succ m hm ih =>
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    rw [logQuadraticMidpointError_succ]
    calc
      _ ≤ |logQuadraticMidpointError m y|+
          |logQuadratic y ((m : ℝ)+1/2)-
            ∫ x : ℝ in (m : ℝ)..(m : ℝ)+1, logQuadratic y x| := abs_add_le _ _
      _ ≤ (1+logQuadratic y m-logQuadratic y 1)+
          (logQuadratic y ((m : ℝ)+1)-logQuadratic y m) :=
        add_le_add ih (logQuadratic_cell_error y m hmR)
      _ = _ := by push_cast; ring

theorem logQuadratic_variation_le_log (y x : ℝ) (hx : 1 ≤ x) :
    logQuadratic y x-logQuadratic y 1 ≤ Real.log x := by
  have hx0 : 0 < x := by linarith
  have h := Real.log_le_log (show 0 < x^2+y^2 by positivity)
    (show x^2+y^2 ≤ x^2*(1+y^2) by
      have hxs : 1 ≤ x^2 := by nlinarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hxs) (sq_nonneg y)])
  rw [Real.log_mul (pow_ne_zero _ hx0.ne') (by positivity : 1+y^2 ≠ 0),
    Real.log_pow] at h
  norm_num only [logQuadratic, one_pow, Nat.cast_ofNat] at h ⊢
  linarith

/-- A fully uniform finite estimate, in fact valid for every real height. -/
theorem logQuadraticMidpointError_abs_le (m : ℕ) (hm : 1 ≤ m) (y : ℝ) :
    |logQuadraticMidpointError m y| ≤ 1+Real.log (m : ℝ) := by
  have h := logQuadraticMidpointError_le_variation m hm y
  have hv := logQuadratic_variation_le_log y m (by exact_mod_cast hm)
  linarith

theorem logQuadratic_hasDerivAt (y x : ℝ) (h : x^2+y^2 ≠ 0) :
    HasDerivAt (logQuadratic y) (x/(x^2+y^2)) x := by
  have hd := ((((hasDerivAt_id x).pow 2).add_const (y^2)).log h).div_const 2
  convert! hd using 1
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat,
    Nat.reduceSub, pow_one, mul_one]
  ring

private theorem logQuadratic_primitive_hasDerivAt (y x : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun t : ℝ => t*logQuadratic y t-t+y*Real.arctan (t/y))
      (logQuadratic y x) x := by
  have hy2 : 0 < y^2 := sq_pos_of_ne_zero hy
  have hden : x^2+y^2 ≠ 0 := by positivity
  have hd := (((hasDerivAt_id x).mul (logQuadratic_hasDerivAt y x hden)).sub
    (hasDerivAt_id x)).add (((hasDerivAt_id x).div_const y).arctan.const_mul y)
  convert! hd using 1
  simp only [id_eq, one_mul]
  field_simp
  nlinarith [sq_nonneg x]

/-- The height-zero integral is evaluated without assuming continuity at zero. -/
theorem integral_logQuadratic_zero (b : ℝ) :
    (∫ x : ℝ in 0..b, logQuadratic 0 x) = b*Real.log b-b := by
  simp only [logQuadratic_zero, integral_log, Real.log_zero, zero_mul, sub_zero,
    add_zero]

/-- Exact elementary evaluation, including height zero (and even signed heights). -/
theorem integral_logQuadratic (y b : ℝ) :
    (∫ x : ℝ in 0..b, logQuadratic y x) =
      b*logQuadratic y b-b+y*Real.arctan (b/y) := by
  by_cases hy : y = 0
  · subst y
    simp
  · have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => logQuadratic_primitive_hasDerivAt y x hy)
      (logQuadratic_intervalIntegrable y 0 b)
    simpa using h

/-- The reciprocal-arctangent form used by the half-integer Gamma phase. -/
theorem integral_logQuadratic_eq_phase (y b : ℝ) (hy : 0 ≤ y) (hb : 0 < b) :
    (∫ x : ℝ in 0..b, logQuadratic y x) =
      b*logQuadratic y b-b-y*Real.arctan (y/b)+Real.pi*y/2 := by
  rw [integral_logQuadratic]
  rcases eq_or_lt_of_le hy with hy | hy
  · rw [← hy]
    simp
  · have h : Real.arctan (b/y) = Real.pi/2-Real.arctan (y/b) := by
      simpa only [inv_div] using Real.arctan_inv_of_pos (div_pos hy hb)
    rw [h]
    ring

/-- The uniform estimate with its elementary integral written out explicitly. -/
theorem logQuadratic_midpoint_sum_abs_le (m : ℕ) (hm : 1 ≤ m) (y : ℝ) :
    |(∑ j ∈ range m, Real.log (((j : ℝ)+1/2)^2+y^2)/2) -
      ((m : ℝ)*Real.log ((m : ℝ)^2+y^2)/2-(m : ℝ)+
        y*Real.arctan ((m : ℝ)/y))| ≤ 1+Real.log (m : ℝ) := by
  have h := logQuadraticMidpointError_abs_le m hm y
  rw [logQuadraticMidpointError, integral_logQuadratic] at h
  simpa only [logQuadratic, mul_div_assoc] using h

/-- The singular height has the same proved bound, with no limiting argument. -/
theorem log_midpoint_sum_abs_le (m : ℕ) (hm : 1 ≤ m) :
    |(∑ j ∈ range m, Real.log ((j : ℝ)+1/2)) -
      ((m : ℝ)*Real.log (m : ℝ)-(m : ℝ))| ≤ 1+Real.log (m : ℝ) := by
  have h := logQuadraticMidpointError_abs_le m hm 0
  simpa only [logQuadraticMidpointError, logQuadratic_zero,
    integral_log, Real.log_zero, zero_mul, sub_zero, add_zero] using h

theorem logQuadraticMidpointError_one_zero :
    logQuadraticMidpointError 1 0 = 1-Real.log 2 := by
  simp [logQuadraticMidpointError]
  ring

/-- The midpoint sum as the logarithm of the positive quadratic product. -/
theorem logQuadratic_midpoint_sum_eq_log_prod (m : ℕ) (y : ℝ) :
    (∑ j ∈ range m, logQuadratic y ((j : ℝ)+1/2)) =
      Real.log (∏ j ∈ range m, (((j : ℝ)+1/2)^2+y^2))/2 := by
  rw [Real.log_prod (fun j _ => by positivity)]
  simp only [logQuadratic, sum_div]

/-- A finite log-product estimate, uniform also at height zero. -/
theorem logQuadratic_log_prod_integral_abs_le (m : ℕ) (hm : 1 ≤ m) (y : ℝ) :
    |Real.log (∏ j ∈ range m, (((j : ℝ)+1/2)^2+y^2))/2 -
      (∫ x : ℝ in 0..(m : ℝ), logQuadratic y x)| ≤ 1+Real.log (m : ℝ) := by
  rw [← logQuadratic_midpoint_sum_eq_log_prod]
  exact logQuadraticMidpointError_abs_le m hm y

/-- The same log-product estimate with the exact arctangent main term. -/
theorem logQuadratic_log_prod_abs_le (m : ℕ) (hm : 1 ≤ m) (y : ℝ) :
    |Real.log (∏ j ∈ range m, (((j : ℝ)+1/2)^2+y^2))/2 -
      ((m : ℝ)*Real.log ((m : ℝ)^2+y^2)/2-(m : ℝ)+
        y*Real.arctan ((m : ℝ)/y))| ≤ 1+Real.log (m : ℝ) := by
  have h := logQuadratic_log_prod_integral_abs_le m hm y
  rw [integral_logQuadratic] at h
  simpa only [logQuadratic, mul_div_assoc] using h

/-- Uniform product error around the main term in the Gamma phase convention. -/
theorem logQuadratic_log_prod_phase_abs_le (m : ℕ) (hm : 1 ≤ m)
    (y : ℝ) (hy : 0 ≤ y) :
    |Real.log (∏ j ∈ range m, (((j : ℝ)+1/2)^2+y^2))/2 -
      ((m : ℝ)*Real.log ((m : ℝ)^2+y^2)/2-(m : ℝ)-
        y*Real.arctan (y/(m : ℝ))+Real.pi*y/2)| ≤ 1+Real.log (m : ℝ) := by
  have h := logQuadratic_log_prod_integral_abs_le m hm y
  rw [integral_logQuadratic_eq_phase y m hy (by exact_mod_cast (show 0 < m by omega))]
    at h
  simpa only [logQuadratic, mul_div_assoc] using h


end

section
open Finset Complex
open scoped ComplexConjugate




theorem sin_pi_half_add_imaginary (y : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((1 / 2 : ℂ) + (y : ℂ) * I)) =
      (Real.cosh (Real.pi * y) : ℂ) := by
  have h : (Real.pi : ℂ) * ((1 / 2 : ℂ) + (y : ℂ) * I) =
      (Real.pi : ℂ) / 2 + ((Real.pi * y : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h, Complex.sin_add_mul_I, Complex.sin_pi_div_two,
    Complex.cos_pi_div_two]
  simp

theorem gamma_half_norm_sq (y : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * y) := by
  let z : ℂ := 1 / 2 + (y : ℂ) * I
  have hz : 1 - z = conj z := by
    dsimp [z]
    apply Complex.ext <;> norm_num
  have h := Complex.Gamma_mul_Gamma_one_sub z
  rw [hz, Complex.Gamma_conj] at h
  have hs := sin_pi_half_add_imaginary y
  change Complex.sin ((Real.pi : ℂ) * z) = _ at hs
  rw [hs] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg,
    sub_neg_eq_add, ← Complex.ofReal_div, Complex.ofReal_re, Complex.sq_norm,
    Complex.normSq_apply, z] using hr

theorem half_integer_norm_sq (m : ℕ) (y : ℝ) :
    ‖(m : ℂ) + 1 / 2 + (y : ℂ) * I‖ ^ 2 =
      ((m : ℝ) + 1 / 2) ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

theorem gamma_half_add_nat_norm_sq (m : ℕ) (y : ℝ) :
    ‖Complex.Gamma ((m : ℂ) + 1 / 2 + (y : ℂ) * I)‖ ^ 2 =
      (Real.pi / Real.cosh (Real.pi * y)) *
        ∏ j ∈ range m, (((j : ℝ) + 1 / 2) ^ 2 + y ^ 2) := by
  induction m with
  | zero => simpa using gamma_half_norm_sq y
  | succ m ih =>
    have hne : (m : ℂ) + 1 / 2 + (y : ℂ) * I ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have harg : ((m + 1 : ℕ) : ℂ) + 1 / 2 + (y : ℂ) * I =
        ((m : ℂ) + 1 / 2 + (y : ℂ) * I) + 1 := by
      push_cast
      ring
    rw [harg, Complex.Gamma_add_one _ hne, norm_mul, mul_pow,
      half_integer_norm_sq, ih, prod_range_succ]
    ring

theorem half_integer_quadratic_pos (j : ℕ) (y : ℝ) :
    0 < ((j : ℝ) + 1 / 2) ^ 2 + y ^ 2 := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith [sq_nonneg y]

theorem log_gamma_half_add_nat_norm (m : ℕ) (y : ℝ) :
    Real.log ‖Complex.Gamma ((m : ℂ) + 1 / 2 + (y : ℂ) * I)‖ =
      (Real.log Real.pi - Real.log (Real.cosh (Real.pi * y)) +
        ∑ j ∈ range m, Real.log (((j : ℝ) + 1 / 2) ^ 2 + y ^ 2)) / 2 := by
  have hprod : (∏ j ∈ range m, (((j : ℝ) + 1 / 2) ^ 2 + y ^ 2)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun j _ => (half_integer_quadratic_pos j y).ne')
  have h := congrArg Real.log (gamma_half_add_nat_norm_sq m y)
  rw [Real.log_pow, Real.log_mul
    (div_ne_zero Real.pi_ne_zero (Real.cosh_pos _).ne') hprod,
    Real.log_div Real.pi_ne_zero (Real.cosh_pos _).ne',
    Real.log_prod (fun j _ => (half_integer_quadratic_pos j y).ne')] at h
  linarith


end

section
open Finset Complex
open scoped ComplexConjugate




/-- The real main term for `log norm Gamma (x + 1/2 + I*y)`. -/
def halfIntegerGammaMain (x y : ℝ) : ℝ :=
  x*Real.log (x^2+y^2)/2-x-y*Real.arctan (y/x)+Real.log (2*Real.pi)/2

/-- The scale-independent part of the main term. -/
def halfIntegerGammaPhase (a s : ℝ) : ℝ :=
  a*Real.log (a^2+s^2)/2-a-s*Real.arctan (s/a)

theorem halfIntegerGammaPhase_neg (a s : ℝ) :
    halfIntegerGammaPhase a (-s) = halfIntegerGammaPhase a s := by
  simp [halfIntegerGammaPhase, neg_div, Real.arctan_neg]

theorem halfIntegerGammaMain_neg (x y : ℝ) :
    halfIntegerGammaMain x (-y) = halfIntegerGammaMain x y := by
  simp [halfIntegerGammaMain, neg_div, Real.arctan_neg]

/-- Conjugation gives even Gamma norms at every real part. -/
theorem gamma_norm_real_add_imaginary_neg (x y : ℝ) :
    ‖Complex.Gamma ((x : ℂ)+((-y : ℝ) : ℂ)*I)‖ =
      ‖Complex.Gamma ((x : ℂ)+(y : ℂ)*I)‖ := by
  have h : (x : ℂ)+((-y : ℝ) : ℂ)*I = conj ((x : ℂ)+(y : ℂ)*I) := by
    simp
  rw [h, Complex.Gamma_conj, Complex.norm_conj]

theorem norm_real_add_imaginary_neg (x y : ℝ) :
    ‖(x : ℂ)+((-y : ℝ) : ℂ)*I‖ = ‖(x : ℂ)+(y : ℂ)*I‖ := by
  have h : (x : ℂ)+((-y : ℝ) : ℂ)*I = conj ((x : ℂ)+(y : ℂ)*I) := by simp
  rw [h, Complex.norm_conj]

theorem log_gamma_half_add_nat_norm_neg (m : ℕ) (y : ℝ) :
    Real.log ‖Complex.Gamma ((m : ℂ)+1/2+((-y : ℝ) : ℂ)*I)‖ =
      Real.log ‖Complex.Gamma ((m : ℂ)+1/2+(y : ℂ)*I)‖ := by
  have h := gamma_norm_real_add_imaginary_neg ((m : ℝ)+1/2) y
  push_cast at h
  simpa only [Complex.ofReal_neg] using congrArg Real.log h

private theorem log_cosh_bounds (t : ℝ) (ht : 0 ≤ t) :
    t-Real.log 2 ≤ Real.log (Real.cosh t) ∧ Real.log (Real.cosh t) ≤ t := by
  have he := Real.exp_le_exp.mpr (show -t ≤ t by linarith)
  have hl := Real.log_le_log (show 0 < Real.exp t/2 by positivity)
    (show Real.exp t/2 ≤ Real.cosh t by
      rw [Real.cosh_eq]
      linarith [Real.exp_pos (-t)])
  have hu := Real.log_le_log (Real.cosh_pos t)
    (show Real.cosh t ≤ Real.exp t by rw [Real.cosh_eq]; linarith)
  rw [Real.log_div (Real.exp_ne_zero t) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_exp] at hl
  rw [Real.log_exp] at hu
  exact ⟨hl, hu⟩

private theorem log_cosh_correction_abs_le (t : ℝ) (ht : 0 ≤ t) :
    |(t-Real.log (Real.cosh t)-Real.log 2)/2| ≤ 1 := by
  have hb := log_cosh_bounds t ht
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Exact decomposition exposing the already-proved finite midpoint error. -/
theorem log_gamma_half_add_nat_norm_eq_main_add_error
    (m : ℕ) (hm : 1 ≤ m) (y : ℝ) (hy : 0 ≤ y) :
    Real.log ‖Complex.Gamma ((m : ℂ)+1/2+(y : ℂ)*I)‖ =
      halfIntegerGammaMain m y+logQuadraticMidpointError m y+
        (Real.pi*y-Real.log (Real.cosh (Real.pi*y))-Real.log 2)/2 := by
  rw [log_gamma_half_add_nat_norm]
  unfold halfIntegerGammaMain logQuadraticMidpointError
  rw [integral_logQuadratic_eq_phase y m hy
    (by exact_mod_cast (show 0 < m by omega))]
  simp only [logQuadratic, ← sum_div]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  ring

theorem log_gamma_half_add_nat_norm_estimate_of_nonneg
    (m : ℕ) (hm : 1 ≤ m) (y : ℝ) (hy : 0 ≤ y) :
    |Real.log ‖Complex.Gamma ((m : ℂ)+1/2+(y : ℂ)*I)‖-
      halfIntegerGammaMain m y| ≤ 2+Real.log (m : ℝ) := by
  rw [log_gamma_half_add_nat_norm_eq_main_add_error m hm y hy]
  have he := logQuadraticMidpointError_abs_le m hm y
  have hc := log_cosh_correction_abs_le (Real.pi*y) (mul_nonneg Real.pi_pos.le hy)
  have htri := abs_add_le (logQuadraticMidpointError m y)
    ((Real.pi*y-Real.log (Real.cosh (Real.pi*y))-Real.log 2)/2)
  convert! (htri.trans (add_le_add he hc)) using 1
  · congr 1
    ring
  · ring

/-- Uniform in all real heights, by conjugation on the negative half-line. -/
theorem log_gamma_half_add_nat_norm_estimate (m : ℕ) (hm : 1 ≤ m) (y : ℝ) :
    |Real.log ‖Complex.Gamma ((m : ℂ)+1/2+(y : ℂ)*I)‖-
      halfIntegerGammaMain m y| ≤ 2+Real.log (m : ℝ) := by
  by_cases hy : 0 ≤ y
  · exact log_gamma_half_add_nat_norm_estimate_of_nonneg m hm y hy
  · have h := log_gamma_half_add_nat_norm_estimate_of_nonneg m hm (-y) (by linarith)
    rwa [log_gamma_half_add_nat_norm_neg, halfIntegerGammaMain_neg] at h

theorem log_norm_real_add_imaginary (x y : ℝ) :
    Real.log ‖(x : ℂ)+(y : ℂ)*I‖ = logQuadratic y x := by
  have hsq : ‖(x : ℂ)+(y : ℂ)*I‖^2 = x^2+y^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  have h := congrArg Real.log hsq
  rw [Real.log_pow] at h
  unfold logQuadratic
  norm_num at h
  linarith

/-- A half-unit shift changes the log norm by at most one for real part at least one. -/
theorem log_norm_half_shift_bounds (x y : ℝ) (hx : 1 ≤ x) :
    0 ≤ Real.log ‖((x+1/2 : ℝ) : ℂ)+(y : ℂ)*I‖-
      Real.log ‖(x : ℂ)+(y : ℂ)*I‖ ∧
    Real.log ‖((x+1/2 : ℝ) : ℂ)+(y : ℂ)*I‖-
      Real.log ‖(x : ℂ)+(y : ℂ)*I‖ ≤ 1 := by
  rw [log_norm_real_add_imaginary, log_norm_real_add_imaginary]
  have hx0 : 0 < x := by linarith
  have hl := logQuadratic_monotoneOn y hx0
    (show 0 < x+1/2 by linarith) (show x ≤ x+1/2 by linarith)
  have hu := Real.log_le_log (show 0 < (x+1/2)^2+y^2 by positivity)
    (show (x+1/2)^2+y^2 ≤ 4*(x^2+y^2) by nlinarith [sq_nonneg y])
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : x^2+y^2 ≠ 0)] at hu
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [h4] at hu
  unfold logQuadratic at hl ⊢
  constructor <;> linarith

/-- Exact recurrence with the positive half-unit norm factor kept explicit. -/
theorem log_gamma_three_half_add_nat_norm (m : ℕ) (y : ℝ) :
    Real.log ‖Complex.Gamma ((m : ℂ)+3/2+(y : ℂ)*I)‖ =
      Real.log ‖Complex.Gamma ((m : ℂ)+1/2+(y : ℂ)*I)‖+
        Real.log ‖(m : ℂ)+1/2+(y : ℂ)*I‖ := by
  have hre : 0 < ((m : ℂ)+1/2+(y : ℂ)*I).re := by
    simp
    positivity
  have hz : (m : ℂ)+1/2+(y : ℂ)*I ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  have hg : Complex.Gamma ((m : ℂ)+1/2+(y : ℂ)*I) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hre
  have harg : (m : ℂ)+3/2+(y : ℂ)*I = ((m : ℂ)+1/2+(y : ℂ)*I)+1 := by ring
  rw [harg, Complex.Gamma_add_one _ hz, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hg)]
  ring

/-- The shifted estimate subtracts `log norm (m + I*y)`, not the half-shifted norm. -/
theorem log_gamma_three_half_add_nat_norm_estimate
    (m : ℕ) (hm : 1 ≤ m) (y : ℝ) :
    |Real.log ‖Complex.Gamma ((m : ℂ)+3/2+(y : ℂ)*I)‖-
      (halfIntegerGammaMain m y+Real.log ‖(m : ℂ)+(y : ℂ)*I‖)| ≤
        3+Real.log (m : ℝ) := by
  have he := log_gamma_half_add_nat_norm_estimate m hm y
  have hs := log_norm_half_shift_bounds m y (by exact_mod_cast hm)
  push_cast at hs
  have hsabs : |Real.log ‖(m : ℂ)+1/2+(y : ℂ)*I‖-
      Real.log ‖(m : ℂ)+(y : ℂ)*I‖| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  rw [log_gamma_three_half_add_nat_norm]
  have htri := abs_add_le
    (Real.log ‖Complex.Gamma ((m : ℂ)+1/2+(y : ℂ)*I)‖-halfIntegerGammaMain m y)
    (Real.log ‖(m : ℂ)+1/2+(y : ℂ)*I‖-Real.log ‖(m : ℂ)+(y : ℂ)*I‖)
  convert! (htri.trans (add_le_add he hsabs)) using 1
  · congr 1
    ring
  · ring

/-- Exact scaling of the real main term; no limiting process is involved. -/
theorem halfIntegerGammaMain_mul (a n s : ℝ) (ha : 0 < a) (hn : 0 < n) :
    halfIntegerGammaMain (a*n) (n*s) =
      n*(a*Real.log n+halfIntegerGammaPhase a s)+Real.log (2*Real.pi)/2 := by
  have hq : (a*n)^2+(n*s)^2 = n^2*(a^2+s^2) := by ring
  have hr : n*s/(a*n) = s/a := by field_simp
  unfold halfIntegerGammaMain halfIntegerGammaPhase
  rw [hq, hr, Real.log_mul (pow_ne_zero _ hn.ne') (by positivity : a^2+s^2 ≠ 0),
    Real.log_pow]
  ring

/-- Exact scaling of the additional norm prefactor in the three-half shift. -/
theorem log_norm_real_add_imaginary_mul (a n s : ℝ) (ha : 0 < a) (hn : 0 < n) :
    Real.log ‖((a*n : ℝ) : ℂ)+((n*s : ℝ) : ℂ)*I‖ =
      Real.log n+Real.log ‖(a : ℂ)+(s : ℂ)*I‖ := by
  have hz : (a : ℂ)+(s : ℂ)*I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have harg : ((a*n : ℝ) : ℂ)+((n*s : ℝ) : ℂ)*I =
      (n : ℂ)*((a : ℂ)+(s : ℂ)*I) := by push_cast; ring
  rw [harg, norm_mul, Complex.norm_of_nonneg hn.le,
    Real.log_mul hn.ne' (norm_ne_zero_iff.mpr hz)]

/-- The half-shift estimate at `m = a*n`, uniform for every real scaled height. -/
theorem log_gamma_half_mul_norm_estimate (a n : ℕ) (ha : 1 ≤ a) (hn : 1 ≤ n)
    (s : ℝ) :
    |Real.log ‖Complex.Gamma ((a : ℂ)*(n : ℂ)+1/2+(n : ℂ)*(s : ℂ)*I)‖-
      ((n : ℝ)*((a : ℝ)*Real.log (n : ℝ)+halfIntegerGammaPhase a s)+
        Real.log (2*Real.pi)/2)| ≤ 2+Real.log (a : ℝ)+Real.log (n : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := log_gamma_half_add_nat_norm_estimate (a*n)
    (Nat.mul_pos (by omega) (by omega)) ((n : ℝ)*s)
  push_cast at h
  rw [halfIntegerGammaMain_mul (a : ℝ) n s haR hnR,
    Real.log_mul haR.ne' hnR.ne'] at h
  simpa only [add_assoc] using h

/-- The three-half shift includes the exact extra `log n + log norm (a + I*s)`. -/
theorem log_gamma_three_half_mul_norm_estimate
    (a n : ℕ) (ha : 1 ≤ a) (hn : 1 ≤ n) (s : ℝ) :
    |Real.log ‖Complex.Gamma ((a : ℂ)*(n : ℂ)+3/2+(n : ℂ)*(s : ℂ)*I)‖-
      ((n : ℝ)*((a : ℝ)*Real.log (n : ℝ)+halfIntegerGammaPhase a s)+
        Real.log (2*Real.pi)/2+Real.log (n : ℝ)+
          Real.log ‖(a : ℂ)+(s : ℂ)*I‖)| ≤
            3+Real.log (a : ℝ)+Real.log (n : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := log_gamma_three_half_add_nat_norm_estimate (a*n)
    (Nat.mul_pos (by omega) (by omega)) ((n : ℝ)*s)
  have hp := log_norm_real_add_imaginary_mul (a : ℝ) n s haR hnR
  push_cast at h hp
  rw [halfIntegerGammaMain_mul (a : ℝ) n s haR hnR, hp,
    Real.log_mul haR.ne' hnR.ne'] at h
  simpa only [add_assoc] using h


end

end OddZetaSix
