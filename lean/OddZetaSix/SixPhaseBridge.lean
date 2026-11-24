import OddZetaSix.SixContour
import OddZetaSix.SixHalfGamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Gamma Factorization, Adaptive Phase Potential, Tail Bound, and 4-Bin Analytic Bridge

Connects the contour determinant majorant in `SixContour.lean` to compact `[0, 2]`
off-root phase certification for the slim 4-bin, 2-root-pair analytic scheme:
1. Exact Gamma factorization of `sixContourIntegrand n 0 0` and uniform Stirling +
   half-integer Gamma density bound in `y = (50 n) * s` coordinates.
2. Exact 2-root-pair adaptive monic polynomial `sixAdaptiveMonic`, contour coordinate
   identity `δ_n = 69/50 + 1/(100 n)`, uniform drift bound `exp (5 / 23)`, and residual
   monomial bound `2^12 (1 + |s|)^12`.
3. Elementary tail derivative bound `≤ -1/2` on `y ≥ 2` for `a₁, a₂, t ∈ [0, 3/10]`,
   fixed integrable polynomial-exponential envelope `(1 + |s|)^18 exp(-1/2 max 0 (|s| - 2))`,
   and full-line modulus moment bound from compact `[0, 2]` off-root ceilings.
4. Elementary 4-bin affine interpolation and `Finset.sum` endgame theorem
   `sixAnalyticRate_of_four_bin_endpoints`, reducing `SixAnalyticRateHypothesis R_bound`
   to verifying 8 rational endpoint ceilings on `[0, 2]`.

Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

noncomputable section
set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix

open Polynomial Finset Filter MeasureTheory Set Complex
open scoped BigOperators Topology ComplexConjugate

/-! ## Section 1: Exact Gamma factorization of the base contour integrand -/

private theorem gamma_integer_shift_ne_zero (z : ℂ)
    (hz : ∀ q : ℤ, z ≠ (q : ℂ)) (a : ℤ) :
    Complex.Gamma (z + (a : ℂ)) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hm
  apply hz (-(m : ℤ) - a)
  push_cast
  linear_combination hm

private theorem rising_complex_eval_gamma (z : ℂ)
    (hz : ∀ q : ℤ, z ≠ (q : ℂ)) (a : ℤ) (k : ℕ) :
    aeval z (rising (a : ℚ) k) =
      Complex.Gamma (z + (a : ℂ) + (k : ℂ)) / Complex.Gamma (z + (a : ℂ)) := by
  have havoid : ∀ j : ℕ, z + (a : ℂ) ≠ -(j : ℂ) := by
    intro j hj
    apply hz (-(j : ℤ) - a)
    push_cast
    linear_combination hj
  rw [Complex.Gamma_add_nat_div_Gamma_eq _ havoid]
  induction k with
  | zero => simp [rising, ascPochhammer_zero]
  | succ k ih =>
    rw [rising, prod_range_succ, map_mul]
    change aeval z (rising (a : ℚ) k) * _ = _
    rw [ih, ascPochhammer_succ_right]
    simp only [eval_mul, eval_add, eval_X, eval_natCast, map_add,
      aeval_X, aeval_C, map_intCast]
    push_cast
    ring

private theorem sixContourPoint_ne_integer (n : ℕ) (y : ℝ) (q : ℤ) :
    sixContourPoint n y ≠ (q : ℂ) := by
  intro h
  apply sixContourAbscissa_ne_int n q
  simpa only [sixContourPoint_re, Complex.intCast_re] using congrArg Complex.re h

private theorem sin_pi_ne_zero_of_noninteger (z : ℂ)
    (hz : ∀ q : ℤ, z ≠ (q : ℂ)) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  intro hs
  obtain ⟨q, hq⟩ := Complex.sin_eq_zero_iff.mp hs
  apply hz q
  apply mul_left_cancel₀ (show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero)
  simpa only [mul_comm] using hq

private theorem gamma_add_one_inv_reflection (z : ℂ)
    (hz : ∀ q : ℤ, z ≠ (q : ℂ)) :
    (Complex.Gamma (z + 1))⁻¹ =
      -(Complex.Gamma (-z)) * Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ) := by
  have hg : Complex.Gamma (z + 1) ≠ 0 := by
    simpa using gamma_integer_shift_ne_zero z hz 1
  have hs := sin_pi_ne_zero_of_noninteger z hz
  have hs' : Complex.sin (z * (Real.pi : ℂ)) ≠ 0 := by simpa only [mul_comm] using hs
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := Complex.Gamma_mul_Gamma_one_sub (-z)
  rw [sub_neg_eq_add, add_comm (1 : ℂ) z, mul_neg, Complex.sin_neg] at h
  field_simp [hg, hs, hs', hp] at h ⊢
  linear_combination h

def sixGammaLeft (n : ℕ) (a : Fin 5) (z : ℂ) : ℂ :=
  Complex.Gamma (z + ((sixZero a * n : ℕ) : ℂ) + 1)

def sixGammaRight (n : ℕ) (a : Fin 5) (z : ℂ) : ℂ :=
  Complex.Gamma (z + (140 * (n : ℂ) + 2 - ((sixZero a * n : ℕ) : ℂ)))

def sixGammaDenStart (n : ℕ) (b : Fin 14) (z : ℂ) : ℂ :=
  Complex.Gamma (z + (((45 + sixOffset b) * n : ℕ) : ℂ) + 1)

def sixGammaDenEnd (n : ℕ) (b : Fin 14) (z : ℂ) : ℂ :=
  Complex.Gamma (z + (((45 + sixOffset b) * n : ℕ) : ℂ) +
    (((50 - 2 * sixOffset b) * n : ℕ) : ℂ) + 2)

private theorem six_left_rising_gamma (n : ℕ) (a : Fin 5) (z : ℂ)
    (hz : ∀ q : ℤ, z ≠ (q : ℂ)) :
    aeval z (rising 1 (sixZero a * n)) =
      sixGammaLeft n a z / Complex.Gamma (z + 1) := by
  simpa [sixGammaLeft, add_comm, add_left_comm, add_assoc] using
    rising_complex_eval_gamma z hz 1 (sixZero a * n)

private theorem six_right_rising_gamma (n : ℕ) (a : Fin 5) (z : ℂ)
    (hz : ∀ q : ℤ, z ≠ (q : ℂ)) :
    aeval z (rising (140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ)) (sixZero a * n)) =
      Complex.Gamma (z + 140 * (n : ℂ) + 2) / sixGammaRight n a z := by
  have h := rising_complex_eval_gamma z hz
    (140 * (n : ℤ) + 2 - ((sixZero a * n : ℕ) : ℤ)) (sixZero a * n)
  dsimp [sixGammaRight]
  push_cast at h ⊢
  convert h using 1
  congr 1; congr 1; ring

private theorem six_den_rising_gamma (n : ℕ) (b : Fin 14) (z : ℂ)
    (hz : ∀ q : ℤ, z ≠ (q : ℂ)) :
    aeval z (rising (((45 + sixOffset b) * n : ℕ) + 1) ((50 - 2 * sixOffset b) * n + 1)) =
      sixGammaDenEnd n b z / sixGammaDenStart n b z := by
  have h := rising_complex_eval_gamma z hz
    (((45 + sixOffset b) * n : ℕ) + 1) ((50 - 2 * sixOffset b) * n + 1)
  dsimp [sixGammaDenEnd, sixGammaDenStart]
  push_cast at h ⊢
  convert h using 1
  congr 1 <;> congr 1 <;> ring

def sixPositiveGammaKernel (n : ℕ) (z : ℂ) : ℂ :=
  Complex.Gamma (z + 140 * (n : ℂ) + 2) ^ 5 * Complex.Gamma (-z) ^ 5 *
    (∏ a : Fin 5, sixGammaLeft n a z / sixGammaRight n a z) *
    (∏ b : Fin 14, sixGammaDenStart n b z / sixGammaDenEnd n b z)

theorem sixEntryComplex_base_gamma (n : ℕ) (z : ℂ)
    (hz : ∀ q : ℤ, z ≠ (q : ℂ)) :
    sixEntryComplex n 0 0 z =
      -(sixNormalization n : ℂ) * (z + 70 * (n : ℂ) + 1) *
        sixPositiveGammaKernel n z * Complex.sin ((Real.pi : ℂ) * z) ^ 5 /
          (Real.pi : ℂ) ^ 5 := by
  have hratios : sixEntryComplex n 0 0 z =
      (sixNormalization n : ℂ) * (z + 70 * (n : ℂ) + 1) *
        (∏ a : Fin 5, (sixGammaLeft n a z / Complex.Gamma (z + 1)) *
          (Complex.Gamma (z + 140 * (n : ℂ) + 2) / sixGammaRight n a z)) /
        (∏ b : Fin 14, sixGammaDenEnd n b z / sixGammaDenStart n b z) := by
    simp only [sixEntryComplex, centeredMultiplier, evenBasis,
      one_comp, mul_one, sixNumerator, sixDenominator, map_mul, map_prod,
      map_add, aeval_X, aeval_C]
    simp_rw [six_left_rising_gamma n _ z hz, six_right_rising_gamma n _ z hz,
      six_den_rising_gamma n _ z hz]
    have halg (q : ℚ) : (algebraMap ℚ ℂ) q = (q : ℂ) := rfl
    simp_rw [halg]
    push_cast
    ring
  rw [hratios]
  simp only [sixPositiveGammaKernel, div_eq_mul_inv, prod_mul_distrib,
    prod_const, card_univ, Fintype.card_fin, prod_inv_distrib, mul_inv_rev, inv_inv]
  rw [gamma_add_one_inv_reflection z hz]
  ring

theorem sixContourIntegrand_base_gamma (n : ℕ) (z : ℂ)
    (hz : ∀ q : ℤ, z ≠ (q : ℂ)) :
    sixContourIntegrand n 0 0 z =
      -(sixNormalization n : ℂ) * (z + 70 * (n : ℂ) + 1) *
        sixPositiveGammaKernel n z *
        (Complex.cos ((Real.pi : ℂ) * z) ^ 3 +
          2 * Complex.cos ((Real.pi : ℂ) * z)) / 3 := by
  have hs := sin_pi_ne_zero_of_noninteger z hz
  have hs' : Complex.sin (z * (Real.pi : ℂ)) ≠ 0 := by simpa only [mul_comm] using hs
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [sixContourIntegrand, sixEntryComplex_base_gamma n z hz, sixContourKernel_eq z hs]
  field_simp [hs, hs', hp]

theorem sixModulusWeight_gamma (n : ℕ) (y : ℝ) :
    sixModulusWeight n y =
      |(sixNormalization n : ℝ)| *
        ‖sixContourPoint n y + 70 * (n : ℂ) + 1‖ *
        ‖sixPositiveGammaKernel n (sixContourPoint n y)‖ *
        ‖Complex.cos ((Real.pi : ℂ) * sixContourPoint n y) ^ 3 +
          2 * Complex.cos ((Real.pi : ℂ) * sixContourPoint n y)‖ / (6 * Real.pi) := by
  rw [sixModulusWeight, sixVerticalIntegrand,
    sixContourIntegrand_base_gamma n _ (sixContourPoint_ne_integer n y)]
  simp only [norm_mul, norm_div, norm_neg, Complex.norm_I, mul_one,
    Complex.norm_ofNat, Complex.norm_ratCast]
  rw [← Rat.cast_abs]
  ring

def sixGammaHalf (m : ℕ) (y : ℝ) : ℂ :=
  Complex.Gamma ((m : ℂ) + 1 / 2 + (y : ℂ) * I)

def sixGammaThreeHalves (m : ℕ) (y : ℝ) : ℂ :=
  Complex.Gamma ((m : ℂ) + 3 / 2 + (y : ℂ) * I)

private theorem sixGammaHalf_ne_zero (m : ℕ) (y : ℝ) : sixGammaHalf m y ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos; norm_num; positivity

private theorem sixGammaThreeHalves_ne_zero (m : ℕ) (y : ℝ) : sixGammaThreeHalves m y ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos; norm_num; positivity

private theorem sixGammaHalf_norm_neg (m : ℕ) (y : ℝ) :
    ‖sixGammaHalf m (-y)‖ = ‖sixGammaHalf m y‖ := by
  have h : (m : ℂ) + 1 / 2 + ((-y : ℝ) : ℂ) * I =
      starRingEnd ℂ ((m : ℂ) + 1 / 2 + (y : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [sixGammaHalf, h, Complex.Gamma_conj]; simp [sixGammaHalf]

private theorem sixGammaThreeHalves_norm_neg (m : ℕ) (y : ℝ) :
    ‖sixGammaThreeHalves m (-y)‖ = ‖sixGammaThreeHalves m y‖ := by
  have h : (m : ℂ) + 3 / 2 + ((-y : ℝ) : ℂ) * I =
      starRingEnd ℂ ((m : ℂ) + 3 / 2 + (y : ℂ) * I) := by
    apply Complex.ext <;> norm_num [map_ofNat]
  rw [sixGammaThreeHalves, h, Complex.Gamma_conj]; simp [sixGammaThreeHalves]

theorem sixPositiveGammaKernel_contour (n : ℕ) (y : ℝ) :
    sixPositiveGammaKernel n (sixContourPoint n y) =
      sixGammaThreeHalves (139 * n) y ^ 5 * sixGammaHalf (1 * n) (-y) ^ 5 *
        (∏ a : Fin 5, sixGammaHalf ((sixZero a - 1) * n) y /
          sixGammaThreeHalves ((139 - sixZero a) * n) y) *
        (∏ b : Fin 14, sixGammaHalf ((44 + sixOffset b) * n) y /
          sixGammaThreeHalves ((94 - sixOffset b) * n) y) := by
  have htop : Complex.Gamma (sixContourPoint n y + 140 * (n : ℂ) + 2) =
      sixGammaThreeHalves (139 * n) y := by
    unfold sixGammaThreeHalves sixContourPoint sixContourAbscissa
    congr 1; push_cast; ring
  have hneg : Complex.Gamma (-sixContourPoint n y) = sixGammaHalf (1 * n) (-y) := by
    unfold sixGammaHalf sixContourPoint sixContourAbscissa
    congr 1; push_cast; ring
  have hleft : ∀ a : Fin 5, sixGammaLeft n a (sixContourPoint n y) =
      sixGammaHalf ((sixZero a - 1) * n) y := by
    intro a
    have hge : 1 ≤ sixZero a := by fin_cases a <;> decide
    unfold sixGammaLeft sixGammaHalf sixContourPoint sixContourAbscissa
    congr 1; push_cast [Nat.cast_sub hge]; ring
  have hright : ∀ a : Fin 5, sixGammaRight n a (sixContourPoint n y) =
      sixGammaThreeHalves ((139 - sixZero a) * n) y := by
    intro a
    have hle : sixZero a ≤ 139 := by fin_cases a <;> decide
    unfold sixGammaRight sixGammaThreeHalves sixContourPoint sixContourAbscissa
    congr 1; push_cast [Nat.cast_sub hle]; ring
  have hdstart : ∀ b : Fin 14, sixGammaDenStart n b (sixContourPoint n y) =
      sixGammaHalf ((44 + sixOffset b) * n) y := by
    intro b
    unfold sixGammaDenStart sixGammaHalf sixContourPoint sixContourAbscissa
    congr 1; push_cast; ring
  have hdend : ∀ b : Fin 14, sixGammaDenEnd n b (sixContourPoint n y) =
      sixGammaThreeHalves ((94 - sixOffset b) * n) y := by
    intro b
    have hle1 : 2 * sixOffset b ≤ 50 := by fin_cases b <;> decide
    have hle2 : sixOffset b ≤ 94 := by fin_cases b <;> decide
    unfold sixGammaDenEnd sixGammaThreeHalves sixContourPoint sixContourAbscissa
    congr 1; push_cast [Nat.cast_sub hle1, Nat.cast_sub hle2]; ring
  unfold sixPositiveGammaKernel
  rw [htop, hneg]
  simp_rw [hleft, hright, hdstart, hdend]

theorem sixPositiveGammaKernel_contour_ne_zero (n : ℕ) (y : ℝ) :
    sixPositiveGammaKernel n (sixContourPoint n y) ≠ 0 := by
  rw [sixPositiveGammaKernel_contour]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero
    (pow_ne_zero _ (sixGammaThreeHalves_ne_zero _ _))
    (pow_ne_zero _ (sixGammaHalf_ne_zero _ _)))
    (prod_ne_zero_iff.mpr fun a _ => div_ne_zero (sixGammaHalf_ne_zero _ _)
      (sixGammaThreeHalves_ne_zero _ _)))
    (prod_ne_zero_iff.mpr fun b _ => div_ne_zero (sixGammaHalf_ne_zero _ _)
      (sixGammaThreeHalves_ne_zero _ _))

theorem log_sixPositiveGammaKernel_contour (n : ℕ) (y : ℝ) :
    Real.log ‖sixPositiveGammaKernel n (sixContourPoint n y)‖ =
      5 * Real.log ‖sixGammaThreeHalves (139 * n) y‖ +
      5 * Real.log ‖sixGammaHalf (1 * n) y‖ +
      (∑ a : Fin 5, (Real.log ‖sixGammaHalf ((sixZero a - 1) * n) y‖ -
        Real.log ‖sixGammaThreeHalves ((139 - sixZero a) * n) y‖)) +
      (∑ b : Fin 14, (Real.log ‖sixGammaHalf ((44 + sixOffset b) * n) y‖ -
        Real.log ‖sixGammaThreeHalves ((94 - sixOffset b) * n) y‖)) := by
  have hh (m : ℕ) (s : ℝ) : ‖sixGammaHalf m s‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sixGammaHalf_ne_zero m s)
  have ht (m : ℕ) (s : ℝ) : ‖sixGammaThreeHalves m s‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sixGammaThreeHalves_ne_zero m s)
  rw [sixPositiveGammaKernel_contour]
  simp only [norm_mul, norm_pow, norm_prod, norm_div, sixGammaHalf_norm_neg]
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (ht _ _)) (pow_ne_zero _ (hh _ _)))
      (prod_ne_zero_iff.mpr fun a _ => div_ne_zero (hh _ _) (ht _ _)))
      (prod_ne_zero_iff.mpr fun b _ => div_ne_zero (hh _ _) (ht _ _)),
    Real.log_mul (mul_ne_zero (pow_ne_zero _ (ht _ _)) (pow_ne_zero _ (hh _ _)))
      (prod_ne_zero_iff.mpr fun a _ => div_ne_zero (hh _ _) (ht _ _)),
    Real.log_mul (pow_ne_zero _ (ht _ _)) (pow_ne_zero _ (hh _ _)),
    Real.log_pow, Real.log_pow,
    Real.log_prod (fun a _ => div_ne_zero (hh _ _) (ht _ _)),
    Real.log_prod (fun b _ => div_ne_zero (hh _ _) (ht _ _))]
  simp_rw [Real.log_div (hh _ _) (ht _ _)]
  norm_num

/-! ## Section 2: Scalar phase, factorial normalization, and uniform density envelope -/

/-- Scale-normalized phase building block `(d/2) log(d^2 + y^2) - y arctan(y/d)`. -/
def sixPhaseX (d y : ℝ) : ℝ :=
  (d / 2) * Real.log (d ^ 2 + y ^ 2) - y * Real.arctan (y / d)

/-- Constant term from `sixNormalization n` after scaling by `L = 50`. -/
def sixPhaseConstant : ℝ :=
  (∑ b : Fin 14, (((50 - 2 * sixOffset b : ℕ) : ℝ) / 50) *
      Real.log (((50 - 2 * sixOffset b : ℕ) : ℝ) / 50)) -
    2 * ∑ a : Fin 5, ((sixZero a : ℝ) / 50) * Real.log ((sixZero a : ℝ) / 50)

/-- Scalar analytic phase `φ(y)` in normalized height `y = |u| / (50 n)`. -/
def sixPhase (y : ℝ) : ℝ :=
  sixPhaseConstant + 5 * sixPhaseX (139 / 50) y + 5 * sixPhaseX (1 / 50) y +
    (∑ a : Fin 5, (sixPhaseX (((sixZero a - 1 : ℕ) : ℝ) / 50) y -
      sixPhaseX (((139 - sixZero a : ℕ) : ℝ) / 50) y)) +
    (∑ b : Fin 14, (sixPhaseX (((44 + sixOffset b : ℕ) : ℝ) / 50) y -
      sixPhaseX (((94 - sixOffset b : ℕ) : ℝ) / 50) y)) +
    3 * Real.pi * y

theorem sixNormalization_real_pos (n : ℕ) : 0 < (sixNormalization n : ℝ) := by
  have hq : 0 < sixNormalization n := by
    unfold sixNormalization
    apply div_pos
    · exact mul_pos (by norm_num) (Finset.prod_pos fun b _ => by positivity)
    · exact Finset.prod_pos fun a _ => by positivity
  exact_mod_cast hq

private def sixFactorialLogError (m : ℕ) : ℝ :=
  Real.log (m.factorial : ℝ) -
    ((m : ℝ) * Real.log (m : ℝ) - (m : ℝ) +
      Real.log (m : ℝ) / 2 + Real.log (2 * Real.pi) / 2)

private theorem sixFactorialLogError_bounds (m : ℕ) (hm : 0 < m) :
    0 ≤ sixFactorialLogError m ∧ sixFactorialLogError m ≤ 1 := by
  rcases m with _ | m
  · omega
  have hmR : (0 : ℝ) < (m + 1 : ℝ) := by positivity
  have hl := Stirling.le_log_factorial_stirling (Nat.succ_ne_zero m)
  have hu := Stirling.log_stirlingSeq'_antitone (Nat.zero_le m)
  dsimp only [Function.comp_def, Nat.succ_eq_add_one] at hu
  have hs : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
    rw [Stirling.stirlingSeq_one, Real.log_div (by positivity) (by positivity),
      Real.log_exp, Real.log_sqrt (by positivity)]
  rw [hs] at hu
  have hf := Stirling.log_stirlingSeq_formula (m + 1)
  push_cast at hf
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hmR.ne',
    Real.log_div hmR.ne' (Real.exp_ne_zero 1), Real.log_exp] at hf
  have hpi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  dsimp only [sixFactorialLogError]
  push_cast at hl ⊢
  constructor <;> linarith

private theorem six_factorial_log_scaled (c n : ℕ) (hc : 0 < c) (hn : 0 < n) :
    Real.log (Nat.factorial (c * n) : ℝ) =
      ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (n : ℝ) * Real.log 50) * (c : ℝ) +
        50 * (n : ℝ) * (((c : ℝ) / 50) * Real.log ((c : ℝ) / 50)) +
        Real.log (n : ℝ) / 2 + (1 / 2 : ℝ) * Real.log (c : ℝ) +
        Real.log (2 * Real.pi) / 2 + sixFactorialLogError (c * n) := by
  have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hc
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold sixFactorialLogError
  rw [Nat.cast_mul, Real.log_mul hcR.ne' hnR.ne',
    Real.log_div hcR.ne' (by norm_num : (50 : ℝ) ≠ 0)]
  ring

private def sixNormalizationLogConstant : ℝ :=
  Real.log 2 + 2 * Real.log (2 * Real.pi) +
    (1 / 2 : ℝ) * (∑ b : Fin 14, Real.log ((50 - 2 * sixOffset b : ℕ) : ℝ)) -
    ∑ a : Fin 5, Real.log (sixZero a : ℝ)

private theorem sixNormalization_log_upper (n : ℕ) (hn : 1 ≤ n) :
    Real.log (sixNormalization n : ℝ) ≤
      174 * (n : ℝ) * Real.log (n : ℝ) + 174 * (n : ℝ) * Real.log 50 - 174 * (n : ℝ) +
        50 * (n : ℝ) * sixPhaseConstant + 2 * Real.log (n : ℝ) +
        sixNormalizationLogConstant + 14 := by
  have hnpos : 0 < n := by omega
  have hf (m : ℕ) : (m.factorial : ℝ) ≠ 0 := by positivity
  have hcast : (sixNormalization n : ℝ) =
      2 * (∏ b : Fin 14, (Nat.factorial ((50 - 2 * sixOffset b) * n) : ℝ)) /
        (∏ a : Fin 5, (Nat.factorial (sixZero a * n) : ℝ) ^ 2) := by
    unfold sixNormalization; push_cast; rfl
  have hlog : Real.log (sixNormalization n : ℝ) = Real.log 2 +
      (∑ b : Fin 14, Real.log (Nat.factorial ((50 - 2 * sixOffset b) * n) : ℝ)) -
      2 * ∑ a : Fin 5, Real.log (Nat.factorial (sixZero a * n) : ℝ) := by
    rw [hcast,
      Real.log_div (mul_ne_zero (by norm_num) (Finset.prod_ne_zero_iff.mpr fun b _ => hf _))
        (Finset.prod_ne_zero_iff.mpr fun a _ => pow_ne_zero 2 (hf _)),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Finset.prod_ne_zero_iff.mpr fun b _ => hf _),
      Real.log_prod fun b _ => hf _,
      Real.log_prod fun a _ => pow_ne_zero 2 (hf _)]
    simp only [Real.log_pow, Nat.cast_ofNat, ← Finset.mul_sum]
  have hb_pos (b : Fin 14) : 0 < 50 - 2 * sixOffset b := by fin_cases b <;> decide
  have ha_pos (a : Fin 5) : 0 < sixZero a := by fin_cases a <;> decide
  have hnum_eq : (∑ b : Fin 14, Real.log (Nat.factorial ((50 - 2 * sixOffset b) * n) : ℝ)) =
      ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (n : ℝ) * Real.log 50) * 582 +
      50 * (n : ℝ) * (∑ b : Fin 14, (((50 - 2 * sixOffset b : ℕ) : ℝ) / 50) *
        Real.log (((50 - 2 * sixOffset b : ℕ) : ℝ) / 50)) +
      7 * Real.log (n : ℝ) +
      (1 / 2 : ℝ) * (∑ b : Fin 14, Real.log ((50 - 2 * sixOffset b : ℕ) : ℝ)) +
      7 * Real.log (2 * Real.pi) +
      ∑ b : Fin 14, sixFactorialLogError ((50 - 2 * sixOffset b) * n) := by
    rw [Finset.sum_congr rfl fun b _ => six_factorial_log_scaled _ n (hb_pos b) hnpos]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hs : (∑ b : Fin 14, ((50 - 2 * sixOffset b : ℕ) : ℝ)) = 582 := by
      have : (∑ b : Fin 14, (50 - 2 * sixOffset b)) = 582 := by decide
      exact_mod_cast this
    rw [hs]; ring
  have hden_eq : (∑ a : Fin 5, Real.log (Nat.factorial (sixZero a * n) : ℝ)) =
      ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (n : ℝ) * Real.log 50) * 204 +
      50 * (n : ℝ) * (∑ a : Fin 5, ((sixZero a : ℝ) / 50) * Real.log ((sixZero a : ℝ) / 50)) +
      (5 / 2 : ℝ) * Real.log (n : ℝ) +
      (1 / 2 : ℝ) * (∑ a : Fin 5, Real.log (sixZero a : ℝ)) +
      (5 / 2 : ℝ) * Real.log (2 * Real.pi) +
      ∑ a : Fin 5, sixFactorialLogError (sixZero a * n) := by
    rw [Finset.sum_congr rfl fun a _ => six_factorial_log_scaled _ n (ha_pos a) hnpos]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hs : (∑ a : Fin 5, (sixZero a : ℝ)) = 204 := by
      have : (∑ a : Fin 5, sixZero a) = 204 := by decide
      exact_mod_cast this
    rw [hs]; ring
  have herr_num : (∑ b : Fin 14, sixFactorialLogError ((50 - 2 * sixOffset b) * n)) ≤ 14 := by
    calc _ ≤ ∑ _b : Fin 14, (1 : ℝ) :=
          Finset.sum_le_sum fun b _ => (sixFactorialLogError_bounds _ (Nat.mul_pos (hb_pos b) hnpos)).2
      _ = 14 := by norm_num
  have herr_den : 0 ≤ ∑ a : Fin 5, sixFactorialLogError (sixZero a * n) :=
    Finset.sum_nonneg fun a _ => (sixFactorialLogError_bounds _ (Nat.mul_pos (ha_pos a) hnpos)).1
  rw [hlog, hnum_eq, hden_eq]
  unfold sixPhaseConstant sixNormalizationLogConstant
  linarith

private theorem halfIntegerGammaPhase_scale50 (a : ℕ) (ha : 1 ≤ a) (s : ℝ) :
    halfIntegerGammaPhase (a : ℝ) (50 * s) =
      (a : ℝ) * (Real.log 50 - 1) + 50 * sixPhaseX ((a : ℝ) / 50) s := by
  have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hq : (a : ℝ) ^ 2 + (50 * s) ^ 2 = (50 : ℝ) ^ 2 * (((a : ℝ) / 50) ^ 2 + s ^ 2) := by ring
  have hr : 50 * s / (a : ℝ) = s / ((a : ℝ) / 50) := by field_simp
  unfold halfIntegerGammaPhase sixPhaseX
  rw [hq, hr, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  ring

private def sixHalfGammaMain (a n : ℕ) (s : ℝ) : ℝ :=
  (n : ℝ) * ((a : ℝ) * Real.log (n : ℝ) + halfIntegerGammaPhase a (50 * s)) +
    Real.log (2 * Real.pi) / 2

private def sixThreeHalfGammaMain (a n : ℕ) (s : ℝ) : ℝ :=
  sixHalfGammaMain a n s + Real.log (n : ℝ) + Real.log ‖(a : ℂ) + ((50 * s : ℝ) : ℂ) * I‖

private def sixGammaError (n : ℕ) : ℝ := 3 + Real.log 139 + Real.log (n : ℝ)

private theorem sixGammaHalf_log_bounds (a n : ℕ) (ha : 1 ≤ a) (ha' : a ≤ 139)
    (hn : 1 ≤ n) (s : ℝ) :
    sixHalfGammaMain a n s - sixGammaError n ≤
        Real.log ‖sixGammaHalf (a * n) (50 * (n : ℝ) * s)‖ ∧
      Real.log ‖sixGammaHalf (a * n) (50 * (n : ℝ) * s)‖ ≤
        sixHalfGammaMain a n s + sixGammaError n := by
  have h := log_gamma_half_mul_norm_estimate a n ha hn (50 * s)
  have hlog : Real.log (a : ℝ) ≤ Real.log 139 :=
    Real.log_le_log (by exact_mod_cast (show 0 < a by omega)) (by exact_mod_cast ha')
  have harg : (a : ℂ) * (n : ℂ) + 1 / 2 + (n : ℂ) * ((50 * s : ℝ) : ℂ) * I =
      ((a * n : ℕ) : ℂ) + 1 / 2 + ((50 * (n : ℝ) * s : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [harg] at h
  change |Real.log ‖sixGammaHalf (a * n) (50 * (n : ℝ) * s)‖ - sixHalfGammaMain a n s| ≤ _ at h
  dsimp [sixGammaError]
  exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩

private theorem sixGammaThreeHalf_log_bounds (a n : ℕ) (ha : 1 ≤ a) (ha' : a ≤ 139)
    (hn : 1 ≤ n) (s : ℝ) :
    sixThreeHalfGammaMain a n s - sixGammaError n ≤
        Real.log ‖sixGammaThreeHalves (a * n) (50 * (n : ℝ) * s)‖ ∧
      Real.log ‖sixGammaThreeHalves (a * n) (50 * (n : ℝ) * s)‖ ≤
        sixThreeHalfGammaMain a n s + sixGammaError n := by
  have h := log_gamma_three_half_mul_norm_estimate a n ha hn (50 * s)
  have hlog : Real.log (a : ℝ) ≤ Real.log 139 :=
    Real.log_le_log (by exact_mod_cast (show 0 < a by omega)) (by exact_mod_cast ha')
  have harg : (a : ℂ) * (n : ℂ) + 3 / 2 + (n : ℂ) * ((50 * s : ℝ) : ℂ) * I =
      ((a * n : ℕ) : ℂ) + 3 / 2 + ((50 * (n : ℝ) * s : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [harg] at h
  change |Real.log ‖sixGammaThreeHalves (a * n) (50 * (n : ℝ) * s)‖ -
      sixThreeHalfGammaMain a n s| ≤ _ at h
  dsimp [sixGammaError]
  exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩

private def sixGammaInventoryMain (n : ℕ) (s : ℝ) : ℝ :=
  5 * sixThreeHalfGammaMain 139 n s + 5 * sixHalfGammaMain 1 n s +
    (∑ a : Fin 5, (sixHalfGammaMain (sixZero a - 1) n s -
      sixThreeHalfGammaMain (139 - sixZero a) n s)) +
    (∑ b : Fin 14, (sixHalfGammaMain (44 + sixOffset b) n s -
      sixThreeHalfGammaMain (94 - sixOffset b) n s))

private theorem log_sixPositiveGammaKernel_le_inventory (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    Real.log ‖sixPositiveGammaKernel n (sixContourPoint n (50 * (n : ℝ) * s))‖ ≤
      sixGammaInventoryMain n s + 48 * sixGammaError n := by
  rw [log_sixPositiveGammaKernel_contour]
  have htop := (sixGammaThreeHalf_log_bounds 139 n (by norm_num) (by norm_num) hn s).2
  have hbase := (sixGammaHalf_log_bounds 1 n (by norm_num) (by norm_num) hn s).2
  have hsumA : (∑ a : Fin 5, (Real.log ‖sixGammaHalf ((sixZero a - 1) * n) (50 * (n : ℝ) * s)‖ -
      Real.log ‖sixGammaThreeHalves ((139 - sixZero a) * n) (50 * (n : ℝ) * s)‖)) ≤
      (∑ a : Fin 5, (sixHalfGammaMain (sixZero a - 1) n s -
        sixThreeHalfGammaMain (139 - sixZero a) n s)) + 10 * sixGammaError n := by
    calc _ ≤ ∑ a : Fin 5, (sixHalfGammaMain (sixZero a - 1) n s -
            sixThreeHalfGammaMain (139 - sixZero a) n s + 2 * sixGammaError n) := by
          apply sum_le_sum; intro a _
          have h1 : 1 ≤ sixZero a - 1 ∧ sixZero a - 1 ≤ 139 := by fin_cases a <;> decide
          have h2 : 1 ≤ 139 - sixZero a ∧ 139 - sixZero a ≤ 139 := by fin_cases a <;> decide
          have hl := (sixGammaHalf_log_bounds _ n h1.1 h1.2 hn s).2
          have hr := (sixGammaThreeHalf_log_bounds _ n h2.1 h2.2 hn s).1
          linarith
      _ = _ := by rw [sum_add_distrib]; simp; ring
  have hsumB : (∑ b : Fin 14, (Real.log ‖sixGammaHalf ((44 + sixOffset b) * n) (50 * (n : ℝ) * s)‖ -
      Real.log ‖sixGammaThreeHalves ((94 - sixOffset b) * n) (50 * (n : ℝ) * s)‖)) ≤
      (∑ b : Fin 14, (sixHalfGammaMain (44 + sixOffset b) n s -
        sixThreeHalfGammaMain (94 - sixOffset b) n s)) + 28 * sixGammaError n := by
    calc _ ≤ ∑ b : Fin 14, (sixHalfGammaMain (44 + sixOffset b) n s -
            sixThreeHalfGammaMain (94 - sixOffset b) n s + 2 * sixGammaError n) := by
          apply sum_le_sum; intro b _
          have h1 : 1 ≤ 44 + sixOffset b ∧ 44 + sixOffset b ≤ 139 := by fin_cases b <;> decide
          have h2 : 1 ≤ 94 - sixOffset b ∧ 94 - sixOffset b ≤ 139 := by fin_cases b <;> decide
          have hl := (sixGammaHalf_log_bounds _ n h1.1 h1.2 hn s).2
          have hr := (sixGammaThreeHalf_log_bounds _ n h2.1 h2.2 hn s).1
          linarith
      _ = _ := by rw [sum_add_distrib]; simp; ring
  unfold sixGammaInventoryMain
  linarith

private theorem sixGammaInventoryMain_eq_phase (n : ℕ) (s : ℝ) :
    sixGammaInventoryMain n s =
      50 * (n : ℝ) * (sixPhase s - sixPhaseConstant - 3 * Real.pi * s) -
        174 * (n : ℝ) * Real.log (n : ℝ) - 174 * (n : ℝ) * Real.log 50 + 174 * (n : ℝ) +
        5 * Real.log (2 * Real.pi) - 14 * Real.log (n : ℝ) +
        5 * Real.log ‖(139 : ℂ) + ((50 * s : ℝ) : ℂ) * I‖ -
        (∑ a : Fin 5, Real.log ‖((139 - sixZero a : ℕ) : ℂ) + ((50 * s : ℝ) : ℂ) * I‖) -
        (∑ b : Fin 14, Real.log ‖((94 - sixOffset b : ℕ) : ℂ) + ((50 * s : ℝ) : ℂ) * I‖) := by
  have hsA : ∀ a : Fin 5,
      sixHalfGammaMain (sixZero a - 1) n s - sixThreeHalfGammaMain (139 - sixZero a) n s =
        (n : ℝ) * ((((sixZero a - 1 : ℕ) : ℝ) - ((139 - sixZero a : ℕ) : ℝ)) *
          (Real.log (n : ℝ) + Real.log 50 - 1)) +
        50 * (n : ℝ) * (sixPhaseX (((sixZero a - 1 : ℕ) : ℝ) / 50) s -
          sixPhaseX (((139 - sixZero a : ℕ) : ℝ) / 50) s) -
        Real.log (n : ℝ) - Real.log ‖((139 - sixZero a : ℕ) : ℂ) + ((50 * s : ℝ) : ℂ) * I‖ := by
    intro a
    have h1 : 1 ≤ sixZero a - 1 := by fin_cases a <;> decide
    have h2 : 1 ≤ 139 - sixZero a := by fin_cases a <;> decide
    unfold sixThreeHalfGammaMain sixHalfGammaMain
    rw [halfIntegerGammaPhase_scale50 _ h1, halfIntegerGammaPhase_scale50 _ h2]
    ring
  have hsB : ∀ b : Fin 14,
      sixHalfGammaMain (44 + sixOffset b) n s - sixThreeHalfGammaMain (94 - sixOffset b) n s =
        (n : ℝ) * ((((44 + sixOffset b : ℕ) : ℝ) - ((94 - sixOffset b : ℕ) : ℝ)) *
          (Real.log (n : ℝ) + Real.log 50 - 1)) +
        50 * (n : ℝ) * (sixPhaseX (((44 + sixOffset b : ℕ) : ℝ) / 50) s -
          sixPhaseX (((94 - sixOffset b : ℕ) : ℝ) / 50) s) -
        Real.log (n : ℝ) - Real.log ‖((94 - sixOffset b : ℕ) : ℂ) + ((50 * s : ℝ) : ℂ) * I‖ := by
    intro b
    have h1 : 1 ≤ 44 + sixOffset b := by fin_cases b <;> decide
    have h2 : 1 ≤ 94 - sixOffset b := by fin_cases b <;> decide
    unfold sixThreeHalfGammaMain sixHalfGammaMain
    rw [halfIntegerGammaPhase_scale50 _ h1, halfIntegerGammaPhase_scale50 _ h2]
    ring
  have hsumA_int : (∑ a : Fin 5, ((sixZero a - 1 : ℕ) : ℝ)) -
      (∑ a : Fin 5, ((139 - sixZero a : ℕ) : ℝ)) = -292 := by
    have h1 : (∑ a : Fin 5, (sixZero a - 1)) = 199 := by decide
    have h2 : (∑ a : Fin 5, (139 - sixZero a)) = 491 := by decide
    have h1' : (∑ a : Fin 5, ((sixZero a - 1 : ℕ) : ℝ)) = 199 := by exact_mod_cast h1
    have h2' : (∑ a : Fin 5, ((139 - sixZero a : ℕ) : ℝ)) = 491 := by exact_mod_cast h2
    linarith
  have hsumB_int : (∑ b : Fin 14, ((44 + sixOffset b : ℕ) : ℝ)) -
      (∑ b : Fin 14, ((94 - sixOffset b : ℕ) : ℝ)) = -582 := by
    have h1 : (∑ b : Fin 14, (44 + sixOffset b)) = 675 := by decide
    have h2 : (∑ b : Fin 14, (94 - sixOffset b)) = 1257 := by decide
    have h1' : (∑ b : Fin 14, ((44 + sixOffset b : ℕ) : ℝ)) = 675 := by exact_mod_cast h1
    have h2' : (∑ b : Fin 14, ((94 - sixOffset b : ℕ) : ℝ)) = 1257 := by exact_mod_cast h2
    linarith
  unfold sixGammaInventoryMain
  rw [Finset.sum_congr rfl fun a _ => hsA a, Finset.sum_congr rfl fun b _ => hsB b]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsumA_int, hsumB_int]
  unfold sixThreeHalfGammaMain sixHalfGammaMain sixPhase
  rw [halfIntegerGammaPhase_scale50 139 (by norm_num),
    halfIntegerGammaPhase_scale50 1 (by norm_num)]
  simp only [Finset.sum_sub_distrib]
  push_cast
  ring

private theorem log_norm_real_add_imag_nonneg (a t : ℝ) (ha : 1 ≤ a) :
    0 ≤ Real.log ‖(a : ℂ) + (t : ℂ) * I‖ := by
  apply Real.log_nonneg
  have h := Complex.abs_re_le_norm ((a : ℂ) + (t : ℂ) * I)
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, add_zero] at h
  rw [abs_of_nonneg (by linarith : 0 ≤ a)] at h
  exact ha.trans h

private theorem log_sixPositiveGammaKernel_le_phase (n : ℕ) (hn : 1 ≤ n)
    (s : ℝ) (hs : 0 ≤ s) :
    Real.log ‖sixPositiveGammaKernel n (sixContourPoint n (50 * (n : ℝ) * s))‖ ≤
      50 * (n : ℝ) * (sixPhase s - sixPhaseConstant - 3 * Real.pi * s) -
        174 * (n : ℝ) * Real.log (n : ℝ) - 174 * (n : ℝ) * Real.log 50 + 174 * (n : ℝ) +
        5 * Real.log (2 * Real.pi) - 14 * Real.log (n : ℝ) +
        5 * (Real.log 139 + Real.log (1 + s)) + 48 * sixGammaError n := by
  have h := log_sixPositiveGammaKernel_le_inventory n hn s
  rw [sixGammaInventoryMain_eq_phase] at h
  have ht : Real.log ‖(139 : ℂ) + ((50 * s : ℝ) : ℂ) * I‖ ≤ Real.log 139 + Real.log (1 + s) := by
    have hne : (139 : ℂ) + ((50 * s : ℝ) : ℂ) * I ≠ 0 := by
      intro he; have hr := congrArg Complex.re he; norm_num at hr
    have hle : ‖(139 : ℂ) + ((50 * s : ℝ) : ℂ) * I‖ ≤ 139 * (1 + s) := by
      calc _ ≤ ‖(139 : ℂ)‖ + ‖((50 * s : ℝ) : ℂ) * I‖ := norm_add_le _ _
        _ = 139 + 50 * s := by simp [abs_of_nonneg hs]
        _ ≤ 139 * (1 + s) := by linarith
    have hb := Real.log_le_log (norm_pos_iff.mpr hne) hle
    rwa [Real.log_mul (by norm_num : (139 : ℝ) ≠ 0) (by positivity : 1 + s ≠ 0)] at hb
  have hdA : 0 ≤ ∑ a : Fin 5, Real.log ‖((139 - sixZero a : ℕ) : ℂ) + ((50 * s : ℝ) : ℂ) * I‖ := by
    apply sum_nonneg; intro a _
    have hge : 1 ≤ 139 - sixZero a := by fin_cases a <;> decide
    simpa only [ofReal_natCast] using log_norm_real_add_imag_nonneg ((139 - sixZero a : ℕ) : ℝ) (50 * s)
      (by exact_mod_cast hge)
  have hdB : 0 ≤ ∑ b : Fin 14, Real.log ‖((94 - sixOffset b : ℕ) : ℂ) + ((50 * s : ℝ) : ℂ) * I‖ := by
    apply sum_nonneg; intro b _
    have hge : 1 ≤ 94 - sixOffset b := by fin_cases b <;> decide
    simpa only [ofReal_natCast] using log_norm_real_add_imag_nonneg ((94 - sixOffset b : ℕ) : ℝ) (50 * s)
      (by exact_mod_cast hge)
  linarith

private theorem six_trig_numerator_norm_le (n : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    ‖Complex.cos ((Real.pi : ℂ) * sixContourPoint n y) ^ 3 +
      2 * Complex.cos ((Real.pi : ℂ) * sixContourPoint n y)‖ ≤
        3 * Real.exp (3 * Real.pi * y) := by
  let z := (Real.pi : ℂ) * sixContourPoint n y
  have him : z.im = Real.pi * y := by simp [z, sixContourPoint]
  have hcos : ‖Complex.cos z‖ ≤ Real.exp (Real.pi * y) := by
    rw [Complex.cos, norm_div]; norm_num only [Complex.norm_ofNat]
    have h := norm_add_le (Complex.exp (z * I)) (Complex.exp (-z * I))
    simp only [Complex.norm_exp, mul_re, I_re, I_im, mul_zero, mul_one,
      zero_sub, neg_im, neg_neg, him] at h
    have h2 : Real.exp (-(Real.pi * y)) ≤ Real.exp (Real.pi * y) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    linarith
  have he : 1 ≤ Real.exp (Real.pi * y) := Real.one_le_exp (by positivity)
  have hp : Real.exp (3 * Real.pi * y) = Real.exp (Real.pi * y) ^ 3 := by
    rw [show 3 * Real.pi * y = Real.pi * y + Real.pi * y + Real.pi * y by ring,
      Real.exp_add, Real.exp_add]; ring
  rw [hp]
  calc _ ≤ ‖Complex.cos z‖ ^ 3 + 2 * ‖Complex.cos z‖ := by
        have htri := norm_add_le ((Complex.cos z) ^ 3) (2 * Complex.cos z)
        rw [Complex.norm_pow, norm_mul] at htri; norm_num only [Complex.norm_ofNat] at htri
        exact htri
    _ ≤ Real.exp (Real.pi * y) ^ 3 + 2 * Real.exp (Real.pi * y) := by gcongr
    _ ≤ _ := by nlinarith [pow_le_pow_right₀ he (show 1 ≤ 3 by omega)]

private theorem six_center_norm_le (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 ≤ s) :
    ‖sixContourPoint n (50 * (n : ℝ) * s) + 70 * (n : ℂ) + 1‖ ≤
      70 * (n : ℝ) * (1 + s) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : sixContourPoint n (50 * (n : ℝ) * s) + 70 * (n : ℂ) + 1 =
      ((69 * (n : ℝ) + 1 / 2 : ℝ) : ℂ) + ((50 * (n : ℝ) * s : ℝ) : ℂ) * I := by
    unfold sixContourPoint sixContourAbscissa; push_cast; ring
  rw [he]
  calc _ ≤ ‖((69 * (n : ℝ) + 1 / 2 : ℝ) : ℂ)‖ + ‖((50 * (n : ℝ) * s : ℝ) : ℂ) * I‖ :=
        norm_add_le _ _
    _ = 69 * (n : ℝ) + 1 / 2 + 50 * (n : ℝ) * s := by
        simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
          abs_of_nonneg (by positivity : 0 ≤ 69 * (n : ℝ) + 1 / 2),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 50),
          abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), abs_of_nonneg hs]
    _ ≤ _ := by nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity) hs]

def sixDensityLogConstant : ℝ :=
  sixNormalizationLogConstant + 158 + 5 * Real.log (2 * Real.pi) + 53 * Real.log 139

def sixDensityConstant : ℝ := 70 * Real.exp sixDensityLogConstant

theorem sixDensityConstant_pos : 0 < sixDensityConstant := by
  unfold sixDensityConstant; positivity

theorem sixModulusWeight_uniform_envelope (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 ≤ s) :
    sixModulusWeight n (50 * (n : ℝ) * s) ≤
      sixDensityConstant * (n : ℝ) ^ 37 * (1 + s) ^ 6 *
        Real.exp (50 * (n : ℝ) * sixPhase s) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN := sixNormalization_real_pos n
  have hlog_env : Real.log (sixNormalization n : ℝ) +
      Real.log ‖sixPositiveGammaKernel n (sixContourPoint n (50 * (n : ℝ) * s))‖ +
      3 * Real.pi * (50 * (n : ℝ) * s) ≤
      sixDensityLogConstant + 36 * Real.log (n : ℝ) + 5 * Real.log (1 + s) +
        50 * (n : ℝ) * sixPhase s := by
    have h1 := sixNormalization_log_upper n hn
    have h2 := log_sixPositiveGammaKernel_le_phase n hn s hs
    dsimp [sixGammaError, sixDensityLogConstant] at *
    linarith
  have hG : (sixNormalization n : ℝ) *
      ‖sixPositiveGammaKernel n (sixContourPoint n (50 * (n : ℝ) * s))‖ *
      Real.exp (3 * Real.pi * (50 * (n : ℝ) * s)) ≤
      Real.exp sixDensityLogConstant * (n : ℝ) ^ 36 * (1 + s) ^ 5 *
        Real.exp (50 * (n : ℝ) * sixPhase s) := by
    have h := Real.exp_le_exp.mpr hlog_env
    have hGp := norm_pos_iff.mpr (sixPositiveGammaKernel_contour_ne_zero n (50 * (n : ℝ) * s))
    have hsR : 0 < 1 + s := by positivity
    have hpow (a : ℝ) (ha : 0 < a) (k : ℕ) : Real.exp ((k : ℝ) * Real.log a) = a ^ k := by
      rw [← Real.log_pow, Real.exp_log (pow_pos ha k)]
    have hp36 : Real.exp (36 * Real.log (n : ℝ)) = (n : ℝ) ^ 36 := hpow (n : ℝ) hnR 36
    have hp5 : Real.exp (5 * Real.log (1 + s)) = (1 + s) ^ 5 := hpow (1 + s) hsR 5
    simpa only [Real.exp_add, Real.exp_log hN, Real.exp_log hGp, hp36, hp5] using h
  have hcenter := six_center_norm_le n hn s hs
  have htrig := six_trig_numerator_norm_le n (50 * (n : ℝ) * s) (by positivity)
  rw [sixModulusWeight_gamma, abs_of_pos hN]
  have hmult : (sixNormalization n : ℝ) *
      ‖sixContourPoint n (50 * (n : ℝ) * s) + 70 * (n : ℂ) + 1‖ *
      ‖sixPositiveGammaKernel n (sixContourPoint n (50 * (n : ℝ) * s))‖ *
      ‖Complex.cos ((Real.pi : ℂ) * sixContourPoint n (50 * (n : ℝ) * s)) ^ 3 +
        2 * Complex.cos ((Real.pi : ℂ) * sixContourPoint n (50 * (n : ℝ) * s))‖ ≤
      3 * (70 * (n : ℝ) * (1 + s)) *
        ((sixNormalization n : ℝ) *
          ‖sixPositiveGammaKernel n (sixContourPoint n (50 * (n : ℝ) * s))‖ *
          Real.exp (3 * Real.pi * (50 * (n : ℝ) * s))) := by
    calc _ ≤ (sixNormalization n : ℝ) * (70 * (n : ℝ) * (1 + s)) *
          ‖sixPositiveGammaKernel n (sixContourPoint n (50 * (n : ℝ) * s))‖ *
          (3 * Real.exp (3 * Real.pi * (50 * (n : ℝ) * s))) := by gcongr
      _ = _ := by ring
  calc _ ≤ (3 * (70 * (n : ℝ) * (1 + s)) *
        ((sixNormalization n : ℝ) *
          ‖sixPositiveGammaKernel n (sixContourPoint n (50 * (n : ℝ) * s))‖ *
          Real.exp (3 * Real.pi * (50 * (n : ℝ) * s)))) / (6 * Real.pi) :=
        div_le_div_of_nonneg_right hmult (by positivity)
    _ ≤ (70 * (n : ℝ) * (1 + s)) *
        ((sixNormalization n : ℝ) *
          ‖sixPositiveGammaKernel n (sixContourPoint n (50 * (n : ℝ) * s))‖ *
          Real.exp (3 * Real.pi * (50 * (n : ℝ) * s))) := by
        apply (div_le_iff₀ (by positivity : 0 < 6 * Real.pi)).mpr
        have hx : 0 ≤ 70 * (n : ℝ) * (1 + s) *
            ((sixNormalization n : ℝ) *
              ‖sixPositiveGammaKernel n (sixContourPoint n (50 * (n : ℝ) * s))‖ *
              Real.exp (3 * Real.pi * (50 * (n : ℝ) * s))) := by positivity
        nlinarith [Real.pi_gt_three]
    _ ≤ (70 * (n : ℝ) * (1 + s)) *
        (Real.exp sixDensityLogConstant * (n : ℝ) ^ 36 * (1 + s) ^ 5 *
          Real.exp (50 * (n : ℝ) * sixPhase s)) :=
        mul_le_mul_of_nonneg_left hG (by positivity)
    _ = _ := by unfold sixDensityConstant; ring

theorem sixModulusWeight_neg (n : ℕ) (y : ℝ) :
    sixModulusWeight n (-y) = sixModulusWeight n y := by
  have hpt : sixContourPoint n (-y) = starRingEnd ℂ (sixContourPoint n y) := by
    simp [sixContourPoint]
  have hgk : ‖sixPositiveGammaKernel n (sixContourPoint n (-y))‖ =
      ‖sixPositiveGammaKernel n (sixContourPoint n y)‖ := by
    simp only [sixPositiveGammaKernel_contour, norm_mul, Complex.norm_pow,
      norm_prod, norm_div, sixGammaThreeHalves_norm_neg, sixGammaHalf_norm_neg]
  have hcenter : sixContourPoint n (-y) + 70 * (n : ℂ) + 1 =
      starRingEnd ℂ (sixContourPoint n y + 70 * (n : ℂ) + 1) := by
    norm_num [hpt, map_ofNat]
  have htrig : Complex.cos ((Real.pi : ℂ) * sixContourPoint n (-y)) ^ 3 +
      2 * Complex.cos ((Real.pi : ℂ) * sixContourPoint n (-y)) =
      starRingEnd ℂ (Complex.cos ((Real.pi : ℂ) * sixContourPoint n y) ^ 3 +
        2 * Complex.cos ((Real.pi : ℂ) * sixContourPoint n y)) := by
    norm_num [hpt, ← Complex.cos_conj, map_ofNat]
  simp only [sixModulusWeight_gamma, hgk, hcenter, htrig, Complex.norm_conj]

theorem sixModulusWeight_abs (n : ℕ) (y : ℝ) :
    sixModulusWeight n |y| = sixModulusWeight n y := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]
  · rw [abs_of_nonpos hy, sixModulusWeight_neg]

theorem sixModulusWeight_uniform_envelope_abs (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    sixModulusWeight n (50 * (n : ℝ) * s) ≤
      sixDensityConstant * (n : ℝ) ^ 37 * (1 + |s|) ^ 6 *
        Real.exp (50 * (n : ℝ) * sixPhase |s|) := by
  have h := sixModulusWeight_uniform_envelope n hn |s| (abs_nonneg s)
  have he : 50 * (n : ℝ) * |s| = |50 * (n : ℝ) * s| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 50 * (n : ℝ))]
  rwa [he, sixModulusWeight_abs] at h

/-! ## Section 3: Two-root adaptive monic polynomials, drift, and contour density -/

/-- Exact rational contour abscissa shift `δ_n = 69/50 + 1/(100 n)`. -/
def sixAdaptiveDelta (n : ℕ) : ℚ := 69 / 50 + 1 / (100 * (n : ℚ))

/-- Degree-2 monic pair polynomial `(X + a^2 - δ^2)^2 + 4 δ^2 a^2`. -/
def sixAdaptivePair (delta a : ℚ) : ℚ[X] :=
  (X + C (a ^ 2 - delta ^ 2)) ^ 2 + C (4 * delta ^ 2 * a ^ 2)

/-- Exact nonnegative squared modulus of `sixAdaptivePair` along `δ + i s`. -/
def sixAdaptivePairModulus (delta a s : ℝ) : ℝ :=
  (s ^ 2 - a ^ 2) ^ 2 * ((s + a) ^ 2 + 4 * delta ^ 2) * ((s - a) ^ 2 + 4 * delta ^ 2)

/-- Four-root block `(P_{a₀} * P_{a₁})^k` of degree `4 k`. -/
def sixAdaptiveBlock (k : ℕ) (delta : ℚ) (a : Fin 2 → ℚ) : ℚ[X] :=
  (∏ j : Fin 2, sixAdaptivePair delta (a j)) ^ k

/-- Degree-`i` monic adaptive polynomial `((P_{a₀} * P_{a₁})^(i / 4)) * X^(i % 4)`. -/
def sixAdaptiveMonic (i : ℕ) (delta : ℚ) (a : Fin 2 → ℚ) : ℚ[X] :=
  sixAdaptiveBlock (i / 4) delta a * X ^ (i % 4)

/-- Effective grouped degree fraction `t_i = 4 ⌊i/4⌋ / (50 n) ∈ [0, 3/10)`. -/
def sixRowTheta (n i : ℕ) : ℝ := (4 * (i / 4 : ℕ) : ℝ) / (50 * (n : ℝ))

/-- Two-root-pair logarithmic phase potential at fixed `δ = 69/50`. -/
def sixPhasePotential (a : Fin 2 → ℝ) (t y : ℝ) : ℝ :=
  sixPhase y + (t / 4) * ∑ j : Fin 2, Real.log (sixAdaptivePairModulus (69 / 50) (a j) y)

theorem sixAdaptivePair_monic (delta a : ℚ) : (sixAdaptivePair delta a).Monic := by
  apply ((monic_X_add_C (a ^ 2 - delta ^ 2)).pow 2).add_of_left
  apply lt_of_le_of_lt degree_C_le
  rw [degree_pow, degree_X_add_C]; norm_num

theorem sixAdaptivePair_natDegree (delta a : ℚ) : (sixAdaptivePair delta a).natDegree = 2 := by
  have h1 : ((X + C (a ^ 2 - delta ^ 2)) ^ 2).natDegree = 2 := by
    rw [(monic_X_add_C _).natDegree_pow, natDegree_X_add_C, mul_one]
  unfold sixAdaptivePair
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · exact h1
  · rw [natDegree_C, h1]; norm_num

theorem sixAdaptiveMonic_monic (i : ℕ) (delta : ℚ) (a : Fin 2 → ℚ) :
    (sixAdaptiveMonic i delta a).Monic :=
  ((monic_prod_of_monic _ _ fun j _ => sixAdaptivePair_monic delta (a j)).pow (i / 4)).mul
    (monic_X.pow (i % 4))

theorem sixAdaptiveMonic_natDegree (i : ℕ) (delta : ℚ) (a : Fin 2 → ℚ) :
    (sixAdaptiveMonic i delta a).natDegree = i := by
  have hp : (∏ j : Fin 2, sixAdaptivePair delta (a j)).Monic :=
    monic_prod_of_monic _ _ fun j _ => sixAdaptivePair_monic delta (a j)
  have hd : (∏ j : Fin 2, sixAdaptivePair delta (a j)).natDegree = 4 := by
    rw [natDegree_prod_of_monic _ _ fun j _ => sixAdaptivePair_monic delta (a j)]
    simp [sixAdaptivePair_natDegree]
  unfold sixAdaptiveMonic sixAdaptiveBlock
  rw [(hp.pow (i / 4)).natDegree_mul (monic_X.pow (i % 4)),
    hp.natDegree_pow, hd, natDegree_X_pow]
  omega

theorem sixAdaptivePairModulus_nonneg (delta a s : ℝ) :
    0 ≤ sixAdaptivePairModulus delta a s := by
  unfold sixAdaptivePairModulus; positivity

theorem sixAdaptivePairModulus_neg (delta a s : ℝ) :
    sixAdaptivePairModulus delta a (-s) = sixAdaptivePairModulus delta a s := by
  unfold sixAdaptivePairModulus; ring

theorem sixAdaptivePairModulus_abs (delta a s : ℝ) :
    sixAdaptivePairModulus delta a |s| = sixAdaptivePairModulus delta a s := by
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]
  · rw [abs_of_nonpos hs, sixAdaptivePairModulus_neg]

private theorem sixAdaptivePair_eval_factorization (delta a : ℚ) (s : ℝ) :
    aeval (((delta : ℂ) + Complex.I * (s : ℂ)) ^ 2) (sixAdaptivePair delta a) =
      (((a : ℝ) ^ 2 - s ^ 2 : ℝ) : ℂ) *
        (2 * (delta : ℂ) + Complex.I * ((s + (a : ℝ) : ℝ) : ℂ)) *
        (2 * (delta : ℂ) + Complex.I * ((s - (a : ℝ) : ℝ) : ℂ)) := by
  simp [sixAdaptivePair]
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring

private theorem sixAdaptivePair_normSq (delta a : ℚ) (s : ℝ) :
    Complex.normSq (aeval (((delta : ℂ) + Complex.I * (s : ℂ)) ^ 2) (sixAdaptivePair delta a)) =
      sixAdaptivePairModulus (delta : ℝ) (a : ℝ) s := by
  rw [sixAdaptivePair_eval_factorization, map_mul, map_mul]
  simp [Complex.normSq_apply, pow_two, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.ratCast_re, Complex.ratCast_im]
  unfold sixAdaptivePairModulus; ring

private theorem sixAdaptivePairModulus_drift (delta b a s : ℝ)
    (hb : 0 < b) (hdelta : b ≤ delta) :
    sixAdaptivePairModulus delta a s ≤ (delta / b) ^ 4 * sixAdaptivePairModulus b a s := by
  have hr : 1 ≤ delta / b := (le_div_iff₀ hb).mpr (by simpa using hdelta)
  have hr2 : 1 ≤ (delta / b) ^ 2 := one_le_pow₀ hr
  have he : (delta / b) ^ 2 * b ^ 2 = delta ^ 2 := by field_simp
  have hfactor (x : ℝ) : x ^ 2 + 4 * delta ^ 2 ≤ (delta / b) ^ 2 * (x ^ 2 + 4 * b ^ 2) := by
    have hx : x ^ 2 ≤ (delta / b) ^ 2 * x ^ 2 := le_mul_of_one_le_left (sq_nonneg x) hr2
    calc x ^ 2 + 4 * delta ^ 2 ≤ (delta / b) ^ 2 * x ^ 2 + 4 * delta ^ 2 := by linarith
      _ = (delta / b) ^ 2 * (x ^ 2 + 4 * b ^ 2) := by linear_combination -4 * he
  have hm := mul_le_mul (hfactor (s + a)) (hfactor (s - a)) (by positivity) (by positivity)
  calc sixAdaptivePairModulus delta a s
      = (s ^ 2 - a ^ 2) ^ 2 * (((s + a) ^ 2 + 4 * delta ^ 2) * ((s - a) ^ 2 + 4 * delta ^ 2)) := by
        unfold sixAdaptivePairModulus; ring
    _ ≤ (s ^ 2 - a ^ 2) ^ 2 *
        (((delta / b) ^ 2 * ((s + a) ^ 2 + 4 * b ^ 2)) *
          ((delta / b) ^ 2 * ((s - a) ^ 2 + 4 * b ^ 2))) :=
        mul_le_mul_of_nonneg_left hm (sq_nonneg _)
    _ = (delta / b) ^ 4 * sixAdaptivePairModulus b a s := by
        unfold sixAdaptivePairModulus; ring

private theorem sixAdaptiveContourCoordinate (n : ℕ) (hn : 0 < n) (y : ℝ) :
    (sixContourPoint n y + (70 * (n : ℂ) + 1)) / (50 * (n : ℂ)) =
      (sixAdaptiveDelta n : ℂ) + Complex.I * ((y / (50 * (n : ℝ)) : ℝ) : ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp only [sixContourPoint, sixContourAbscissa, sixAdaptiveDelta]
  push_cast; field_simp; ring

private theorem sixAdaptiveContourValue (n : ℕ) (hn : 0 < n) (Q : ℚ[X]) (y : ℝ) :
    sixBasisContourValue n (Q.comp (C ((50 * (n : ℚ))⁻¹ ^ 2) * X ^ 2)) y =
      aeval (((sixAdaptiveDelta n : ℂ) + Complex.I * ((y / (50 * (n : ℝ)) : ℝ) : ℂ)) ^ 2) Q := by
  simp only [sixBasisContourValue, aeval_comp, map_mul, map_pow, aeval_C, aeval_X, map_add]
  apply congrArg (fun z : ℂ => aeval z Q)
  rw [← sixAdaptiveContourCoordinate n hn y]
  simp; ring

def sixAdaptiveDensity (n i : ℕ) (a : Fin 2 → ℚ) (y : ℝ) : ℝ :=
  sixModulusWeight n y *
    ‖sixBasisContourValue n
      ((sixAdaptiveMonic i (sixAdaptiveDelta n) a).comp (C ((50 * (n : ℚ))⁻¹ ^ 2) * X ^ 2)) y‖ ^ 2

def sixAdaptiveDensityConstant : ℝ :=
  sixDensityConstant * Real.exp (5 / 23) * (2 : ℝ) ^ 12

theorem sixAdaptiveDensityConstant_pos : 0 < sixAdaptiveDensityConstant := by
  unfold sixAdaptiveDensityConstant
  exact mul_pos (mul_pos sixDensityConstant_pos (Real.exp_pos _)) (by positivity)

theorem sixAdaptiveDensity_nonneg (n i : ℕ) (a : Fin 2 → ℚ) (y : ℝ) :
    0 ≤ sixAdaptiveDensity n i a y :=
  mul_nonneg (sixModulusWeight_nonneg _ _) (sq_nonneg _)

theorem sixAdaptiveDensity_continuous (n i : ℕ) (a : Fin 2 → ℚ) :
    Continuous (sixAdaptiveDensity n i a) := by
  unfold sixAdaptiveDensity sixModulusWeight sixBasisContourValue
  have h1 : Continuous (fun y : ℝ => ‖sixVerticalIntegrand n 0 0 y‖ / (2 * Real.pi)) :=
    (sixVerticalIntegrand_continuous n 0 0).norm.div_const _
  have h2 : Continuous (fun y : ℝ => aeval (sixContourPoint n y)
      (((sixAdaptiveMonic i (sixAdaptiveDelta n) a).comp (C ((50 * (n : ℚ))⁻¹ ^ 2) * X ^ 2)).comp
        (X + C (70 * (n : ℚ) + 1)))) := by
    have hp : Continuous (fun z : ℂ => aeval z
        (((sixAdaptiveMonic i (sixAdaptiveDelta n) a).comp (C ((50 * (n : ℚ))⁻¹ ^ 2) * X ^ 2)).comp
          (X + C (70 * (n : ℚ) + 1)))) := by
      simp_rw [aeval_def, eval₂_eq_sum_range]
      exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_id.pow k)
    exact hp.comp (by unfold sixContourPoint; fun_prop)
  exact h1.mul (h2.norm.pow 2)

theorem sixAdaptiveDensity_uniform (n i : ℕ) (hn : 1 ≤ n) (hi : i < 15 * n)
    (a : Fin 2 → ℚ) (s : ℝ) :
    sixAdaptiveDensity n i a (50 * (n : ℝ) * s) ≤
      sixAdaptiveDensityConstant * (n : ℝ) ^ 37 * (1 + |s|) ^ 18 *
        Real.exp (50 * (n : ℝ) * sixPhasePotential (fun j => (a j : ℝ)) (sixRowTheta n i) |s|) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h50n : (50 * (n : ℝ)) ≠ 0 := by positivity
  have hcoord : (50 * (n : ℝ) * s) / (50 * (n : ℝ)) = s := mul_div_cancel_left₀ s h50n
  have hQeq : ‖sixBasisContourValue n
      ((sixAdaptiveMonic i (sixAdaptiveDelta n) a).comp (C ((50 * (n : ℚ))⁻¹ ^ 2) * X ^ 2))
        (50 * (n : ℝ) * s)‖ ^ 2 =
      (∏ j : Fin 2, sixAdaptivePairModulus (sixAdaptiveDelta n : ℝ) (a j : ℝ) s) ^ (i / 4) *
        ((sixAdaptiveDelta n : ℝ) ^ 2 + s ^ 2) ^ (2 * (i % 4)) := by
    rw [sixAdaptiveContourValue n (by omega), hcoord, Complex.sq_norm]
    unfold sixAdaptiveMonic sixAdaptiveBlock
    have hpt : Complex.normSq ((sixAdaptiveDelta n : ℂ) + Complex.I * (s : ℂ)) =
        (sixAdaptiveDelta n : ℝ) ^ 2 + s ^ 2 := by
      simp [Complex.normSq_apply, pow_two]
    simp only [map_mul, map_pow, map_prod, aeval_X, hpt, ← pow_mul, sixAdaptivePair_normSq]
  have hd_ge : (69 / 50 : ℝ) ≤ (sixAdaptiveDelta n : ℝ) := by
    unfold sixAdaptiveDelta; push_cast; linarith [show (0 : ℝ) ≤ 1 / (100 * (n : ℝ)) by positivity]
  have hd_le2 : (sixAdaptiveDelta n : ℝ) ≤ 2 := by
    unfold sixAdaptiveDelta; push_cast
    have h1 : 1 / (100 * (n : ℝ)) ≤ 1 / 100 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    linarith
  have hd_ratio : (sixAdaptiveDelta n : ℝ) / (69 / 50) = 1 + 1 / (138 * (n : ℝ)) := by
    unfold sixAdaptiveDelta; push_cast; field_simp; ring
  have hprod_drift :
      (∏ j : Fin 2, sixAdaptivePairModulus (sixAdaptiveDelta n : ℝ) (a j : ℝ) s) ≤
        (1 + 1 / (138 * (n : ℝ))) ^ 8 *
          ∏ j : Fin 2, sixAdaptivePairModulus (69 / 50) (a j : ℝ) s := by
    calc _ ≤ ∏ j : Fin 2, (((sixAdaptiveDelta n : ℝ) / (69 / 50)) ^ 4 *
              sixAdaptivePairModulus (69 / 50) (a j : ℝ) s) :=
          Finset.prod_le_prod₀ (fun j _ => sixAdaptivePairModulus_nonneg _ _ _)
            (fun j _ => sixAdaptivePairModulus_drift _ (69 / 50) _ s (by norm_num) hd_ge)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, ← pow_mul, hd_ratio]
  have hpow_drift : (1 + 1 / (138 * (n : ℝ))) ^ (8 * (i / 4)) ≤ Real.exp (5 / 23) := by
    have hbase : 1 + 1 / (138 * (n : ℝ)) ≤ Real.exp (1 / (138 * (n : ℝ))) := by
      simpa [add_comm] using Real.add_one_le_exp (1 / (138 * (n : ℝ)))
    have h1 := pow_le_pow_left₀ (by positivity) hbase (8 * (i / 4))
    rw [← Real.exp_nat_mul] at h1
    apply h1.trans (Real.exp_le_exp.mpr _)
    have hk : ((8 * (i / 4) : ℕ) : ℝ) ≤ 30 * (n : ℝ) := by
      exact_mod_cast (show 8 * (i / 4) ≤ 30 * n by omega)
    rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 138 * (n : ℝ))]
    linarith
  have hblock_exp :
      (∏ j : Fin 2, sixAdaptivePairModulus (69 / 50) (a j : ℝ) s) ^ (i / 4) ≤
        Real.exp (((i / 4 : ℕ) : ℝ) *
          ∑ j : Fin 2, Real.log (sixAdaptivePairModulus (69 / 50) (a j : ℝ) |s|)) := by
    have hsingle (j : Fin 2) : sixAdaptivePairModulus (69 / 50) (a j : ℝ) s ≤
        Real.exp (Real.log (sixAdaptivePairModulus (69 / 50) (a j : ℝ) |s|)) := by
      rw [sixAdaptivePairModulus_abs]
      by_cases hz : sixAdaptivePairModulus (69 / 50) (a j : ℝ) s = 0
      · rw [hz]; positivity
      · rw [Real.exp_log (lt_of_le_of_ne (sixAdaptivePairModulus_nonneg _ _ _) (Ne.symm hz))]
    have hp := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin 2)))
      (fun j _ => sixAdaptivePairModulus_nonneg _ _ _)
      (fun j _ => hsingle j)
    have hk := pow_le_pow_left₀
      (Finset.prod_nonneg fun j _ => sixAdaptivePairModulus_nonneg _ _ _) hp (i / 4)
    simpa only [← Real.exp_sum, ← Real.exp_nat_mul] using hk
  have hres : ((sixAdaptiveDelta n : ℝ) ^ 2 + s ^ 2) ^ (2 * (i % 4)) ≤
      (2 : ℝ) ^ 12 * (1 + |s|) ^ 12 := by
    have hd0 : (0 : ℝ) ≤ (sixAdaptiveDelta n : ℝ) := by linarith
    have hb : (sixAdaptiveDelta n : ℝ) ^ 2 + s ^ 2 ≤ (2 * (1 + |s|)) ^ 2 := by
      nlinarith [sq_abs s, abs_nonneg s, sq_nonneg s]
    have hbase : (1 : ℝ) ≤ 2 * (1 + |s|) := by linarith [abs_nonneg s]
    calc _ ≤ ((2 * (1 + |s|)) ^ 2) ^ (2 * (i % 4)) := pow_le_pow_left₀ (by positivity) hb _
      _ = (2 * (1 + |s|)) ^ (4 * (i % 4)) := by rw [← pow_mul]; congr 1; omega
      _ ≤ (2 * (1 + |s|)) ^ 12 := pow_le_pow_right₀ hbase (by omega)
      _ = _ := by rw [mul_pow]
  have hQ_bound : ‖sixBasisContourValue n
      ((sixAdaptiveMonic i (sixAdaptiveDelta n) a).comp (C ((50 * (n : ℚ))⁻¹ ^ 2) * X ^ 2))
        (50 * (n : ℝ) * s)‖ ^ 2 ≤
      Real.exp (5 / 23) *
        Real.exp (((i / 4 : ℕ) : ℝ) *
          ∑ j : Fin 2, Real.log (sixAdaptivePairModulus (69 / 50) (a j : ℝ) |s|)) *
        ((2 : ℝ) ^ 12 * (1 + |s|) ^ 12) := by
    rw [hQeq]
    have hblock_tot :
        (∏ j : Fin 2, sixAdaptivePairModulus (sixAdaptiveDelta n : ℝ) (a j : ℝ) s) ^ (i / 4) ≤
          Real.exp (5 / 23) *
            Real.exp (((i / 4 : ℕ) : ℝ) *
              ∑ j : Fin 2, Real.log (sixAdaptivePairModulus (69 / 50) (a j : ℝ) |s|)) := by
      calc _ ≤ ((1 + 1 / (138 * (n : ℝ))) ^ 8 *
                ∏ j : Fin 2, sixAdaptivePairModulus (69 / 50) (a j : ℝ) s) ^ (i / 4) :=
            pow_le_pow_left₀ (Finset.prod_nonneg fun j _ => sixAdaptivePairModulus_nonneg _ _ _)
              hprod_drift _
        _ = (1 + 1 / (138 * (n : ℝ))) ^ (8 * (i / 4)) *
              (∏ j : Fin 2, sixAdaptivePairModulus (69 / 50) (a j : ℝ) s) ^ (i / 4) := by
            rw [mul_pow, ← pow_mul]
        _ ≤ _ := mul_le_mul hpow_drift hblock_exp
              (pow_nonneg (Finset.prod_nonneg fun j _ => sixAdaptivePairModulus_nonneg _ _ _) _)
              (Real.exp_pos _).le
    exact mul_le_mul hblock_tot hres (by positivity) (by positivity)
  have hW := sixModulusWeight_uniform_envelope_abs n hn s
  have hC0 := sixDensityConstant_pos.le
  unfold sixAdaptiveDensity
  have h := mul_le_mul hW hQ_bound (sq_nonneg _) (by positivity)
  apply h.trans_eq
  have he : 50 * (n : ℝ) * sixPhasePotential (fun j => (a j : ℝ)) (sixRowTheta n i) |s| =
      50 * (n : ℝ) * sixPhase |s| +
        ((i / 4 : ℕ) : ℝ) *
          ∑ j : Fin 2, Real.log (sixAdaptivePairModulus (69 / 50) (a j : ℝ) |s|) := by
    unfold sixPhasePotential sixRowTheta; push_cast; field_simp
  rw [he, Real.exp_add]
  unfold sixAdaptiveDensityConstant
  ring

/-! ## Section 4: Tail derivative bound on `y ≥ 2` and integrable moment envelope -/

def sixPhaseDerivative (y : ℝ) : ℝ :=
  3 * Real.pi - 5 * Real.arctan (50 * y / 139) - 5 * Real.arctan (50 * y) +
    (∑ a : Fin 5, (Real.arctan (50 * y / ((139 - sixZero a : ℕ) : ℝ)) -
      Real.arctan (50 * y / ((sixZero a - 1 : ℕ) : ℝ)))) +
    (∑ b : Fin 14, (Real.arctan (50 * y / ((94 - sixOffset b : ℕ) : ℝ)) -
      Real.arctan (50 * y / ((44 + sixOffset b : ℕ) : ℝ))))

def sixPairSlope (a y : ℝ) : ℝ :=
  2 * y / (y ^ 2 - a ^ 2) +
    (y + a) / ((y + a) ^ 2 + 4 * (69 / 50 : ℝ) ^ 2) +
    (y - a) / ((y - a) ^ 2 + 4 * (69 / 50 : ℝ) ^ 2)

def sixPhasePotentialDerivative (a : Fin 2 → ℝ) (t y : ℝ) : ℝ :=
  sixPhaseDerivative y + (t / 2) * ∑ j : Fin 2, sixPairSlope (a j) y

private theorem sixPhaseX_hasDerivAt {d : ℝ} (hd : 0 < d) (y : ℝ) :
    HasDerivAt (sixPhaseX d) (-Real.arctan (y / d)) y := by
  have hz : d ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hlog := (((hasDerivAt_const y (d ^ 2)).add
    ((hasDerivAt_id y).pow 2)).log hz).const_mul (d / 2)
  have hatan := ((hasDerivAt_id y).div_const d).arctan
  unfold sixPhaseX
  convert hlog.sub ((hasDerivAt_id y).mul hatan) using 1 <;> try rfl
  dsimp; field_simp; ring

theorem sixPhase_hasDerivAt (y : ℝ) :
    HasDerivAt sixPhase (sixPhaseDerivative y) y := by
  have hdiv (m : ℕ) (hm : 0 < m) : y / ((m : ℝ) / 50) = 50 * y / (m : ℝ) := by field_simp
  have hsumA : HasDerivAt
      (fun u => ∑ a : Fin 5, (sixPhaseX (((sixZero a - 1 : ℕ) : ℝ) / 50) u -
        sixPhaseX (((139 - sixZero a : ℕ) : ℝ) / 50) u))
      (∑ a : Fin 5, (-Real.arctan (y / (((sixZero a - 1 : ℕ) : ℝ) / 50)) -
        -Real.arctan (y / (((139 - sixZero a : ℕ) : ℝ) / 50)))) y := by
    apply HasDerivAt.fun_sum; intro a _
    have h1 : 0 < sixZero a - 1 := by fin_cases a <;> decide
    have h2 : 0 < 139 - sixZero a := by fin_cases a <;> decide
    exact (sixPhaseX_hasDerivAt (by positivity) y).sub (sixPhaseX_hasDerivAt (by positivity) y)
  have hsumB : HasDerivAt
      (fun u => ∑ b : Fin 14, (sixPhaseX (((44 + sixOffset b : ℕ) : ℝ) / 50) u -
        sixPhaseX (((94 - sixOffset b : ℕ) : ℝ) / 50) u))
      (∑ b : Fin 14, (-Real.arctan (y / (((44 + sixOffset b : ℕ) : ℝ) / 50)) -
        -Real.arctan (y / (((94 - sixOffset b : ℕ) : ℝ) / 50)))) y := by
    apply HasDerivAt.fun_sum; intro b _
    have h1 : 0 < 44 + sixOffset b := by fin_cases b <;> decide
    have h2 : 0 < 94 - sixOffset b := by fin_cases b <;> decide
    exact (sixPhaseX_hasDerivAt (by positivity) y).sub (sixPhaseX_hasDerivAt (by positivity) y)
  have h := ((((((hasDerivAt_const y sixPhaseConstant).add
    ((sixPhaseX_hasDerivAt (by norm_num : (0 : ℝ) < 139 / 50) y).const_mul 5)).add
    ((sixPhaseX_hasDerivAt (by norm_num : (0 : ℝ) < 1 / 50) y).const_mul 5)).add hsumA).add hsumB).add
    ((hasDerivAt_id y).const_mul (3 * Real.pi)))
  refine h.congr_deriv ?_
  unfold sixPhaseDerivative
  have h139 : y / (139 / 50 : ℝ) = 50 * y / 139 := by ring
  have h1 : y / (1 / 50 : ℝ) = 50 * y := by ring
  rw [h139, h1]
  have hAeq : (∑ a : Fin 5, (-Real.arctan (y / (((sixZero a - 1 : ℕ) : ℝ) / 50)) -
      -Real.arctan (y / (((139 - sixZero a : ℕ) : ℝ) / 50)))) =
      ∑ a : Fin 5, (Real.arctan (50 * y / ((139 - sixZero a : ℕ) : ℝ)) -
        Real.arctan (50 * y / ((sixZero a - 1 : ℕ) : ℝ))) := by
    apply Finset.sum_congr rfl; intro a _
    have h1' : 0 < sixZero a - 1 := by fin_cases a <;> decide
    have h2' : 0 < 139 - sixZero a := by fin_cases a <;> decide
    rw [hdiv _ h1', hdiv _ h2']; ring
  have hBeq : (∑ b : Fin 14, (-Real.arctan (y / (((44 + sixOffset b : ℕ) : ℝ) / 50)) -
      -Real.arctan (y / (((94 - sixOffset b : ℕ) : ℝ) / 50)))) =
      ∑ b : Fin 14, (Real.arctan (50 * y / ((94 - sixOffset b : ℕ) : ℝ)) -
        Real.arctan (50 * y / ((44 + sixOffset b : ℕ) : ℝ))) := by
    apply Finset.sum_congr rfl; intro b _
    have h1' : 0 < 44 + sixOffset b := by fin_cases b <;> decide
    have h2' : 0 < 94 - sixOffset b := by fin_cases b <;> decide
    rw [hdiv _ h1', hdiv _ h2']; ring
  rw [hAeq, hBeq]; ring

private theorem arctan_le_self_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h := image_sub_le_mul_sub_of_deriv_le Real.differentiable_arctan
    (C := 1) (fun y => by
      rw [Real.deriv_arctan]
      exact (div_le_one (by positivity : 0 < 1 + y ^ 2)).2 (by nlinarith [sq_nonneg y])) hx
  simpa using h

theorem sixPhaseDerivative_tail_le {y : ℝ} (hy : 2 ≤ y) :
    sixPhaseDerivative y ≤ -(7 / 5 : ℝ) := by
  have hy0 : 0 ≤ y := by linarith
  have hsumA : (∑ a : Fin 5, (Real.arctan (50 * y / ((139 - sixZero a : ℕ) : ℝ)) -
      Real.arctan (50 * y / ((sixZero a - 1 : ℕ) : ℝ)))) ≤ 0 := by
    apply Finset.sum_nonpos; intro a _
    have hlt : sixZero a - 1 ≤ 139 - sixZero a ∧ 0 < sixZero a - 1 := by fin_cases a <;> decide
    exact sub_nonpos.mpr (Real.arctan_mono
      (div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hlt.2) (by exact_mod_cast hlt.1)))
  have hsumB : (∑ b : Fin 14, (Real.arctan (50 * y / ((94 - sixOffset b : ℕ) : ℝ)) -
      Real.arctan (50 * y / ((44 + sixOffset b : ℕ) : ℝ)))) ≤ 0 := by
    apply Finset.sum_nonpos; intro b _
    have hlt : 44 + sixOffset b ≤ 94 - sixOffset b ∧ 0 < 44 + sixOffset b := by fin_cases b <;> decide
    exact sub_nonpos.mpr (Real.arctan_mono
      (div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hlt.2) (by exact_mod_cast hlt.1)))
  have h139_at : Real.pi / 4 - 39 / 239 ≤ Real.arctan (100 / 139 : ℝ) := by
    have hadd := Real.arctan_add (x := (100 / 139 : ℝ)) (y := (39 / 239 : ℝ)) (by norm_num)
    norm_num [Real.arctan_one] at hadd
    have hsm := arctan_le_self_nonneg (x := (39 / 239 : ℝ)) (by norm_num)
    linarith
  have h100_at : Real.pi / 2 - 1 / 100 ≤ Real.arctan (100 : ℝ) := by
    have hinv := Real.arctan_inv_of_pos (x := (100 : ℝ)) (by norm_num)
    have hsm := arctan_le_self_nonneg (x := (100 : ℝ)⁻¹) (by positivity)
    norm_num at hinv hsm
    linarith
  have hm1 := Real.arctan_mono (show (100 / 139 : ℝ) ≤ 50 * y / 139 by linarith)
  have hm2 := Real.arctan_mono (show (100 : ℝ) ≤ 50 * y by linarith)
  have hpi := Real.pi_gt_d2
  unfold sixPhaseDerivative
  linarith

private theorem sixPair_tail_pos {a y : ℝ} (ha0 : 0 ≤ a) (ha3 : a ≤ 3 / 10) (hy : 2 ≤ y) :
    0 < y - a ∧ 0 < y + a ∧ 0 < y ^ 2 - a ^ 2 := by
  have hm : 0 < y - a := by linarith
  have hp : 0 < y + a := by linarith
  exact ⟨hm, hp, by nlinarith [mul_pos hm hp]⟩

private theorem sixPairModulus_tail_pos {a y : ℝ} (ha0 : 0 ≤ a) (ha3 : a ≤ 3 / 10) (hy : 2 ≤ y) :
    0 < sixAdaptivePairModulus (69 / 50) a y := by
  have hd := (sixPair_tail_pos ha0 ha3 hy).2.2
  unfold sixAdaptivePairModulus; positivity

private theorem sixPairSlope_tail_le {a y : ℝ} (ha0 : 0 ≤ a) (ha3 : a ≤ 3 / 10) (hy : 2 ≤ y) :
    sixPairSlope a y ≤ 40 / 19 := by
  obtain ⟨hm, hp, hd⟩ := sixPair_tail_pos ha0 ha3 hy
  have hfrac (x : ℝ) (hx : 0 < x) : x / (x ^ 2 + 4 * (69 / 50 : ℝ) ^ 2) ≤ 1 / x := by
    apply (div_le_div_iff₀ (by positivity) hx).2; nlinarith
  have heq : 2 * y / (y ^ 2 - a ^ 2) + 1 / (y + a) + 1 / (y - a) = 4 * y / (y ^ 2 - a ^ 2) := by
    field_simp; ring
  have ha2 : a ^ 2 ≤ 9 / 100 := by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha3)]
  have hquad : (19 / 10 : ℝ) * y ≤ y ^ 2 - a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy) (show 0 ≤ y + 1 / 10 by linarith)]
  calc sixPairSlope a y ≤ 2 * y / (y ^ 2 - a ^ 2) + 1 / (y + a) + 1 / (y - a) := by
        unfold sixPairSlope; linarith [hfrac (y + a) hp, hfrac (y - a) hm]
    _ = 4 * y / (y ^ 2 - a ^ 2) := heq
    _ ≤ 40 / 19 := (div_le_iff₀ hd).2 (by linarith)

private theorem sixPairLog_hasDerivAt {a y : ℝ} (ha0 : 0 ≤ a) (ha3 : a ≤ 3 / 10) (hy : 2 ≤ y) :
    HasDerivAt (fun u => Real.log (sixAdaptivePairModulus (69 / 50) a u))
      (2 * sixPairSlope a y) y := by
  have hd := (sixPair_tail_pos ha0 ha3 hy).2.2
  have hz := ne_of_gt (sixPairModulus_tail_pos ha0 ha3 hy)
  have hp : (y + a) ^ 2 + 4 * (69 / 50 : ℝ) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hm : (y - a) ^ 2 + 4 * (69 / 50 : ℝ) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hd1 : HasDerivAt (fun u : ℝ => (u ^ 2 - a ^ 2) ^ 2) (4 * y * (y ^ 2 - a ^ 2)) y := by
    have h := (((hasDerivAt_id y).pow 2).sub_const (a ^ 2)).pow 2
    exact h.congr_deriv (by simp only [Pi.pow_apply, id_eq]; ring)
  have hd2 : HasDerivAt (fun u : ℝ => (u + a) ^ 2 + 4 * (69 / 50 : ℝ) ^ 2) (2 * (y + a)) y := by
    have h := (((hasDerivAt_id y).add_const a).pow 2).add_const (4 * (69 / 50 : ℝ) ^ 2)
    exact h.congr_deriv (by simp only [id_eq]; ring)
  have hd3 : HasDerivAt (fun u : ℝ => (u - a) ^ 2 + 4 * (69 / 50 : ℝ) ^ 2) (2 * (y - a)) y := by
    have h := (((hasDerivAt_id y).sub_const a).pow 2).add_const (4 * (69 / 50 : ℝ) ^ 2)
    exact h.congr_deriv (by simp only [id_eq]; ring)
  have hprod := (hd1.mul hd2).mul hd3
  have hlog : HasDerivAt (fun u => Real.log (sixAdaptivePairModulus (69 / 50) a u))
      (((4 * y * (y ^ 2 - a ^ 2) * ((y + a) ^ 2 + 4 * (69 / 50 : ℝ) ^ 2) +
          (y ^ 2 - a ^ 2) ^ 2 * (2 * (y + a))) *
        ((y - a) ^ 2 + 4 * (69 / 50 : ℝ) ^ 2) +
          (y ^ 2 - a ^ 2) ^ 2 * ((y + a) ^ 2 + 4 * (69 / 50 : ℝ) ^ 2) * (2 * (y - a))) /
        sixAdaptivePairModulus (69 / 50) a y) y := hprod.log hz
  refine hlog.congr_deriv ?_
  unfold sixPairSlope sixAdaptivePairModulus
  field_simp [hd.ne', hp, hm]; ring

theorem sixPhasePotential_tail_line (a : Fin 2 → ℝ) (t : ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 3 / 10) (ht0 : 0 ≤ t) (ht3 : t ≤ 3 / 10)
    {y : ℝ} (hy : 2 ≤ y) :
    sixPhasePotential a t y ≤ sixPhasePotential a t 2 - (1 / 2) * (y - 2) := by
  have hderiv : ∀ x ∈ Ici (2 : ℝ), HasDerivAt (sixPhasePotential a t)
      (sixPhasePotentialDerivative a t x) x := by
    intro x hx
    have hsum : HasDerivAt
        (fun u => ∑ j : Fin 2, Real.log (sixAdaptivePairModulus (69 / 50) (a j) u))
        (∑ j : Fin 2, 2 * sixPairSlope (a j) x) x :=
      HasDerivAt.fun_sum fun j _ => sixPairLog_hasDerivAt (ha j).1 (ha j).2 hx
    have h := (sixPhase_hasDerivAt x).add (hsum.const_mul (t / 4))
    refine h.congr_deriv ?_
    unfold sixPhasePotentialDerivative
    rw [← Finset.mul_sum]; ring
  have hderiv_le : ∀ x ∈ interior (Ici (2 : ℝ)),
      deriv (sixPhasePotential a t) x ≤ -(1 / 2 : ℝ) := by
    intro x hx
    have hx2 : 2 ≤ x := interior_subset hx
    rw [(hderiv x hx2).deriv]
    unfold sixPhasePotentialDerivative
    have hsum : (∑ j : Fin 2, sixPairSlope (a j) x) ≤ 80 / 19 := by
      calc _ ≤ ∑ _j : Fin 2, (40 / 19 : ℝ) :=
            Finset.sum_le_sum fun j _ => sixPairSlope_tail_le (ha j).1 (ha j).2 hx2
        _ = 80 / 19 := by norm_num
    have hcorr := mul_le_mul_of_nonneg_left hsum (show 0 ≤ t / 2 by positivity)
    have hbase := sixPhaseDerivative_tail_le hx2
    nlinarith
  have hc : ContinuousOn (sixPhasePotential a t) (Ici 2) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (sixPhasePotential a t) (interior (Ici 2)) := fun x hx =>
    (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hh := (convex_Ici (2 : ℝ)).image_sub_le_mul_sub_of_deriv_le hc hd hderiv_le
    2 (by simp) y hy hy
  linarith

def sixEnvelope (s : ℝ) : ℝ :=
  (1 + |s|) ^ 18 * Real.exp (-(1 / 2) * max 0 (|s| - 2))

def sixEnvelopeConstant : ℝ := ∫ s : ℝ, sixEnvelope s

private theorem sixEnvelope_pos (s : ℝ) : 0 < sixEnvelope s := by
  unfold sixEnvelope; positivity

private theorem sixEnvelope_continuous : Continuous sixEnvelope := by
  unfold sixEnvelope; fun_prop

private theorem sixEnvelope_integrable : Integrable sixEnvelope := by
  have hpos : IntegrableOn sixEnvelope (Ioi 0) := by
    have h0 : IntegrableOn (fun s : ℝ => Real.exp (-(1 / 2) * s)) (Ioi 0) :=
      integrableOn_exp_mul_Ioi (by norm_num) 0
    have h18 : IntegrableOn (fun s : ℝ => s ^ 18 * Real.exp (-(1 / 2) * s)) (Ioi 0) := by
      simpa only [Real.rpow_natCast, Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (18 : ℕ)) (p := 1) (b := 1 / 2)
          (by norm_num) (by norm_num) (by norm_num))
    have hb := (h0.add h18).const_mul ((2 : ℝ) ^ 17 * Real.exp 1)
    apply hb.mono' sixEnvelope_continuous.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 ≤ s := hs.le
    rw [Real.norm_eq_abs, abs_of_pos (sixEnvelope_pos s)]
    unfold sixEnvelope
    rw [abs_of_nonneg hs0]
    have hp : (1 + s) ^ 18 ≤ (2 : ℝ) ^ 17 * (1 + s ^ 18) := by
      simpa only [Nat.reduceSub, one_pow] using add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hs0 18
    have he : Real.exp (-(1 / 2) * max 0 (s - 2)) ≤ Real.exp 1 * Real.exp (-(1 / 2) * s) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      have hmax := le_max_right (0 : ℝ) (s - 2); linarith
    calc _ ≤ ((2 : ℝ) ^ 17 * (1 + s ^ 18)) * (Real.exp 1 * Real.exp (-(1 / 2) * s)) :=
          mul_le_mul hp he (Real.exp_pos _).le (by positivity)
      _ = _ := by simp only [Pi.add_apply]; ring
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  have hneg : (fun s => sixEnvelope (-s)) = sixEnvelope := funext fun s => by simp [sixEnvelope]
  simpa only [Function.comp_def, hneg, neg_preimage, neg_Iio, neg_zero] using hpos

theorem sixEnvelopeConstant_pos : 0 < sixEnvelopeConstant :=
  integral_pos_of_integrable_nonneg_nonzero sixEnvelope_continuous sixEnvelope_integrable
    (fun s => (sixEnvelope_pos s).le) (sixEnvelope_pos 0).ne'

def sixAdaptiveMomentConstant : ℝ :=
  50 * sixAdaptiveDensityConstant * sixEnvelopeConstant

theorem sixAdaptiveMomentConstant_pos : 0 < sixAdaptiveMomentConstant :=
  mul_pos (mul_pos (by norm_num) sixAdaptiveDensityConstant_pos) sixEnvelopeConstant_pos

/-- Complete-line modulus moment bound from a compact `[0, 2]` off-root phase ceiling `M`. -/
theorem sixAdaptiveMoment_le_of_compact (n i : ℕ) (hn : 1 ≤ n) (hi : i < 15 * n)
    (a : Fin 2 → ℚ) (ha : ∀ j, 0 ≤ (a j : ℝ) ∧ (a j : ℝ) ≤ 3 / 10) (M : ℝ)
    (hcompact : ∀ y : ℝ, 0 ≤ y → y ≤ 2 →
      (∀ j : Fin 2, 0 < sixAdaptivePairModulus (69 / 50) (a j : ℝ) y) →
      sixPhasePotential (fun j => (a j : ℝ)) (sixRowTheta n i) y ≤ M) :
    sixBasisModulusMoment n
      ((sixAdaptiveMonic i (sixAdaptiveDelta n) a).comp (C ((50 * (n : ℚ))⁻¹ ^ 2) * X ^ 2)) ≤
      sixAdaptiveMomentConstant * (n : ℝ) ^ 38 * Real.exp (50 * (n : ℝ) * M) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h50n : (0 : ℝ) < 50 * (n : ℝ) := by positivity
  have ht0 : 0 ≤ sixRowTheta n i := by unfold sixRowTheta; positivity
  have ht3 : sixRowTheta n i ≤ 3 / 10 := by
    unfold sixRowTheta
    rw [div_le_iff₀ h50n]
    have h4 : ((4 * (i / 4) : ℕ) : ℝ) ≤ 15 * (n : ℝ) := by exact_mod_cast (show 4 * (i / 4) ≤ 15 * n by omega)
    push_cast at h4 ⊢; linarith
  have hne : ∀ᵐ s : ℝ, ∀ j : Fin 2, 0 < sixAdaptivePairModulus (69 / 50) (a j : ℝ) |s| := by
    have hae : ∀ᵐ s : ℝ, ∀ j : Fin 2, s ≠ (a j : ℝ) ∧ s ≠ -(a j : ℝ) :=
      ae_all_iff.mpr fun j => (volume.ae_ne (a j : ℝ)).and (volume.ae_ne (-(a j : ℝ)))
    filter_upwards [hae] with s hs j
    have hsq : s ^ 2 ≠ (a j : ℝ) ^ 2 := by
      intro he; rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
      · exact (hs j).1 he
      · exact (hs j).2 he
    have hd : |s| ^ 2 - (a j : ℝ) ^ 2 ≠ 0 := by rw [sq_abs, sub_ne_zero]; exact hsq
    unfold sixAdaptivePairModulus
    have hfirst := sq_pos_of_ne_zero hd
    positivity
  have h2 : sixPhasePotential (fun j => (a j : ℝ)) (sixRowTheta n i) 2 ≤ M :=
    hcompact 2 (by norm_num) le_rfl fun j => sixPairModulus_tail_pos (ha j).1 (ha j).2 le_rfl
  let A : ℝ := sixAdaptiveDensityConstant * (n : ℝ) ^ 37 * Real.exp (50 * (n : ℝ) * M)
  have hbound : ∀ᵐ s : ℝ, sixAdaptiveDensity n i a (50 * (n : ℝ) * s) ≤ A * sixEnvelope s := by
    filter_upwards [hne] with s hs
    have hpsi : sixPhasePotential (fun j => (a j : ℝ)) (sixRowTheta n i) |s| ≤
        M - (1 / 2) * max 0 (|s| - 2) := by
      by_cases hsc : |s| ≤ 2
      · rw [max_eq_left (sub_nonpos.mpr hsc), mul_zero, sub_zero]
        exact hcompact |s| (abs_nonneg s) hsc hs
      · rw [max_eq_right (by linarith : 0 ≤ |s| - 2)]
        exact (sixPhasePotential_tail_line (fun j => (a j : ℝ)) (sixRowTheta n i)
          ha ht0 ht3 (le_of_not_ge hsc)).trans (sub_le_sub_right h2 _)
    have hmax := le_max_left (0 : ℝ) (|s| - 2)
    have hp : 50 * (n : ℝ) * sixPhasePotential (fun j => (a j : ℝ)) (sixRowTheta n i) |s| ≤
        50 * (n : ℝ) * M - (1 / 2) * max 0 (|s| - 2) := by
      have hm := mul_le_mul_of_nonneg_left hpsi h50n.le
      have h50ge : (1 : ℝ) ≤ 50 * (n : ℝ) := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr h50ge) hmax]
    have hE := Real.exp_le_exp.mpr hp
    rw [Real.exp_sub] at hE
    have hC0 := sixAdaptiveDensityConstant_pos.le
    calc _ ≤ sixAdaptiveDensityConstant * (n : ℝ) ^ 37 * (1 + |s|) ^ 18 *
            Real.exp (50 * (n : ℝ) * sixPhasePotential (fun j => (a j : ℝ)) (sixRowTheta n i) |s|) :=
          sixAdaptiveDensity_uniform n i hn hi a s
      _ ≤ sixAdaptiveDensityConstant * (n : ℝ) ^ 37 * (1 + |s|) ^ 18 *
            (Real.exp (50 * (n : ℝ) * M) / Real.exp ((1 / 2) * max 0 (|s| - 2))) := by gcongr
      _ = A * sixEnvelope s := by
          unfold A sixEnvelope
          rw [neg_mul, Real.exp_neg]; ring
  have hcont_s : Continuous (fun s : ℝ => sixAdaptiveDensity n i a (50 * (n : ℝ) * s)) :=
    (sixAdaptiveDensity_continuous n i a).comp (continuous_const.mul continuous_id)
  have henv := sixEnvelope_integrable.const_mul A
  have hint_s : Integrable (fun s : ℝ => sixAdaptiveDensity n i a (50 * (n : ℝ) * s)) :=
    henv.mono' hcont_s.aestronglyMeasurable (by
      filter_upwards [hbound] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (sixAdaptiveDensity_nonneg n i a _)]
      exact hs)
  have hb := integral_mono_ae hint_s henv hbound
  rw [integral_const_mul] at hb
  have hscale : (∫ y : ℝ, sixAdaptiveDensity n i a y) =
      50 * (n : ℝ) * (∫ s : ℝ, sixAdaptiveDensity n i a (50 * (n : ℝ) * s)) := by
    rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr h50n), smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ h50n.ne', one_mul]
  change (∫ y : ℝ, sixAdaptiveDensity n i a y) ≤ _
  rw [hscale]
  calc _ ≤ 50 * (n : ℝ) * (A * sixEnvelopeConstant) := mul_le_mul_of_nonneg_left hb h50n.le
    _ = _ := by unfold A sixAdaptiveMomentConstant; ring

/-! ## Section 5: Four-bin affine interpolation and analytic rate endgame -/

/-- Exact bin knots `0, 3/40, 3/20, 9/40, 3/10` indexed by `(b : Fin 4, side : Fin 2)`. -/
def sixBinKnot (b : Fin 4) (side : Fin 2) : ℝ :=
  3 * ((b.val + side.val : ℕ) : ℝ) / 40

/-- Affine interpolation between the two endpoint ceilings `cap b 0` and `cap b 1` on bin `b`. -/
def sixBinAffine (cap : Fin 4 → Fin 2 → ℚ) (b : Fin 4) (t : ℝ) : ℝ :=
  (cap b 0 : ℝ) + (40 / 3 : ℝ) * ((cap b 1 : ℝ) - (cap b 0 : ℝ)) * (t - 3 * (b.val : ℝ) / 40)

/-- Bin selector on `[0, 3/10)`. -/
def sixBinOf (t : ℝ) : Fin 4 :=
  if t < 3 / 40 then 0 else if t < 3 / 20 then 1 else if t < 9 / 40 then 2 else 3

private theorem sixBinOf_mem {t : ℝ} (ht0 : 0 ≤ t) (ht3 : t ≤ 3 / 10) :
    sixBinKnot (sixBinOf t) 0 ≤ t ∧ t ≤ sixBinKnot (sixBinOf t) 1 := by
  unfold sixBinOf sixBinKnot
  split_ifs <;> norm_num <;> constructor <;> linarith

private theorem sixPhasePotential_affine_le (a : Fin 2 → ℝ) (cap : Fin 4 → Fin 2 → ℚ)
    (b : Fin 4) {t y : ℝ}
    (htL : sixBinKnot b 0 ≤ t) (htR : t ≤ sixBinKnot b 1)
    (hL : sixPhasePotential a (sixBinKnot b 0) y ≤ (cap b 0 : ℝ))
    (hR : sixPhasePotential a (sixBinKnot b 1) y ≤ (cap b 1 : ℝ)) :
    sixPhasePotential a t y ≤ sixBinAffine cap b t := by
  let lam : ℝ := (40 / 3 : ℝ) * (t - 3 * (b.val : ℝ) / 40)
  have hL' : 3 * (b.val : ℝ) / 40 ≤ t := by
    simpa [sixBinKnot] using htL
  have hR' : t ≤ 3 * ((b.val : ℝ) + 1) / 40 := by
    simpa [sixBinKnot, Nat.cast_add, Nat.cast_one] using htR
  have hlam0 : 0 ≤ lam := by dsimp [lam]; linarith
  have hlam1 : lam ≤ 1 := by dsimp [lam]; linarith
  have hlin : sixPhasePotential a t y =
      (1 - lam) * sixPhasePotential a (sixBinKnot b 0) y +
        lam * sixPhasePotential a (sixBinKnot b 1) y := by
    unfold sixPhasePotential sixBinKnot
    push_cast; dsimp [lam]; ring
  have haff : sixBinAffine cap b t = (1 - lam) * (cap b 0 : ℝ) + lam * (cap b 1 : ℝ) := by
    unfold sixBinAffine; dsimp [lam]; ring
  rw [hlin, haff]
  exact add_le_add (mul_le_mul_of_nonneg_left hL (by linarith))
    (mul_le_mul_of_nonneg_left hR hlam0)

private theorem sum_Ico_natCast (A B : ℕ) (hAB : A ≤ B) :
    (∑ i ∈ Finset.Ico A B, (i : ℝ)) =
      (((B : ℝ) - (A : ℝ)) * ((A : ℝ) + (B : ℝ) - 1)) / 2 := by
  have hnat : ∀ m : ℕ, (∑ i ∈ Finset.range m, (i : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have hsplit : (∑ i ∈ Finset.range A, (i : ℝ)) + (∑ i ∈ Finset.Ico A B, (i : ℝ)) =
      ∑ i ∈ Finset.range B, (i : ℝ) := by
    rw [← Finset.sum_union (Finset.disjoint_left.mpr fun x hx1 hx2 => by
      simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2; omega)]
    congr 1; ext x; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
  linarith [hnat A, hnat B]

set_option maxHeartbeats 400000 in
private theorem sixBinAffine_sum_bound (cap : Fin 4 → Fin 2 → ℚ) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (∑ i : Fin (rank n), sixBinAffine cap (sixBinOf (sixRowTheta n i.val)) (sixRowTheta n i.val)) ≤
        15 * (n : ℝ) * ((∑ b : Fin 4, ((cap b 0 : ℝ) + (cap b 1 : ℝ))) / 8) + C := by
  let M : ℝ := 1 + ∑ b : Fin 4, (|(cap b 0 : ℝ)| + |(cap b 1 : ℝ)|)
  have hM0 : 0 ≤ M := by
    dsimp [M]; positivity
  have hcap_le (b : Fin 4) (s : Fin 2) : |(cap b s : ℝ)| ≤ M := by
    have h1 : |(cap b 0 : ℝ)| + |(cap b 1 : ℝ)| ≤
        ∑ c : Fin 4, (|(cap c 0 : ℝ)| + |(cap c 1 : ℝ)|) :=
      Finset.single_le_sum (f := fun c : Fin 4 => |(cap c 0 : ℝ)| + |(cap c 1 : ℝ)|)
        (fun c _ => by positivity) (Finset.mem_univ b)
    fin_cases s <;> dsimp [M] <;> linarith [abs_nonneg (cap b 0 : ℝ), abs_nonneg (cap b 1 : ℝ)]
  have haff_abs (b : Fin 4) {t : ℝ} (htL : 3 * (b.val : ℝ) / 40 ≤ t)
      (htR : t ≤ 3 * ((b.val : ℝ) + 1) / 40) : |sixBinAffine cap b t| ≤ M := by
    let lam : ℝ := (40 / 3 : ℝ) * (t - 3 * (b.val : ℝ) / 40)
    have hlam0 : 0 ≤ lam := by dsimp [lam]; linarith
    have hlam1 : lam ≤ 1 := by dsimp [lam]; linarith
    have haff : sixBinAffine cap b t = (1 - lam) * (cap b 0 : ℝ) + lam * (cap b 1 : ℝ) := by
      unfold sixBinAffine; dsimp [lam]; ring
    rw [haff]
    calc |(1 - lam) * (cap b 0 : ℝ) + lam * (cap b 1 : ℝ)|
        ≤ |(1 - lam) * (cap b 0 : ℝ)| + |lam * (cap b 1 : ℝ)| := abs_add_le _ _
      _ = (1 - lam) * |(cap b 0 : ℝ)| + lam * |(cap b 1 : ℝ)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hlam0]
      _ ≤ (1 - lam) * M + lam * M := add_le_add
          (mul_le_mul_of_nonneg_left (hcap_le b 0) (by linarith))
          (mul_le_mul_of_nonneg_left (hcap_le b 1) hlam0)
      _ = M := by ring
  refine ⟨100 * M, fun n hn => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let K (k : ℕ) : ℕ := (15 * k * n) / 4
  have hK0 : K 0 = 0 := by simp [K]
  have hK4 : K 4 = 15 * n := by dsimp [K]; omega
  have hKmono : ∀ k, K k ≤ K (k + 1) := fun k => Nat.div_le_div_right (by nlinarith)
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => sixBinAffine cap (sixBinOf (sixRowTheta n i)) (sixRowTheta n i)) (rank n)]
  change (∑ i ∈ Finset.range (15 * n),
    sixBinAffine cap (sixBinOf (sixRowTheta n i)) (sixRowTheta n i)) ≤ _
  have hpart : (∑ i ∈ Finset.range (15 * n),
      sixBinAffine cap (sixBinOf (sixRowTheta n i)) (sixRowTheta n i)) =
      ∑ b : Fin 4, ∑ i ∈ Finset.Ico (K b.val) (K (b.val + 1)),
        sixBinAffine cap (sixBinOf (sixRowTheta n i)) (sixRowTheta n i) := by
    have h01 : K 0 ≤ K 1 := hKmono 0
    have h12 : K 1 ≤ K 2 := hKmono 1
    have h23 : K 2 ≤ K 3 := hKmono 2
    have h34 : K 3 ≤ K 4 := hKmono 3
    have h1 : Finset.range (15 * n) =
        Finset.Ico (K 0) (K 1) ∪ Finset.Ico (K 1) (K 2) ∪
          Finset.Ico (K 2) (K 3) ∪ Finset.Ico (K 3) (K 4) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      rw [hK0, hK4]; omega
    have hd1 : Disjoint (Finset.Ico (K 0) (K 1)) (Finset.Ico (K 1) (K 2)) :=
      Finset.Ico_disjoint_Ico_consecutive _ _ _
    have hd2 : Disjoint (Finset.Ico (K 0) (K 1) ∪ Finset.Ico (K 1) (K 2)) (Finset.Ico (K 2) (K 3)) :=
      Finset.disjoint_left.mpr fun x hx1 hx2 => by
        simp only [Finset.mem_union, Finset.mem_Ico] at hx1 hx2; omega
    have hd3 : Disjoint (Finset.Ico (K 0) (K 1) ∪ Finset.Ico (K 1) (K 2) ∪ Finset.Ico (K 2) (K 3))
        (Finset.Ico (K 3) (K 4)) :=
      Finset.disjoint_left.mpr fun x hx1 hx2 => by
        simp only [Finset.mem_union, Finset.mem_Ico] at hx1 hx2; omega
    rw [h1, Finset.sum_union hd3, Finset.sum_union hd2, Finset.sum_union hd1,
      Fin.sum_univ_four]
    rfl
  rw [hpart]
  have hbin : ∀ b : Fin 4,
      (∑ i ∈ Finset.Ico (K b.val) (K (b.val + 1)),
        sixBinAffine cap (sixBinOf (sixRowTheta n i)) (sixRowTheta n i)) ≤
        (15 * (n : ℝ) / 4) * (((cap b 0 : ℝ) + (cap b 1 : ℝ)) / 2) + 25 * M := by
    intro b
    have hAB : K b.val ≤ K (b.val + 1) := hKmono b.val
    have hpt : ∀ i ∈ Finset.Ico (K b.val) (K (b.val + 1)),
        sixBinAffine cap (sixBinOf (sixRowTheta n i)) (sixRowTheta n i) ≤
          sixBinAffine cap b ((i : ℝ) / (50 * (n : ℝ))) +
            (if i < K b.val + 4 then 3 * M else (8 / (5 * (n : ℝ))) * M) := by
      intro i hi
      simp only [Finset.mem_Ico] at hi
      have hi15 : i < 15 * n := lt_of_lt_of_le hi.2 (by
        have hb : b.val + 1 ≤ 4 := by omega
        calc K (b.val + 1) = (15 * (b.val + 1) * n) / 4 := rfl
          _ ≤ (15 * 4 * n) / 4 := Nat.div_le_div_right (by nlinarith)
          _ = 15 * n := by omega)
      have ht0 : 0 ≤ sixRowTheta n i := by unfold sixRowTheta; positivity
      have ht3 : sixRowTheta n i ≤ 3 / 10 := by
        unfold sixRowTheta; rw [div_le_iff₀ (by positivity)]
        have : ((4 * (i / 4) : ℕ) : ℝ) ≤ 15 * (n : ℝ) := by exact_mod_cast (show 4 * (i / 4) ≤ 15 * n by omega)
        push_cast at this ⊢; linarith
      have hi_lo : 3 * (b.val : ℝ) / 40 - 1 / (50 * (n : ℝ)) ≤ (i : ℝ) / (50 * (n : ℝ)) := by
        have hKlo : (15 * (b.val : ℝ) * (n : ℝ)) / 4 - 1 ≤ (K b.val : ℝ) := by
          have : 15 * b.val * n < 4 * (K b.val + 1) := by dsimp [K]; omega
          have h' : (15 * (b.val : ℝ) * (n : ℝ)) < 4 * ((K b.val : ℝ) + 1) := by exact_mod_cast this
          linarith
        have hi' : (K b.val : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi.1
        rw [le_div_iff₀ (by positivity : 0 < 50 * (n : ℝ))]
        have hmul : (3 * (b.val : ℝ) / 40 - 1 / (50 * (n : ℝ))) * (50 * (n : ℝ)) =
            15 * (b.val : ℝ) * (n : ℝ) / 4 - 1 := by field_simp; ring
        rw [hmul]; linarith
      have hi_hi : (i : ℝ) / (50 * (n : ℝ)) ≤ 3 * ((b.val : ℝ) + 1) / 40 := by
        have hKhi : (K (b.val + 1) : ℝ) ≤ (15 * ((b.val : ℝ) + 1) * (n : ℝ)) / 4 := by
          have : 4 * K (b.val + 1) ≤ 15 * (b.val + 1) * n := by dsimp [K]; omega
          have h' : 4 * (K (b.val + 1) : ℝ) ≤ 15 * ((b.val : ℝ) + 1) * (n : ℝ) := by exact_mod_cast this
          linarith
        have hi' : (i : ℝ) ≤ (K (b.val + 1) : ℝ) := by exact_mod_cast hi.2.le
        rw [div_le_iff₀ (by positivity : 0 < 50 * (n : ℝ))]
        nlinarith
      split_ifs with hlt
      · have hmem := sixBinOf_mem ht0 ht3
        have h1 : sixBinAffine cap (sixBinOf (sixRowTheta n i)) (sixRowTheta n i) ≤ M :=
          (le_abs_self _).trans (haff_abs (sixBinOf (sixRowTheta n i))
            (by simpa [sixBinKnot] using hmem.1)
            (by simpa [sixBinKnot, Nat.cast_add, Nat.cast_one] using hmem.2))
        have h2 : -2 * M ≤ sixBinAffine cap b ((i : ℝ) / (50 * (n : ℝ))) := by
          by_cases hge : 3 * (b.val : ℝ) / 40 ≤ (i : ℝ) / (50 * (n : ℝ))
          · linarith [neg_le_of_abs_le (haff_abs b hge hi_hi)]
          · have hdist : |(i : ℝ) / (50 * (n : ℝ)) - 3 * (b.val : ℝ) / 40| ≤ 1 / (50 * (n : ℝ)) :=
              abs_le.mpr ⟨by linarith, by linarith⟩
            have hsub : |(cap b 1 : ℝ) - (cap b 0 : ℝ)| ≤ 2 * M :=
              (abs_sub _ _).trans (by linarith [hcap_le b 1, hcap_le b 0])
            have hstep : |sixBinAffine cap b ((i : ℝ) / (50 * (n : ℝ))) - (cap b 0 : ℝ)| ≤
                (40 / 3 : ℝ) * (2 * M) * (1 / (50 * (n : ℝ))) := by
              unfold sixBinAffine
              rw [add_sub_cancel_left, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 40 / 3)]
              exact mul_le_mul (mul_le_mul_of_nonneg_left hsub (by norm_num)) hdist (abs_nonneg _) (by positivity)
            have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
            have hsmall : (40 / 3 : ℝ) * (2 * M) * (1 / (50 * (n : ℝ))) ≤ M := by
              rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 50 * (n : ℝ))]; nlinarith
            have hc0 := neg_le_of_abs_le (hcap_le b 0)
            linarith [(abs_le.mp hstep).1]
        linarith
      · have hge4 : K b.val + 4 ≤ i := by omega
        have hth_lo : 3 * (b.val : ℝ) / 40 ≤ sixRowTheta n i := by
          have h4i : 15 * b.val * n < 4 * (4 * (i / 4)) := by dsimp [K] at hge4; omega
          have h4i' : 15 * (b.val : ℝ) * (n : ℝ) < 4 * ((4 * (i / 4) : ℕ) : ℝ) := by exact_mod_cast h4i
          unfold sixRowTheta
          rw [le_div_iff₀ (by positivity : 0 < 50 * (n : ℝ))]
          push_cast at h4i' ⊢; linarith
        have hth_lt : sixRowTheta n i < 3 * ((b.val : ℝ) + 1) / 40 := by
          have h4i : 4 * (4 * (i / 4)) < 15 * (b.val + 1) * n := by
            have : 4 * K (b.val + 1) ≤ 15 * (b.val + 1) * n := by dsimp [K]; omega
            omega
          have h4i' : 4 * ((4 * (i / 4) : ℕ) : ℝ) < 15 * ((b.val : ℝ) + 1) * (n : ℝ) := by
            exact_mod_cast h4i
          unfold sixRowTheta
          rw [div_lt_iff₀ (by positivity : 0 < 50 * (n : ℝ))]
          push_cast at h4i' ⊢; linarith
        have hbin_eq : sixBinOf (sixRowTheta n i) = b := by
          fin_cases b <;> unfold sixBinOf <;> norm_num at hth_lo hth_lt <;>
            split_ifs <;> first | rfl | linarith
        rw [hbin_eq]
        have hdiff_t : 0 ≤ (i : ℝ) / (50 * (n : ℝ)) - sixRowTheta n i ∧
            (i : ℝ) / (50 * (n : ℝ)) - sixRowTheta n i ≤ 3 / (50 * (n : ℝ)) := by
          unfold sixRowTheta
          rw [← sub_div]
          constructor
          · apply div_nonneg _ (by positivity)
            have : 4 * (i / 4) ≤ i := by omega
            have h' : ((4 * (i / 4) : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast this
            push_cast at h' ⊢; linarith
          · apply div_le_div_of_nonneg_right _ (by positivity)
            have : i ≤ 4 * (i / 4) + 3 := by omega
            have h' : (i : ℝ) ≤ ((4 * (i / 4) : ℕ) : ℝ) + 3 := by exact_mod_cast this
            push_cast at h' ⊢; linarith
        have hsub : |(cap b 1 : ℝ) - (cap b 0 : ℝ)| ≤ 2 * M :=
          (abs_sub _ _).trans (by linarith [hcap_le b 1, hcap_le b 0])
        have hstep : sixBinAffine cap b (sixRowTheta n i) -
            sixBinAffine cap b ((i : ℝ) / (50 * (n : ℝ))) ≤ (8 / (5 * (n : ℝ))) * M := by
          have heq : sixBinAffine cap b (sixRowTheta n i) -
              sixBinAffine cap b ((i : ℝ) / (50 * (n : ℝ))) =
              -((40 / 3 : ℝ) * ((cap b 1 : ℝ) - (cap b 0 : ℝ)) *
                ((i : ℝ) / (50 * (n : ℝ)) - sixRowTheta n i)) := by
            unfold sixBinAffine; ring
          rw [heq]
          calc _ ≤ |((40 / 3 : ℝ) * ((cap b 1 : ℝ) - (cap b 0 : ℝ)) *
                    ((i : ℝ) / (50 * (n : ℝ)) - sixRowTheta n i))| := neg_le_abs _
            _ = (40 / 3 : ℝ) * |(cap b 1 : ℝ) - (cap b 0 : ℝ)| *
                  ((i : ℝ) / (50 * (n : ℝ)) - sixRowTheta n i) := by
                rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 40 / 3),
                  abs_of_nonneg hdiff_t.1]
            _ ≤ (40 / 3 : ℝ) * (2 * M) * (3 / (50 * (n : ℝ))) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hsub (by norm_num)) hdiff_t.2 hdiff_t.1 (by positivity)
            _ = (8 / (5 * (n : ℝ))) * M := by ring
        linarith
    -- Now sum `hpt` over `Ico (K b) (K (b+1))`:
    have hsum1 : (∑ i ∈ Finset.Ico (K b.val) (K (b.val + 1)),
        sixBinAffine cap (sixBinOf (sixRowTheta n i)) (sixRowTheta n i)) ≤
        (∑ i ∈ Finset.Ico (K b.val) (K (b.val + 1)),
          sixBinAffine cap b ((i : ℝ) / (50 * (n : ℝ)))) +
        (∑ i ∈ Finset.Ico (K b.val) (K (b.val + 1)),
          (if i < K b.val + 4 then 3 * M else (8 / (5 * (n : ℝ))) * M)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hpt
    have herr_sum : (∑ i ∈ Finset.Ico (K b.val) (K (b.val + 1)),
        (if i < K b.val + 4 then 3 * M else (8 / (5 * (n : ℝ))) * M)) ≤ 19 * M := by
      calc _ ≤ ∑ i ∈ Finset.Ico (K b.val) (K (b.val + 1)),
            ((if i < K b.val + 4 then 3 * M else 0) + (8 / (5 * (n : ℝ))) * M) := by
            apply Finset.sum_le_sum; intro i _
            have hnn : 0 ≤ (8 / (5 * (n : ℝ))) * M := by positivity
            split_ifs <;> linarith
        _ = (∑ i ∈ Finset.Ico (K b.val) (K (b.val + 1)), if i < K b.val + 4 then 3 * M else 0) +
            ((K (b.val + 1) - K b.val : ℕ) : ℝ) * ((8 / (5 * (n : ℝ))) * M) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ (∑ i ∈ Finset.Ico (K b.val) (K b.val + 4), 3 * M) +
            (4 * (n : ℝ)) * ((8 / (5 * (n : ℝ))) * M) := by
          apply add_le_add
          · rw [← Finset.sum_filter]
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (fun x hx => by
                simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢
                exact ⟨hx.1.1, hx.2⟩)
              (fun _ _ _ => by positivity)
          · apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast (show K (b.val + 1) - K b.val ≤ 4 * n by
              have hstep : 15 * (b.val + 1) * n = 15 * b.val * n + 15 * n := by ring
              dsimp [K]; rw [hstep]; omega)
        _ = 12 * M + (32 / 5 : ℝ) * M := by
          rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]
          push_cast; field_simp; ring
        _ ≤ 19 * M := by linarith
    -- Exact arithmetic-progression evaluation of the linear sum:
    have hlin_sum : (∑ i ∈ Finset.Ico (K b.val) (K (b.val + 1)),
        sixBinAffine cap b ((i : ℝ) / (50 * (n : ℝ)))) ≤
        (15 * (n : ℝ) / 4) * (((cap b 0 : ℝ) + (cap b 1 : ℝ)) / 2) + 6 * M := by
      have hexp : (∑ i ∈ Finset.Ico (K b.val) (K (b.val + 1)),
          sixBinAffine cap b ((i : ℝ) / (50 * (n : ℝ)))) =
          ((K (b.val + 1) : ℝ) - (K b.val : ℝ)) *
            ((cap b 0 : ℝ) + ((cap b 1 : ℝ) - (cap b 0 : ℝ)) *
              ((4 * ((K b.val : ℝ) + (K (b.val + 1) : ℝ) - 1) / (30 * (n : ℝ))) - (b.val : ℝ))) := by
        have hstep (i : ℕ) : sixBinAffine cap b ((i : ℝ) / (50 * (n : ℝ))) =
            ((cap b 0 : ℝ) - (b.val : ℝ) * ((cap b 1 : ℝ) - (cap b 0 : ℝ))) +
              ((4 * ((cap b 1 : ℝ) - (cap b 0 : ℝ))) / (15 * (n : ℝ))) * (i : ℝ) := by
          unfold sixBinAffine; field_simp; ring
        rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_add_distrib, Finset.sum_const,
          Nat.card_Ico, nsmul_eq_mul, ← Finset.mul_sum, sum_Ico_natCast _ _ hAB,
          Nat.cast_sub hAB]
        field_simp; ring
      rw [hexp]
      set dK : ℝ := (K (b.val + 1) : ℝ) - (K b.val : ℝ)
      set mK : ℝ := (4 * ((K b.val : ℝ) + (K (b.val + 1) : ℝ) - 1) / (30 * (n : ℝ))) - (b.val : ℝ)
      have hKlo (k : ℕ) : (15 * (k : ℝ) * (n : ℝ)) / 4 - 1 ≤ (K k : ℝ) := by
        have : 15 * k * n < 4 * (K k + 1) := by dsimp [K]; omega
        have h' : 15 * (k : ℝ) * (n : ℝ) < 4 * ((K k : ℝ) + 1) := by exact_mod_cast this
        linarith
      have hKhi (k : ℕ) : (K k : ℝ) ≤ (15 * (k : ℝ) * (n : ℝ)) / 4 := by
        have : 4 * K k ≤ 15 * k * n := by dsimp [K]; omega
        have h' : 4 * (K k : ℝ) ≤ 15 * (k : ℝ) * (n : ℝ) := by exact_mod_cast this
        linarith
      have hdK : |dK - 15 * (n : ℝ) / 4| ≤ 1 := by
        have h1 := hKlo b.val; have h2 := hKhi b.val
        have h3 := hKlo (b.val + 1); have h4 := hKhi (b.val + 1)
        push_cast at h3 h4
        exact abs_le.mpr ⟨by dsimp [dK]; linarith, by dsimp [dK]; linarith⟩
      have hmK : |mK - 1 / 2| ≤ 2 / (5 * (n : ℝ)) := by
        have h1 := hKlo b.val; have h2 := hKhi b.val
        have h3 := hKlo (b.val + 1); have h4 := hKhi (b.val + 1)
        push_cast at h3 h4
        have hnum_lo : 15 * (2 * (b.val : ℝ) + 1) * (n : ℝ) / 4 - 3 ≤
            (K b.val : ℝ) + (K (b.val + 1) : ℝ) - 1 := by linarith
        have hnum_hi : (K b.val : ℝ) + (K (b.val + 1) : ℝ) - 1 ≤
            15 * (2 * (b.val : ℝ) + 1) * (n : ℝ) / 4 := by linarith
        apply abs_le.mpr
        have h5 : (0 : ℝ) < 30 * (n : ℝ) := by positivity
        have heq' : mK - 1 / 2 =
            (4 * ((K b.val : ℝ) + (K (b.val + 1) : ℝ) - 1) -
              15 * (2 * (b.val : ℝ) + 1) * (n : ℝ)) / (30 * (n : ℝ)) := by
          dsimp [mK]; field_simp; ring
        have h12 : (2 / (5 * (n : ℝ))) * (30 * (n : ℝ)) = 12 := by field_simp; ring
        rw [heq']
        constructor
        · rw [le_div_iff₀ h5, neg_mul, h12]; linarith
        · rw [div_le_iff₀ h5, h12]; linarith
      have hsub : |(cap b 1 : ℝ) - (cap b 0 : ℝ)| ≤ 2 * M :=
        (abs_sub _ _).trans (by linarith [hcap_le b 1, hcap_le b 0])
      have havg : |((cap b 0 : ℝ) + (cap b 1 : ℝ)) / 2| ≤ M := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := (abs_add_le (cap b 0 : ℝ) (cap b 1 : ℝ)).trans
          (add_le_add (hcap_le b 0) (hcap_le b 1))
        linarith
      have hsplit : dK * ((cap b 0 : ℝ) + ((cap b 1 : ℝ) - (cap b 0 : ℝ)) * mK) -
          (15 * (n : ℝ) / 4) * (((cap b 0 : ℝ) + (cap b 1 : ℝ)) / 2) =
          (dK - 15 * (n : ℝ) / 4) * (((cap b 0 : ℝ) + (cap b 1 : ℝ)) / 2) +
            dK * (((cap b 1 : ℝ) - (cap b 0 : ℝ)) * (mK - 1 / 2)) := by ring
      have hdK_le : |dK| ≤ 15 * (n : ℝ) / 4 + 1 := by
        have h0 : 0 ≤ dK := by
          dsimp [dK]
          have : (K b.val : ℝ) ≤ (K (b.val + 1) : ℝ) := by exact_mod_cast hAB
          linarith
        rw [abs_of_nonneg h0]; linarith [(abs_le.mp hdK).2]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hdK_le2 : |dK| ≤ 5 * (n : ℝ) := by linarith
      have herr_tot :
          |dK * ((cap b 0 : ℝ) + ((cap b 1 : ℝ) - (cap b 0 : ℝ)) * mK) -
            (15 * (n : ℝ) / 4) * (((cap b 0 : ℝ) + (cap b 1 : ℝ)) / 2)| ≤ 6 * M := by
        rw [hsplit]
        calc _ ≤ |(dK - 15 * (n : ℝ) / 4) * (((cap b 0 : ℝ) + (cap b 1 : ℝ)) / 2)| +
              |dK * (((cap b 1 : ℝ) - (cap b 0 : ℝ)) * (mK - 1 / 2))| := abs_add_le _ _
          _ = |dK - 15 * (n : ℝ) / 4| * |((cap b 0 : ℝ) + (cap b 1 : ℝ)) / 2| +
              |dK| * (|(cap b 1 : ℝ) - (cap b 0 : ℝ)| * |mK - 1 / 2|) := by
              simp only [abs_mul]
          _ ≤ 1 * M + (5 * (n : ℝ)) * ((2 * M) * (2 / (5 * (n : ℝ)))) := by
              apply add_le_add
              · exact mul_le_mul hdK havg (abs_nonneg _) (by norm_num)
              · exact mul_le_mul hdK_le2
                  (mul_le_mul hsub hmK (abs_nonneg _) (by positivity))
                  (by positivity) (by positivity)
          _ = 5 * M := by field_simp; ring
          _ ≤ 6 * M := by linarith
      linarith [(abs_le.mp herr_tot).2]
    linarith
  calc (∑ b : Fin 4, ∑ i ∈ Finset.Ico (K b.val) (K (b.val + 1)),
          sixBinAffine cap (sixBinOf (sixRowTheta n i)) (sixRowTheta n i))
      ≤ ∑ b : Fin 4, ((15 * (n : ℝ) / 4) * (((cap b 0 : ℝ) + (cap b 1 : ℝ)) / 2) + 25 * M) :=
        Finset.sum_le_sum fun b _ => hbin b
    _ = 15 * (n : ℝ) * ((∑ b : Fin 4, ((cap b 0 : ℝ) + (cap b 1 : ℝ))) / 8) + 100 * M := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_div]
        push_cast; ring

private theorem sixMoment_prefactor_subquadratic (C : ℝ) (hC : 0 < C)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (C * (n : ℝ) ^ 38) ^ (15 * n) ≤ Real.exp (ε * sixNorm n) := by
  have hlog : Tendsto (fun n : ℕ => (Real.log C + 38 * Real.log (n : ℝ)) / (n : ℝ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq] using!
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).add (h1.const_mul 38)
    simp only [mul_zero, add_zero] at h
    refine h.congr' (Eventually.of_forall fun n => by ring)
  have hlt := hlog.eventually_lt_const (show (0 : ℝ) < 50 * ε by positivity)
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with n hln hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpos : 0 < (C * (n : ℝ) ^ 38) ^ (15 * n) := pow_pos (mul_pos hC (pow_pos hnR 38)) _
  apply (Real.log_le_iff_le_exp hpos).mp
  rw [Real.log_pow, Real.log_mul hC.ne' (pow_ne_zero _ hnR.ne'), Real.log_pow, sixNorm_eq]
  push_cast
  have hmul : Real.log C + 38 * Real.log (n : ℝ) < 50 * ε * (n : ℝ) := (div_lt_iff₀ hnR).mp hln
  nlinarith

/-- **Main Analytic Assembly Theorem**: given 4 rational root pairs in `[0, 3/10]` and
8 rational endpoint ceilings `cap : Fin 4 → Fin 2 → ℚ` proved valid on `[0, 2]` off the
two roots, if `9/10 + (3/5) log (5/3) + (∑ b, cap b 0 + cap b 1) / 8 < R_bound`, then
`SixAnalyticRateHypothesis R_bound` holds unconditionally. -/
theorem sixAnalyticRate_of_four_bin_endpoints
    (roots : Fin 4 → Fin 2 → ℚ)
    (hroots : ∀ b j, 0 ≤ (roots b j : ℝ) ∧ (roots b j : ℝ) ≤ 3 / 10)
    (cap : Fin 4 → Fin 2 → ℚ)
    (hcap : ∀ b : Fin 4, ∀ side : Fin 2, ∀ y : ℝ, 0 ≤ y → y ≤ 2 →
      (∀ j : Fin 2, 0 < sixAdaptivePairModulus (69 / 50) (roots b j : ℝ) y) →
      sixPhasePotential (fun j => (roots b j : ℝ)) (sixBinKnot b side) y ≤ (cap b side : ℝ))
    (R_bound : ℝ)
    (hrate : (9 : ℝ) / 10 + 3 / 5 * Real.log (5 / 3) +
      (∑ b : Fin 4, ((cap b 0 : ℝ) + (cap b 1 : ℝ))) / 8 < R_bound) :
    SixAnalyticRateHypothesis R_bound := by
  obtain ⟨Csum, hCsum⟩ := sixBinAffine_sum_bound cap
  let avg : ℝ := (∑ b : Fin 4, ((cap b 0 : ℝ) + (cap b 1 : ℝ))) / 8
  let gap : ℝ := R_bound - ((9 : ℝ) / 10 + 3 / 5 * Real.log (5 / 3) + avg)
  have hgap : 0 < gap := by dsimp [gap, avg]; linarith
  have hq : 0 < gap / 4 := by positivity
  have hlin : ∀ᶠ n : ℕ in atTop, 50 * Csum * (n : ℝ) ≤ (gap / 4) * sixNorm n := by
    have hlim : Tendsto (fun n : ℕ => (50 * Csum) / (750 * (n : ℝ))) atTop (𝓝 0) := by
      simpa only [div_mul_eq_div_div] using
        (tendsto_const_div_atTop_nhds_zero_nat (50 * Csum / 750))
    filter_upwards [hlim.eventually_lt_const hq, eventually_gt_atTop (0 : ℕ)] with n hlt hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [sixNorm_eq]
    have h1 : 50 * Csum < (gap / 4) * (750 * (n : ℝ)) := (div_lt_iff₀ (by positivity)).mp hlt
    nlinarith
  filter_upwards [rank_factorial_subquadratic (gap / 4) hq,
    sixBasisNormalization_eventually_le (gap / 4) hq,
    sixMoment_prefactor_subquadratic sixAdaptiveMomentConstant sixAdaptiveMomentConstant_pos (gap / 4) hq,
    hlin, eventually_ge_atTop (1 : ℕ)] with n hfac hnorm hpref hCbound hn
  have hnpos : 0 < n := by omega
  let rowBin (i : Fin (rank n)) : Fin 4 := sixBinOf (sixRowTheta n i.val)
  let Q (i : Fin (rank n)) : ℚ[X] :=
    sixAdaptiveMonic i.val (sixAdaptiveDelta n) (roots (rowBin i))
  have hdet := sixFunctional_det_abs_le_monicMoments n hnpos Q
    (fun i => sixAdaptiveMonic_monic i.val _ _)
    (fun i => sixAdaptiveMonic_natDegree i.val _ _)
  have hmom : ∀ i : Fin (rank n),
      sixBasisModulusMoment n ((Q i).comp (C ((50 * (n : ℚ))⁻¹ ^ 2) * X ^ 2)) ≤
        sixAdaptiveMomentConstant * (n : ℝ) ^ 38 *
          Real.exp (50 * (n : ℝ) * sixBinAffine cap (rowBin i) (sixRowTheta n i.val)) := by
    intro i
    have ht0 : 0 ≤ sixRowTheta n i.val := by unfold sixRowTheta; positivity
    have ht3 : sixRowTheta n i.val ≤ 3 / 10 := by
      unfold sixRowTheta; rw [div_le_iff₀ (by positivity : 0 < 50 * (n : ℝ))]
      have hlt : i.val < 15 * n := i.isLt
      have : ((4 * (i.val / 4) : ℕ) : ℝ) ≤ 15 * (n : ℝ) := by
        exact_mod_cast (show 4 * (i.val / 4) ≤ 15 * n by omega)
      push_cast at this ⊢; linarith
    have hmem := sixBinOf_mem ht0 ht3
    exact sixAdaptiveMoment_le_of_compact n i.val hn i.isLt (roots (rowBin i)) (hroots (rowBin i))
      (sixBinAffine cap (rowBin i) (sixRowTheta n i.val)) fun y hy0 hy2 hpos =>
        sixPhasePotential_affine_le (fun j => (roots (rowBin i) j : ℝ)) cap (rowBin i)
          hmem.1 hmem.2 (hcap (rowBin i) 0 y hy0 hy2 hpos) (hcap (rowBin i) 1 y hy0 hy2 hpos)
  have hprod : (∏ i : Fin (rank n),
      sixBasisModulusMoment n ((Q i).comp (C ((50 * (n : ℚ))⁻¹ ^ 2) * X ^ 2))) ≤
      (sixAdaptiveMomentConstant * (n : ℝ) ^ 38) ^ (15 * n) *
        Real.exp ((avg + gap / 4) * sixNorm n) := by
    calc _ ≤ ∏ i : Fin (rank n), (sixAdaptiveMomentConstant * (n : ℝ) ^ 38 *
            Real.exp (50 * (n : ℝ) * sixBinAffine cap (rowBin i) (sixRowTheta n i.val))) :=
          Finset.prod_le_prod₀ (fun i _ => sixBasisModulusMoment_nonneg n _) (fun i _ => hmom i)
      _ = (sixAdaptiveMomentConstant * (n : ℝ) ^ 38) ^ (15 * n) *
            Real.exp (50 * (n : ℝ) *
              ∑ i : Fin (rank n), sixBinAffine cap (rowBin i) (sixRowTheta n i.val)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← Real.exp_sum, ← Finset.mul_sum]; rfl
      _ ≤ (sixAdaptiveMomentConstant * (n : ℝ) ^ 38) ^ (15 * n) *
            Real.exp ((avg + gap / 4) * sixNorm n) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _)
            (pow_nonneg (mul_nonneg sixAdaptiveMomentConstant_pos.le (by positivity)) _)
          have hs := mul_le_mul_of_nonneg_left (hCsum n hn) (by positivity : (0 : ℝ) ≤ 50 * (n : ℝ))
          rw [sixNorm_eq] at hCbound ⊢
          dsimp only [avg] at *
          nlinarith
  have hnorm0 := (sixBasisNormalization_pos n hnpos).le
  have hmom0 : 0 ≤ (sixAdaptiveMomentConstant * (n : ℝ) ^ 38) ^ (15 * n) *
      Real.exp ((avg + gap / 4) * sixNorm n) :=
    mul_nonneg (pow_nonneg (mul_nonneg sixAdaptiveMomentConstant_pos.le (by positivity)) _)
      (Real.exp_pos _).le
  calc |Matrix.det (sixFunctional n)|
      ≤ ((rank n).factorial : ℝ) * sixBasisNormalization n *
          ((sixAdaptiveMomentConstant * (n : ℝ) ^ 38) ^ (15 * n) *
            Real.exp ((avg + gap / 4) * sixNorm n)) :=
        hdet.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
    _ ≤ Real.exp ((gap / 4) * sixNorm n) *
          Real.exp (((9 : ℝ) / 10 + 3 / 5 * Real.log (5 / 3) + gap / 4) * sixNorm n) *
          (Real.exp ((gap / 4) * sixNorm n) * Real.exp ((avg + gap / 4) * sixNorm n)) := by
        gcongr
    _ = Real.exp (R_bound * sixNorm n) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1; dsimp [gap]; ring

end OddZetaSix
