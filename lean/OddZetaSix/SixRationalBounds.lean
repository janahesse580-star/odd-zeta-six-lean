import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Computable Rational Bounds for `log`, `arctan`, and `π`

Self-contained rational enclosures adapted from `OddZetaMixed.RationalLogBounds`,
`OddZetaMixed.RationalArctanBounds`, and `OddZetaMixed.CompactPhase.Enclosure`:
- `RationalLogBounds`: atanh-series rational lower/upper bounds for `Real.log q`
  (both exact and common-denominator rounded) with kernel-checkable `Bool` predicates.
- `RationalArctanBounds`: alternating-series rational lower/upper bounds for
  `Real.arctan q` (`q ≥ 0`) and 20-digit rational bounds for `Real.pi`.
- `Enclosure`: proof-carrying interval `[lo, hi] ⊂ ℚ` around a real number `x : ℝ`,
  closed under `rat`, `add`, `sub`, `scale`, `sum`, `congr`, and `abs_le`.

Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix

/-! ## Part 1: Computable rational logarithm enclosures -/

namespace RationalLogBounds

open Finset

/-- Twice the first `n` terms of the atanh series. -/
def atanhLower (x : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1 : ℕ)

/-- Rational upper bound for the omitted tail when `0 ≤ x < 1`. -/
def atanhError (x : ℚ) (n : ℕ) : ℚ :=
  2 * (x ^ (2 * n + 1) / (1 - x ^ 2))

def atanhUpper (x : ℚ) (n : ℕ) : ℚ :=
  atanhLower x n + atanhError x n

theorem atanh_sound (x : ℚ) (n : ℕ) (h₀ : 0 ≤ x) (h₁ : x < 1) :
    (atanhLower x n : ℝ) ≤ Real.log ((1 + (x : ℝ)) / (1 - (x : ℝ))) ∧
      Real.log ((1 + (x : ℝ)) / (1 - (x : ℝ))) ≤ (atanhUpper x n : ℝ) := by
  have h₀R : (0 : ℝ) ≤ x := by exact_mod_cast h₀
  have h₁R : (x : ℝ) < 1 := by exact_mod_cast h₁
  have hl := Real.sum_range_le_log_div h₀R h₁R n
  have hu := Real.log_div_le_sum_range_add h₀R h₁R n
  dsimp only [atanhUpper, atanhLower, atanhError]
  push_cast
  constructor <;> linarith

/-- The atanh argument after reduction to `[1, 2]`. -/
def argument (y : ℚ) : ℚ := (y - 1) / (y + 1)

theorem argument_mem (y : ℚ) (hy : 1 ≤ y ∧ y ≤ 2) :
    0 ≤ argument y ∧ argument y ≤ 1 / 3 := by
  have hd : 0 < y + 1 := by linarith [hy.1]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hy.1) hd.le
  · apply (div_le_iff₀ hd).mpr
    linarith [hy.2]

def unitLower (y : ℚ) (n : ℕ) : ℚ := atanhLower (argument y) n

def unitUpper (y : ℚ) (n : ℕ) : ℚ := atanhUpper (argument y) n

theorem unit_sound (y : ℚ) (n : ℕ) (hy : 1 ≤ y ∧ y ≤ 2) :
    (unitLower y n : ℝ) ≤ Real.log (y : ℝ) ∧
      Real.log (y : ℝ) ≤ (unitUpper y n : ℝ) := by
  have hx := argument_mem y hy
  have h := atanh_sound (argument y) n hx.1 (by linarith [hx.2])
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy.1
  have hd : (y : ℝ) + 1 ≠ 0 := by linarith
  have heq : (1 + (argument y : ℝ)) / (1 - (argument y : ℝ)) = (y : ℝ) := by
    unfold argument
    push_cast
    field_simp
    ring
  simpa only [unitLower, unitUpper, heq] using h

def logTwoLower (n : ℕ) : ℚ := unitLower 2 n

def logTwoUpper (n : ℕ) : ℚ := unitUpper 2 n

theorem logTwo_sound (n : ℕ) :
    (logTwoLower n : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (logTwoUpper n : ℝ) := by
  simpa only [logTwoLower, logTwoUpper, Rat.cast_ofNat] using
    unit_sound 2 n (by norm_num)

/-- Range-reduced mantissa `q / 2^k` for a caller-supplied exponent `k : ℤ`. -/
def mantissa (q : ℚ) (k : ℤ) : ℚ := q / (2 : ℚ) ^ k

def lower (q : ℚ) (k : ℤ) (n : ℕ) : ℚ :=
  unitLower (mantissa q k) n +
    (k : ℚ) * (if 0 ≤ k then logTwoLower n else logTwoUpper n)

def upper (q : ℚ) (k : ℤ) (n : ℕ) : ℚ :=
  unitUpper (mantissa q k) n +
    (k : ℚ) * (if 0 ≤ k then logTwoUpper n else logTwoLower n)

theorem log_eq_reduced (q : ℚ) (k : ℤ) (hq : 0 < q) :
    Real.log (q : ℝ) = Real.log (mantissa q k : ℝ) + (k : ℝ) * Real.log 2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hp : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  simp only [mantissa, Rat.cast_div, Rat.cast_zpow, Rat.cast_ofNat,
    Real.log_div hqR.ne' hp.ne', Real.log_zpow]
  ring

theorem sound (q : ℚ) (k : ℤ) (n : ℕ) (hq : 0 < q)
    (hscale : 1 ≤ mantissa q k ∧ mantissa q k ≤ 2) :
    (lower q k n : ℝ) ≤ Real.log (q : ℝ) ∧
      Real.log (q : ℝ) ≤ (upper q k n : ℝ) := by
  have hy := unit_sound (mantissa q k) n hscale
  have htwo := logTwo_sound n
  rw [log_eq_reduced q k hq]
  unfold lower upper
  by_cases hk : 0 ≤ k
  · simp only [ite_eq_left hk]
    push_cast
    have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk
    exact ⟨add_le_add hy.1 (mul_le_mul_of_nonneg_left htwo.1 hkR),
      add_le_add hy.2 (mul_le_mul_of_nonneg_left htwo.2 hkR)⟩
  · simp only [ite_eq_right hk]
    push_cast
    have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hk)
    exact ⟨add_le_add hy.1 (mul_le_mul_of_nonpos_left htwo.2 hkR),
      add_le_add hy.2 (mul_le_mul_of_nonpos_left htwo.1 hkR)⟩

theorem of_bounds (q : ℚ) (k : ℤ) (n : ℕ) (lo hi : ℚ) (hq : 0 < q)
    (hscale : 1 ≤ mantissa q k ∧ mantissa q k ≤ 2)
    (hlo : lo ≤ lower q k n) (hhi : upper q k n ≤ hi) :
    (lo : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (hi : ℝ) := by
  have h := sound q k n hq hscale
  have hloR : (lo : ℝ) ≤ lower q k n := by exact_mod_cast hlo
  have hhiR : (upper q k n : ℝ) ≤ hi := by exact_mod_cast hhi
  exact ⟨hloR.trans h.1, h.2.trans hhiR⟩

def check (q : ℚ) (k : ℤ) (n : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 < q ∧ 1 ≤ mantissa q k ∧ mantissa q k ≤ 2 ∧
    lo ≤ lower q k n ∧ upper q k n ≤ hi)

theorem of_check (q : ℚ) (k : ℤ) (n : ℕ) (lo hi : ℚ)
    (h : check q k n lo hi = true) :
    (lo : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (hi : ℝ) := by
  unfold check at h
  rcases of_decide_eq_true h with ⟨hq, hl, hu, hlo, hhi⟩
  exact of_bounds q k n lo hi hq ⟨hl, hu⟩ hlo hhi

/-- Directed rational rounding with denominator `d`. -/
def roundDown (d : ℕ) (a : ℚ) : ℚ := (⌊(d : ℚ) * a⌋ : ℤ) / (d : ℚ)

def roundUp (d : ℕ) (a : ℚ) : ℚ := (⌈(d : ℚ) * a⌉ : ℤ) / (d : ℚ)

theorem roundDown_le (d : ℕ) (hd : 0 < d) (a : ℚ) : roundDown d a ≤ a := by
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  apply (div_le_iff₀ hdQ).mpr
  simpa only [mul_comm] using Int.floor_le ((d : ℚ) * a)

theorem le_roundUp (d : ℕ) (hd : 0 < d) (a : ℚ) : a ≤ roundUp d a := by
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  apply (le_div_iff₀ hdQ).mpr
  simpa only [mul_comm] using Int.le_ceil ((d : ℚ) * a)

def roundedAtanhLower (x : ℚ) (n d : ℕ) : ℚ :=
  2 * ∑ i ∈ range n, roundDown d (x ^ (2 * i + 1) / (2 * i + 1 : ℕ))

def roundedAtanhUpper (x : ℚ) (n d : ℕ) : ℚ :=
  2 * (∑ i ∈ range n, roundUp d (x ^ (2 * i + 1) / (2 * i + 1 : ℕ))) +
    roundUp d (atanhError x n)

theorem roundedAtanh_outer (x : ℚ) (n d : ℕ) (hd : 0 < d) :
    roundedAtanhLower x n d ≤ atanhLower x n ∧
      atanhUpper x n ≤ roundedAtanhUpper x n d := by
  constructor
  · exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun _ _ => roundDown_le d hd _)) (by norm_num)
  · exact add_le_add (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun _ _ => le_roundUp d hd _)) (by norm_num))
      (le_roundUp d hd _)

def roundedUnitLower (y : ℚ) (n d : ℕ) : ℚ := roundedAtanhLower (argument y) n d

def roundedUnitUpper (y : ℚ) (n d : ℕ) : ℚ := roundedAtanhUpper (argument y) n d

def roundedLower (q : ℚ) (k : ℤ) (n d : ℕ) : ℚ :=
  roundedUnitLower (mantissa q k) n d +
    (k : ℚ) * (if 0 ≤ k then roundedUnitLower 2 n d else roundedUnitUpper 2 n d)

def roundedUpper (q : ℚ) (k : ℤ) (n d : ℕ) : ℚ :=
  roundedUnitUpper (mantissa q k) n d +
    (k : ℚ) * (if 0 ≤ k then roundedUnitUpper 2 n d else roundedUnitLower 2 n d)

theorem rounded_outer (q : ℚ) (k : ℤ) (n d : ℕ) (hd : 0 < d) :
    roundedLower q k n d ≤ lower q k n ∧
      upper q k n ≤ roundedUpper q k n d := by
  have hy := roundedAtanh_outer (argument (mantissa q k)) n d hd
  have htwo := roundedAtanh_outer (argument 2) n d hd
  unfold roundedLower roundedUpper lower upper
  by_cases hk : 0 ≤ k
  · simp only [ite_eq_left hk]
    have hkQ : (0 : ℚ) ≤ k := by exact_mod_cast hk
    exact ⟨add_le_add hy.1 (mul_le_mul_of_nonneg_left htwo.1 hkQ),
      add_le_add hy.2 (mul_le_mul_of_nonneg_left htwo.2 hkQ)⟩
  · simp only [ite_eq_right hk]
    have hkQ : (k : ℚ) ≤ 0 := by exact_mod_cast (le_of_not_ge hk)
    exact ⟨add_le_add hy.1 (mul_le_mul_of_nonpos_left htwo.2 hkQ),
      add_le_add hy.2 (mul_le_mul_of_nonpos_left htwo.1 hkQ)⟩

theorem rounded_sound (q : ℚ) (k : ℤ) (n d : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hscale : 1 ≤ mantissa q k ∧ mantissa q k ≤ 2) :
    (roundedLower q k n d : ℝ) ≤ Real.log (q : ℝ) ∧
      Real.log (q : ℝ) ≤ (roundedUpper q k n d : ℝ) := by
  have h := rounded_outer q k n d hd
  exact of_bounds q k n _ _ hq hscale h.1 h.2

def checkRounded (q : ℚ) (k : ℤ) (n d : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 < d ∧ 0 < q ∧ 1 ≤ mantissa q k ∧ mantissa q k ≤ 2 ∧
    lo ≤ roundedLower q k n d ∧ roundedUpper q k n d ≤ hi)

theorem of_checkRounded (q : ℚ) (k : ℤ) (n d : ℕ) (lo hi : ℚ)
    (h : checkRounded q k n d lo hi = true) :
    (lo : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (hi : ℝ) := by
  unfold checkRounded at h
  rcases of_decide_eq_true h with ⟨hd, hq, hl, hu, hlo, hhi⟩
  have hlog := rounded_sound q k n d hd hq ⟨hl, hu⟩
  have hloR : (lo : ℝ) ≤ roundedLower q k n d := by exact_mod_cast hlo
  have hhiR : (roundedUpper q k n d : ℝ) ≤ hi := by exact_mod_cast hhi
  exact ⟨hloR.trans hlog.1, hlog.2.trans hhiR⟩

end RationalLogBounds

/-! ## Part 2: Computable rational arctangent and `π` enclosures -/

namespace RationalArctanBounds

open Finset

def series (q : ℚ) (m : ℕ) : ℚ :=
  ∑ i ∈ range m, (-1 : ℚ) ^ i * q ^ (2 * i + 1) / (2 * i + 1)

def smallLower (q : ℚ) (n : ℕ) : ℚ := series q (2 * n)
def smallUpper (q : ℚ) (n : ℕ) : ℚ := series q (2 * n + 1)

private theorem series_cast (q : ℚ) (m : ℕ) :
    (series q m : ℝ) = ∑ i ∈ range m, (-1 : ℝ) ^ i * (q : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
  simp [series]

theorem small_sound (q : ℚ) (n : ℕ) (hq : 0 ≤ q) (hq1 : q < 1) :
    (smallLower q n : ℝ) ≤ Real.arctan (q : ℝ) ∧
      Real.arctan (q : ℝ) ≤ (smallUpper q n : ℝ) := by
  have hx : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have hx1 : (q : ℝ) < 1 := by exact_mod_cast hq1
  have hsum := (Real.hasSum_arctan (x := (q : ℝ)) (by
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
    exact hx1)).tendsto_sum_nat
  have hm : Antitone (fun i : ℕ => (q : ℝ) ^ (2 * i + 1) / (2 * i + 1)) := by
    intro i j hij
    apply div_le_div₀ (by positivity)
      (pow_le_pow_of_le_one hx hx1.le (by omega)) (by positivity)
    exact_mod_cast (show 2 * i + 1 ≤ 2 * j + 1 by omega)
  have hl := hm.alternating_series_le_tendsto (by simpa [div_eq_mul_inv, mul_assoc] using hsum) n
  have hu := hm.tendsto_le_alternating_series (by simpa [div_eq_mul_inv, mul_assoc] using hsum) n
  simpa [smallLower, smallUpper, series_cast, div_eq_mul_inv, mul_assoc] using And.intro hl hu

def piLower : ℚ := 314159265358979323846 / 100000000000000000000
def piUpper : ℚ := 314159265358979323847 / 100000000000000000000

theorem pi_sound : (piLower : ℝ) ≤ Real.pi ∧ Real.pi ≤ (piUpper : ℝ) := by
  constructor
  · norm_num [piLower]
    linarith [Real.pi_gt_d20]
  · norm_num [piUpper]
    linarith [Real.pi_lt_d20]

def lower (q : ℚ) (n : ℕ) : ℚ :=
  if q ≤ 1 / 2 then smallLower q n
  else if q ≤ 1 then piLower / 4 - smallUpper ((1 - q) / (1 + q)) n
  else if q ≤ 2 then piLower / 4 + smallLower ((q - 1) / (q + 1)) n
  else piLower / 2 - smallUpper (1 / q) n

def upper (q : ℚ) (n : ℕ) : ℚ :=
  if q ≤ 1 / 2 then smallUpper q n
  else if q ≤ 1 then piUpper / 4 - smallLower ((1 - q) / (1 + q)) n
  else if q ≤ 2 then piUpper / 4 + smallUpper ((q - 1) / (q + 1)) n
  else piUpper / 2 - smallLower (1 / q) n

private theorem arctan_reduction_below {x : ℝ} (hx : 0 ≤ x) (_hx1 : x ≤ 1) :
    Real.arctan x + Real.arctan ((1 - x) / (1 + x)) = Real.pi / 4 := by
  have hp : 0 < 1 + x := by linarith
  have hadd := Real.arctan_add (x := x) (y := (1 - x) / (1 + x)) (by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hp).2
    nlinarith [sq_nonneg x])
  have heq : (x + (1 - x) / (1 + x)) / (1 - x * ((1 - x) / (1 + x))) = 1 := by
    have hsq : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring_nf
    field_simp
    ring
  rw [heq, Real.arctan_one] at hadd
  exact hadd

private theorem arctan_reduction_above {x : ℝ} (hx : 1 ≤ x) :
    Real.pi / 4 + Real.arctan ((x - 1) / (x + 1)) = Real.arctan x := by
  have hp : 0 < x + 1 := by linarith
  have hadd := Real.arctan_add (x := (1 : ℝ)) (y := (x - 1) / (x + 1)) (by
    rw [one_mul]
    exact (div_lt_one hp).2 (by linarith))
  have heq : (1 + (x - 1) / (x + 1)) / (1 - 1 * ((x - 1) / (x + 1))) = x := by
    field_simp
    ring
  rw [heq, Real.arctan_one] at hadd
  exact hadd

theorem sound (q : ℚ) (n : ℕ) (hq : 0 ≤ q) :
    (lower q n : ℝ) ≤ Real.arctan (q : ℝ) ∧
      Real.arctan (q : ℝ) ≤ (upper q n : ℝ) := by
  have hx : (0 : ℝ) ≤ q := by exact_mod_cast hq
  rcases pi_sound with ⟨hpiL, hpiU⟩
  by_cases hhalf : q ≤ 1 / 2
  · simp only [lower, upper, ite_eq_left hhalf]
    exact small_sound q n hq (by linarith)
  by_cases hone : q ≤ 1
  · have hsmall := small_sound ((1 - q) / (1 + q)) n (by positivity)
      ((div_lt_one (by linarith : (0 : ℚ) < 1 + q)).2 (by linarith))
    have hadd := arctan_reduction_below hx (by exact_mod_cast hone)
    simp only [lower, upper, ite_eq_right hhalf, ite_eq_left hone]
    push_cast at hsmall ⊢
    constructor <;> linarith [hsmall.1, hsmall.2]
  by_cases htwo : q ≤ 2
  · have hq1 : 1 ≤ q := by linarith
    have hsmall := small_sound ((q - 1) / (q + 1)) n (div_nonneg (by linarith) (by linarith))
      ((div_lt_one (by linarith : (0 : ℚ) < q + 1)).2 (by linarith))
    have hadd := arctan_reduction_above (x := (q : ℝ)) (by exact_mod_cast (le_of_not_ge hone))
    simp only [lower, upper, ite_eq_right hhalf, ite_eq_right hone, ite_eq_left htwo]
    push_cast at hsmall ⊢
    constructor <;> linarith [hsmall.1, hsmall.2]
  · have hqpos : (0 : ℚ) < q := by linarith
    have hsmall := small_sound (1 / q) n (by positivity)
      ((div_lt_one hqpos).2 (by linarith))
    have hinv := Real.arctan_inv_of_pos (x := (q : ℝ)) (by exact_mod_cast hqpos)
    simp only [lower, upper, ite_eq_right hhalf, ite_eq_right hone, ite_eq_right htwo]
    push_cast at hsmall ⊢
    simp only [one_div] at hsmall ⊢
    constructor <;> linarith [hsmall.1, hsmall.2]

/-- Directed rounded alternating-series bounds for `arctan q` (`q ≥ 0`). -/
def roundedSmallLower (q : ℚ) (n d : ℕ) : ℚ :=
  ∑ i ∈ range (2 * n),
    RationalLogBounds.roundDown d ((-1 : ℚ) ^ i * q ^ (2 * i + 1) / (2 * i + 1))

def roundedSmallUpper (q : ℚ) (n d : ℕ) : ℚ :=
  ∑ i ∈ range (2 * n + 1),
    RationalLogBounds.roundUp d ((-1 : ℚ) ^ i * q ^ (2 * i + 1) / (2 * i + 1))

theorem roundedSmall_outer (q : ℚ) (n d : ℕ) (hd : 0 < d) :
    roundedSmallLower q n d ≤ smallLower q n ∧
      smallUpper q n ≤ roundedSmallUpper q n d := by
  exact ⟨Finset.sum_le_sum (fun _ _ => RationalLogBounds.roundDown_le d hd _),
    Finset.sum_le_sum (fun _ _ => RationalLogBounds.le_roundUp d hd _)⟩

def roundedLower (q : ℚ) (n d : ℕ) : ℚ :=
  if q ≤ 1 / 2 then roundedSmallLower q n d
  else if q ≤ 1 then piLower / 4 - roundedSmallUpper ((1 - q) / (1 + q)) n d
  else if q ≤ 2 then piLower / 4 + roundedSmallLower ((q - 1) / (q + 1)) n d
  else piLower / 2 - roundedSmallUpper (1 / q) n d

def roundedUpper (q : ℚ) (n d : ℕ) : ℚ :=
  if q ≤ 1 / 2 then roundedSmallUpper q n d
  else if q ≤ 1 then piUpper / 4 - roundedSmallLower ((1 - q) / (1 + q)) n d
  else if q ≤ 2 then piUpper / 4 + roundedSmallUpper ((q - 1) / (q + 1)) n d
  else piUpper / 2 - roundedSmallLower (1 / q) n d

theorem rounded_outer (q : ℚ) (n d : ℕ) (hd : 0 < d) :
    roundedLower q n d ≤ lower q n ∧ upper q n ≤ roundedUpper q n d := by
  unfold roundedLower roundedUpper lower upper
  split_ifs
  · exact roundedSmall_outer q n d hd
  · have h := roundedSmall_outer ((1 - q) / (1 + q)) n d hd
    exact ⟨by linarith, by linarith⟩
  · have h := roundedSmall_outer ((q - 1) / (q + 1)) n d hd
    exact ⟨by linarith, by linarith⟩
  · have h := roundedSmall_outer (1 / q) n d hd
    exact ⟨by linarith, by linarith⟩

theorem rounded_sound (q : ℚ) (n d : ℕ) (hd : 0 < d) (hq : 0 ≤ q) :
    (roundedLower q n d : ℝ) ≤ Real.arctan (q : ℝ) ∧
      Real.arctan (q : ℝ) ≤ (roundedUpper q n d : ℝ) := by
  have hs := sound q n hq
  have ho := rounded_outer q n d hd
  exact ⟨(by exact_mod_cast ho.1 : (roundedLower q n d : ℝ) ≤ lower q n).trans hs.1,
    hs.2.trans (by exact_mod_cast ho.2)⟩

def check (q : ℚ) (n : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 ≤ q ∧ lo ≤ lower q n ∧ upper q n ≤ hi)

theorem of_check (q : ℚ) (n : ℕ) (lo hi : ℚ) (h : check q n lo hi = true) :
    (lo : ℝ) ≤ Real.arctan (q : ℝ) ∧ Real.arctan (q : ℝ) ≤ (hi : ℝ) := by
  have hc : 0 ≤ q ∧ lo ≤ lower q n ∧ upper q n ≤ hi := by simpa [check] using h
  have hreal := sound q n hc.1
  exact ⟨(by exact_mod_cast hc.2.1 : (lo : ℝ) ≤ (lower q n : ℝ)).trans hreal.1,
    hreal.2.trans (by exact_mod_cast hc.2.2)⟩

def checkRounded (q : ℚ) (n d : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 < d ∧ 0 ≤ q ∧ lo ≤ roundedLower q n d ∧ roundedUpper q n d ≤ hi)

theorem of_checkRounded (q : ℚ) (n d : ℕ) (lo hi : ℚ)
    (h : checkRounded q n d lo hi = true) :
    (lo : ℝ) ≤ Real.arctan (q : ℝ) ∧ Real.arctan (q : ℝ) ≤ (hi : ℝ) := by
  unfold checkRounded at h
  rcases of_decide_eq_true h with ⟨hd, hq, hlo, hhi⟩
  have hreal := rounded_sound q n d hd hq
  exact ⟨(by exact_mod_cast hlo : (lo : ℝ) ≤ roundedLower q n d).trans hreal.1,
    hreal.2.trans (by exact_mod_cast hhi)⟩

end RationalArctanBounds

/-! ## Part 3: Proof-carrying rational enclosures -/

/-- A proof-carrying rational interval `[lo, hi]` enclosing `x : ℝ`. -/
structure Enclosure (x : ℝ) where
  lo : ℚ
  hi : ℚ
  lower : (lo : ℝ) ≤ x
  upper : x ≤ (hi : ℝ)

namespace Enclosure

def rat (q : ℚ) : Enclosure (q : ℝ) := ⟨q, q, le_rfl, le_rfl⟩

def pi : Enclosure Real.pi :=
  ⟨RationalArctanBounds.piLower, RationalArctanBounds.piUpper,
    RationalArctanBounds.pi_sound.1, RationalArctanBounds.pi_sound.2⟩

def add {x y : ℝ} (a : Enclosure x) (b : Enclosure y) : Enclosure (x + y) where
  lo := a.lo + b.lo
  hi := a.hi + b.hi
  lower := by push_cast; exact add_le_add a.lower b.lower
  upper := by push_cast; exact add_le_add a.upper b.upper

def sub {x y : ℝ} (a : Enclosure x) (b : Enclosure y) : Enclosure (x - y) where
  lo := a.lo - b.hi
  hi := a.hi - b.lo
  lower := by push_cast; exact sub_le_sub a.lower b.upper
  upper := by push_cast; exact sub_le_sub a.upper b.lower

def scale {x : ℝ} (q : ℚ) (a : Enclosure x) : Enclosure ((q : ℝ) * x) where
  lo := if 0 ≤ q then q * a.lo else q * a.hi
  hi := if 0 ≤ q then q * a.hi else q * a.lo
  lower := by
    split_ifs with h
    · push_cast; exact mul_le_mul_of_nonneg_left a.lower (by exact_mod_cast h)
    · push_cast; exact mul_le_mul_of_nonpos_left a.upper (by exact_mod_cast le_of_not_ge h)
  upper := by
    split_ifs with h
    · push_cast; exact mul_le_mul_of_nonneg_left a.upper (by exact_mod_cast h)
    · push_cast; exact mul_le_mul_of_nonpos_left a.lower (by exact_mod_cast le_of_not_ge h)

def sum {ι : Type*} [Fintype ι] {x : ι → ℝ} (a : ∀ i, Enclosure (x i)) :
    Enclosure (∑ i, x i) where
  lo := ∑ i, (a i).lo
  hi := ∑ i, (a i).hi
  lower := by push_cast; exact Finset.sum_le_sum (fun i _ => (a i).lower)
  upper := by push_cast; exact Finset.sum_le_sum (fun i _ => (a i).upper)

def congr {x y : ℝ} (a : Enclosure x) (h : x = y) : Enclosure y :=
  ⟨a.lo, a.hi, h ▸ a.lower, h ▸ a.upper⟩

theorem abs_le {x : ℝ} (a : Enclosure x) : |x| ≤ (max |a.lo| |a.hi| : ℚ) := by
  rw [_root_.abs_le]
  push_cast
  exact ⟨(neg_le_neg (le_max_left |(a.lo : ℝ)| |(a.hi : ℝ)|)).trans
      ((neg_abs_le (a.lo : ℝ)).trans a.lower),
    a.upper.trans (le_max_of_le_right (le_abs_self _))⟩

end Enclosure

end OddZetaSix
