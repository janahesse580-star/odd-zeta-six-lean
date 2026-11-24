import OddZetaSix.EvenBasis
import OddZetaSix.ProperFractions
import OddZetaSix.FourthDerivative
import OddZetaSix.ZetaTail
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Nodup
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Six-Value Kernel (`local50-45-209`), Reflection, Decay, Partial Fractions, and Functional

Implements Section 1 of `zeta6_irrationality_proof.tex` for the winning profile
`local50-45-209`:
* `L = 50`, `U = 45`, `R = 95`, `h = 15 * n`, `θ = 3 / 10`
* `zeros = [40, 40, 40, 41, 43]`
* `offsets = [0, 0, 0, 0, 0, 2, 4, 5, 5, 6, 8, 9, 9, 11]`

Proves without `sorry` or `native_decide`:
1. Exact numerator/denominator degrees and the decay inequality
   `∑ (L - 2 d_b) - 2 ∑ z_a > 4 L θ` together with `O(t^{-2})` decay at infinity.
2. Odd reflection symmetry of `R_n(t)` and `R_n(t) E_i(t + c_n) E_j(t + c_n)`
   under `t ↦ -2 c_n - t` (`c_n = 70 n + 1`).
3. Fivefold protected zeros at `-40 n, ..., -1` away from all poles.
4. Unique strictly proper partial-fraction decomposition, vanishing of the
   simple-residue sum (`ζ(5)` cancellation), and the convergent fourth-derivative
   functional `sixFunctional`.
-/

noncomputable section
set_option autoImplicit false

namespace OddZetaSix

open Polynomial Finset
open scoped BigOperators Topology

/-! ## Parameters for `local50-45-209` -/

def paramL : ℕ := 50
def paramU : ℕ := 45
def paramR : ℕ := paramU + paramL
def rank (n : ℕ) : ℕ := 15 * n
def paramTheta : ℚ := 3 / 10
def paramS : ℕ := 40

def zerosList : List ℕ := [40, 40, 40, 41, 43]
def offsetsList : List ℕ := [0, 0, 0, 0, 0, 2, 4, 5, 5, 6, 8, 9, 9, 11]

def sixZero : Fin 5 → ℕ := ![40, 40, 40, 41, 43]
def sixOffset : Fin 14 → ℕ := ![0, 0, 0, 0, 0, 2, 4, 5, 5, 6, 8, 9, 9, 11]

/-- Integer reflection center `c_n = (U + R) n / 2 + 1 = 70 n + 1`. -/
def sixCenter (n : ℕ) : ℕ := 70 * n + 1

theorem paramR_eq : paramR = 95 := rfl

theorem two_mul_sixCenter (n : ℕ) : 2 * sixCenter n = (paramU + paramR) * n + 2 := by
  unfold sixCenter paramR paramU paramL
  ring

theorem sixZero_ge_paramS (a : Fin 5) : paramS ≤ sixZero a := by
  fin_cases a <;> decide

theorem sixOffset_le_eleven (b : Fin 14) : sixOffset b ≤ 11 := by
  fin_cases b <;> decide

theorem two_mul_sixOffset_le_L (b : Fin 14) : 2 * sixOffset b ≤ paramL := by
  have := sixOffset_le_eleven b
  unfold paramL
  omega

theorem sixZero_sum : (∑ a : Fin 5, sixZero a) = 204 := by decide

theorem sixOffset_sum : (∑ b : Fin 14, sixOffset b) = 59 := by decide

theorem six_block_length_sum : (∑ b : Fin 14, (paramL - 2 * sixOffset b)) = 582 := by decide

/-- The paper's degree decay inequality `∑_b (L - 2 d_b) - 2 ∑_a z_a > 4 L θ`. -/
theorem six_degree_decay_inequality :
    4 * (paramL : ℚ) * paramTheta <
      (∑ b : Fin 14, (paramL - 2 * sixOffset b) : ℕ) -
        2 * (∑ a : Fin 5, sixZero a : ℕ) := by
  rw [six_block_length_sum, sixZero_sum]
  norm_num [paramL, paramTheta]

/-! ## Rising factorials and kernel definition -/

/-- Polynomial rising factorial `∏_{j=0}^{k-1} (X + a + j)`. -/
def rising (a : ℚ) (k : ℕ) : ℚ[X] :=
  ∏ j ∈ range k, (X + C (a + j))

theorem rising_monic (a : ℚ) (k : ℕ) : (rising a k).Monic := by
  apply monic_prod_of_monic
  intro j _
  exact monic_X_add_C _

theorem rising_degree (a : ℚ) (k : ℕ) : (rising a k).natDegree = k := by
  rw [rising, natDegree_prod_of_monic]
  · simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  · intro j _
    exact monic_X_add_C _

/-- Unnormalized monic numerator of `R_n(t)`. -/
def sixNumerator (n : ℕ) : ℚ[X] :=
  (X + C (70 * (n : ℚ) + 1)) * ∏ a : Fin 5,
    rising 1 (sixZero a * n) *
      rising (140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ)) (sixZero a * n)

/-- Unreduced monic denominator of `R_n(t)` with 14 nested blocks. -/
def sixDenominator (n : ℕ) : ℚ[X] :=
  ∏ b : Fin 14, rising (((45 + sixOffset b) * n : ℕ) + 1) ((50 - 2 * sixOffset b) * n + 1)

/-- Exact rational factorial normalization of `R_n(t)`. -/
def sixNormalization (n : ℕ) : ℚ :=
  2 * (∏ b : Fin 14, (Nat.factorial ((50 - 2 * sixOffset b) * n) : ℚ)) /
    (∏ a : Fin 5, (Nat.factorial (sixZero a * n) : ℚ) ^ 2)

/-- The nested-pole rational kernel `R_n(t)` in `RatFunc ℚ`. -/
def sixKernel (n : ℕ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (C (sixNormalization n) * sixNumerator n) /
    algebraMap ℚ[X] (RatFunc ℚ) (sixDenominator n)

/-- The centered even-basis product `E_i(t + c_n) E_j(t + c_n)`. -/
def centeredMultiplier (n i j : ℕ) : ℚ[X] :=
  (evenBasis i * evenBasis j).comp (X + C (70 * (n : ℚ) + 1))

/-- The rational function `R_n(t) E_i(t + c_n) E_j(t + c_n)`. -/
def matrixEntryKernel (n i j : ℕ) : RatFunc ℚ :=
  sixKernel n * algebraMap ℚ[X] (RatFunc ℚ) (centeredMultiplier n i j)

/-! ## Degrees and strict decay -/

theorem sixNumerator_monic (n : ℕ) : (sixNumerator n).Monic := by
  apply (monic_X_add_C _).mul
  apply monic_prod_of_monic
  intro a _
  exact (rising_monic _ _).mul (rising_monic _ _)

theorem sixDenominator_monic (n : ℕ) : (sixDenominator n).Monic := by
  apply monic_prod_of_monic
  intro b _
  exact rising_monic _ _

theorem sixNumerator_degree (n : ℕ) : (sixNumerator n).natDegree = 408 * n + 1 := by
  unfold sixNumerator
  rw [natDegree_mul (monic_X_add_C _).ne_zero
    (monic_prod_of_monic _ _ (fun a _ => (rising_monic _ _).mul (rising_monic _ _))).ne_zero]
  rw [natDegree_X_add_C]
  rw [natDegree_prod_of_monic _ _ (fun a _ => (rising_monic _ _).mul (rising_monic _ _))]
  simp_rw [natDegree_mul (rising_monic _ _).ne_zero (rising_monic _ _).ne_zero, rising_degree]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, sixZero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]
  omega

theorem sixDenominator_degree (n : ℕ) : (sixDenominator n).natDegree = 582 * n + 14 := by
  rw [sixDenominator, natDegree_prod_of_monic _ _ (fun b _ => rising_monic _ _)]
  simp_rw [rising_degree]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, sixOffset, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]
  omega

theorem sixNormalization_ne_zero (n : ℕ) : sixNormalization n ≠ 0 := by
  unfold sixNormalization
  apply div_ne_zero
  · apply mul_ne_zero (by norm_num)
    apply Finset.prod_ne_zero_iff.mpr
    intro b _
    exact_mod_cast Nat.factorial_ne_zero _
  · apply Finset.prod_ne_zero_iff.mpr
    intro a _
    apply pow_ne_zero
    exact_mod_cast Nat.factorial_ne_zero _

theorem sixKernel_degree (n : ℕ) :
    (sixKernel n).intDegree = -174 * (n : ℤ) - 13 := by
  have hn : C (sixNormalization n) * sixNumerator n ≠ 0 :=
    mul_ne_zero (by simpa using sixNormalization_ne_zero n) (sixNumerator_monic n).ne_zero
  have hd := (sixDenominator_monic n).ne_zero
  have hinj := IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  have hn' : algebraMap ℚ[X] (RatFunc ℚ) (C (sixNormalization n) * sixNumerator n) ≠ 0 :=
    by simpa only [map_zero] using hinj.ne hn
  have hd' : algebraMap ℚ[X] (RatFunc ℚ) (sixDenominator n) ≠ 0 :=
    by simpa only [map_zero] using hinj.ne hd
  rw [sixKernel, RatFunc.intDegree_div hn' hd', RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial, natDegree_C_mul (sixNormalization_ne_zero n),
    sixNumerator_degree, sixDenominator_degree]
  push_cast
  ring

theorem sixKernel_ne_zero (n : ℕ) : sixKernel n ≠ 0 := by
  intro h
  have hd := sixKernel_degree n
  rw [h, RatFunc.intDegree_zero] at hd
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg _
  omega

theorem centeredMultiplier_ne_zero (n i j : ℕ) : centeredMultiplier n i j ≠ 0 := by
  apply comp_X_add_C_ne_zero_iff.mpr
  exact mul_ne_zero (evenBasis_ne_zero i) (evenBasis_ne_zero j)

theorem centeredMultiplier_degree (n i j : ℕ) :
    (centeredMultiplier n i j).natDegree = 2 * i + 2 * j := by
  rw [centeredMultiplier, natDegree_comp,
    natDegree_mul (evenBasis_ne_zero i) (evenBasis_ne_zero j),
    evenBasis_natDegree, evenBasis_natDegree, natDegree_X_add_C, mul_one]

theorem matrixEntryKernel_degree (n i j : ℕ) :
    (matrixEntryKernel n i j).intDegree = -174 * (n : ℤ) - 13 + 2 * (i : ℤ) + 2 * (j : ℤ) := by
  have hinj := IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  have hm : algebraMap ℚ[X] (RatFunc ℚ) (centeredMultiplier n i j) ≠ 0 := by
    simpa only [map_zero] using hinj.ne (centeredMultiplier_ne_zero n i j)
  rw [matrixEntryKernel, RatFunc.intDegree_mul (sixKernel_ne_zero n) hm,
    sixKernel_degree, RatFunc.intDegree_polynomial, centeredMultiplier_degree]
  push_cast
  ring

/-- Every entry at rank `h = 15 n` decays strictly faster than `t^{-2}` (in fact `≤ -114n - 17`). -/
theorem six_entry_degree_bound (n : ℕ) (i j : Fin (rank n)) :
    (matrixEntryKernel n i j).intDegree ≤ -114 * (n : ℤ) - 17 := by
  rw [matrixEntryKernel_degree]
  have hi : i.val < 15 * n := i.isLt
  have hj : j.val < 15 * n := j.isLt
  omega

theorem six_entry_degree_le_neg_two (n : ℕ) (i j : Fin (rank n)) :
    (matrixEntryKernel n i j).intDegree ≤ -2 := by
  have hb := six_entry_degree_bound n i j
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg _
  omega

/-! ## Protected fivefold zeros at `-40 n, ..., -1` -/

theorem rising_linear_factor_dvd (k m : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
    X + C (k : ℚ) ∣ rising 1 m := by
  have hmem : k - 1 ∈ range m := by simp only [mem_range]; omega
  have h := Finset.dvd_prod_of_mem (fun j : ℕ => (X + C ((1 : ℚ) + j))) hmem
  have heq : (1 : ℚ) + ((k - 1 : ℕ) : ℚ) = k := by
    rw [Nat.cast_sub hk]
    norm_num
  simpa only [heq, rising] using h

theorem protected_fifth_power_dvd (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ 40 * n) :
    (X + C (k : ℚ)) ^ 5 ∣ sixNumerator n := by
  have hb (a : Fin 5) (_ha : a ∈ (Finset.univ : Finset (Fin 5))) :
      X + C (k : ℚ) ∣ rising 1 (sixZero a * n) *
        rising (140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ)) (sixZero a * n) := by
    apply dvd_mul_of_dvd_left
    apply rising_linear_factor_dvd k _ hk
    have ha' : 40 ≤ sixZero a := sixZero_ge_paramS a
    nlinarith
  have hp := Finset.prod_dvd_prod_of_dvd (s := (Finset.univ : Finset (Fin 5)))
    (fun _ => X + C (k : ℚ)) _ hb
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  exact dvd_mul_of_dvd_right hp _

theorem protected_numerator_derivatives (n k j : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ 40 * n) (hj : j ≤ 4) :
    (Polynomial.derivative^[j] (sixNumerator n)).eval (-(k : ℚ)) = 0 := by
  have hdiv := pow_sub_dvd_iterate_derivative_of_pow_dvd j (protected_fifth_power_dvd n k hk hkn)
  have hpow : X + C (k : ℚ) ∣ (X + C (k : ℚ)) ^ (5 - j) := dvd_pow_self _ (by omega)
  obtain ⟨q, hq⟩ := hpow.trans hdiv
  rw [hq]
  simp

theorem protected_denominator_pos (n k : ℕ) (hkn : k ≤ 40 * n) :
    0 < (sixDenominator n).eval (-(k : ℚ)) := by
  simp only [sixDenominator, rising, eval_prod]
  apply Finset.prod_pos
  intro b _
  apply Finset.prod_pos
  intro j _
  simp only [eval_add, eval_X, eval_C]
  have hnat : k < (45 + sixOffset b) * n + 1 + j := by nlinarith
  have hrat : (k : ℚ) < (((45 + sixOffset b) * n + 1 + j : ℕ) : ℚ) := by exact_mod_cast hnat
  push_cast at hrat ⊢
  linarith

/-! ## Odd reflection symmetry under `t ↦ -2 c_n - t` (`X ↦ -X - (140 n + 2)`) -/

theorem rising_reflection (a s : ℚ) (k : ℕ) :
    (rising a k).comp (-X - C s) =
      (-1 : ℚ[X]) ^ k * rising (s - a - k + 1) k := by
  simp only [rising, Polynomial.prod_comp, add_comp, X_comp, C_comp]
  calc
    ∏ j ∈ range k, (-X - C s + C (a + j)) =
        ∏ j ∈ range k,
          (-1 : ℚ[X]) * (X + C (s - a - k + 1 + (k - 1 - j : ℕ))) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hjk : j < k := mem_range.mp hj
      have hcast : ((k - 1 - j : ℕ) : ℚ) = (k : ℚ) - 1 - j := by
        rw [Nat.cast_sub (by omega : j ≤ k - 1),
          Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      rw [hcast]
      simp only [map_add, map_sub, map_one]
      ring
    _ = (-1 : ℚ[X]) ^ k * ∏ j ∈ range k, (X + C (s - a - k + 1 + j)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        Finset.prod_range_reflect (fun j : ℕ => (X : ℚ[X]) + C (s - a - k + 1 + j)) k]

theorem rising_pair_reflection (s : ℚ) (k : ℕ) :
    (rising 1 k * rising (s - k) k).comp (-X - C s) =
      rising 1 k * rising (s - k) k := by
  rw [mul_comp, rising_reflection, rising_reflection,
    show s - 1 - k + 1 = s - k by ring,
    show s - (s - k) - k + 1 = (1 : ℚ) by ring]
  have hsign : (-1 : ℚ[X]) ^ k * (-1 : ℚ[X]) ^ k = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = ((-1 : ℚ[X]) ^ k * (-1 : ℚ[X]) ^ k) *
        (rising 1 k * rising (s - k) k) := by ring
    _ = _ := by rw [hsign, one_mul]

theorem sixNumerator_reflection (n : ℕ) :
    (sixNumerator n).comp (-X - C (140 * (n : ℚ) + 2)) = -sixNumerator n := by
  have hcenter : (X + C (70 * (n : ℚ) + 1)).comp
      (-X - C (140 * (n : ℚ) + 2)) = -(X + C (70 * (n : ℚ) + 1)) := by
    rw [add_comp, X_comp, C_comp]
    simp only [map_add, map_mul, map_ofNat, map_one]
    ring
  unfold sixNumerator
  rw [mul_comp, hcenter, Polynomial.prod_comp]
  simp only [rising_pair_reflection, neg_mul]

theorem sixDenominator_block_odd (n : ℕ) (b : Fin 14) :
    Odd ((50 - 2 * sixOffset b) * n + 1) := by
  have hb := two_mul_sixOffset_le_L b
  unfold paramL at hb
  refine ⟨(25 - sixOffset b) * n, ?_⟩
  rw [show 50 - 2 * sixOffset b = 2 * (25 - sixOffset b) by omega]
  ring

theorem sixDenominator_block_reflection (n : ℕ) (b : Fin 14) :
    (rising (((45 + sixOffset b) * n : ℕ) + 1) ((50 - 2 * sixOffset b) * n + 1)).comp
        (-X - C (140 * (n : ℚ) + 2)) =
      -rising (((45 + sixOffset b) * n : ℕ) + 1) ((50 - 2 * sixOffset b) * n + 1) := by
  have hb := two_mul_sixOffset_le_L b
  unfold paramL at hb
  have hstart : 140 * (n : ℚ) + 2 - (((45 + sixOffset b) * n : ℕ) + 1) -
      (((50 - 2 * sixOffset b) * n + 1 : ℕ) : ℚ) + 1 =
      (((45 + sixOffset b) * n : ℕ) + 1) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hb, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [rising_reflection, hstart, (sixDenominator_block_odd n b).neg_one_pow, neg_one_mul]

/-- The 14 odd-length denominator blocks together are reflection-even. -/
theorem sixDenominator_reflection (n : ℕ) :
    (sixDenominator n).comp (-X - C (140 * (n : ℚ) + 2)) = sixDenominator n := by
  unfold sixDenominator
  rw [Polynomial.prod_comp]
  calc
    _ = ∏ b : Fin 14, -rising (((45 + sixOffset b) * n : ℕ) + 1)
          ((50 - 2 * sixOffset b) * n + 1) := by
      apply Finset.prod_congr rfl
      intro b _
      exact sixDenominator_block_reflection n b
    _ = _ := by rw [Finset.prod_neg]; norm_num

/-- `R_n(t)` is strictly odd under `t ↦ -2 c_n - t`. -/
theorem sixKernel_reflection (n : ℕ) :
    algebraMap ℚ[X] (RatFunc ℚ)
        ((C (sixNormalization n) * sixNumerator n).comp
          (-X - C (140 * (n : ℚ) + 2))) /
      algebraMap ℚ[X] (RatFunc ℚ)
        ((sixDenominator n).comp (-X - C (140 * (n : ℚ) + 2))) =
      -sixKernel n := by
  simp only [mul_comp, C_comp, sixNumerator_reflection, sixDenominator_reflection,
    mul_neg, map_neg, neg_div, sixKernel]

theorem centeredMultiplier_reflection (n i j : ℕ) :
    (centeredMultiplier n i j).comp (-X - C (140 * (n : ℚ) + 2)) =
      centeredMultiplier n i j := by
  apply Polynomial.funext
  intro t
  simp only [centeredMultiplier, eval_comp, eval_mul, eval_add, eval_X, eval_C,
    eval_sub, eval_neg]
  rw [show -t - (140 * (n : ℚ) + 2) + (70 * (n : ℚ) + 1) =
      -(t + (70 * (n : ℚ) + 1)) by ring,
    evenBasis_eval_neg, evenBasis_eval_neg]

theorem matrixEntryKernel_reflection (n i j : ℕ) :
    algebraMap ℚ[X] (RatFunc ℚ)
        ((C (sixNormalization n) * sixNumerator n * centeredMultiplier n i j).comp
          (-X - C (140 * (n : ℚ) + 2))) /
      algebraMap ℚ[X] (RatFunc ℚ)
        ((sixDenominator n).comp (-X - C (140 * (n : ℚ) + 2))) =
      -matrixEntryKernel n i j := by
  rw [mul_comp, centeredMultiplier_reflection, map_mul, mul_div_right_comm,
    sixKernel_reflection, neg_mul]
  rfl

/-! ## Poles, multiplicities, and unique partial fractions -/

/-- All pole addresses with full multiplicity across the 14 denominator blocks. -/
def sixPoleList (n : ℕ) : List ℕ :=
  (List.finRange 14).flatMap fun b =>
    (List.range ((50 - 2 * sixOffset b) * n + 1)).map fun j =>
      (45 + sixOffset b) * n + 1 + j

def sixPoleSet (n : ℕ) : Finset ℕ := (sixPoleList n).toFinset

def sixPoleOrder (n k : ℕ) : ℕ := (sixPoleList n).count k

private theorem list_flatMap_map_prod {α M : Type*} [CommMonoid M]
    (l : List α) (f : α → List ℕ) (g : ℕ → M) :
    ((l.flatMap f).map g).prod = (l.map fun b => ((f b).map g).prod).prod := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

private theorem range_map_prod_eq {M : Type*} [CommMonoid M] (m : ℕ) (f : ℕ → M) :
    ((List.range m).map f).prod = ∏ j ∈ range m, f j := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.prod_range_succ, ih]

private theorem finRange_map_prod_eq {M : Type*} [CommMonoid M] (m : ℕ) (f : Fin m → M) :
    ((List.finRange m).map f).prod = ∏ b : Fin m, f b := by
  rw [← Fin.prod_univ_def]

theorem six_denominator_list (n : ℕ) :
    sixDenominator n = ((sixPoleList n).map fun k : ℕ => X + C (k : ℚ)).prod := by
  simp only [sixPoleList, list_flatMap_map_prod, List.map_map, Function.comp_def]
  simp only [range_map_prod_eq, finRange_map_prod_eq]
  unfold sixDenominator rising
  apply Finset.prod_congr rfl
  intro b _
  apply Finset.prod_congr rfl
  intro j _
  congr 2
  push_cast
  ring

theorem six_denominator_powers (n : ℕ) :
    sixDenominator n = ∏ k ∈ sixPoleSet n, (X + C (k : ℚ)) ^ (sixPoleOrder n k) := by
  rw [six_denominator_list, Finset.prod_list_map_count (sixPoleList n)
    (fun k : ℕ => X + C (k : ℚ))]
  rfl

theorem six_pole_address_bounds (n k : ℕ) (hk : k ∈ sixPoleSet n) :
    45 * n + 1 ≤ k ∧ k ≤ 95 * n + 1 := by
  simp only [sixPoleSet, List.mem_toFinset, sixPoleList, List.mem_flatMap,
    List.mem_finRange, true_and, List.mem_map, List.mem_range] at hk
  obtain ⟨b, j, hj, rfl⟩ := hk
  have hb := two_mul_sixOffset_le_L b
  unfold paramL at hb
  have hsub : 50 - 2 * sixOffset b + 2 * sixOffset b = 50 := by omega
  constructor <;> nlinarith

theorem six_pole_order_positive (n k : ℕ) (hk : k ∈ sixPoleSet n) :
    0 < sixPoleOrder n k := by
  simpa only [sixPoleOrder, sixPoleSet, List.mem_toFinset] using
    (List.count_pos_iff.mpr (List.mem_toFinset.mp hk))

theorem list_count_flatMap {α : Type*} (l : List α) (f : α → List ℕ) (k : ℕ) :
    (l.flatMap f).count k = (l.map fun b => (f b).count k).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

/-- Pole orders are at most 14 (since there are 14 denominator blocks). -/
theorem six_pole_order_le (n k : ℕ) : sixPoleOrder n k ≤ 14 := by
  unfold sixPoleOrder sixPoleList
  rw [list_count_flatMap]
  have hb (b : Fin 14) :
      ((List.range ((50 - 2 * sixOffset b) * n + 1)).map
        fun j => (45 + sixOffset b) * n + 1 + j).count k ≤ 1 := by
    apply List.nodup_iff_count_le_one.mp
    apply (List.nodup_map_iff (fun _ _ h => Nat.add_left_cancel h)).mpr
    exact List.nodup_range
  calc
    _ ≤ ((List.finRange 14).map fun _ => 1).sum := List.sum_le_sum (fun b _ => hb b)
    _ = 14 := by decide

theorem six_pole_factors_coprime (n : ℕ) :
    Set.Pairwise (sixPoleSet n : Set ℕ) (fun k l : ℕ =>
      IsCoprime (X + C (k : ℚ)) (X + C (l : ℚ))) := by
  intro k _ l _ hkl
  have hinj : Function.Injective (fun j : ℕ => -(j : ℚ)) := by
    intro a b h
    exact_mod_cast neg_injective h
  simpa only [C_neg, sub_neg_eq_add] using
    (Polynomial.pairwise_coprime_X_sub_C hinj hkl)

private theorem constant_of_degree_lt_one (p : ℚ[X]) (hp : p.degree < 1) :
    p = C (p.coeff 0) := by
  have hcoeff := (degree_lt_iff_coeff_zero p 1).mp hp
  ext j
  by_cases hj : j = 0
  · simp [hj]
  · simp [coeff_C, hj, hcoeff j (by omega)]

def sixPrincipalTerm (k l : ℕ) (a : ℚ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (C a) /
    algebraMap ℚ[X] (RatFunc ℚ) ((X + C (k : ℚ)) ^ (l + 1))

theorem six_partial_fractions (n : ℕ) (i j : Fin (rank n)) :
    ∃ b : (k : ℕ) → Fin (sixPoleOrder n k) → ℚ,
      matrixEntryKernel n i j =
        ∑ k ∈ sixPoleSet n, ∑ l, sixPrincipalTerm k l.val (b k l) := by
  let f := C (sixNormalization n) * sixNumerator n * centeredMultiplier n i j
  let g : ℕ → ℚ[X] := fun k => X + C (k : ℚ)
  let gi : ℕ → RatFunc ℚ := fun k => (algebraMap ℚ[X] (RatFunc ℚ) (g k))⁻¹
  have hgi (k : ℕ) (_hk : k ∈ sixPoleSet n) :
      gi k * algebraMap ℚ[X] (RatFunc ℚ) (g k) = 1 := by
    apply inv_mul_cancel₀
    have hz := (monic_X_add_C (k : ℚ)).ne_zero
    simpa only [map_zero, g] using (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).ne hz
  obtain ⟨q, r, hr, heq⟩ :=
    mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse f
      (fun k (_ : k ∈ sixPoleSet n) => monic_X_add_C (k : ℚ))
      (six_pole_factors_coprime n) (sixPoleOrder n) hgi
  let b : (k : ℕ) → Fin (sixPoleOrder n k) → ℚ := fun k l => (r k l).coeff 0
  have hconstant (k : ℕ) (hk : k ∈ sixPoleSet n) (l : Fin (sixPoleOrder n k)) :
      r k l = C (b k l) := by
    apply constant_of_degree_lt_one
    simpa only [degree_X_add_C] using hr k hk l
  have hprod : (∏ k ∈ sixPoleSet n, gi k ^ sixPoleOrder n k) =
      (algebraMap ℚ[X] (RatFunc ℚ) (sixDenominator n))⁻¹ := by
    rw [six_denominator_powers, map_prod]
    simp only [gi, g, map_pow, Finset.prod_inv_distrib, inv_pow]
  have hleft : algebraMap ℚ[X] (RatFunc ℚ) f *
      ∏ k ∈ sixPoleSet n, gi k ^ sixPoleOrder n k = matrixEntryKernel n i j := by
    rw [hprod]
    simp only [f, map_mul, matrixEntryKernel, sixKernel, div_eq_mul_inv]
    ring
  have hsum : (∑ k ∈ sixPoleSet n, ∑ l,
      algebraMap ℚ[X] (RatFunc ℚ) (r k l) * gi k ^ (l.val + 1)) =
      ∑ k ∈ sixPoleSet n, ∑ l, sixPrincipalTerm k l.val (b k l) := by
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l _
    rw [hconstant k hk l]
    simp only [sixPrincipalTerm, gi, g, div_eq_mul_inv, map_pow, inv_pow]
  rw [hleft, hsum] at heq
  have hf : StrictlyProper (matrixEntryKernel n i j) := Or.inr (by
    have hdeg := six_entry_degree_le_neg_two n i j
    omega)
  have hs : StrictlyProper (∑ k ∈ sixPoleSet n, ∑ l,
      sixPrincipalTerm k l.val (b k l)) := by
    apply strictlyProper_sum
    intro k _
    apply strictlyProper_sum
    intro l _
    exact strictlyProper_principal _ _ _
  have hq := quotient_eq_zero_of_strictlyProper _ _ _ hf hs heq
  exact ⟨b, by simpa only [hq, map_zero, zero_add] using heq⟩

def sixPrincipalCoefficients (n : ℕ) (i j : Fin (rank n)) :
    (k : ℕ) → Fin (sixPoleOrder n k) → ℚ :=
  Classical.choose (six_partial_fractions n i j)

theorem sixPrincipalCoefficients_spec (n : ℕ) (i j : Fin (rank n)) :
    matrixEntryKernel n i j = ∑ k ∈ sixPoleSet n, ∑ l,
      sixPrincipalTerm k l.val (sixPrincipalCoefficients n i j k l) :=
  Classical.choose_spec (six_partial_fractions n i j)

theorem six_principal_coefficients_unique (n : ℕ)
    (a b : (k : ℕ) → Fin (sixPoleOrder n k) → ℚ)
    (h : (∑ k ∈ sixPoleSet n, ∑ l, sixPrincipalTerm k l.val (a k l)) =
      ∑ k ∈ sixPoleSet n, ∑ l, sixPrincipalTerm k l.val (b k l)) :
    ∀ k ∈ sixPoleSet n, a k = b k := by
  let gi : ℕ → RatFunc ℚ := fun k =>
    (algebraMap ℚ[X] (RatFunc ℚ) (X + C (k : ℚ)))⁻¹
  have hgi (k : ℕ) (_hk : k ∈ sixPoleSet n) :
      gi k * algebraMap ℚ[X] (RatFunc ℚ) (X + C (k : ℚ)) = 1 := by
    apply inv_mul_cancel₀
    simpa only [map_zero] using (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).ne
      (monic_X_add_C (k : ℚ)).ne_zero
  have hc (c : ℚ) (k : ℕ) : (C c).degree < (X + C (k : ℚ)).degree :=
    degree_C_le.trans_lt (by rw [degree_X_add_C]; norm_num)
  have heq : algebraMap ℚ[X] (RatFunc ℚ) 0 +
      (∑ k ∈ sixPoleSet n, ∑ l, algebraMap ℚ[X] (RatFunc ℚ) (C (a k l)) *
        gi k ^ (l.val + 1)) = algebraMap ℚ[X] (RatFunc ℚ) 0 +
      ∑ k ∈ sixPoleSet n, ∑ l, algebraMap ℚ[X] (RatFunc ℚ) (C (b k l)) *
        gi k ^ (l.val + 1) := by
    simpa only [map_zero, zero_add, sixPrincipalTerm, gi, div_eq_mul_inv,
      map_pow, inv_pow] using h
  have hu := quo_add_sum_rem_mul_pow_inverse_unique
    (fun k (_ : k ∈ sixPoleSet n) => monic_X_add_C (k : ℚ))
    (six_pole_factors_coprime n) hgi (fun k _ l => hc (a k l) k)
      (fun k _ l => hc (b k l) k) heq
  intro k hk
  funext l
  have hl := congrArg (fun f : Fin (sixPoleOrder n k) → ℚ[X] => (f l).coeff 0)
    (hu.2 k hk)
  simpa using hl

/-! ## Cleared polynomial identity and simple-residue cancellation (`ζ(5)` = 0) -/

def sixPoleComplement (n k l : ℕ) : ℚ[X] :=
  (X + C (k : ℚ)) ^ (sixPoleOrder n k - (l + 1)) *
    ∏ a ∈ (sixPoleSet n).erase k, (X + C (a : ℚ)) ^ (sixPoleOrder n a)

theorem sixPoleComplement_monic (n k l : ℕ) : (sixPoleComplement n k l).Monic := by
  apply ((monic_X_add_C _).pow _).mul
  apply monic_prod_of_monic
  intro a _
  exact (monic_X_add_C _).pow _

theorem sixPoleComplement_mul (n k l : ℕ) (hk : k ∈ sixPoleSet n)
    (hl : l < sixPoleOrder n k) :
    (X + C (k : ℚ)) ^ (l + 1) * sixPoleComplement n k l = sixDenominator n := by
  rw [sixPoleComplement, ← mul_assoc, ← pow_add, Nat.add_sub_of_le (by omega)]
  exact (Finset.mul_prod_erase (sixPoleSet n)
    (fun a : ℕ => (X + C (a : ℚ)) ^ (sixPoleOrder n a)) hk).trans
      (six_denominator_powers n).symm

theorem sixPoleComplement_degree (n k l : ℕ) (hk : k ∈ sixPoleSet n)
    (hl : l < sixPoleOrder n k) :
    (sixPoleComplement n k l).natDegree + (l + 1) = 582 * n + 14 := by
  have h := congrArg Polynomial.natDegree (sixPoleComplement_mul n k l hk hl)
  rw [natDegree_mul ((monic_X_add_C _).pow _).ne_zero
    (sixPoleComplement_monic n k l).ne_zero,
    (monic_X_add_C _).natDegree_pow, natDegree_X_add_C, mul_one,
    sixDenominator_degree] at h
  omega

theorem sixPrincipalTerm_clear (n k l : ℕ) (hk : k ∈ sixPoleSet n)
    (hl : l < sixPoleOrder n k) (a : ℚ) :
    algebraMap ℚ[X] (RatFunc ℚ) (sixDenominator n) * sixPrincipalTerm k l a =
      algebraMap ℚ[X] (RatFunc ℚ) (C a * sixPoleComplement n k l) := by
  have hne : algebraMap ℚ[X] (RatFunc ℚ) ((X + C (k : ℚ)) ^ (l + 1)) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).ne
      ((monic_X_add_C (k : ℚ)).pow (l + 1)).ne_zero
  rw [← sixPoleComplement_mul n k l hk hl]
  simp only [map_mul, sixPrincipalTerm]
  field_simp

theorem six_cleared_partial_fractions (n : ℕ) (i j : Fin (rank n)) :
    C (sixNormalization n) * sixNumerator n * centeredMultiplier n i j =
      ∑ k ∈ sixPoleSet n, ∑ l,
        C (sixPrincipalCoefficients n i j k l) * sixPoleComplement n k l.val := by
  apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  have h := congrArg (fun f : RatFunc ℚ =>
    algebraMap ℚ[X] (RatFunc ℚ) (sixDenominator n) * f)
      (sixPrincipalCoefficients_spec n i j)
  have hd : algebraMap ℚ[X] (RatFunc ℚ) (sixDenominator n) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).ne
      (sixDenominator_monic n).ne_zero
  simp only [Finset.mul_sum] at h
  have heach : (∑ k ∈ sixPoleSet n, ∑ l,
      algebraMap ℚ[X] (RatFunc ℚ) (sixDenominator n) *
      sixPrincipalTerm k l.val (sixPrincipalCoefficients n i j k l)) =
      algebraMap ℚ[X] (RatFunc ℚ) (∑ k ∈ sixPoleSet n, ∑ l,
        C (sixPrincipalCoefficients n i j k l) * sixPoleComplement n k l.val) := by
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l _
    exact sixPrincipalTerm_clear n k l.val hk l.isLt _
  rw [heach] at h
  calc
    _ = algebraMap ℚ[X] (RatFunc ℚ) (sixDenominator n) * matrixEntryKernel n i j := by
      simp only [matrixEntryKernel, sixKernel, map_mul]
      field_simp
    _ = _ := h

theorem sixPoleComplement_top_coeff (n k l : ℕ) (hk : k ∈ sixPoleSet n)
    (hl : l < sixPoleOrder n k) :
    (sixPoleComplement n k l).coeff (582 * n + 13) = if l = 0 then 1 else 0 := by
  have hd := sixPoleComplement_degree n k l hk hl
  by_cases hl0 : l = 0
  · rw [ite_eq_left_iff.mpr (fun h => (h hl0).elim)]
    have he : (sixPoleComplement n k l).natDegree = 582 * n + 13 := by omega
    rw [← he]
    exact (sixPoleComplement_monic n k l).coeff_natDegree
  · rw [ite_eq_right_iff.mpr (fun h => (hl0 h).elim)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem six_entry_numerator_top_coeff (n : ℕ) (i j : Fin (rank n)) :
    (C (sixNormalization n) * sixNumerator n * centeredMultiplier n i j).coeff
      (582 * n + 13) = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  rw [natDegree_mul
    (mul_ne_zero (by simpa using sixNormalization_ne_zero n) (sixNumerator_monic n).ne_zero)
    (centeredMultiplier_ne_zero n i j), natDegree_C_mul (sixNormalization_ne_zero n),
    sixNumerator_degree, centeredMultiplier_degree]
  have hi : i.val < 15 * n := i.isLt
  have hj : j.val < 15 * n := j.isLt
  omega

/-- The sum of all simple-pole residues vanishes, eliminating the `ζ(5)` term. -/
theorem six_residue_sum_zero (n : ℕ) (i j : Fin (rank n)) :
    (∑ k ∈ sixPoleSet n, ∑ l,
      if l.val = 0 then sixPrincipalCoefficients n i j k l else 0) = 0 := by
  have h := congrArg (fun p : ℚ[X] => p.coeff (582 * n + 13))
    (six_cleared_partial_fractions n i j)
  rw [six_entry_numerator_top_coeff] at h
  simp only [finsetSum_coeff, coeff_C_mul] at h
  symm
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l _
  rw [sixPoleComplement_top_coeff n k l.val hk l.isLt]
  split_ifs <;> simp

/-! ## Real evaluation, `O(t^{-2})` decay at infinity, and fourth-derivative functional -/

/-- Real evaluation of `R_n(x) E_i(x + c_n) E_j(x + c_n)`. -/
def sixEntryReal (n i j : ℕ) (x : ℝ) : ℝ :=
  aeval x (C (sixNormalization n) * sixNumerator n * centeredMultiplier n i j) /
    aeval x (sixDenominator n)

theorem six_pole_translate_pos (n k : ℕ) (hk : k ∈ sixPoleSet n)
    (x : ℝ) (hx : -(45 * (n : ℝ) + 1) < x) : 0 < x + (k : ℝ) := by
  have hb := (six_pole_address_bounds n k hk).1
  have hb' : 45 * (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hb
  linarith

theorem six_denominator_eval_pos (n : ℕ) (x : ℝ)
    (hx : -(45 * (n : ℝ) + 1) < x) : 0 < aeval x (sixDenominator n) := by
  rw [six_denominator_powers]
  simp only [map_prod, map_pow, map_add, aeval_X, map_natCast]
  exact Finset.prod_pos fun k hk => pow_pos (six_pole_translate_pos n k hk x hx) _

theorem sixPoleComplement_eval (n k l : ℕ) (hk : k ∈ sixPoleSet n)
    (hl : l < sixPoleOrder n k) (x : ℝ) (hx : -(45 * (n : ℝ) + 1) < x) :
    aeval x (sixPoleComplement n k l) =
      aeval x (sixDenominator n) / (x + (k : ℝ)) ^ (l + 1) := by
  have h := congrArg (fun P : ℚ[X] => aeval x P) (sixPoleComplement_mul n k l hk hl)
  simp only [map_mul, map_pow, map_add, aeval_X, map_natCast] at h
  exact (eq_div_iff (pow_ne_zero _ (ne_of_gt (six_pole_translate_pos n k hk x hx)))).mpr
    (by simpa only [mul_comm] using h)

theorem sixEntryReal_partial_fractions (n : ℕ) (i j : Fin (rank n))
    (x : ℝ) (hx : -(45 * (n : ℝ) + 1) < x) :
    sixEntryReal n i j x = ∑ k ∈ sixPoleSet n, ∑ l,
      (sixPrincipalCoefficients n i j k l : ℝ) / (x + (k : ℝ)) ^ (l.val + 1) := by
  unfold sixEntryReal
  rw [six_cleared_partial_fractions]
  simp only [map_sum, map_mul, aeval_C, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l _
  rw [sixPoleComplement_eval n k l.val hk l.isLt x hx]
  have hd := ne_of_gt (six_denominator_eval_pos n x hx)
  have hp := pow_ne_zero (l.val + 1) (ne_of_gt (six_pole_translate_pos n k hk x hx))
  field_simp
  simp

/-- Explicit `O(t^{-2})` decay at `+∞` for every matrix-entry kernel `R_n(t) E_i(t+c_n) E_j(t+c_n)`. -/
theorem sixEntryReal_isBigO_inv_sq (n : ℕ) (i j : Fin (rank n)) :
    (sixEntryReal n i j) =O[Filter.atTop] (fun x : ℝ => x ^ (-2 : ℤ)) := by
  rw [Asymptotics.isBigO_iff]
  let C0 : ℝ := ∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
    |(sixPrincipalCoefficients n i j k l : ℝ)| * (if l.val = 0 then (k : ℝ) else 1)
  refine ⟨C0, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx1
  have hxpos : 0 < x := by linarith
  have hxhalf : -(45 * (n : ℝ) + 1) < x := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hres0 : (∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
      (if l.val = 0 then (sixPrincipalCoefficients n i j k l : ℝ) else 0) / x) = 0 := by
    have hq := congrArg (fun q : ℚ => (q : ℝ) / x) (six_residue_sum_zero n i j)
    simp only [Rat.cast_sum, Rat.cast_zero, zero_div, Finset.sum_div, apply_ite] at hq
    exact hq
  have hrewrite : sixEntryReal n i j x =
      ∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
        if l.val = 0 then
          -((sixPrincipalCoefficients n i j k l : ℝ) * (k : ℝ)) / (x * (x + (k : ℝ)))
        else
          (sixPrincipalCoefficients n i j k l : ℝ) / (x + (k : ℝ)) ^ (l.val + 1) := by
    rw [sixEntryReal_partial_fractions n i j x hxhalf, ← sub_zero (∑ k ∈ sixPoleSet n, _),
      ← hres0, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    have hxk : 0 < x + (k : ℝ) := six_pole_translate_pos n k hk x hxhalf
    by_cases hl : l.val = 0
    · simp only [hl, ite_true, zero_add, pow_one]
      field_simp [hxpos.ne', hxk.ne']
      ring
    · simp only [hl, ite_false, zero_div, sub_zero]
  rw [hrewrite, Real.norm_eq_abs, Real.norm_eq_abs, zpow_neg, zpow_two, abs_inv,
    abs_mul, abs_of_pos hxpos]
  calc
    |∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k), _|
        ≤ ∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
            |if l.val = 0 then
              -((sixPrincipalCoefficients n i j k l : ℝ) * (k : ℝ)) / (x * (x + (k : ℝ)))
            else
              (sixPrincipalCoefficients n i j k l : ℝ) / (x + (k : ℝ)) ^ (l.val + 1)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
            (|(sixPrincipalCoefficients n i j k l : ℝ)| *
              (if l.val = 0 then (k : ℝ) else 1)) * (x * x)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l _
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hxk_ge : x ≤ x + (k : ℝ) := by linarith
      have hxk_pos : 0 < x + (k : ℝ) := by linarith
      by_cases hl : l.val = 0
      · simp only [hl, ite_true, abs_div, abs_neg, abs_mul, abs_of_nonneg hk0,
          abs_of_pos hxpos, abs_of_pos hxk_pos]
        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) hk0)
        exact inv_anti₀ (mul_pos hxpos hxpos) (mul_le_mul_of_nonneg_left hxk_ge hxpos.le)
      · simp only [hl, ite_false, mul_one, abs_div, abs_pow, abs_of_pos hxk_pos]
        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hge1 : 1 ≤ x + (k : ℝ) := by linarith
        have hpow_ge : x * x ≤ (x + (k : ℝ)) ^ (l.val + 1) := by
          have h2 : 2 ≤ l.val + 1 := by omega
          calc
            x * x = x ^ 2 := by ring
            _ ≤ (x + (k : ℝ)) ^ 2 := pow_le_pow_left₀ hxpos.le hxk_ge 2
            _ ≤ (x + (k : ℝ)) ^ (l.val + 1) := pow_le_pow_right₀ hge1 h2
        exact inv_anti₀ (mul_pos hxpos hxpos) hpow_ge
    _ = C0 * (x * x)⁻¹ := by
      simp only [C0, Finset.sum_mul]

theorem six_summation_point_in_halfline (n v : ℕ) :
    -(45 * (n : ℝ) + 1) < (v : ℝ) - 40 * (n : ℝ) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hv : (0 : ℝ) ≤ v := Nat.cast_nonneg v
  linarith

theorem sixEntryReal_eventuallyEq_partial_fractions (n : ℕ) (i j : Fin (rank n))
    (x : ℝ) (hx : -(45 * (n : ℝ) + 1) < x) :
    sixEntryReal n i j =ᶠ[𝓝 x]
      (fun t : ℝ => ∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
        (sixPrincipalCoefficients n i j k l : ℝ) / (t + (k : ℝ)) ^ (l.val + 1)) := by
  filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
  exact sixEntryReal_partial_fractions n i j t ht

/-- The normalized fourth derivative `(R_n E_i E_j)^{(4)}(x) / 4!` on the open half-line. -/
theorem sixEntryReal_fourthDerivative (n : ℕ) (i j : Fin (rank n))
    (x : ℝ) (hx : -(45 * (n : ℝ) + 1) < x) :
    iteratedDeriv 4 (sixEntryReal n i j) x / 24 =
      ∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
        (sixPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) /
          (x + (k : ℝ)) ^ (l.val + 5) := by
  have hsmooth (k : ℕ) (hk : k ∈ sixPoleSet n) :
      ContDiffAt ℝ 4 (fun t : ℝ => ∑ l : Fin (sixPoleOrder n k),
        (sixPrincipalCoefficients n i j k l : ℝ) / (t + (k : ℝ)) ^ (l.val + 1)) x := by
    apply ContDiffAt.sum
    intro l _
    exact contDiffAt_const_div_pow_add 4 (l.val + 1)
      (sixPrincipalCoefficients n i j k l : ℝ) x (k : ℝ)
      (ne_of_gt (six_pole_translate_pos n k hk x hx))
  rw [Filter.EventuallyEq.iteratedDeriv_eq 4
    (sixEntryReal_eventuallyEq_partial_fractions n i j x hx)]
  rw [iteratedDeriv_fun_sum hsmooth, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    fourthDerivative_finset_sum (Finset.univ : Finset (Fin (sixPoleOrder n k)))
      (fun l => (sixPrincipalCoefficients n i j k l : ℝ))
      (fun _ => (k : ℝ)) (fun l => l.val + 1) x
      (fun _ _ => by omega)
      (fun _ _ => ne_of_gt (six_pole_translate_pos n k hk x hx))

theorem sixEntryReal_fourthDerivative_at_index (n : ℕ) (i j : Fin (rank n)) (v : ℕ) :
    iteratedDeriv 4 (sixEntryReal n i j) ((v : ℝ) - 40 * (n : ℝ)) / 24 =
      ∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
        (sixPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) /
          ((v : ℝ) - 40 * (n : ℝ) + (k : ℝ)) ^ (l.val + 5) :=
  sixEntryReal_fourthDerivative n i j _ (six_summation_point_in_halfline n v)

/-- Summation of the normalized fourth derivative from `t = -40 n` to `+∞`. -/
theorem hasSum_sixEntryReal_fourthDerivative (n : ℕ) (i j : Fin (rank n)) :
    HasSum (fun v : ℕ =>
      iteratedDeriv 4 (sixEntryReal n i j) ((v : ℝ) - 40 * (n : ℝ)) / 24)
      (∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
        (sixPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) *
          (zetaNat (l.val + 5) - (harmonicCutoff (l.val + 5) (k - 40 * n - 1) : ℝ))) := by
  have hterm (k : ℕ) (hk : k ∈ sixPoleSet n) (l : Fin (sixPoleOrder n k)) :
      HasSum (fun v : ℕ =>
        (sixPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) /
          ((v : ℝ) - 40 * (n : ℝ) + (k : ℝ)) ^ (l.val + 5))
        ((sixPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) *
          (zetaNat (l.val + 5) - (harmonicCutoff (l.val + 5) (k - 40 * n - 1) : ℝ))) := by
    have hkstart : 40 * n < k := by
      have := (six_pole_address_bounds n k hk).1
      omega
    simpa only [Nat.add_assoc, Nat.reduceAdd, div_eq_mul_inv, one_mul] using
      (hasSum_six_shifted_inv_pow n k (l.val + 1) hkstart).mul_left
        ((sixPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ))
  have hsum := hasSum_sum (fun k hk => hasSum_sum
    (fun l (_ : l ∈ (Finset.univ : Finset (Fin (sixPoleOrder n k)))) => hterm k hk l))
  exact hsum.congr_fun (sixEntryReal_fourthDerivative_at_index n i j)

theorem summable_sixEntryReal_fourthDerivative (n : ℕ) (i j : Fin (rank n)) :
    Summable (fun v : ℕ =>
      iteratedDeriv 4 (sixEntryReal n i j) ((v : ℝ) - 40 * (n : ℝ)) / 24) :=
  (hasSum_sixEntryReal_fourthDerivative n i j).summable

/-- The actual six-value determinant matrix entry `(𝓗_n(ζ))_{ij}`. -/
def sixFunctional (n : ℕ) (i j : Fin (rank n)) : ℝ :=
  ∑' v : ℕ, iteratedDeriv 4 (sixEntryReal n i j) ((v : ℝ) - 40 * (n : ℝ)) / 24

theorem sixFunctional_eq_pole_sum (n : ℕ) (i j : Fin (rank n)) :
    sixFunctional n i j =
      ∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
        (sixPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) *
          (zetaNat (l.val + 5) - (harmonicCutoff (l.val + 5) (k - 40 * n - 1) : ℝ)) :=
  (hasSum_sixEntryReal_fourthDerivative n i j).tsum_eq

end OddZetaSix
