import OddZetaSix.SixFunctional
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-!
# Parity Cancellation, Six-Zeta Identity, and Primitive Determinant Polynomial

Implements the partial-fraction identity, parity/residue cancellations, formal
6-variable determinant matrix `𝓗_n(X)`, and primitive integer polynomial `P_n(X)`
of total degree at most `h = 15 n` from Section 1 of `zeta6_irrationality_proof.tex`.

Zero `sorry`, zero `native_decide`.
-/

noncomputable section
set_option autoImplicit false

namespace OddZetaSix

open Polynomial Finset

/-! ## Pole reflection and parity cancellation -/

def sixReflectedPole (n k : ℕ) : ℕ := 140 * n + 2 - k

private theorem interval_list_count (a d k : ℕ) :
    ((List.range (d + 1)).map (fun j => a + j)).count k =
      if a ≤ k ∧ k ≤ a + d then 1 else 0 := by
  have hmem : k ∈ (List.range (d + 1)).map (fun j => a + j) ↔
      a ≤ k ∧ k ≤ a + d := by
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      omega
    · rintro ⟨hk, hd⟩
      exact ⟨k - a, by omega, by omega⟩
  split_ifs with h
  · apply List.count_eq_one_of_mem
    · exact (List.nodup_map_iff (fun _ _ h => Nat.add_left_cancel h)).mpr
        List.nodup_range
    · exact hmem.mpr h
  · exact List.count_eq_zero_of_not_mem (fun hk => h (hmem.mp hk))

theorem six_pole_order_reflection (n k : ℕ) :
    sixPoleOrder n (sixReflectedPole n k) = sixPoleOrder n k := by
  unfold sixPoleOrder sixPoleList
  rw [list_count_flatMap, list_count_flatMap]
  congr 1
  apply List.map_congr_left
  intro b _
  have hb := two_mul_sixOffset_le_L b
  unfold paramL at hb
  rw [interval_list_count, interval_list_count]
  have hsub : 50 - 2 * sixOffset b + 2 * sixOffset b = 50 := by omega
  have hend : 2 * ((45 + sixOffset b) * n + 1) + (50 - 2 * sixOffset b) * n = 140 * n + 2 := by
    nlinarith
  have hiff : ((45 + sixOffset b) * n + 1 ≤ sixReflectedPole n k ∧
      sixReflectedPole n k ≤ (45 + sixOffset b) * n + 1 + (50 - 2 * sixOffset b) * n) ↔
      ((45 + sixOffset b) * n + 1 ≤ k ∧
        k ≤ (45 + sixOffset b) * n + 1 + (50 - 2 * sixOffset b) * n) := by
    unfold sixReflectedPole
    omega
  simp only [hiff]

theorem six_pole_mem_reflection (n k : ℕ) :
    sixReflectedPole n k ∈ sixPoleSet n ↔ k ∈ sixPoleSet n := by
  have hmem (a : ℕ) : a ∈ sixPoleSet n ↔ 0 < sixPoleOrder n a := by
    simp only [sixPoleSet, sixPoleOrder, List.mem_toFinset, List.count_pos_iff]
  rw [hmem, hmem, six_pole_order_reflection]

theorem six_pole_reflection_involutive (n k : ℕ) (hk : k ∈ sixPoleSet n) :
    sixReflectedPole n (sixReflectedPole n k) = k := by
  have hb := six_pole_address_bounds n k hk
  unfold sixReflectedPole
  omega

theorem six_sum_reflection {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    (∑ k ∈ sixPoleSet n, f (sixReflectedPole n k)) =
      ∑ k ∈ sixPoleSet n, f k := by
  apply Finset.sum_bij (fun k _ => sixReflectedPole n k)
  · intro k hk
    exact (six_pole_mem_reflection n k).mpr hk
  · intro k hk l hl h
    have := congrArg (sixReflectedPole n) h
    simpa only [six_pole_reflection_involutive n k hk,
      six_pole_reflection_involutive n l hl] using this
  · intro k hk
    exact ⟨sixReflectedPole n k, (six_pole_mem_reflection n k).mpr hk,
      six_pole_reflection_involutive n k hk⟩
  · intros
    rfl

theorem six_pole_factor_reflection (n k : ℕ) (hk : k ∈ sixPoleSet n) :
    (X + C (k : ℚ)).comp (-X - C (140 * (n : ℚ) + 2)) =
      -(X + C (sixReflectedPole n k : ℚ)) := by
  have hb := six_pole_address_bounds n k hk
  have hle : k ≤ 140 * n + 2 := by omega
  simp only [sixReflectedPole, Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, add_comp, X_comp, C_comp, map_sub, map_add, map_mul, map_ofNat]
  ring

theorem sixPoleComplement_reflection (n k l : ℕ) (hk : k ∈ sixPoleSet n)
    (hl : l < sixPoleOrder n k) :
    (sixPoleComplement n k l).comp (-X - C (140 * (n : ℚ) + 2)) =
      (-1 : ℚ[X]) ^ (l + 1) * sixPoleComplement n (sixReflectedPole n k) l := by
  have hr := (six_pole_mem_reflection n k).mpr hk
  have hlr : l < sixPoleOrder n (sixReflectedPole n k) := by
    rwa [six_pole_order_reflection]
  have h := congrArg (fun p : ℚ[X] => p.comp (-X - C (140 * (n : ℚ) + 2)))
    (sixPoleComplement_mul n k l hk hl)
  rw [mul_comp, pow_comp, six_pole_factor_reflection n k hk,
    sixDenominator_reflection, ← sixPoleComplement_mul n _ l hr hlr] at h
  have hs : (-1 : ℚ[X]) ^ (l + 1) * (-1 : ℚ[X]) ^ (l + 1) = 1 := by
    rw [← mul_pow]
    simp
  apply mul_left_cancel₀ ((monic_X_add_C (sixReflectedPole n k : ℚ)).pow (l + 1)).ne_zero
  rw [neg_pow] at h
  have h' := congrArg (fun p : ℚ[X] => (-1) ^ (l + 1) * p) h
  calc
    _ = ((-1 : ℚ[X]) ^ (l + 1) * (-1 : ℚ[X]) ^ (l + 1)) *
        ((X + C (sixReflectedPole n k : ℚ)) ^ (l + 1) *
          (sixPoleComplement n k l).comp (-X - C (140 * (n : ℚ) + 2))) := by
      rw [hs, one_mul]
    _ = _ := by linear_combination h'

/-- Reflection sends the coefficient at `k` (pole order `l + 1`) to `(-1)^l` times
the coefficient at `2 c_n - k`. -/
theorem six_principal_coefficients_reflection (n : ℕ) (i j : Fin (rank n))
    (k : ℕ) (hk : k ∈ sixPoleSet n) (l : Fin (sixPoleOrder n k)) :
    sixPrincipalCoefficients n i j k l = (-1 : ℚ) ^ l.val *
      sixPrincipalCoefficients n i j (sixReflectedPole n k)
        (l.cast (six_pole_order_reflection n k).symm) := by
  let b : (a : ℕ) → Fin (sixPoleOrder n a) → ℚ := fun a t =>
    (-1 : ℚ) ^ t.val * sixPrincipalCoefficients n i j (sixReflectedPole n a)
      (t.cast (six_pole_order_reflection n a).symm)
  let F := C (sixNormalization n) * sixNumerator n * centeredMultiplier n i j
  let phi : ℚ[X] := -X - C (140 * (n : ℚ) + 2)
  have hneg : F = ∑ a ∈ sixPoleSet n, ∑ t,
      -(C (sixPrincipalCoefficients n i j a t) *
        (sixPoleComplement n a t.val).comp phi) := by
    have h := congrArg (fun p : ℚ[X] => -(p.comp phi))
      (six_cleared_partial_fractions n i j)
    simpa only [F, phi, Polynomial.sum_comp, mul_comp, C_comp,
      sixNumerator_reflection, centeredMultiplier_reflection,
      mul_neg, neg_mul, neg_neg, Finset.sum_neg_distrib] using h
  have hnum : F = ∑ a ∈ sixPoleSet n, ∑ t,
      C (b a t) * sixPoleComplement n a t.val := by
    calc
      F = ∑ a ∈ sixPoleSet n, ∑ t,
          -(C (sixPrincipalCoefficients n i j a t) *
            (sixPoleComplement n a t.val).comp phi) := hneg
      _ = ∑ a ∈ sixPoleSet n, ∑ t,
          -(C (sixPrincipalCoefficients n i j (sixReflectedPole n a) t) *
            (sixPoleComplement n (sixReflectedPole n a) t.val).comp phi) :=
        (six_sum_reflection n (fun a => ∑ t,
          -(C (sixPrincipalCoefficients n i j a t) *
            (sixPoleComplement n a t.val).comp phi))).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Fintype.sum_equiv (finCongr (six_pole_order_reflection n a))
        intro t
        have hr := (six_pole_mem_reflection n a).mpr ha
        rw [show phi = -X - C (140 * (n : ℚ) + 2) from rfl,
          sixPoleComplement_reflection n _ t.val hr t.isLt,
          six_pole_reflection_involutive n a ha]
        simp only [b, finCongr_apply, Fin.cast_cast, Fin.cast_refl,
          id_eq, Fin.val_cast, map_mul, map_pow, map_neg, map_one, pow_succ]
        ring
  have hclear (a : (k : ℕ) → Fin (sixPoleOrder n k) → ℚ) :
      algebraMap ℚ[X] (RatFunc ℚ) (sixDenominator n) *
        (∑ k ∈ sixPoleSet n, ∑ t, sixPrincipalTerm k t.val (a k t)) =
      algebraMap ℚ[X] (RatFunc ℚ) (∑ k ∈ sixPoleSet n, ∑ t,
        C (a k t) * sixPoleComplement n k t.val) := by
    simp only [Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro t _
    exact sixPrincipalTerm_clear n k t.val hk t.isLt _
  have hd : algebraMap ℚ[X] (RatFunc ℚ) (sixDenominator n) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).ne
      (sixDenominator_monic n).ne_zero
  have heq : (∑ k ∈ sixPoleSet n, ∑ t,
      sixPrincipalTerm k t.val (sixPrincipalCoefficients n i j k t)) =
      ∑ k ∈ sixPoleSet n, ∑ t, sixPrincipalTerm k t.val (b k t) := by
    apply mul_left_cancel₀ hd
    rw [hclear, hclear, ← six_cleared_partial_fractions n i j, ← hnum]
  exact congrFun (six_principal_coefficients_unique n
    (sixPrincipalCoefficients n i j) b heq k hk) l

def sixAggregatePrincipalCoefficient (n : ℕ) (i j : Fin (rank n)) (m : ℕ) : ℚ :=
  ∑ k ∈ sixPoleSet n, ∑ l,
    if l.val + 1 = m then sixPrincipalCoefficients n i j k l else 0

/-- Every even pole order cancels (eliminating all even zeta values). -/
theorem six_even_pole_sum_zero (n : ℕ) (i j : Fin (rank n)) (m : ℕ) (hm : Even m) :
    sixAggregatePrincipalCoefficient n i j m = 0 := by
  let A := sixAggregatePrincipalCoefficient n i j m
  have hsign (v : ℕ) (hv : v + 1 = m) : (-1 : ℚ) ^ v = -1 := by
    have hvodd : Odd v := by
      obtain ⟨a, ha⟩ := hm
      exact ⟨a - 1, by omega⟩
    exact hvodd.neg_one_pow
  have hA : A = -A := by
    calc
      A = ∑ k ∈ sixPoleSet n, ∑ l,
          if l.val + 1 = m then
            sixPrincipalCoefficients n i j (sixReflectedPole n k) l else 0 :=
        (six_sum_reflection n (fun k => ∑ l : Fin (sixPoleOrder n k),
          if l.val + 1 = m then sixPrincipalCoefficients n i j k l else 0)).symm
      _ = ∑ k ∈ sixPoleSet n, ∑ l,
          -(if l.val + 1 = m then sixPrincipalCoefficients n i j k l else 0) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Fintype.sum_equiv (finCongr (six_pole_order_reflection n k))
        intro l
        have hc := six_principal_coefficients_reflection n i j k hk
          (l.cast (six_pole_order_reflection n k))
        simp only [Fin.cast_cast, Fin.cast_refl, id_eq, Fin.val_cast] at hc
        simp only [finCongr_apply, Fin.val_cast]
        by_cases hl : l.val + 1 = m
        · rw [hsign l.val hl, neg_one_mul] at hc
          simp only [hl, ite_true]
          linarith
        · simp only [hl, ite_false, neg_zero]
      _ = -A := by
        simp only [Finset.sum_neg_distrib, A, sixAggregatePrincipalCoefficient]
  change A = 0
  linarith

theorem six_aggregate_simple_zero (n : ℕ) (i j : Fin (rank n)) :
    sixAggregatePrincipalCoefficient n i j 1 = 0 := by
  simpa [sixAggregatePrincipalCoefficient] using six_residue_sum_zero n i j

theorem six_aggregate_above_fourteen_zero (n : ℕ) (i j : Fin (rank n))
    (m : ℕ) (hm : 14 < m) : sixAggregatePrincipalCoefficient n i j m = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  have horder := six_pole_order_le n k
  have hl := l.isLt
  rw [ite_eq_right (by omega)]

/-- Only pole orders `{3, 5, 7, 9, 11, 13}` can survive, giving exactly
`ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17)` after four derivatives. -/
theorem six_aggregate_support (n : ℕ) (i j : Fin (rank n)) (m : ℕ)
    (hm : m ∉ ({3, 5, 7, 9, 11, 13} : Finset ℕ)) :
    sixAggregatePrincipalCoefficient n i j m = 0 := by
  by_cases h1 : m = 1
  · subst m
    exact six_aggregate_simple_zero n i j
  by_cases he : Even m
  · exact six_even_pole_sum_zero n i j m he
  apply six_aggregate_above_fourteen_zero n i j m
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rw [Nat.even_iff] at he
  omega

theorem six_odd_index_sum_zero (n : ℕ) (i j : Fin (rank n)) (s : ℕ) (hs : Odd s) :
    (∑ k ∈ sixPoleSet n, ∑ l,
      if l.val = s then sixPrincipalCoefficients n i j k l else 0) = 0 := by
  have he : Even (s + 1) := by
    obtain ⟨a, ha⟩ := hs
    exact ⟨a + 1, by omega⟩
  simpa [sixAggregatePrincipalCoefficient] using six_even_pole_sum_zero n i j (s + 1) he

/-! ## Rational coefficients and six-variable affine moment matrix -/

/-- Index `s` corresponds to `ζ(s + 5)` (pole order `s + 1`). -/
def sixOrderCoefficient (n : ℕ) (i j : Fin (rank n)) (s : ℕ) : ℚ :=
  ∑ k ∈ sixPoleSet n, ∑ l,
    if l.val = s then sixPrincipalCoefficients n i j k l else 0

def sixZetaCoefficient (n : ℕ) (i j : Fin (rank n)) (s : ℕ) : ℚ :=
  ((s + 4).choose 4 : ℚ) * sixOrderCoefficient n i j s

def sixMomentConstant (n : ℕ) (i j : Fin (rank n)) : ℚ :=
  -(∑ k ∈ sixPoleSet n, ∑ l,
    sixPrincipalCoefficients n i j k l * ((l.val + 4).choose 4 : ℚ) *
      harmonicCutoff (l.val + 5) (k - 40 * n - 1))

theorem sixOrderCoefficient_zero (n : ℕ) (i j : Fin (rank n)) :
    sixOrderCoefficient n i j 0 = 0 := six_residue_sum_zero n i j

/-- The `ζ(5)` coefficient is strictly zero. -/
theorem sixZetaCoefficient_zero (n : ℕ) (i j : Fin (rank n)) :
    sixZetaCoefficient n i j 0 = 0 := by
  simp [sixZetaCoefficient, sixOrderCoefficient_zero]

/-- Every even-weight zeta coefficient (`s` odd, i.e. `s + 5` even) is strictly zero. -/
theorem sixZetaCoefficient_odd (n : ℕ) (i j : Fin (rank n)) (s : ℕ) (hs : Odd s) :
    sixZetaCoefficient n i j s = 0 := by
  simp [sixZetaCoefficient, sixOrderCoefficient, six_odd_index_sum_zero n i j s hs]

theorem six_order_regroup (n : ℕ) (i j : Fin (rank n)) (z : ℕ → ℝ) :
    (∑ s : Fin 14, (sixZetaCoefficient n i j s : ℝ) * z s) =
      ∑ k ∈ sixPoleSet n, ∑ l,
        (sixPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) * z l.val := by
  simp only [sixZetaCoefficient, sixOrderCoefficient, Rat.cast_mul, Rat.cast_sum,
    Rat.cast_natCast, apply_ite, Rat.cast_zero, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  let s : Fin 14 := ⟨l.val, l.isLt.trans_le (six_pole_order_le n k)⟩
  rw [Finset.sum_eq_single s]
  · simp only [s, ite_true]
    ring
  · intro b _ hbs
    have hne : l.val ≠ b.val := by
      intro he
      exact hbs (Fin.ext he.symm)
    simp [hne]
  · simp

theorem six_complete_sum_regroup (n : ℕ) (i j : Fin (rank n)) (z : ℕ → ℝ) :
    (sixMomentConstant n i j : ℝ) +
        (∑ s : Fin 14, (sixZetaCoefficient n i j s : ℝ) * z s) =
      ∑ k ∈ sixPoleSet n, ∑ l,
        (sixPrincipalCoefficients n i j k l : ℝ) * ((l.val + 4).choose 4 : ℝ) *
          (z l.val - (harmonicCutoff (l.val + 5) (k - 40 * n - 1) : ℝ)) := by
  rw [six_order_regroup]
  simp only [sixMomentConstant, Rat.cast_neg, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_natCast, mul_sub, Finset.sum_sub_distrib]
  ring

theorem six_coordinate_reduction (n : ℕ) (i j : Fin (rank n)) (z : ℕ → ℝ) :
    (∑ s : Fin 14, (sixZetaCoefficient n i j s : ℝ) * z (s.val + 5)) =
      ∑ s : Fin 6, (sixZetaCoefficient n i j (2 + 2 * s.val) : ℝ) * z (7 + 2 * s.val) := by
  have hz (s : ℕ) : sixZetaCoefficient n i j (2 * s + 1) = 0 :=
    sixZetaCoefficient_odd n i j (2 * s + 1) ⟨s, by omega⟩
  have h1 := hz 0
  have h3 := hz 1
  have h5 := hz 2
  have h7 := hz 3
  have h9 := hz 4
  have h11 := hz 5
  have h13 := hz 6
  norm_num [Fin.sum_univ_succ, sixZetaCoefficient_zero, h1, h3, h5, h7, h9, h11, h13]

/-- Fourth-derivative partial-fraction identity: every entry of `𝓗_n(ζ)` is an
exact affine rational combination of `ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17)`. -/
theorem sixFunctional_eq_six (n : ℕ) (i j : Fin (rank n)) :
    sixFunctional n i j = (sixMomentConstant n i j : ℝ) +
      ∑ s : Fin 6, (sixZetaCoefficient n i j (2 + 2 * s.val) : ℝ) * sixZetaValues s := by
  rw [sixFunctional_eq_pole_sum,
    ← six_complete_sum_regroup n i j (fun s => zetaNat (s + 5)),
    six_coordinate_reduction]
  rfl

/-! ## Formal 6-variable polynomial matrix and determinant degree bound -/

abbrev SixPolynomial := MvPolynomial (Fin 6) ℚ

def affineEntry (a : ℚ) (b : Fin 6 → ℚ) : SixPolynomial :=
  MvPolynomial.C a + ∑ k, MvPolynomial.C (b k) * MvPolynomial.X k

def sixMatrix (n : ℕ) : Matrix (Fin (rank n)) (Fin (rank n)) SixPolynomial :=
  fun i j => affineEntry (sixMomentConstant n i j)
    (fun s => sixZetaCoefficient n i j (2 + 2 * s.val))

theorem affineEntry_degree (a : ℚ) (b : Fin 6 → ℚ) :
    (affineEntry a b).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro k _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

theorem determinant_degree_le {r : ℕ} (H : Matrix (Fin r) (Fin r) SixPolynomial)
    (hH : ∀ i j, (H i j).totalDegree ≤ 1) :
    H.det.totalDegree ≤ r := by
  classical
  rw [Matrix.det_apply']
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have hs : ((Equiv.Perm.sign σ : ℤ) : SixPolynomial).totalDegree = 0 := by
    change (MvPolynomial.C (Equiv.Perm.sign σ : ℚ)).totalDegree = 0
    exact MvPolynomial.totalDegree_C _
  rw [hs, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ i : Fin r, (H (σ i) i).totalDegree ≤ ∑ _i : Fin r, 1 :=
      Finset.sum_le_sum (fun i _ => hH _ _)
    _ = r := by simp

theorem sixMatrix_det_totalDegree_le (n : ℕ) :
    (sixMatrix n).det.totalDegree ≤ rank n :=
  determinant_degree_le _ (fun _ _ => affineEntry_degree _ _)

theorem sixMatrix_entry_eval (n : ℕ) (i j : Fin (rank n)) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) sixZetaValues (sixMatrix n i j) =
      sixFunctional n i j := by
  rw [sixFunctional_eq_six]
  simp [sixMatrix, affineEntry]

/-- Evaluating the formal polynomial determinant at the six actual odd zeta values
recovers `det 𝓗_n(ζ)`. -/
theorem sixMatrix_det_eval (n : ℕ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) sixZetaValues (sixMatrix n).det =
      Matrix.det (sixFunctional n) := by
  change (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) sixZetaValues)
    (sixMatrix n).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact sixMatrix_entry_eval n i j

/-! ## Primitive integer polynomial `P_n(X)` and total degree `≤ h` -/

def integerPolynomialContent {σ : Type*} (P : MvPolynomial σ ℤ) : ℤ :=
  P.support.gcd P.coeff

theorem integerPolynomialContent_dvd_coeff {σ : Type*} (P : MvPolynomial σ ℤ)
    (m : σ →₀ ℕ) : integerPolynomialContent P ∣ P.coeff m := by
  classical
  by_cases hm : m ∈ P.support
  · exact Finset.gcd_dvd hm
  · rw [MvPolynomial.notMem_support_iff.mp hm]
    exact dvd_zero _

theorem integerPolynomialContent_ne_zero {σ : Type*} (P : MvPolynomial σ ℤ)
    (hP : P ≠ 0) : integerPolynomialContent P ≠ 0 := by
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hP
  exact Finset.gcd_ne_zero_iff.mpr ⟨m, hm, MvPolynomial.mem_support_iff.mp hm⟩

theorem exists_integer_primitive_part {σ : Type*} (A : MvPolynomial σ ℤ)
    (hA : A ≠ 0) :
    ∃ P : MvPolynomial σ ℤ,
      A = MvPolynomial.C (integerPolynomialContent A) * P ∧
      integerPolynomialContent P = 1 ∧ P ≠ 0 := by
  have hg := integerPolynomialContent_ne_zero A hA
  have hdvd : MvPolynomial.C (integerPolynomialContent A) ∣ A :=
    (MvPolynomial.C_dvd_iff_dvd_coeff _ _).mpr (integerPolynomialContent_dvd_coeff A)
  obtain ⟨P, hP⟩ := hdvd
  have hs : A.support = P.support := by
    rw [hP, MvPolynomial.C_mul', MvPolynomial.support_smul_eq hg]
  have hcoeff (m : σ →₀ ℕ) :
      A.coeff m = integerPolynomialContent A * P.coeff m := by
    simpa only [MvPolynomial.coeff_C_mul] using
      congrArg (fun B : MvPolynomial σ ℤ => B.coeff m) hP
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hA
  have hprimitive : A.support.gcd P.coeff = 1 :=
    Finset.extract_gcd' A.coeff P.coeff
      ⟨m, hm, MvPolynomial.mem_support_iff.mp hm⟩ (fun m _ => hcoeff m)
  refine ⟨P, hP, ?_, ?_⟩
  · simpa only [integerPolynomialContent, hs] using hprimitive
  · intro hzero
    exact hA (by simpa [hzero] using hP)

theorem exists_integer_coefficient_multiple {σ : Type*} (F : MvPolynomial σ ℚ) :
    ∃ D : ℤ, 0 < D ∧ ∃ A : MvPolynomial σ ℤ,
      A.map (Int.castRingHom ℚ) = MvPolynomial.C (D : ℚ) * F := by
  classical
  obtain ⟨D, hD⟩ :=
    IsLocalization.exist_integer_multiples (Submonoid.pos ℤ) F.support F.coeff
  refine ⟨D, D.property, ?_⟩
  apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
  intro b hb
  obtain ⟨m, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hb
  rw [MvPolynomial.coeff_C_mul]
  by_cases hm : m ∈ F.support
  · obtain ⟨a, ha⟩ := hD m hm
    refine ⟨a, ?_⟩
    simpa only [Algebra.smul_def, eq_intCast] using ha
  · refine ⟨0, ?_⟩
    simp [MvPolynomial.notMem_support_iff.mp hm]

theorem normalized_integral_totalDegree {σ : Type*} (P : MvPolynomial σ ℤ)
    (F : MvPolynomial σ ℚ) (c : ℚ) (hc : c ≠ 0)
    (hnorm : F = MvPolynomial.C c * P.map (Int.castRingHom ℚ)) :
    P.totalDegree = F.totalDegree := by
  have hs : F.support = P.support := by
    rw [hnorm, MvPolynomial.C_mul', MvPolynomial.support_smul_eq hc,
      MvPolynomial.support_map_of_injective P Int.cast_injective]
  simp only [MvPolynomial.totalDegree, hs]

theorem exists_six_primitive_normalization (F : SixPolynomial) (hF : F ≠ 0) :
    ∃ c : ℚ, c ≠ 0 ∧ ∃ P : MvPolynomial (Fin 6) ℤ,
      P ≠ 0 ∧ integerPolynomialContent P = 1 ∧
      F = MvPolynomial.C c * P.map (Int.castRingHom ℚ) ∧
      P.totalDegree = F.totalDegree := by
  obtain ⟨D, hD, A, hA⟩ := exists_integer_coefficient_multiple F
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hCD : (MvPolynomial.C (D : ℚ) : SixPolynomial) ≠ 0 := by simpa using hD'
  have hAne : A ≠ 0 := by
    intro hzero
    apply mul_ne_zero hCD hF
    simpa [hzero] using hA.symm
  obtain ⟨P, hAP, hprimitive, hP⟩ := exists_integer_primitive_part A hAne
  let g := integerPolynomialContent A
  have hg : g ≠ 0 := integerPolynomialContent_ne_zero A hAne
  have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  have hc : (g : ℚ) / (D : ℚ) ≠ 0 := div_ne_zero hg' hD'
  have hscalar : (D : ℚ) * ((g : ℚ) / (D : ℚ)) = g := by field_simp
  have hnorm : F = MvPolynomial.C ((g : ℚ) / (D : ℚ)) *
      P.map (Int.castRingHom ℚ) := by
    apply mul_left_cancel₀ hCD
    rw [← mul_assoc, ← MvPolynomial.C_mul, hscalar, ← hA, hAP]
    simp only [map_mul, MvPolynomial.map_C]
    rfl
  exact ⟨_, hc, P, hP, hprimitive, hnorm, normalized_integral_totalDegree P F _ hc hnorm⟩

/-- Rational content `γ_n` of `det 𝓗_n(X)` (set to `1` if the determinant is zero,
matching Section 1 of `zeta6_irrationality_proof.tex`). -/
def sixPrimitiveScalar (n : ℕ) : ℚ :=
  if h : (sixMatrix n).det = 0 then 1
  else Classical.choose (exists_six_primitive_normalization (sixMatrix n).det h)

/-- Primitive integer determinant polynomial `P_n(X) ∈ ℤ[X_0, ..., X_5]`
(set to `0` if `det 𝓗_n(X) = 0`). -/
def sixPrimitivePolynomial (n : ℕ) : MvPolynomial (Fin 6) ℤ :=
  if h : (sixMatrix n).det = 0 then 0
  else Classical.choose
    (Classical.choose_spec (exists_six_primitive_normalization (sixMatrix n).det h)).2

theorem sixPrimitiveScalar_ne_zero (n : ℕ) : sixPrimitiveScalar n ≠ 0 := by
  unfold sixPrimitiveScalar
  split_ifs with h
  · exact one_ne_zero
  · exact (Classical.choose_spec (exists_six_primitive_normalization (sixMatrix n).det h)).1

theorem sixPrimitivePolynomial_det_eq (n : ℕ) :
    (sixMatrix n).det =
      MvPolynomial.C (sixPrimitiveScalar n) *
        (sixPrimitivePolynomial n).map (Int.castRingHom ℚ) := by
  unfold sixPrimitiveScalar sixPrimitivePolynomial
  split_ifs with h
  · simp [h]
  · exact (Classical.choose_spec
      (Classical.choose_spec (exists_six_primitive_normalization (sixMatrix n).det h)).2).2.2.1

theorem sixPrimitivePolynomial_content_eq_one (n : ℕ) (h : (sixMatrix n).det ≠ 0) :
    integerPolynomialContent (sixPrimitivePolynomial n) = 1 := by
  unfold sixPrimitivePolynomial
  split_ifs with h0
  · exact (h h0).elim
  · exact (Classical.choose_spec
      (Classical.choose_spec (exists_six_primitive_normalization (sixMatrix n).det h0)).2).2.1

/-- Unconditional degree bound: `totalDegree P_n ≤ h = 15 n`. -/
theorem sixPrimitivePolynomial_totalDegree_le (n : ℕ) :
    (sixPrimitivePolynomial n).totalDegree ≤ rank n := by
  unfold sixPrimitivePolynomial
  split_ifs with h
  · simp
  · have hdeg := (Classical.choose_spec
      (Classical.choose_spec (exists_six_primitive_normalization (sixMatrix n).det h)).2).2.2.2
    rw [hdeg]
    exact sixMatrix_det_totalDegree_le n

theorem sixPrimitivePolynomial_eval_actual (n : ℕ) :
    (sixPrimitiveScalar n : ℝ) *
        (sixPrimitivePolynomial n).eval₂ (Int.castRingHom ℝ) sixZetaValues =
      Matrix.det (sixFunctional n) := by
  have hring : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ :=
    RingHom.ext fun z => by simp
  rw [← sixMatrix_det_eval, sixPrimitivePolynomial_det_eq, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_map, hring]
  rfl

end OddZetaSix
