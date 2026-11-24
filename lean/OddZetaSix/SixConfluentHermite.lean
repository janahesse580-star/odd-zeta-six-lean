import OddZetaSix.SixFunctional
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# J = 3 Confluent Hermite Interpolation Matrix over `ZMod (50n + 1)`

Proves invertibility of the `15n × 15n` Taylor-jet evaluation matrix `V mod p`
at the `5n` tail poles `k_t = 90n + 2 + t` (`t : Fin (5*n)`) with `J = 3`
jets per site (`a : Fin 3`), using **abstract linear-map injectivity**:

1. The `5n` squared nodes `x_t^2 mod p` are pairwise distinct and nonzero
   because `20n + 1 ≤ |x_t| ≤ 25n`, so `2|x_t| ≤ 50n < p = 50n + 1`.
2. Vanishing of the first 3 Taylor jets of `P((x_t + w)^2)` at `w = 0`
   (with `2 x_t ≠ 0` in `ZMod p`) forces `(Y - x_t^2)^3 ∣ P(Y)`.
3. A polynomial `P` of degree `< 15n` divisible by `∏_t (Y - x_t^2)^3` (degree `15n`)
   must vanish identically, forcing any left-kernel vector of `V` to be zero.
4. Hence `det V ≠ 0` in `ZMod p` for every prime `p = 50n + 1`, without computing
   any explicit confluent Vandermonde determinant.
-/

noncomputable section
set_option autoImplicit false

namespace OddZetaSix

open Polynomial Finset

/-! ## Gate prime and tail nodes -/

def gatePrime (n : ℕ) : ℕ := 50 * n + 1

def gateTailPole (n : ℕ) (t : Fin (5 * n)) : ℕ := 90 * n + 2 + t.val

/-- Positive distance `|c_n - k_t| = 20n + 1 + t`. -/
def gateAbsNode (n : ℕ) (t : Fin (5 * n)) : ℕ := 20 * n + 1 + t.val

/-- Centered coordinate `x_t = c_n - k_t = -(20n + 1 + t)`. -/
def gateNode (n : ℕ) (t : Fin (5 * n)) : ℤ := (sixCenter n : ℤ) - (gateTailPole n t : ℤ)

theorem gateNode_eq_neg_abs (n : ℕ) (t : Fin (5 * n)) :
    gateNode n t = -(gateAbsNode n t : ℤ) := by
  unfold gateNode sixCenter gateTailPole gateAbsNode
  omega

theorem gatePrime_pos_index (n : ℕ) (hp : (gatePrime n).Prime) : 0 < n := by
  have h2 := hp.two_le
  unfold gatePrime at h2
  omega

theorem gatePrime_ge_51 (n : ℕ) (hp : (gatePrime n).Prime) : 51 ≤ gatePrime n := by
  have hn := gatePrime_pos_index n hp
  unfold gatePrime
  omega

theorem gatePrime_not_dvd_two (n : ℕ) (hp : (gatePrime n).Prime) : ¬ gatePrime n ∣ 2 := by
  have h51 := gatePrime_ge_51 n hp
  exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)

theorem gatePrime_not_dvd_five (n : ℕ) (hp : (gatePrime n).Prime) : ¬ gatePrime n ∣ 5 := by
  have h51 := gatePrime_ge_51 n hp
  exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)

theorem gatePrime_two_ne_zero (n : ℕ) [Fact (gatePrime n).Prime] :
    (2 : ZMod (gatePrime n)) ≠ 0 := by
  intro hz
  exact gatePrime_not_dvd_two n Fact.out ((ZMod.natCast_eq_zero_iff 2 (gatePrime n)).mp hz)

theorem gatePrime_five_ne_zero (n : ℕ) [Fact (gatePrime n).Prime] :
    (5 : ZMod (gatePrime n)) ≠ 0 := by
  intro hz
  exact gatePrime_not_dvd_five n Fact.out ((ZMod.natCast_eq_zero_iff 5 (gatePrime n)).mp hz)

/-- Squared nodes `x_t^2 ∈ ZMod (50n + 1)`. -/
def gateSquare (n : ℕ) (t : Fin (5 * n)) : ZMod (gatePrime n) :=
  ((gateNode n t : ℤ) : ZMod (gatePrime n)) ^ 2

theorem gateSquare_eq_abs_sq (n : ℕ) (t : Fin (5 * n)) :
    gateSquare n t = (gateAbsNode n t : ZMod (gatePrime n)) ^ 2 := by
  rw [gateSquare, gateNode_eq_neg_abs, Int.cast_neg, Int.cast_natCast, neg_sq]

theorem gateNode_cast_ne_zero (n : ℕ) [Fact (gatePrime n).Prime] (t : Fin (5 * n)) :
    ((gateNode n t : ℤ) : ZMod (gatePrime n)) ≠ 0 := by
  rw [gateNode_eq_neg_abs, Int.cast_neg, Int.cast_natCast, neg_ne_zero]
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff (gateAbsNode n t) (gatePrime n)).mp hz
  have hpos : 0 < gateAbsNode n t := by unfold gateAbsNode; omega
  have hlt : gateAbsNode n t < gatePrime n := by
    unfold gateAbsNode gatePrime
    have := t.isLt
    omega
  exact Nat.not_dvd_of_pos_of_lt hpos hlt hd

theorem gate_two_mul_node_ne_zero (n : ℕ) [Fact (gatePrime n).Prime] (t : Fin (5 * n)) :
    2 * ((gateNode n t : ℤ) : ZMod (gatePrime n)) ≠ 0 :=
  mul_ne_zero (gatePrime_two_ne_zero n) (gateNode_cast_ne_zero n t)

/-- The `5n` squared tail nodes are pairwise distinct modulo `p = 50n + 1`. -/
theorem gate_squares_injective (n : ℕ) [Fact (gatePrime n).Prime] :
    Function.Injective (gateSquare n) := by
  intro t₁ t₂ h
  rw [gateSquare_eq_abs_sq, gateSquare_eq_abs_sq] at h
  have h1 : gateAbsNode n t₁ < gatePrime n := by
    unfold gateAbsNode gatePrime; have := t₁.isLt; omega
  have h2 : gateAbsNode n t₂ < gatePrime n := by
    unfold gateAbsNode gatePrime; have := t₂.isLt; omega
  have hsum : gateAbsNode n t₁ + gateAbsNode n t₂ < gatePrime n := by
    unfold gateAbsNode gatePrime; have := t₁.isLt; have := t₂.isLt; omega
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with heq | hneg
  · have hv := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hv
    apply Fin.ext
    unfold gateAbsNode at hv
    omega
  · have hz : ((gateAbsNode n t₁ + gateAbsNode n t₂ : ℕ) : ZMod (gatePrime n)) = 0 := by
      rw [Nat.cast_add, hneg, neg_add_cancel]
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hsum, ZMod.val_zero] at hv
    unfold gateAbsNode at hv
    omega

/-! ## Even basis polynomials reduced modulo `p = 50n + 1` -/

/-- Monic polynomial in `Y = X^2` representing the root part of `E_i`. -/
def gateMonicBasis (K : Type*) [Field K] : ℕ → K[X]
  | 0 => 1
  | m + 1 => X * ∏ j ∈ range m, (X - C (((j : K) + 1) ^ 2))

theorem gateMonicBasis_monic (K : Type*) [Field K] (i : ℕ) :
    (gateMonicBasis K i).Monic := by
  cases i with
  | zero => exact monic_one
  | succ m =>
    apply monic_X.mul
    apply monic_prod_of_monic
    intro j _
    exact monic_X_sub_C _

theorem gateMonicBasis_natDegree (K : Type*) [Field K] (i : ℕ) :
    (gateMonicBasis K i).natDegree = i := by
  cases i with
  | zero => simp [gateMonicBasis]
  | succ m =>
    rw [gateMonicBasis, natDegree_mul X_ne_zero
      (monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)).ne_zero,
      natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)]
    simp only [natDegree_X, natDegree_X_sub_C, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one]
    omega

def gateBasisCoeff (n : ℕ) [Fact (gatePrime n).Prime] (i : Fin (rank n)) :
    ZMod (gatePrime n) :=
  if i.val = 0 then 1
  else (2 : ZMod (gatePrime n)) / ((2 * i.val).factorial : ZMod (gatePrime n))

theorem gateBasisCoeff_ne_zero (n : ℕ) [Fact (gatePrime n).Prime] (i : Fin (rank n)) :
    gateBasisCoeff n i ≠ 0 := by
  have hp : (gatePrime n).Prime := Fact.out
  unfold gateBasisCoeff
  split_ifs
  · exact one_ne_zero
  · apply div_ne_zero (gatePrime_two_ne_zero n)
    intro hz
    have hd : gatePrime n ∣ (2 * i.val).factorial :=
      (ZMod.natCast_eq_zero_iff (2 * i.val).factorial (gatePrime n)).mp hz
    have hle := hp.dvd_factorial.mp hd
    have hi : i.val < 15 * n := i.isLt
    unfold gatePrime at hle
    omega

/-- `E_i` viewed as a polynomial in `Y = X^2` over `ZMod (50n + 1)`. -/
def gateEvenPolySq (n : ℕ) [Fact (gatePrime n).Prime] (i : Fin (rank n)) :
    (ZMod (gatePrime n))[X] :=
  C (gateBasisCoeff n i) * gateMonicBasis (ZMod (gatePrime n)) i.val

/-- `E_i(X)` over `ZMod (50n + 1)`. -/
def gateEvenPoly (n : ℕ) [Fact (gatePrime n).Prime] (i : Fin (rank n)) :
    (ZMod (gatePrime n))[X] :=
  (gateEvenPolySq n i).comp (X ^ 2)

theorem gateEvenPolySq_natDegree (n : ℕ) [Fact (gatePrime n).Prime] (i : Fin (rank n)) :
    (gateEvenPolySq n i).natDegree = i.val := by
  rw [gateEvenPolySq, natDegree_C_mul (gateBasisCoeff_ne_zero n i),
    gateMonicBasis_natDegree]

theorem gateEvenPolySq_coeff_self (n : ℕ) [Fact (gatePrime n).Prime] (i : Fin (rank n)) :
    (gateEvenPolySq n i).coeff i.val = gateBasisCoeff n i := by
  rw [← gateEvenPolySq_natDegree n i, ← leadingCoeff, gateEvenPolySq,
    (gateMonicBasis_monic _ _).leadingCoeff_C_mul]

/-! ## Abstract 3-jet Hermite divisibility and injectivity -/

private theorem poly_decompose_three {K : Type*} [Field K] (Q : K[X]) :
    ∃ R : K[X], Q = C (Q.coeff 0) + C (Q.coeff 1) * X + C (Q.coeff 2) * X ^ 2 + X ^ 3 * R := by
  let Q₁ := Q.divX
  have h1 : X * Q₁ + C (Q.coeff 0) = Q := X_mul_divX_add Q
  let Q₂ := Q₁.divX
  have h2 : X * Q₂ + C (Q₁.coeff 0) = Q₁ := X_mul_divX_add Q₁
  let Q₃ := Q₂.divX
  have h3 : X * Q₃ + C (Q₂.coeff 0) = Q₂ := X_mul_divX_add Q₂
  have hc1 : Q₁.coeff 0 = Q.coeff 1 := by simp [Q₁]
  have hc2 : Q₂.coeff 0 = Q.coeff 2 := by simp [Q₂, Q₁]
  refine ⟨Q₃, ?_⟩
  conv_lhs => rw [← h1, ← h2, ← h3, hc1, hc2]
  ring

/-- Vanishing of the first 3 Taylor coefficients of `P((x + w)^2)` at `w = 0`
(when `2x ≠ 0`) forces `(Y - x^2)^3 ∣ P(Y)`. -/
theorem pow_three_dvd_of_taylor_comp_sq_vanish {K : Type*} [Field K]
    (P : K[X]) (x : K) (h2x : 2 * x ≠ 0)
    (h0 : (taylor x (P.comp (X ^ 2))).coeff 0 = 0)
    (h1 : (taylor x (P.comp (X ^ 2))).coeff 1 = 0)
    (h2 : (taylor x (P.comp (X ^ 2))).coeff 2 = 0) :
    (X - C (x ^ 2)) ^ 3 ∣ P := by
  let Q : K[X] := P.comp (X + C (x ^ 2))
  have hP_eq : P = Q.comp (X - C (x ^ 2)) := by
    simp only [Q, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]
  let u : K[X] := X ^ 2 + C (2 * x) * X
  have hcomp_eq : taylor x (P.comp (X ^ 2)) = Q.comp u := by
    rw [taylor_apply, comp_assoc]
    simp only [Q, comp_assoc]
    congr 1
    simp only [u, pow_comp, add_comp, X_comp, C_comp, map_pow, map_mul, map_ofNat]
    ring
  obtain ⟨R, hQ⟩ := poly_decompose_three Q
  have hu3 : ∀ k < 3, (u ^ 3 * R.comp u).coeff k = 0 := by
    intro k hk
    have hu_fac : u = X * (X + C (2 * x)) := by dsimp [u]; ring
    rw [hu_fac, mul_pow, mul_assoc, coeff_X_pow_mul']
    simp [show ¬ (3 ≤ k) by omega]
  have hQu : Q.comp u = C (Q.coeff 0) + C (Q.coeff 1) * u + C (Q.coeff 2) * u ^ 2 +
      u ^ 3 * R.comp u := by
    conv_lhs => rw [hQ]
    simp only [add_comp, mul_comp, pow_comp, C_comp, X_comp]
  have hq0 : Q.coeff 0 = 0 := by
    rw [hcomp_eq, hQu] at h0
    simp only [coeff_add, hu3 0 (by omega), add_zero] at h0
    have hcu0 : (C (Q.coeff 1) * u).coeff 0 = 0 := by
      simp [u]
    have hcu20 : (C (Q.coeff 2) * u ^ 2).coeff 0 = 0 := by
      rw [show u ^ 2 = X ^ 2 * (X + C (2 * x)) ^ 2 by dsimp [u]; ring,
        ← mul_assoc, mul_comm (C (Q.coeff 2)), mul_assoc, coeff_X_pow_mul']
      simp
    simpa [hcu0, hcu20] using h0
  have hq1 : Q.coeff 1 = 0 := by
    rw [hcomp_eq, hQu, hq0, map_zero, zero_add] at h1
    simp only [coeff_add, hu3 1 (by omega), add_zero] at h1
    have hcu21 : (C (Q.coeff 2) * u ^ 2).coeff 1 = 0 := by
      rw [show u ^ 2 = X ^ 2 * (X + C (2 * x)) ^ 2 by dsimp [u]; ring,
        ← mul_assoc, mul_comm (C (Q.coeff 2)), mul_assoc, coeff_X_pow_mul']
      simp
    have hcu1 : (C (Q.coeff 1) * u).coeff 1 = Q.coeff 1 * (2 * x) := by
      simp [u, coeff_C_mul, coeff_X_pow]
    rw [hcu21, add_zero, hcu1] at h1
    exact (mul_eq_zero.mp h1).resolve_right h2x
  have hq2 : Q.coeff 2 = 0 := by
    rw [hcomp_eq, hQu, hq0, hq1, map_zero, zero_mul, zero_add, zero_add] at h2
    simp only [coeff_add, hu3 2 (by omega), add_zero] at h2
    have hcu2 : (C (Q.coeff 2) * u ^ 2).coeff 2 = Q.coeff 2 * (2 * x) ^ 2 := by
      have hu2 : u ^ 2 = C ((2 * x) ^ 2) * X ^ 2 + X ^ 3 * (X + C (4 * x)) := by
        dsimp [u]; simp only [map_pow, map_mul, map_ofNat]; ring
      rw [hu2, mul_add, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul']
      simp
    rw [hcu2] at h2
    exact (mul_eq_zero.mp h2).resolve_right (pow_ne_zero 2 h2x)
  rw [hq0, hq1, hq2] at hQ
  simp only [map_zero, zero_mul, add_zero, zero_add] at hQ
  refine ⟨R.comp (X - C (x ^ 2)), ?_⟩
  rw [hP_eq, hQ, mul_comp, pow_comp, X_comp]

/-- Any polynomial of degree `< 15n` whose first 3 Taylor jets in `w` vanish at
all `5n` tail nodes `x_t` must be zero. -/
theorem poly_eq_zero_of_confluent_jets_zero (n : ℕ) [Fact (gatePrime n).Prime]
    (P : (ZMod (gatePrime n))[X])
    (hdeg : P.natDegree < rank n)
    (hjets : ∀ (t : Fin (5 * n)) (a : Fin 3),
      (taylor ((gateNode n t : ℤ) : ZMod (gatePrime n)) (P.comp (X ^ 2))).coeff a.val = 0) :
    P = 0 := by
  by_contra hP
  have hdvd_each : ∀ t ∈ (Finset.univ : Finset (Fin (5 * n))),
      (X - C (gateSquare n t)) ^ 3 ∣ P := by
    intro t _
    exact pow_three_dvd_of_taylor_comp_sq_vanish P _ (gate_two_mul_node_ne_zero n t)
      (hjets t 0) (hjets t 1) (hjets t 2)
  have hcop : Set.Pairwise ((Finset.univ : Finset (Fin (5 * n))) : Set (Fin (5 * n)))
      (fun t₁ t₂ => IsCoprime ((X - C (gateSquare n t₁)) ^ 3)
        ((X - C (gateSquare n t₂)) ^ 3)) := by
    intro t₁ _ t₂ _ hne
    exact (Polynomial.pairwise_coprime_X_sub_C (gate_squares_injective n) hne).pow
  have hprod_dvd : (∏ t : Fin (5 * n), (X - C (gateSquare n t)) ^ 3) ∣ P :=
    Finset.prod_dvd_of_coprime hcop hdvd_each
  have hprod_monic : (∏ t : Fin (5 * n), (X - C (gateSquare n t)) ^ 3).Monic :=
    monic_prod_of_monic _ _ (fun t _ => (monic_X_sub_C _).pow 3)
  have hprod_deg : (∏ t : Fin (5 * n), (X - C (gateSquare n t)) ^ 3).natDegree = rank n := by
    rw [natDegree_prod_of_monic _ _ (fun t _ => (monic_X_sub_C _).pow 3)]
    simp_rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    simp [rank]
    ring
  have hle := Polynomial.natDegree_le_of_dvd hprod_dvd hP
  omega

/-- Linear independence of `{gateEvenPolySq n i | i : Fin (15n)}` by strictly
increasing degrees. -/
theorem gateEvenPolySq_linear_independent (n : ℕ) [Fact (gatePrime n).Prime]
    (c : Fin (rank n) → ZMod (gatePrime n))
    (hsum : (∑ i : Fin (rank n), C (c i) * gateEvenPolySq n i) = 0) :
    c = 0 := by
  have hdown : ∀ m : ℕ, ∀ i : Fin (rank n), rank n - m ≤ i.val → c i = 0 := by
    intro m
    induction m with
    | zero =>
      intro i hi
      have := i.isLt
      omega
    | succ m ih =>
      intro i hi
      by_cases hgt : rank n - m ≤ i.val
      · exact ih i hgt
      · have hieq : i.val = rank n - (m + 1) := by omega
        have hcoeff := congrArg (fun p : (ZMod (gatePrime n))[X] => p.coeff i.val) hsum
        rw [coeff_zero, finsetSum_coeff] at hcoeff
        have hsingle : (∑ j : Fin (rank n), (C (c j) * gateEvenPolySq n j).coeff i.val) =
            c i * gateBasisCoeff n i := by
          rw [Finset.sum_eq_single i]
          · rw [coeff_C_mul, gateEvenPolySq_coeff_self]
          · intro j _ hji
            rw [coeff_C_mul]
            by_cases hjlt : j.val < i.val
            · rw [coeff_eq_zero_of_natDegree_lt (by rw [gateEvenPolySq_natDegree]; exact hjlt),
                mul_zero]
            · have hjgt : rank n - m ≤ j.val := by
                have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
                omega
              rw [ih j hjgt, zero_mul]
          · intro hi'
            exact (hi' (Finset.mem_univ i)).elim
        rw [hsingle] at hcoeff
        exact (mul_eq_zero.mp hcoeff).resolve_right (gateBasisCoeff_ne_zero n i)
  funext i
  exact hdown (rank n) i (by omega)

/-! ## Canonical index equivalence and invertibility of `V mod p` -/

/-- Bijection between `(t, a) ∈ Fin (5n) × Fin 3` and `Fin (15n)`. -/
def sixGateIndexEquiv (n : ℕ) : Fin (5 * n) × Fin 3 ≃ Fin (rank n) where
  toFun p := ⟨3 * p.1.val + p.2.val, by unfold rank; have := p.1.isLt; have := p.2.isLt; omega⟩
  invFun k := (⟨k.val / 3, by unfold rank at k; have := k.isLt; omega⟩,
               ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩)
  left_inv p := by
    ext
    · dsimp; have := p.2.isLt; omega
    · dsimp; have := p.2.isLt; omega
  right_inv k := by
    ext
    dsimp
    omega

/-- The `15n × (5n × 3)` Taylor-jet evaluation matrix `V` over `ZMod (50n + 1)`. -/
def sixGateEvalMatrixMod (n : ℕ) [Fact (gatePrime n).Prime] :
    Matrix (Fin (rank n)) (Fin (5 * n) × Fin 3) (ZMod (gatePrime n)) :=
  fun i ta =>
    (taylor ((gateNode n ta.1 : ℤ) : ZMod (gatePrime n)) (gateEvenPoly n i)).coeff ta.2.val

/-- Square form of `V mod p` via `sixGateIndexEquiv`. -/
def sixGateEvalMatrixModSq (n : ℕ) [Fact (gatePrime n).Prime] :
    Matrix (Fin (rank n)) (Fin (rank n)) (ZMod (gatePrime n)) :=
  fun i k => sixGateEvalMatrixMod n i ((sixGateIndexEquiv n).symm k)

/-- Triviality of the left kernel of `V mod p`. -/
theorem sixGateEvalMatrixMod_left_kernel_trivial (n : ℕ) [Fact (gatePrime n).Prime]
    (c : Fin (rank n) → ZMod (gatePrime n))
    (hc : ∀ ta : Fin (5 * n) × Fin 3,
      (∑ i : Fin (rank n), c i * sixGateEvalMatrixMod n i ta) = 0) :
    c = 0 := by
  let P : (ZMod (gatePrime n))[X] := ∑ i : Fin (rank n), C (c i) * gateEvenPolySq n i
  have hPdeg : P.natDegree < rank n := by
    by_cases h0 : rank n = 0
    · exfalso
      have hn := gatePrime_pos_index n Fact.out
      unfold rank at h0
      omega
    · refine (Polynomial.natDegree_sum_le _ _).trans_lt ?_
      rw [Finset.fold_max_lt]
      refine ⟨Nat.pos_of_ne_zero h0, ?_⟩
      intro i _
      exact (Polynomial.natDegree_C_mul_le _ _).trans_lt
        (by rw [gateEvenPolySq_natDegree]; exact i.isLt)
  have hPjets : ∀ (t : Fin (5 * n)) (a : Fin 3),
      (taylor ((gateNode n t : ℤ) : ZMod (gatePrime n)) (P.comp (X ^ 2))).coeff a.val = 0 := by
    intro t a
    have hcomp : P.comp (X ^ 2) = ∑ i : Fin (rank n), C (c i) * gateEvenPoly n i := by
      simp only [P, Polynomial.sum_comp, mul_comp, C_comp, gateEvenPoly]
    rw [hcomp, map_sum, finsetSum_coeff]
    have heq : (∑ i : Fin (rank n),
        (taylor ((gateNode n t : ℤ) : ZMod (gatePrime n))
          (C (c i) * gateEvenPoly n i)).coeff a.val) =
        ∑ i : Fin (rank n), c i * sixGateEvalMatrixMod n i (t, a) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [taylor_mul, taylor_C, coeff_C_mul]
      rfl
    rw [heq]
    exact hc (t, a)
  have hPzero : P = 0 := poly_eq_zero_of_confluent_jets_zero n P hPdeg hPjets
  exact gateEvenPolySq_linear_independent n c hPzero

/-- The square `15n × 15n` confluent Hermite evaluation matrix `V mod p` is
invertible (`det ≠ 0`) for every prime `p = 50n + 1`. -/
theorem sixGateEvalMatrixModSq_det_ne_zero (n : ℕ) [Fact (gatePrime n).Prime] :
    (sixGateEvalMatrixModSq n).det ≠ 0 := by
  have hker : ∀ c : Fin (rank n) → ZMod (gatePrime n),
      (sixGateEvalMatrixModSq n).transpose.mulVec c = 0 → c = 0 := by
    intro c hc
    apply sixGateEvalMatrixMod_left_kernel_trivial n c
    intro ta
    have hrow := congrFun hc (sixGateIndexEquiv n ta)
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply,
      sixGateEvalMatrixModSq, Equiv.symm_apply_apply] at hrow
    simpa only [mul_comm] using hrow
  have hlin : LinearMap.ker (Matrix.mulVecLin (sixGateEvalMatrixModSq n).transpose) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact hker c hc
  have hinj : Function.Injective (Matrix.mulVecLin (sixGateEvalMatrixModSq n).transpose) :=
    LinearMap.ker_eq_bot.mp hlin
  have hdetT : (sixGateEvalMatrixModSq n).transpose.det ≠ 0 := by
    intro hzero
    obtain ⟨v, hv_ne, hv_zero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
    exact hv_ne (hker v hv_zero)
  simpa only [Matrix.det_transpose] using hdetT

end OddZetaSix
