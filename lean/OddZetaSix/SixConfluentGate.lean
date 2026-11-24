import OddZetaSix.SixAssembly
import OddZetaSix.SixGateLocal
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Stage 1B: `J = 3` Confluent `p`-Adic Gate and Live Closure of `SixGateHypothesis`

Assembles the asymmetric pure-integer diagonal scaling
`D_L = diag(p^(5 - a))`, `D_R = diag(p^(4 - b))` (`a, b : Fin 3`, total exponent `105n`)
together with the `ℤ_(p)`-integral inverse `W = V⁻¹` of the confluent Hermite evaluation
matrix `V` (`SixConfluentHermite.lean`) and the local tail-pole singular collapse
(`SixGateLocal.lean`) to prove, for every prime `p = 50n + 1` and every `q ∈ ℤ_(p)^6`:

1. `M := D_L * W * H(q) * Wᵀ * D_R` has all entries in `ℤ_(p)`;
2. `M mod p` is block-diagonal with `5n` diagonal `3 × 3` blocks
   `((-1)^(q_t + 1) * U_t(0)) • sixGateBlock q_t`, all invertible in `ZMod p`
   with zero bad primes excluded;
3. `det H(q) ≠ 0` and `padicValRat p (det H(q)) = -105 * n`;
4. Combining with Mathlib's elementary `Nat.exists_prime_gt_modEq_one` closes
   `SixGateHypothesis` (`sixGate_proved`) and reduces `SixZetaIrrationalityStatement`
   purely to the two asymptotic rate hypotheses (`sixZeta_irrational_of_arith_and_analytic`).
-/

noncomputable section
set_option autoImplicit false

namespace OddZetaSix

open Polynomial Finset

/-! ## Rational confluent evaluation matrix `V` and its `ℤ_(p)`-integral inverse `W` -/

/-- The `15n × (5n × 3)` rational Taylor-jet evaluation matrix `V`. -/
def sixGateEvalMatrixQ (n : ℕ) : Matrix (Fin (rank n)) (Fin (5 * n) × Fin 3) ℚ :=
  fun i ta => (taylor (gateNode n ta.1 : ℚ) (evenBasis i.val)).coeff ta.2.val

/-- Square form of `V` indexed by `Fin (15n)` via `sixGateIndexEquiv`. -/
def sixGateEvalMatrixQSq (n : ℕ) : Matrix (Fin (rank n)) (Fin (rank n)) ℚ :=
  fun i k => sixGateEvalMatrixQ n i ((sixGateIndexEquiv n).symm k)

theorem sixGateEvalMatrixQSq_mem (n : ℕ) [Fact (gatePrime n).Prime]
    (i k : Fin (rank n)) :
    sixGateEvalMatrixQSq n i k ∈ sixGateIntegralRing (gatePrime n) := by
  unfold sixGateEvalMatrixQSq sixGateEvalMatrixQ
  exact (polyInSubring_taylor (sixGate_evenBasis_in_subring n i)
    (intCast_mem (sixGateIntegralRing (gatePrime n)) _)) _

theorem sixGateEvalMatrixQSq_cast (n : ℕ) [Fact (gatePrime n).Prime]
    (i k : Fin (rank n)) :
    ((sixGateEvalMatrixQSq n i k : ℚ) : ZMod (gatePrime n)) =
      sixGateEvalMatrixModSq n i k := by
  unfold sixGateEvalMatrixQSq sixGateEvalMatrixQ sixGateEvalMatrixModSq sixGateEvalMatrixMod
  exact sixGate_taylor_evenBasis_coeff_cast n i _ _

/-- `V` viewed as a matrix over the local ring `ℤ_(p)`. -/
def sixGateEvalMatrixLocal (n : ℕ) [Fact (gatePrime n).Prime] :
    Matrix (Fin (rank n)) (Fin (rank n)) (sixGateIntegralRing (gatePrime n)) :=
  fun i k => ⟨sixGateEvalMatrixQSq n i k, sixGateEvalMatrixQSq_mem n i k⟩

theorem sixGateEvalMatrixLocal_subtype_map (n : ℕ) [Fact (gatePrime n).Prime] :
    (sixGateIntegralRing (gatePrime n)).subtype.mapMatrix (sixGateEvalMatrixLocal n) =
      sixGateEvalMatrixQSq n := by
  ext i k
  rfl

theorem sixGateEvalMatrixLocal_reduction_map (n : ℕ) [Fact (gatePrime n).Prime] :
    (sixGateReduction (gatePrime n)).mapMatrix (sixGateEvalMatrixLocal n) =
      sixGateEvalMatrixModSq n := by
  ext i k
  exact sixGateEvalMatrixQSq_cast n i k

/-- `det V` is a `p`-adic unit in `ℚ` for every prime `p = 50n + 1`. -/
theorem sixGateEvalMatrixQSq_det_unit (n : ℕ) [Fact (gatePrime n).Prime] :
    (sixGateEvalMatrixQSq n).det ≠ 0 ∧
      padicValRat (gatePrime n) (sixGateEvalMatrixQSq n).det = 0 := by
  have hdet_sub : ((sixGateEvalMatrixLocal n).det : ℚ) = (sixGateEvalMatrixQSq n).det := by
    rw [← sixGateEvalMatrixLocal_subtype_map n, ← RingHom.map_det]
    rfl
  have hdet_red : sixGateReduction (gatePrime n) (sixGateEvalMatrixLocal n).det =
      (sixGateEvalMatrixModSq n).det := by
    rw [← sixGateEvalMatrixLocal_reduction_map n, ← RingHom.map_det]
  have hne : sixGateReduction (gatePrime n) (sixGateEvalMatrixLocal n).det ≠ 0 := by
    rw [hdet_red]
    exact sixGateEvalMatrixModSq_det_ne_zero n
  have hunit := (sixGateReduction_ne_zero_iff (gatePrime n) (sixGateEvalMatrixLocal n).det).mp hne
  rwa [hdet_sub] at hunit

/-- Explicit rational inverse `W = V⁻¹ = (det V)⁻¹ • adjugate V`. -/
def sixGateInvEvalMatrix (n : ℕ) : Matrix (Fin (rank n)) (Fin (rank n)) ℚ :=
  (sixGateEvalMatrixQSq n).det⁻¹ • (sixGateEvalMatrixQSq n).adjugate

theorem sixGateInvEvalMatrix_mul_right (n : ℕ) [Fact (gatePrime n).Prime] :
    sixGateInvEvalMatrix n * sixGateEvalMatrixQSq n = 1 := by
  have hne := (sixGateEvalMatrixQSq_det_unit n).1
  rw [sixGateInvEvalMatrix, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul,
    inv_mul_cancel₀ hne, one_smul]

theorem sixGateInvEvalMatrix_mem (n : ℕ) [Fact (gatePrime n).Prime]
    (k i : Fin (rank n)) :
    sixGateInvEvalMatrix n k i ∈ sixGateIntegralRing (gatePrime n) := by
  let S := sixGateIntegralRing (gatePrime n)
  have hdet := sixGateEvalMatrixQSq_det_unit n
  have hinv : (sixGateEvalMatrixQSq n).det⁻¹ ∈ S :=
    sixGateIntegralRing_inv_of_unit _ _ hdet.1 hdet.2
  have hadj : (sixGateEvalMatrixQSq n).adjugate k i ∈ S := by
    have hmap : S.subtype.mapMatrix (sixGateEvalMatrixLocal n).adjugate =
        (sixGateEvalMatrixQSq n).adjugate := by
      rw [← sixGateEvalMatrixLocal_subtype_map n]
      exact RingHom.map_adjugate S.subtype (sixGateEvalMatrixLocal n)
    have hki : (sixGateEvalMatrixQSq n).adjugate k i =
        ((sixGateEvalMatrixLocal n).adjugate k i : ℚ) := by
      have := congrFun (congrFun hmap k) i
      exact this.symm
    rw [hki]
    exact ((sixGateEvalMatrixLocal n).adjugate k i).property
  exact S.mul_mem hinv hadj

theorem sixGateInvEvalMatrix_det_unit (n : ℕ) [Fact (gatePrime n).Prime] :
    (sixGateInvEvalMatrix n).det ≠ 0 ∧
      padicValRat (gatePrime n) (sixGateInvEvalMatrix n).det = 0 := by
  have hmul : (sixGateInvEvalMatrix n).det * (sixGateEvalMatrixQSq n).det = 1 := by
    rw [← Matrix.det_mul, sixGateInvEvalMatrix_mul_right n, Matrix.det_one]
  have hWne : (sixGateInvEvalMatrix n).det ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hV := sixGateEvalMatrixQSq_det_unit n
  refine ⟨hWne, ?_⟩
  have hv := congrArg (padicValRat (gatePrime n)) hmul
  rw [padicValRat.mul hWne hV.1, hV.2, add_zero, padicValRat.one] at hv
  exact hv

/-- Contraction of row `k` of `W` against the `a`-th Taylor jet of `E_i` at `x_t`. -/
def sixGateWJet (n : ℕ) (k : Fin (rank n)) (t : Fin (5 * n)) (a : ℕ) : ℚ :=
  ∑ i : Fin (rank n),
    sixGateInvEvalMatrix n k i * (taylor (gateNode n t : ℚ) (evenBasis i.val)).coeff a

theorem sixGateWJet_mem (n : ℕ) [Fact (gatePrime n).Prime]
    (k : Fin (rank n)) (t : Fin (5 * n)) (a : ℕ) :
    sixGateWJet n k t a ∈ sixGateIntegralRing (gatePrime n) := by
  let S := sixGateIntegralRing (gatePrime n)
  apply S.sum_mem
  intro i _
  exact S.mul_mem (sixGateInvEvalMatrix_mem n k i)
    ((polyInSubring_taylor (sixGate_evenBasis_in_subring n i) (intCast_mem S _)) a)

theorem sixGateWJet_lt_three (n : ℕ) [Fact (gatePrime n).Prime]
    (k : Fin (rank n)) (t : Fin (5 * n)) (a : Fin 3) :
    sixGateWJet n k t a.val = if k = sixGateIndexEquiv n (t, a) then 1 else 0 := by
  have hmul := congrFun (congrFun (sixGateInvEvalMatrix_mul_right n) k)
    (sixGateIndexEquiv n (t, a))
  simp only [Matrix.mul_apply, Matrix.one_apply, sixGateEvalMatrixQSq,
    Equiv.symm_apply_apply, sixGateEvalMatrixQ] at hmul
  exact hmul

/-! ## Asymmetric pure-integer diagonal scalings `D_L` and `D_R` -/

/-- Left integer scaling exponents `5 - a ∈ {5, 4, 3}`. -/
def sixGateLeftExp (n : ℕ) (k : Fin (rank n)) : ℕ :=
  5 - ((sixGateIndexEquiv n).symm k).2.val

/-- Right integer scaling exponents `4 - b ∈ {4, 3, 2}`. -/
def sixGateRightExp (n : ℕ) (k : Fin (rank n)) : ℕ :=
  4 - ((sixGateIndexEquiv n).symm k).2.val

def sixGateLeftDiag (n : ℕ) : Matrix (Fin (rank n)) (Fin (rank n)) ℚ :=
  Matrix.diagonal (fun k => (gatePrime n : ℚ) ^ sixGateLeftExp n k)

def sixGateRightDiag (n : ℕ) : Matrix (Fin (rank n)) (Fin (rank n)) ℚ :=
  Matrix.diagonal (fun k => (gatePrime n : ℚ) ^ sixGateRightExp n k)

theorem sixGateLeftDiag_det (n : ℕ) :
    (sixGateLeftDiag n).det = (gatePrime n : ℚ) ^ (60 * n) := by
  rw [sixGateLeftDiag, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  congr 1
  have hsum : (∑ k : Fin (rank n), sixGateLeftExp n k) =
      ∑ p : Fin (5 * n) × Fin 3, (5 - p.2.val) := by
    refine Fintype.sum_equiv (sixGateIndexEquiv n).symm _ _ ?_
    intro k
    rfl
  rw [hsum, Fintype.sum_prod_type]
  have hinner : (∑ a : Fin 3, (5 - a.val)) = 12 := by decide
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

theorem sixGateRightDiag_det (n : ℕ) :
    (sixGateRightDiag n).det = (gatePrime n : ℚ) ^ (45 * n) := by
  rw [sixGateRightDiag, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  congr 1
  have hsum : (∑ k : Fin (rank n), sixGateRightExp n k) =
      ∑ p : Fin (5 * n) × Fin 3, (4 - p.2.val) := by
    refine Fintype.sum_equiv (sixGateIndexEquiv n).symm _ _ ?_
    intro k
    rfl
  rw [hsum, Fintype.sum_prod_type]
  have hinner : (∑ b : Fin 3, (4 - b.val)) = 9 := by decide
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-! ## Scaled matrix `M = D_L * W * H(q) * Wᵀ * D_R` and mod-`p` block diagonalization -/

/-- The `3 × 3` diagonal block at tail pole `t` over `ZMod (50n + 1)`. -/
def sixGateDiagBlock (n : ℕ) [Fact (gatePrime n).Prime] (t : Fin (5 * n)) :
    Matrix (Fin 3) (Fin 3) (ZMod (gatePrime n)) :=
  (((-1 : ZMod (gatePrime n)) ^ ((sixGateTailZeroCount n t).val + 1)) *
    ((sixGateUnitSeries n t).coeff 0 : ZMod (gatePrime n))) •
    (sixGateBlock (sixGateTailZeroCount n t)).map (Int.castRingHom (ZMod (gatePrime n)))

/-- The full `15n × 15n` block-diagonal target matrix over `ZMod (50n + 1)`. -/
def sixGateTargetMod (n : ℕ) [Fact (gatePrime n).Prime] :
    Matrix (Fin (rank n)) (Fin (rank n)) (ZMod (gatePrime n)) :=
  fun k₁ k₂ =>
    let p₁ := (sixGateIndexEquiv n).symm k₁
    let p₂ := (sixGateIndexEquiv n).symm k₂
    if p₁.1 = p₂.1 then sixGateDiagBlock n p₁.1 p₁.2 p₂.2 else 0

theorem sixGateDiagBlock_det_ne_zero (n : ℕ) [Fact (gatePrime n).Prime] (t : Fin (5 * n)) :
    (sixGateDiagBlock n t).det ≠ 0 := by
  unfold sixGateDiagBlock
  rw [Matrix.det_smul, Fintype.card_fin]
  apply mul_ne_zero
  · apply pow_ne_zero 3
    apply mul_ne_zero
    · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    · have hU := sixGateUnitSeries_zero_unit n t
      have hUmem : (sixGateUnitSeries n t).coeff 0 ∈ sixGateIntegralRing (gatePrime n) :=
        sixGateUnitSeries_in_subring n t 0
      exact (sixGateReduction_ne_zero_iff (gatePrime n) ⟨_, hUmem⟩).mpr hU
  · exact sixGateBlock_det_zmod_ne_zero n (sixGateTailZeroCount n t)

theorem sixGateTargetMod_det_ne_zero (n : ℕ) [Fact (gatePrime n).Prime] :
    (sixGateTargetMod n).det ≠ 0 := by
  let e : Fin 3 × Fin (5 * n) ≃ Fin (rank n) :=
    (Equiv.prodComm (Fin 3) (Fin (5 * n))).trans (sixGateIndexEquiv n)
  have hreindex : Matrix.reindex e.symm e.symm (sixGateTargetMod n) =
      Matrix.blockDiagonal (sixGateDiagBlock n) := by
    ext ⟨a, t₁⟩ ⟨b, t₂⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      sixGateTargetMod, Matrix.blockDiagonal_apply, e, Equiv.trans_apply,
      Equiv.prodComm_apply, Equiv.symm_apply_apply, Prod.swap_prod_mk]
  have hdet : (sixGateTargetMod n).det = ∏ t : Fin (5 * n), (sixGateDiagBlock n t).det := by
    rw [← Matrix.det_reindex_self e.symm (sixGateTargetMod n), hreindex,
      Matrix.det_blockDiagonal]
  rw [hdet]
  exact Finset.prod_ne_zero_iff.mpr (fun t _ => sixGateDiagBlock_det_ne_zero n t)

/-- Conjugation by `D_L * W * (·) * Wᵀ * D_R`. -/
def sixGateScaledMatrix (n : ℕ) (A : Matrix (Fin (rank n)) (Fin (rank n)) ℚ) :
    Matrix (Fin (rank n)) (Fin (rank n)) ℚ :=
  sixGateLeftDiag n * sixGateInvEvalMatrix n * A *
    (sixGateInvEvalMatrix n).transpose * sixGateRightDiag n

private theorem sixGateScaledMatrix_apply (n : ℕ)
    (A : Matrix (Fin (rank n)) (Fin (rank n)) ℚ) (k₁ k₂ : Fin (rank n)) :
    sixGateScaledMatrix n A k₁ k₂ =
      (gatePrime n : ℚ) ^ (sixGateLeftExp n k₁ + sixGateRightExp n k₂) *
        ∑ i : Fin (rank n), ∑ j : Fin (rank n),
          sixGateInvEvalMatrix n k₁ i * A i j * sixGateInvEvalMatrix n k₂ j := by
  unfold sixGateScaledMatrix sixGateLeftDiag sixGateRightDiag
  rw [Matrix.mul_diagonal, Matrix.mul_assoc (Matrix.diagonal _),
    Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul]
  have hmid : (sixGateInvEvalMatrix n * (A * (sixGateInvEvalMatrix n).transpose)) k₁ k₂ =
      ∑ i : Fin (rank n), ∑ j : Fin (rank n),
        sixGateInvEvalMatrix n k₁ i * A i j * sixGateInvEvalMatrix n k₂ j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [Matrix.mul_assoc (sixGateInvEvalMatrix n), hmid, pow_add]
  ring

private theorem coeff_triple_mul (U E₁ E₂ : ℚ[X]) (s : ℕ) :
    (U * E₁ * E₂).coeff s =
      ∑ r ∈ range (s + 1), ∑ a' ∈ range (s - r + 1),
        U.coeff r * E₁.coeff a' * E₂.coeff (s - r - a') := by
  rw [mul_assoc, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun r u => U.coeff r * (E₁ * E₂).coeff u)]
  apply Finset.sum_congr rfl
  intro r _
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a' b' => E₁.coeff a' * E₂.coeff b'), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a' _
  ring

/-- Regular remainder contribution is in `p * ℤ_(p)`, hence `ℤ_(p)`-integral and `0 mod p`. -/
private theorem sixGateScaled_regular_mem_and_zero (n : ℕ) [Fact (gatePrime n).Prime]
    (q : Fin 6 → ℚ) (hq : ∀ s : Fin 6, q s ∈ sixGateIntegralRing (gatePrime n))
    (k₁ k₂ : Fin (rank n)) :
    let Hreg : Matrix (Fin (rank n)) (Fin (rank n)) ℚ :=
      fun i j => MvPolynomial.eval q (sixMatrix n i j) - sixSingularEntry n i j
    sixGateScaledMatrix n Hreg k₁ k₂ ∈ sixGateIntegralRing (gatePrime n) ∧
      ((sixGateScaledMatrix n Hreg k₁ k₂ : ℚ) : ZMod (gatePrime n)) = 0 := by
  intro Hreg
  let p := gatePrime n
  let S := sixGateIntegralRing p
  rw [sixGateScaledMatrix_apply]
  have hsum_mem : (∑ i : Fin (rank n), ∑ j : Fin (rank n),
      sixGateInvEvalMatrix n k₁ i * Hreg i j * sixGateInvEvalMatrix n k₂ j) ∈ S := by
    apply S.sum_mem; intro i _
    apply S.sum_mem; intro j _
    exact S.mul_mem
      (S.mul_mem (sixGateInvEvalMatrix_mem n k₁ i)
        (sixMatrix_eval_sub_singular_mem n q hq i j))
      (sixGateInvEvalMatrix_mem n k₂ j)
  have hexp_pos : 1 ≤ sixGateLeftExp n k₁ + sixGateRightExp n k₂ := by
    unfold sixGateLeftExp sixGateRightExp
    have h1 := ((sixGateIndexEquiv n).symm k₁).2.isLt
    have h2 := ((sixGateIndexEquiv n).symm k₂).2.isLt
    omega
  refine ⟨S.mul_mem (S.pow_mem (natCast_mem S p) _) hsum_mem, ?_⟩
  exact sixGateReduction_p_pow_mul_eq_zero p hexp_pos _ hsum_mem

/-- Entrywise expansion of `D_L * W * H_sing * Wᵀ * D_R` as a finite sum over `(t, s, r, a')`. -/
private theorem sixGateScaled_singular_expand (n : ℕ) [Fact (gatePrime n).Prime]
    (k₁ k₂ : Fin (rank n)) :
    let Hsing : Matrix (Fin (rank n)) (Fin (rank n)) ℚ := sixSingularEntry n
    sixGateScaledMatrix n Hsing k₁ k₂ =
      ∑ t : Fin (5 * n),
        ∑ s ∈ range (sixPoleOrder n (gateTailPole n t)),
          ∑ r ∈ range (s + 1),
            ∑ a' ∈ range (s - r + 1),
              (-1 : ℚ) ^ ((sixGateTailZeroCount n t).val + 1) *
                ((8 - s).choose (sixPoleOrder n (gateTailPole n t) - 1 - s) : ℚ) *
                (sixGateUnitSeries n t).coeff r *
                sixGateWJet n k₁ t a' *
                sixGateWJet n k₂ t (s - r - a') *
                ((gatePrime n : ℚ) ^ (sixGateLeftExp n k₁ + sixGateRightExp n k₂) *
                  (gatePrime n : ℚ) ^ (-(9 : ℤ) + (s : ℤ))) := by
  intro Hsing
  rw [sixGateScaledMatrix_apply]
  let p : ℚ := (gatePrime n : ℚ)
  let e : ℕ := sixGateLeftExp n k₁ + sixGateRightExp n k₂
  -- Rewrite inner sum over (i, j) using `sixSingularEntry_eq_collapsed` and `coeff_triple_mul`
  have hinner : (∑ i : Fin (rank n), ∑ j : Fin (rank n),
      sixGateInvEvalMatrix n k₁ i * Hsing i j * sixGateInvEvalMatrix n k₂ j) =
      ∑ t : Fin (5 * n),
        ∑ s ∈ range (sixPoleOrder n (gateTailPole n t)),
          ∑ r ∈ range (s + 1),
            ∑ a' ∈ range (s - r + 1),
              (-1 : ℚ) ^ ((sixGateTailZeroCount n t).val + 1) *
                ((8 - s).choose (sixPoleOrder n (gateTailPole n t) - 1 - s) : ℚ) *
                (sixGateUnitSeries n t).coeff r *
                sixGateWJet n k₁ t a' *
                sixGateWJet n k₂ t (s - r - a') *
                p ^ (-(9 : ℤ) + (s : ℤ)) := by
    have hstep1 : ∀ i j : Fin (rank n),
        sixGateInvEvalMatrix n k₁ i * Hsing i j * sixGateInvEvalMatrix n k₂ j =
        ∑ t : Fin (5 * n),
          ∑ s ∈ range (sixPoleOrder n (gateTailPole n t)),
            ∑ r ∈ range (s + 1),
              ∑ a' ∈ range (s - r + 1),
                (-1 : ℚ) ^ ((sixGateTailZeroCount n t).val + 1) *
                  ((8 - s).choose (sixPoleOrder n (gateTailPole n t) - 1 - s) : ℚ) *
                  (sixGateUnitSeries n t).coeff r *
                  (sixGateInvEvalMatrix n k₁ i *
                    (taylor (gateNode n t : ℚ) (evenBasis i.val)).coeff a') *
                  (sixGateInvEvalMatrix n k₂ j *
                    (taylor (gateNode n t : ℚ) (evenBasis j.val)).coeff (s - r - a')) *
                  p ^ (-(9 : ℤ) + (s : ℤ)) := by
      intro i j
      change sixGateInvEvalMatrix n k₁ i * sixSingularEntry n i j *
        sixGateInvEvalMatrix n k₂ j = _
      rw [sixSingularEntry_eq_collapsed n i j, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro t _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro s _
      rw [coeff_triple_mul]
      simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro a' _
      ring
    simp_rw [hstep1]
    -- Commute (∑ i, ∑ j) inside (∑ t, ∑ s, ∑ r, ∑ a')
    have hswap1 : ∀ (f : Fin (rank n) → Fin (rank n) → Fin (5 * n) → ℚ),
        (∑ i, ∑ j, ∑ t, f i j t) = ∑ t, ∑ i, ∑ j, f i j t := by
      intro f
      calc
        (∑ i, ∑ j, ∑ t, f i j t) = ∑ i, ∑ t, ∑ j, f i j t := by
          apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
        _ = ∑ t, ∑ i, ∑ j, f i j t := Finset.sum_comm
    rw [hswap1]
    apply Finset.sum_congr rfl; intro t _
    have hswap2 : ∀ (S : Finset ℕ) (f : Fin (rank n) → Fin (rank n) → ℕ → ℚ),
        (∑ i, ∑ j, ∑ s ∈ S, f i j s) = ∑ s ∈ S, ∑ i, ∑ j, f i j s := by
      intro S f
      calc
        (∑ i, ∑ j, ∑ s ∈ S, f i j s) = ∑ i, ∑ s ∈ S, ∑ j, f i j s := by
          apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
        _ = ∑ s ∈ S, ∑ i, ∑ j, f i j s := Finset.sum_comm
    rw [hswap2]
    apply Finset.sum_congr rfl; intro s _
    rw [hswap2]
    apply Finset.sum_congr rfl; intro r _
    rw [hswap2]
    apply Finset.sum_congr rfl; intro a' _
    -- Factor out independent constants and separate i and j into `sixGateWJet`
    have hfactor : ∀ (c : ℚ) (u v : Fin (rank n) → ℚ) (d : ℚ),
        (∑ i : Fin (rank n), ∑ j : Fin (rank n), c * u i * v j * d) =
          c * (∑ i : Fin (rank n), u i) * (∑ j : Fin (rank n), v j) * d := by
      intro c u v d
      calc
        (∑ i : Fin (rank n), ∑ j : Fin (rank n), c * u i * v j * d)
            = ∑ i : Fin (rank n), (c * u i) * (∑ j : Fin (rank n), v j) * d := by
              apply Finset.sum_congr rfl; intro i _
              rw [Finset.mul_sum, Finset.sum_mul]
        _ = c * (∑ i : Fin (rank n), u i) * (∑ j : Fin (rank n), v j) * d := by
              rw [show c * (∑ i : Fin (rank n), u i) * (∑ j : Fin (rank n), v j) * d =
                  (∑ i : Fin (rank n), u i) * (c * (∑ j : Fin (rank n), v j) * d) by ring,
                Finset.sum_mul]
              apply Finset.sum_congr rfl; intro i _; ring
    exact hfactor _ _ _ _
  rw [hinner]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro a' _
  ring

/-- Every individual summand `(t, s, r, a')` of `D_L * W * H_sing * Wᵀ * D_R` is in `ℤ_(p)`,
and reduces mod `p` to `0` except at the unique diagonal block coordinate
`t = t₁ = t₂`, `r = 0`, `a' = a`, `s = a + b`. -/
private theorem sixGateScaled_singular_term_mem_and_cast (n : ℕ) [Fact (gatePrime n).Prime]
    (k₁ k₂ : Fin (rank n)) (t : Fin (5 * n)) (s r a' : ℕ)
    (_hs : s < sixPoleOrder n (gateTailPole n t)) (hr : r ≤ s) (ha' : a' ≤ s - r) :
    let p := gatePrime n
    let p₁ := (sixGateIndexEquiv n).symm k₁
    let p₂ := (sixGateIndexEquiv n).symm k₂
    let term : ℚ :=
      (-1 : ℚ) ^ ((sixGateTailZeroCount n t).val + 1) *
        ((8 - s).choose (sixPoleOrder n (gateTailPole n t) - 1 - s) : ℚ) *
        (sixGateUnitSeries n t).coeff r *
        sixGateWJet n k₁ t a' *
        sixGateWJet n k₂ t (s - r - a') *
        ((p : ℚ) ^ (sixGateLeftExp n k₁ + sixGateRightExp n k₂) *
          (p : ℚ) ^ (-(9 : ℤ) + (s : ℤ)))
    term ∈ sixGateIntegralRing p ∧
      ((term : ℚ) : ZMod p) =
        if t = p₁.1 ∧ p₁.1 = p₂.1 ∧ r = 0 ∧ a' = p₁.2.val ∧ s = p₁.2.val + p₂.2.val then
          sixGateDiagBlock n p₁.1 p₁.2 p₂.2
        else 0 := by
  intro p p₁ p₂ term
  have hp : p.Prime := Fact.out
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let S := sixGateIntegralRing p
  let b' : ℕ := s - r - a'
  let a := p₁.2
  let b := p₂.2
  have ha_lt : a.val < 3 := a.isLt
  have hb_lt : b.val < 3 := b.isLt
  have he_eq : sixGateLeftExp n k₁ + sixGateRightExp n k₂ = 9 - a.val - b.val := by
    unfold sixGateLeftExp sixGateRightExp
    change (5 - a.val) + (4 - b.val) = 9 - a.val - b.val
    omega
  have hbase_mem : (-1 : ℚ) ^ ((sixGateTailZeroCount n t).val + 1) *
      ((8 - s).choose (sixPoleOrder n (gateTailPole n t) - 1 - s) : ℚ) *
      (sixGateUnitSeries n t).coeff r *
      sixGateWJet n k₁ t a' *
      sixGateWJet n k₂ t b' ∈ S :=
    S.mul_mem
      (S.mul_mem
        (S.mul_mem
          (S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _) (natCast_mem S _))
          (sixGateUnitSeries_in_subring n t r))
        (sixGateWJet_mem n k₁ t a'))
      (sixGateWJet_mem n k₂ t b')
  -- Helper when the combined p-exponent is a positive natural number `d ≥ 1`
  have hpos_exp : ∀ d : ℕ, 1 ≤ d →
      ((sixGateLeftExp n k₁ + sixGateRightExp n k₂ : ℕ) : ℤ) + (-(9 : ℤ) + (s : ℤ)) = (d : ℤ) →
      term ∈ S ∧ ((term : ℚ) : ZMod p) = 0 := by
    intro d hd hdeq
    have hpp : (p : ℚ) ^ (sixGateLeftExp n k₁ + sixGateRightExp n k₂) *
        (p : ℚ) ^ (-(9 : ℤ) + (s : ℤ)) = (p : ℚ) ^ d := by
      rw [← zpow_natCast (p : ℚ), ← zpow_add₀ hpne, hdeq, zpow_natCast]
    have hterm_eq : term = (p : ℚ) ^ d *
        ((-1 : ℚ) ^ ((sixGateTailZeroCount n t).val + 1) *
          ((8 - s).choose (sixPoleOrder n (gateTailPole n t) - 1 - s) : ℚ) *
          (sixGateUnitSeries n t).coeff r *
          sixGateWJet n k₁ t a' *
          sixGateWJet n k₂ t b') := by
      dsimp [term, b']
      rw [hpp]; ring
    rw [hterm_eq]
    exact ⟨S.mul_mem (S.pow_mem (natCast_mem S p) d) hbase_mem,
      sixGateReduction_p_pow_mul_eq_zero p hd _ hbase_mem⟩
  -- Helper when the term is literally 0
  have hzero_term : term = 0 →
      ¬ (t = p₁.1 ∧ p₁.1 = p₂.1 ∧ r = 0 ∧ a' = a.val ∧ s = a.val + b.val) →
      term ∈ S ∧ ((term : ℚ) : ZMod p) =
        if t = p₁.1 ∧ p₁.1 = p₂.1 ∧ r = 0 ∧ a' = a.val ∧ s = a.val + b.val then
          sixGateDiagBlock n p₁.1 a b
        else 0 := by
    intro ht0 hcond
    rw [ht0, ite_eq_right (fun h => (hcond h).elim)]
    exact ⟨S.zero_mem, by simp⟩
  -- Four-case split on `a' < 3` and `b' < 3`
  by_cases ha3 : a' < 3
  · have hw1 := sixGateWJet_lt_three n k₁ t ⟨a', ha3⟩
    by_cases hk1 : k₁ = sixGateIndexEquiv n (t, ⟨a', ha3⟩)
    · have hp1_eq : p₁ = (t, ⟨a', ha3⟩) := by
        dsimp [p₁]; rw [hk1, Equiv.symm_apply_apply]
      have ht1 : t = p₁.1 := by rw [hp1_eq]
      have ha_eq : a' = a.val := by
        have := congrArg (fun x : Fin (5 * n) × Fin 3 => x.2.val) hp1_eq
        exact this.symm
      by_cases hb3 : b' < 3
      · have hw2 := sixGateWJet_lt_three n k₂ t ⟨b', hb3⟩
        by_cases hk2 : k₂ = sixGateIndexEquiv n (t, ⟨b', hb3⟩)
        · have hp2_eq : p₂ = (t, ⟨b', hb3⟩) := by
            dsimp [p₂]; rw [hk2, Equiv.symm_apply_apply]
          have ht2 : p₁.1 = p₂.1 := by rw [hp1_eq, hp2_eq]
          have hb_eq : b' = b.val := by
            have := congrArg (fun x : Fin (5 * n) × Fin 3 => x.2.val) hp2_eq
            exact this.symm
          by_cases hr0 : r = 0
          · -- The unique surviving diagonal-block entry!
            have hs_eq : s = a.val + b.val := by omega
            have hcond : (t = p₁.1 ∧ p₁.1 = p₂.1 ∧ r = 0 ∧ a' = p₁.2.val ∧ s = p₁.2.val + p₂.2.val) ↔ True :=
              iff_true_intro ⟨ht1, ht2, hr0, ha_eq, hs_eq⟩
            rw [if_congr hcond rfl rfl]
            simp only [ite_true]
            have hpp1 : (p : ℚ) ^ (sixGateLeftExp n k₁ + sixGateRightExp n k₂) *
                (p : ℚ) ^ (-(9 : ℤ) + (s : ℤ)) = 1 := by
              rw [← zpow_natCast (p : ℚ), ← zpow_add₀ hpne]
              have hexp0 : ((sixGateLeftExp n k₁ + sixGateRightExp n k₂ : ℕ) : ℤ) +
                  (-(9 : ℤ) + (s : ℤ)) = 0 := by omega
              rw [hexp0, zpow_zero]
            have hw1_one : sixGateWJet n k₁ t a' = 1 := by simpa [hk1] using hw1
            have hw2_one : sixGateWJet n k₂ t b' = 1 := by simpa [hk2] using hw2
            have hterm_simp : term =
                (-1 : ℚ) ^ ((sixGateTailZeroCount n p₁.1).val + 1) *
                  ((8 - a.val - b.val).choose ((sixGateTailZeroCount n p₁.1).val + 4 - a.val - b.val) : ℚ) *
                  (sixGateUnitSeries n p₁.1).coeff 0 := by
              dsimp [term]
              change (-1 : ℚ) ^ ((sixGateTailZeroCount n t).val + 1) *
                  ((8 - s).choose (sixPoleOrder n (gateTailPole n t) - 1 - s) : ℚ) *
                  (sixGateUnitSeries n t).coeff r *
                  sixGateWJet n k₁ t a' *
                  sixGateWJet n k₂ t b' *
                  ((p : ℚ) ^ (sixGateLeftExp n k₁ + sixGateRightExp n k₂) *
                    (p : ℚ) ^ (-(9 : ℤ) + (s : ℤ))) = _
              rw [hw1_one, hw2_one, hpp1, hr0, ht1, sixGateTailOrder_eq n p₁.1, hs_eq]
              have h1 : 8 - (a.val + b.val) = 8 - a.val - b.val := by omega
              have h2 : (sixGateTailZeroCount n p₁.1).val + 5 - 1 - (a.val + b.val) =
                  (sixGateTailZeroCount n p₁.1).val + 4 - a.val - b.val := by omega
              rw [h1, h2]
              ring
            rw [hterm_simp]
            have hm1 : (-1 : ℚ) ^ ((sixGateTailZeroCount n p₁.1).val + 1) ∈ S :=
              S.pow_mem (S.neg_mem S.one_mem) _
            have hm2 : ((8 - a.val - b.val).choose
                ((sixGateTailZeroCount n p₁.1).val + 4 - a.val - b.val) : ℚ) ∈ S :=
              natCast_mem S _
            have hm3 : (sixGateUnitSeries n p₁.1).coeff 0 ∈ S :=
              sixGateUnitSeries_in_subring n p₁.1 0
            refine ⟨S.mul_mem (S.mul_mem hm1 hm2) hm3, ?_⟩
            rw [sixGateIntegralRing_cast_mul p (S.mul_mem hm1 hm2) hm3,
              sixGateIntegralRing_cast_mul p hm1 hm2,
              sixGateIntegralRing_cast_pow p (S.neg_mem S.one_mem)]
            have hneg1 : ((-1 : ℚ) : ZMod p) = -1 := by simp
            rw [hneg1, Rat.cast_natCast]
            unfold sixGateDiagBlock sixGateBlock
            simp only [Matrix.smul_apply, smul_eq_mul]
            change (-1 : ZMod p) ^ ((sixGateTailZeroCount n p₁.1).val + 1) *
                (((8 - a.val - b.val).choose ((sixGateTailZeroCount n p₁.1).val + 4 - a.val - b.val) : ℕ) : ZMod p) *
                ((sixGateUnitSeries n p₁.1).coeff 0 : ZMod p) =
              (-1 : ZMod p) ^ ((sixGateTailZeroCount n p₁.1).val + 1) *
                ((sixGateUnitSeries n p₁.1).coeff 0 : ZMod p) *
                (((8 - a.val - b.val).choose ((sixGateTailZeroCount n p₁.1).val + 4 - a.val - b.val) : ℤ) : ZMod p)
            rw [Int.cast_natCast]
            ring
          · -- `r ≥ 1`: exponent is `r ≥ 1`, vanishes mod `p`
            have hcond : ¬ (t = p₁.1 ∧ p₁.1 = p₂.1 ∧ r = 0 ∧ a' = a.val ∧ s = a.val + b.val) :=
              fun h => hr0 h.2.2.1
            rw [ite_eq_right (fun h => (hcond h).elim)]
            exact hpos_exp r (by omega) (by omega)
        · -- `k₂ ≠ equiv (t, b')`: `wJet k₂ t b' = 0`
          have hw2_zero : sixGateWJet n k₂ t b' = 0 := by simpa [hk2] using hw2
          have ht0 : term = 0 := by
            dsimp [term]; change _ * sixGateWJet n k₂ t b' * _ = 0
            rw [hw2_zero]; ring
          have hcond : ¬ (t = p₁.1 ∧ p₁.1 = p₂.1 ∧ r = 0 ∧ a' = a.val ∧ s = a.val + b.val) := by
            rintro ⟨ht', ht12, hr', ha'', hs'⟩
            apply hk2
            have hb_val : b' = b.val := by omega
            have hpair : (t, (⟨b', hb3⟩ : Fin 3)) = p₂ :=
              Prod.ext (ht'.trans ht12) (Fin.ext hb_val)
            rw [hpair, Equiv.apply_symm_apply]
          exact hzero_term ht0 hcond
      · -- `a' < 3`, `k₁ = equiv(t, a')`, `b' ≥ 3`: exponent `r + (b' - b) ≥ 1`
        have hcond : ¬ (t = p₁.1 ∧ p₁.1 = p₂.1 ∧ r = 0 ∧ a' = a.val ∧ s = a.val + b.val) := by
          rintro ⟨_, _, hr', ha'', hs'⟩; omega
        rw [ite_eq_right (fun h => (hcond h).elim)]
        exact hpos_exp (r + b' - b.val) (by omega) (by omega)
    · -- `k₁ ≠ equiv(t, a')`: `wJet k₁ t a' = 0`
      have hw1_zero : sixGateWJet n k₁ t a' = 0 := by simpa [hk1] using hw1
      have ht0 : term = 0 := by
        dsimp [term]; rw [hw1_zero]; ring
      have hcond : ¬ (t = p₁.1 ∧ p₁.1 = p₂.1 ∧ r = 0 ∧ a' = a.val ∧ s = a.val + b.val) := by
        rintro ⟨ht', _, _, ha'', _⟩
        apply hk1
        have hpair : (t, (⟨a', ha3⟩ : Fin 3)) = p₁ :=
          Prod.ext ht' (Fin.ext ha'')
        rw [hpair, Equiv.apply_symm_apply]
      exact hzero_term ht0 hcond
  · -- `a' ≥ 3`
    have hcond : ¬ (t = p₁.1 ∧ p₁.1 = p₂.1 ∧ r = 0 ∧ a' = a.val ∧ s = a.val + b.val) := by
      rintro ⟨_, _, _, ha'', _⟩; omega
    by_cases hb3 : b' < 3
    · have hw2 := sixGateWJet_lt_three n k₂ t ⟨b', hb3⟩
      by_cases hk2 : k₂ = sixGateIndexEquiv n (t, ⟨b', hb3⟩)
      · have hp2_eq : p₂ = (t, ⟨b', hb3⟩) := by
          dsimp [p₂]; rw [hk2, Equiv.symm_apply_apply]
        have hb_eq : b' = b.val := by
          have := congrArg (fun x : Fin (5 * n) × Fin 3 => x.2.val) hp2_eq
          exact this.symm
        rw [ite_eq_right (fun h => (hcond h).elim)]
        exact hpos_exp (r + a' - a.val) (by omega) (by omega)
      · have hw2_zero : sixGateWJet n k₂ t b' = 0 := by simpa [hk2] using hw2
        have ht0 : term = 0 := by
          dsimp [term]; change _ * sixGateWJet n k₂ t b' * _ = 0
          rw [hw2_zero]; ring
        exact hzero_term ht0 hcond
    · -- `a' ≥ 3` and `b' ≥ 3`: exponent `r + (a' - a) + (b' - b) ≥ 2 ≥ 1`
      rw [ite_eq_right (fun h => (hcond h).elim)]
      exact hpos_exp (r + a' - a.val + b' - b.val) (by omega) (by omega)

/-- Entrywise integrality and mod-`p` reduction of `D_L * W * H_sing * Wᵀ * D_R`. -/
private theorem sixGateScaled_singular_mem_and_cast (n : ℕ) [Fact (gatePrime n).Prime]
    (k₁ k₂ : Fin (rank n)) :
    let Hsing : Matrix (Fin (rank n)) (Fin (rank n)) ℚ := sixSingularEntry n
    sixGateScaledMatrix n Hsing k₁ k₂ ∈ sixGateIntegralRing (gatePrime n) ∧
      ((sixGateScaledMatrix n Hsing k₁ k₂ : ℚ) : ZMod (gatePrime n)) =
        sixGateTargetMod n k₁ k₂ := by
  intro Hsing
  let p := gatePrime n
  let S := sixGateIntegralRing p
  let p₁ := (sixGateIndexEquiv n).symm k₁
  let p₂ := (sixGateIndexEquiv n).symm k₂
  rw [sixGateScaled_singular_expand n k₁ k₂]
  let f : Fin (5 * n) → ℕ → ℕ → ℕ → ℚ := fun t s r a' =>
    (-1 : ℚ) ^ ((sixGateTailZeroCount n t).val + 1) *
      ((8 - s).choose (sixPoleOrder n (gateTailPole n t) - 1 - s) : ℚ) *
      (sixGateUnitSeries n t).coeff r *
      sixGateWJet n k₁ t a' *
      sixGateWJet n k₂ t (s - r - a') *
      ((p : ℚ) ^ (sixGateLeftExp n k₁ + sixGateRightExp n k₂) *
        (p : ℚ) ^ (-(9 : ℤ) + (s : ℤ)))
  have hmem : ∀ t : Fin (5 * n), ∀ s ∈ range (sixPoleOrder n (gateTailPole n t)),
      ∀ r ∈ range (s + 1), ∀ a' ∈ range (s - r + 1), f t s r a' ∈ S := by
    intro t s hs r hr a' ha'
    exact (sixGateScaled_singular_term_mem_and_cast n k₁ k₂ t s r a'
      (mem_range.mp hs) (Nat.lt_succ_iff.mp (mem_range.mp hr))
      (Nat.lt_succ_iff.mp (mem_range.mp ha'))).1
  refine ⟨?_, ?_⟩
  · apply S.sum_mem; intro t _
    apply S.sum_mem; intro s hs
    apply S.sum_mem; intro r hr
    apply S.sum_mem; intro a' ha'
    exact hmem t s hs r hr a' ha'
  · rw [sixGateIntegralRing_cast_sum p _ _ (fun t _ =>
      S.sum_mem fun s hs => S.sum_mem fun r hr => S.sum_mem fun a' ha' => hmem t s hs r hr a' ha')]
    have hcast_t : ∀ t : Fin (5 * n),
        ((∑ s ∈ range (sixPoleOrder n (gateTailPole n t)),
          ∑ r ∈ range (s + 1), ∑ a' ∈ range (s - r + 1), f t s r a' : ℚ) : ZMod p) =
        ∑ s ∈ range (sixPoleOrder n (gateTailPole n t)),
          ∑ r ∈ range (s + 1), ∑ a' ∈ range (s - r + 1),
            if t = p₁.1 ∧ p₁.1 = p₂.1 ∧ r = 0 ∧ a' = p₁.2.val ∧ s = p₁.2.val + p₂.2.val then
              sixGateDiagBlock n p₁.1 p₁.2 p₂.2
            else 0 := by
      intro t
      rw [sixGateIntegralRing_cast_sum p _ _ (fun s hs =>
        S.sum_mem fun r hr => S.sum_mem fun a' ha' => hmem t s hs r hr a' ha')]
      apply Finset.sum_congr rfl; intro s hs
      rw [sixGateIntegralRing_cast_sum p _ _ (fun r hr =>
        S.sum_mem fun a' ha' => hmem t s hs r hr a' ha')]
      apply Finset.sum_congr rfl; intro r hr
      rw [sixGateIntegralRing_cast_sum p _ _ (fun a' ha' => hmem t s hs r hr a' ha')]
      apply Finset.sum_congr rfl; intro a' ha'
      exact (sixGateScaled_singular_term_mem_and_cast n k₁ k₂ t s r a'
        (mem_range.mp hs) (Nat.lt_succ_iff.mp (mem_range.mp hr))
        (Nat.lt_succ_iff.mp (mem_range.mp ha'))).2
    simp_rw [hcast_t]
    change (∑ t : Fin (5 * n), ∑ s ∈ range (sixPoleOrder n (gateTailPole n t)),
        ∑ r ∈ range (s + 1), ∑ a' ∈ range (s - r + 1),
          if t = p₁.1 ∧ p₁.1 = p₂.1 ∧ r = 0 ∧ a' = p₁.2.val ∧ s = p₁.2.val + p₂.2.val then
            sixGateDiagBlock n p₁.1 p₁.2 p₂.2
          else 0) =
      if p₁.1 = p₂.1 then sixGateDiagBlock n p₁.1 p₁.2 p₂.2 else 0
    by_cases ht12 : p₁.1 = p₂.1
    · conv_rhs => simp only [ht12, ↓reduceIte]
      rw [Finset.sum_eq_single p₁.1]
      · have hs_mem : p₁.2.val + p₂.2.val ∈ range (sixPoleOrder n (gateTailPole n p₁.1)) := by
          rw [mem_range, sixGateTailOrder_eq]
          have h1 := p₁.2.isLt; have h2 := p₂.2.isLt; omega
        rw [Finset.sum_eq_single (p₁.2.val + p₂.2.val)]
        · rw [Finset.sum_eq_single 0]
          · rw [Finset.sum_eq_single p₁.2.val]
            · simp [ht12]
            · intro a' _ hne; simp [hne]
            · intro h; exact (h (mem_range.mpr (by omega))).elim
          · intro r _ hne; apply Finset.sum_eq_zero; intro a' _; simp [hne]
          · intro h; exact (h (mem_range.mpr (by omega))).elim
        · intro s _ hne
          apply Finset.sum_eq_zero; intro r _
          apply Finset.sum_eq_zero; intro a' _
          simp [hne]
        · intro h; exact (h hs_mem).elim
      · intro t _ hne
        apply Finset.sum_eq_zero; intro s _
        apply Finset.sum_eq_zero; intro r _
        apply Finset.sum_eq_zero; intro a' _
        simp [hne]
      · intro h; exact (h (mem_univ _)).elim
    · conv_rhs => simp only [ht12, ↓reduceIte]
      apply Finset.sum_eq_zero; intro t _
      apply Finset.sum_eq_zero; intro s _
      apply Finset.sum_eq_zero; intro r _
      apply Finset.sum_eq_zero; intro a' _
      simp [ht12]

/-- Entrywise integrality and mod-`p` reduction of `M = D_L * W * H(q) * Wᵀ * D_R`. -/
theorem sixGateScaled_H_mem_and_cast (n : ℕ) [Fact (gatePrime n).Prime]
    (q : Fin 6 → ℚ) (hq : ∀ s : Fin 6, q s ∈ sixGateIntegralRing (gatePrime n))
    (k₁ k₂ : Fin (rank n)) :
    let H : Matrix (Fin (rank n)) (Fin (rank n)) ℚ := (sixMatrix n).map (MvPolynomial.eval q)
    sixGateScaledMatrix n H k₁ k₂ ∈ sixGateIntegralRing (gatePrime n) ∧
      ((sixGateScaledMatrix n H k₁ k₂ : ℚ) : ZMod (gatePrime n)) =
        sixGateTargetMod n k₁ k₂ := by
  intro H
  let Hreg : Matrix (Fin (rank n)) (Fin (rank n)) ℚ :=
    fun i j => MvPolynomial.eval q (sixMatrix n i j) - sixSingularEntry n i j
  let Hsing : Matrix (Fin (rank n)) (Fin (rank n)) ℚ := sixSingularEntry n
  have hsplit : H = Hreg + Hsing := by
    ext i j
    change MvPolynomial.eval q (sixMatrix n i j) =
      (MvPolynomial.eval q (sixMatrix n i j) - sixSingularEntry n i j) + sixSingularEntry n i j
    ring
  have hM : sixGateScaledMatrix n H =
      sixGateScaledMatrix n Hreg + sixGateScaledMatrix n Hsing := by
    unfold sixGateScaledMatrix
    rw [hsplit, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  rw [hM, Matrix.add_apply]
  have hreg := sixGateScaled_regular_mem_and_zero n q hq k₁ k₂
  have hsing := sixGateScaled_singular_mem_and_cast n k₁ k₂
  refine ⟨(sixGateIntegralRing (gatePrime n)).add_mem hreg.1 hsing.1, ?_⟩
  rw [sixGateIntegralRing_cast_add (gatePrime n) hreg.1 hsing.1, hreg.2, hsing.2, zero_add]

/-! ## Exact `p`-adic valuation `v_p(det 𝓗_n(q)) = -105n` and nonvanishing -/

private theorem padicValRat_pow_nat (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : x ≠ 0) (k : ℕ) :
    padicValRat p (x ^ k) = (k : ℤ) * padicValRat p x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, padicValRat.mul (pow_ne_zero k hx) hx, ih]
    push_cast
    ring

/-- For every prime `p = 50n + 1` and every `p`-integral rational tuple `q ∈ ℤ_(p)^6`,
`det 𝓗_n(q) ≠ 0` and `v_p(det 𝓗_n(q)) = -105n`. -/
theorem sixGate_rational_det_valuation (n : ℕ) [Fact (gatePrime n).Prime]
    (q : Fin 6 → ℚ) (hq : ∀ s : Fin 6, q s ∈ sixGateIntegralRing (gatePrime n)) :
    let H : Matrix (Fin (rank n)) (Fin (rank n)) ℚ := (sixMatrix n).map (MvPolynomial.eval q)
    H.det ≠ 0 ∧ padicValRat (gatePrime n) H.det = -(105 * (n : ℤ)) := by
  intro H
  let p := gatePrime n
  have hp : p.Prime := Fact.out
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let M : Matrix (Fin (rank n)) (Fin (rank n)) ℚ := sixGateScaledMatrix n H
  let M_loc : Matrix (Fin (rank n)) (Fin (rank n)) (sixGateIntegralRing p) :=
    fun k₁ k₂ => ⟨M k₁ k₂, (sixGateScaled_H_mem_and_cast n q hq k₁ k₂).1⟩
  have hM_sub : (sixGateIntegralRing p).subtype.mapMatrix M_loc = M := by
    ext k₁ k₂; rfl
  have hM_red : (sixGateReduction p).mapMatrix M_loc = sixGateTargetMod n := by
    ext k₁ k₂
    exact (sixGateScaled_H_mem_and_cast n q hq k₁ k₂).2
  have hMdet_sub : (M_loc.det : ℚ) = M.det := by
    rw [← hM_sub, ← RingHom.map_det]; rfl
  have hMdet_red : sixGateReduction p M_loc.det = (sixGateTargetMod n).det := by
    rw [← hM_red, ← RingHom.map_det]
  have hMunit : M.det ≠ 0 ∧ padicValRat p M.det = 0 := by
    have hne : sixGateReduction p M_loc.det ≠ 0 := by
      rw [hMdet_red]
      exact sixGateTargetMod_det_ne_zero n
    have hu := (sixGateReduction_ne_zero_iff p M_loc.det).mp hne
    rwa [hMdet_sub] at hu
  have hMdet_eq : M.det =
      (p : ℚ) ^ (105 * n) * (sixGateInvEvalMatrix n).det ^ 2 * H.det := by
    dsimp [M, sixGateScaledMatrix]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, sixGateLeftDiag_det, sixGateRightDiag_det]
    have hpow : (p : ℚ) ^ (60 * n) * (p : ℚ) ^ (45 * n) = (p : ℚ) ^ (105 * n) := by
      rw [← pow_add]; congr 1; omega
    calc
      (p : ℚ) ^ (60 * n) * (sixGateInvEvalMatrix n).det * H.det *
          (sixGateInvEvalMatrix n).det * (p : ℚ) ^ (45 * n)
          = ((p : ℚ) ^ (60 * n) * (p : ℚ) ^ (45 * n)) *
              (sixGateInvEvalMatrix n).det ^ 2 * H.det := by ring
      _ = _ := by rw [hpow]
  have hHne : H.det ≠ 0 := by
    intro h0
    apply hMunit.1
    rw [hMdet_eq, h0, mul_zero]
  refine ⟨hHne, ?_⟩
  have hW := sixGateInvEvalMatrix_det_unit n
  have h105ne : (p : ℚ) ^ (105 * n) ≠ 0 := pow_ne_zero _ hpne
  have hW2ne : (sixGateInvEvalMatrix n).det ^ 2 ≠ 0 := pow_ne_zero 2 hW.1
  have hv := hMunit.2
  rw [hMdet_eq, padicValRat.mul (mul_ne_zero h105ne hW2ne) hHne,
    padicValRat.mul h105ne hW2ne, padicValRat_pow_nat p hpne (105 * n),
    padicValRat_pow_nat p hW.1 2, padicValRat.self hp.one_lt, hW.2] at hv
  simp only [mul_one, mul_zero, add_zero, Nat.cast_mul, Nat.cast_ofNat] at hv
  dsimp only [p] at hv
  omega

/-- Consequence: `P_n(q) ≠ 0` whenever `50n + 1` is prime and `q ∈ ℤ_(50n + 1)^6`. -/
theorem sixGate_primitivePolynomial_ne_zero (n : ℕ) [Fact (gatePrime n).Prime]
    (q : Fin 6 → ℚ) (hq : ∀ s : Fin 6, q s ∈ sixGateIntegralRing (gatePrime n)) :
    (sixPrimitivePolynomial n).eval₂ (Int.castRingHom ℚ) q ≠ 0 := by
  have hdet := (sixGate_rational_det_valuation n q hq).1
  have hpoly : ((sixMatrix n).map (MvPolynomial.eval q)).det =
      sixPrimitiveScalar n * (sixPrimitivePolynomial n).eval₂ (Int.castRingHom ℚ) q := by
    have hmap : ((sixMatrix n).map (MvPolynomial.eval q)).det =
        MvPolynomial.eval q (sixMatrix n).det := by
      change ((MvPolynomial.eval q).mapMatrix (sixMatrix n)).det = _
      rw [← RingHom.map_det]
    rw [hmap, sixPrimitivePolynomial_det_eq n, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_map]
  intro h0
  apply hdet
  rw [hpoly, h0, mul_zero]

/-! ## Elementary prime gate (`p = 50n + 1`) and live closure of `SixGateHypothesis` -/

/-- Elementary prime gate: for every positive natural `Q` and threshold `N₀`,
there exists `n ≥ N₀` with `50n + 1` prime and `¬ (50n + 1) ∣ Q`. -/
theorem sixGate_exists_prime_above (Q N₀ : ℕ) (hQ : 0 < Q) :
    ∃ n : ℕ, N₀ ≤ n ∧ Nat.Prime (gatePrime n) ∧ ¬ gatePrime n ∣ Q := by
  obtain ⟨p, hp, hbound, hmod⟩ :=
    Nat.exists_prime_gt_modEq_one (max (50 * N₀ + 1) Q) (by decide : 50 ≠ 0)
  have hNp : 50 * N₀ + 1 < p := lt_of_le_of_lt (le_max_left _ _) hbound
  have hQp : Q < p := lt_of_le_of_lt (le_max_right _ _) hbound
  have hrem : p % 50 = 1 := by simpa [Nat.ModEq] using hmod
  have heq : gatePrime (p / 50) = p := by
    unfold gatePrime
    simpa [hrem] using Nat.div_add_mod p 50
  refine ⟨p / 50, by omega, ?_, ?_⟩
  · simpa only [heq] using hp
  · rw [heq]
    intro hdvd
    exact (not_le_of_gt hQp) (Nat.le_of_dvd hQ hdvd)

/-- **Stage 1B Main Theorem**: `SixGateHypothesis` is unconditionally proved
(using only Mathlib's elementary cyclotomic `Nat.exists_prime_gt_modEq_one`). -/
theorem sixGate_proved : SixGateHypothesis := by
  intro Q hQpos N₀
  have hQnat : 0 < Q.natAbs := Int.natAbs_pos.mpr hQpos.ne'
  obtain ⟨n, hn, hp, hnd⟩ := sixGate_exists_prime_above Q.natAbs N₀ hQnat
  have : Fact (gatePrime n).Prime := ⟨hp⟩
  refine ⟨n, hn, ?_⟩
  intro q hq
  apply sixGate_primitivePolynomial_ne_zero n q
  intro s
  obtain ⟨a, ha⟩ := hq s
  have hQne : (Q : ℚ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hqs : q s = (a : ℚ) * (Q : ℚ)⁻¹ := by
    apply mul_left_cancel₀ hQne
    rw [ha]
    field_simp
  rw [hqs]
  have hQval : padicValRat (gatePrime n) (Q : ℚ) = 0 := by
    have hndZ : ¬ ((gatePrime n : ℤ) ∣ Q) := fun hd =>
      hnd (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd))
    rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd hndZ
  exact (sixGateIntegralRing (gatePrime n)).mul_mem
    (intCast_mem _ a)
    (sixGateIntegralRing_inv_of_unit _ _ hQne hQval)

/-- Reduced endgame theorem: `SixGateHypothesis` is now discharged, so proving
`SixZetaIrrationalityStatement` requires only the arithmetic and analytic rate bounds
with `R_bound + C_bound < 0`. -/
theorem sixZeta_irrational_of_arith_and_analytic
    (R_bound C_bound : ℝ) (hsum : R_bound + C_bound < 0)
    (harith : SixArithRateHypothesis C_bound)
    (hanal : SixAnalyticRateHypothesis R_bound) :
    SixZetaIrrationalityStatement :=
  sixZeta_irrational_of_hypotheses R_bound C_bound hsum sixGate_proved harith hanal

end OddZetaSix
