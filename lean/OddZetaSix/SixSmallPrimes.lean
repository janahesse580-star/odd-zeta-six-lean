import OddZetaSix.SixIdentity
import OddZetaSix.SixTaylor
import OddZetaSix.SixGateLocal

/-!
# Stage 2A (File 2): Lemma 3 — Universal All-Prime-Power Denominator Bound & `p > 55n` Integrality

Proves:
1. Multivariate Gauss-valuation floor `FormalValAtLeast` and exact bridge to
   `padicValRat p (sixPrimitiveScalar n)`.
2. Exact block-wise factorization of `sixLocalCofactor n k` and `sixLocalNumerator n i j k`
   against the factorial normalization `sixNormalization n`, proving for EVERY prime `p`
   (with NO `p^2 > M₀` hypothesis) and `M₀ = 55 * n`:
   - `sixPrincipalCoefficients n i j k l` has `ValAtLeast p (-((13 - l.val) * Nat.log p (55 * n)))`;
   - `sixMatrix n i j` has `FormalValAtLeast p (-(18 * Nat.log p (55 * n)))`;
   - `sixMatrix_cleared_by_lcm_18`: `D_{M₀}^18 * (sixMatrix n i j)` has integer coefficients
     (for `M₀ = 55 * n` and `M₀ = 140 * n + 2`);
   - `sixPrimitiveScalar_universal_bound`: `-v_p(sixPrimitiveScalar n) ≤ 18 * (15n) * Nat.log p M₀`;
   - `sixPrimitiveScalar_large_prime_integral`: for `p > 55 * n`, `sixMatrix n` is entrywise
     `p`-integral and `0 ≤ v_p(sixPrimitiveScalar n)`.
-/

noncomputable section
set_option autoImplicit false

namespace OddZetaSix

open Polynomial Finset

/-! ## Multivariate Gauss-valuation floors and bridge to `sixPrimitiveScalar` -/

/-- Coefficientwise zero-safe `p`-adic valuation lower bound on `SixPolynomial`. -/
def FormalValAtLeast (p : ℕ) (a : ℤ) (F : SixPolynomial) : Prop :=
  ∀ m : Fin 6 →₀ ℕ, ValAtLeast p a (F.coeff m)

theorem formalValAtLeast_zero (p : ℕ) (a : ℤ) : FormalValAtLeast p a 0 := fun m => by
  simp [valAtLeast_zero]

theorem formalValAtLeast_mono {p : ℕ} {a b : ℤ} {F : SixPolynomial}
    (h : FormalValAtLeast p a F) (hab : b ≤ a) : FormalValAtLeast p b F :=
  fun m => valAtLeast_mono (h m) hab

theorem formalValAtLeast_C {p : ℕ} {a : ℤ} {c : ℚ} (hc : ValAtLeast p a c) :
    FormalValAtLeast p a (MvPolynomial.C c) := by
  intro m
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact hc
  · exact valAtLeast_zero p a

theorem formalValAtLeast_one (p : ℕ) [Fact p.Prime] : FormalValAtLeast p 0 1 := by
  simpa using formalValAtLeast_C (valAtLeast_one p)

theorem formalValAtLeast_X (p : ℕ) [Fact p.Prime] (s : Fin 6) :
    FormalValAtLeast p 0 (MvPolynomial.X s) := by
  intro m
  rw [MvPolynomial.X, MvPolynomial.coeff_monomial]
  split_ifs
  · exact valAtLeast_one p
  · exact valAtLeast_zero p 0

theorem formalValAtLeast_neg {p : ℕ} {a : ℤ} {F : SixPolynomial}
    (h : FormalValAtLeast p a F) : FormalValAtLeast p a (-F) := by
  intro m; rw [MvPolynomial.coeff_neg]; exact valAtLeast_neg (h m)

theorem formalValAtLeast_add {p : ℕ} [Fact p.Prime] {a : ℤ} {F G : SixPolynomial}
    (hF : FormalValAtLeast p a F) (hG : FormalValAtLeast p a G) :
    FormalValAtLeast p a (F + G) := by
  intro m
  have h : (F + G).coeff m = F.coeff m + G.coeff m := by simp
  rw [h]
  exact valAtLeast_add (hF m) (hG m)

theorem formalValAtLeast_sub {p : ℕ} [Fact p.Prime] {a : ℤ} {F G : SixPolynomial}
    (hF : FormalValAtLeast p a F) (hG : FormalValAtLeast p a G) :
    FormalValAtLeast p a (F - G) := by
  simpa only [sub_eq_add_neg] using formalValAtLeast_add hF (formalValAtLeast_neg hG)

theorem formalValAtLeast_mul {p : ℕ} [Fact p.Prime] {a b : ℤ} {F G : SixPolynomial}
    (hF : FormalValAtLeast p a F) (hG : FormalValAtLeast p b G) :
    FormalValAtLeast p (a + b) (F * G) := by
  intro m
  rw [MvPolynomial.coeff_mul]
  apply valAtLeast_sum
  intro x _
  exact valAtLeast_mul (hF x.1) (hG x.2)

theorem formalValAtLeast_C_mul {p : ℕ} [Fact p.Prime] {a b : ℤ} {c : ℚ} {F : SixPolynomial}
    (hc : ValAtLeast p a c) (hF : FormalValAtLeast p b F) :
    FormalValAtLeast p (a + b) (MvPolynomial.C c * F) :=
  formalValAtLeast_mul (formalValAtLeast_C hc) hF

theorem formalValAtLeast_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → SixPolynomial) (a : ℤ) (hf : ∀ i ∈ s, FormalValAtLeast p a (f i)) :
    FormalValAtLeast p a (∑ i ∈ s, f i) := by
  intro m
  rw [MvPolynomial.coeff_sum]
  exact valAtLeast_sum s (fun i => (f i).coeff m) a (fun i hi => hf i hi m)

theorem formalValAtLeast_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → SixPolynomial) (a : ι → ℤ) (hf : ∀ i ∈ s, FormalValAtLeast p (a i) (f i)) :
    FormalValAtLeast p (∑ i ∈ s, a i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using formalValAtLeast_one p
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact formalValAtLeast_mul (hf i (mem_insert_self _ _))
      (ih (fun j hj => hf j (mem_insert_of_mem hj)))

theorem formalValAtLeast_det_uniform {p h : ℕ} [Fact p.Prime]
    (M : Matrix (Fin h) (Fin h) SixPolynomial) (b : ℤ)
    (hM : ∀ i j : Fin h, FormalValAtLeast p b (M i j)) :
    FormalValAtLeast p ((h : ℤ) * b) M.det := by
  rw [Matrix.det_apply]
  apply formalValAtLeast_sum
  intro σ _
  have hprod := formalValAtLeast_prod (Finset.univ : Finset (Fin h))
    (fun i => M (σ i) i) (fun _ => b) (fun i _ => hM (σ i) i)
  have hsum : (∑ _i : Fin h, b) = (h : ℤ) * b := by
    simp [Finset.sum_const]
  rw [hsum] at hprod
  intro m
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact hprod m
  · rw [hs, Units.neg_smul, one_smul, MvPolynomial.coeff_neg]; exact valAtLeast_neg (hprod m)

/-- A primitive integer polynomial has some monomial coefficient not divisible by `p`. -/
theorem exists_primitive_coeff_not_dvd {σ : Type*} (P : MvPolynomial σ ℤ)
    (hprim : integerPolynomialContent P = 1) (p : ℕ) (hp : p.Prime) :
    ∃ m ∈ P.support, ¬ (p : ℤ) ∣ P.coeff m := by
  by_contra hall
  push Not at hall
  have hdvd : (p : ℤ) ∣ integerPolynomialContent P := by
    unfold integerPolynomialContent
    exact Finset.dvd_gcd (fun m hm => hall m hm)
  rw [hprim] at hdvd
  exact hp.not_dvd_one (Int.ofNat_dvd.mp (by simpa using hdvd))

/-- Exact Gauss valuation identity: when `(sixMatrix n).det ≠ 0`, any coefficientwise floor `L`
on `(sixMatrix n).det` is a lower bound on `padicValRat p (sixPrimitiveScalar n)`. -/
theorem sixPrimitiveScalar_padicValRat_ge_of_formal (n p : ℕ) [Fact p.Prime] (L : ℤ)
    (hL : FormalValAtLeast p L (sixMatrix n).det)
    (hdet : (sixMatrix n).det ≠ 0) :
    L ≤ padicValRat p (sixPrimitiveScalar n) := by
  have hp : p.Prime := Fact.out
  have hprim := sixPrimitivePolynomial_content_eq_one n hdet
  obtain ⟨m, hm, hnd⟩ := exists_primitive_coeff_not_dvd (sixPrimitivePolynomial n) hprim p hp
  have hPne : ((sixPrimitivePolynomial n).coeff m : ℚ) ≠ 0 := by
    intro h0
    have hZ : (sixPrimitivePolynomial n).coeff m = 0 := by exact_mod_cast h0
    exact MvPolynomial.mem_support_iff.mp hm hZ
  have hPval : padicValRat p ((sixPrimitivePolynomial n).coeff m : ℚ) = 0 := by
    rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd hnd
  have hcoeff : ((sixMatrix n).det).coeff m =
      sixPrimitiveScalar n * ((sixPrimitivePolynomial n).coeff m : ℚ) := by
    rw [sixPrimitivePolynomial_det_eq n, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
    rfl
  have hne : ((sixMatrix n).det).coeff m ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (sixPrimitiveScalar_ne_zero n) hPne
  have hval := valAtLeast_of_ne_zero (hL m) hne
  rw [hcoeff, padicValRat.mul (sixPrimitiveScalar_ne_zero n) hPne, hPval, add_zero] at hval
  exact hval

/-- Unconditional version when `L ≤ 0` (also handles `(sixMatrix n).det = 0`, where
`sixPrimitiveScalar n = 1` has valuation `0 ≥ L`). -/
theorem sixPrimitiveScalar_padicValRat_ge_of_formal_nonpos (n p : ℕ) [Fact p.Prime] (L : ℤ)
    (hL0 : L ≤ 0) (hL : FormalValAtLeast p L (sixMatrix n).det) :
    L ≤ padicValRat p (sixPrimitiveScalar n) := by
  by_cases hdet : (sixMatrix n).det = 0
  · unfold sixPrimitiveScalar
    simp [hdet, hL0]
  · exact sixPrimitiveScalar_padicValRat_ge_of_formal n p L hL hdet

/-! ## Truncated power-series division with slope `S` -/

/-- If `U.coeff 0 = 1`, `U` and `N` both have slope `S` from `0`, and `X^m ∣ N - Q * U`,
then `Q.coeff q` has valuation `≥ -S * q` for all `q < m`. -/
theorem truncated_division_weighted {p : ℕ} [Fact p.Prime]
    {N Q U : ℚ[X]} {m : ℕ} {S : ℤ}
    (hU0 : U.coeff 0 = 1)
    (hU : PolyWeighted p U 0 S)
    (hN : PolyWeighted p N 0 S)
    (hdvd : X ^ m ∣ N - Q * U) :
    ∀ q < m, ValAtLeast p (-(S * (q : ℤ))) (Q.coeff q) := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hqm
    have hcoeff_zero : (N - Q * U).coeff q = 0 := by
      obtain ⟨R, hR⟩ := hdvd
      rw [hR, coeff_X_pow_mul']
      simp [show ¬ (m ≤ q) by omega]
    have hNq : (Q * U).coeff q = N.coeff q := by
      rw [coeff_sub, sub_eq_zero] at hcoeff_zero
      exact hcoeff_zero.symm
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => Q.coeff a * U.coeff b),
      Finset.sum_range_succ, Nat.sub_self, hU0, mul_one] at hNq
    have hQq : Q.coeff q = N.coeff q - ∑ j ∈ range q, Q.coeff j * U.coeff (q - j) := by
      linarith
    rw [hQq]
    apply valAtLeast_sub
    · simpa using hN q
    · apply valAtLeast_sum
      intro j hj
      have hjq : j < q := mem_range.mp hj
      have hQj := ih j hjq (hjq.trans hqm)
      have hUj := hU (q - j)
      have hmul := valAtLeast_mul hQj hUj
      have hexp : -(S * (q : ℤ)) = -(S * (j : ℤ)) + (0 - S * ((q - j : ℕ) : ℤ)) := by
        rw [Nat.cast_sub hjq.le]; ring
      exact valAtLeast_mono hmul hexp.le

/-! ## Block-wise factorial normalization and `p`-adic valuation of `sixLocalCofactor` -/

private theorem div_add_add_one_le (A B P : ℕ) (hP : 0 < P) :
    (A + B + 1) / P ≤ A / P + B / P + 1 := by
  have h1 := Nat.div_add_mod A P
  have h2 := Nat.div_add_mod B P
  have hm1 : A % P < P := Nat.mod_lt A hP
  have hm2 : B % P < P := Nat.mod_lt B hP
  have hlt : A + B + 1 < P * (A / P + B / P + 2) := by nlinarith
  have hle : (A + B + 1) / P < A / P + B / P + 2 := (Nat.div_lt_iff_lt_mul hP).mpr (by nlinarith)
  omega

/-- Key Legendre bound for an off-block denominator factor: for `d ≥ 1` and `d + L ≤ M₀`,
`v_p((d + L)! / ((d - 1)! * L!)) ≤ Nat.log p M₀` for EVERY prime `p`. -/
theorem offBlock_factorial_ratio_val_le (p : ℕ) [Fact p.Prime]
    (d L M₀ : ℕ) (hd : 1 ≤ d) (hM : d + L ≤ M₀) :
    (padicValNat p (d + L).factorial : ℤ) -
      (padicValNat p (d - 1).factorial : ℤ) -
      (padicValNat p L.factorial : ℤ) ≤ (Nat.log p M₀ : ℤ) := by
  have hp : p.Prime := Fact.out
  let K : ℕ := Nat.log p M₀ + 1
  have h1 : Nat.log p (d + L) < K := Nat.lt_succ_of_le (Nat.log_mono_right hM)
  have h2 : Nat.log p (d - 1) < K := Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
  have h3 : Nat.log p L < K := Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
  rw [padicValNat_factorial h1, padicValNat_factorial h2, padicValNat_factorial h3]
  push_cast
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have hterm : ∀ e ∈ Finset.Ico 1 K,
      (((d + L) / p ^ e : ℕ) : ℤ) - (((d - 1) / p ^ e : ℕ) : ℤ) - ((L / p ^ e : ℕ) : ℤ) ≤ 1 := by
    intro e _
    have hpe : 0 < p ^ e := pow_pos hp.pos e
    have hle := div_add_add_one_le (d - 1) L (p ^ e) hpe
    have heq : d - 1 + L + 1 = d + L := by omega
    rw [heq] at hle
    have hleZ : (((d + L) / p ^ e : ℕ) : ℤ) ≤
        (((d - 1) / p ^ e : ℕ) : ℤ) + ((L / p ^ e : ℕ) : ℤ) + 1 := by
      exact_mod_cast hle
    omega
  calc
    (∑ e ∈ Finset.Ico 1 K,
        ((((d + L) / p ^ e : ℕ) : ℤ) - (((d - 1) / p ^ e : ℕ) : ℤ) - ((L / p ^ e : ℕ) : ℤ)))
        ≤ ∑ _e ∈ Finset.Ico 1 K, (1 : ℤ) := Finset.sum_le_sum hterm
    _ = (Nat.log p M₀ : ℤ) := by simp [K]

/-- Block length `L_b = (50 - 2 * d_b) * n`. -/
def sixBlockLen (n : ℕ) (b : Fin 14) : ℕ := (50 - 2 * sixOffset b) * n

/-- Block start `a_b = (45 + d_b) * n + 1`. -/
def sixBlockStart (n : ℕ) (b : Fin 14) : ℕ := (45 + sixOffset b) * n + 1

/-- Normalized numerator `Ñ_k = (2 / ∏ (z_a n)!^2) * taylor (-k) (sixNumerator * centeredMultiplier)`. -/
def sixNormLocalNum (n : ℕ) (i j : Fin (rank n)) (k : ℕ) : ℚ[X] :=
  C (2 / (∏ a : Fin 5, ((sixZero a * n).factorial : ℚ) ^ 2)) *
    taylor (-(k : ℚ)) (sixNumerator n * centeredMultiplier n i.val j.val)

/-- Normalized cofactor `C̃_k = (1 / ∏ L_b!) * sixLocalCofactor n k`. -/
def sixNormLocalCof (n k : ℕ) : ℚ[X] :=
  C (1 / (∏ b : Fin 14, ((sixBlockLen n b).factorial : ℚ))) * sixLocalCofactor n k

theorem sixNormLocal_congruence (n : ℕ) (i j : Fin (rank n)) (k : ℕ)
    (hk : k ∈ sixPoleSet n) :
    X ^ sixPoleOrder n k ∣
      sixNormLocalNum n i j k - sixLocalPrincipal n i j k * sixNormLocalCof n k := by
  have hden_ne : (∏ b : Fin 14, ((sixBlockLen n b).factorial : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun b _ => by exact_mod_cast Nat.factorial_ne_zero _)
  have hcong := sixLocalPrincipal_congruence n i j k hk
  have hmul := dvd_mul_of_dvd_right hcong
    (C (1 / (∏ b : Fin 14, ((sixBlockLen n b).factorial : ℚ))))
  have heq : C (1 / (∏ b : Fin 14, ((sixBlockLen n b).factorial : ℚ))) *
      (sixLocalNumerator n i j k - sixLocalPrincipal n i j k * sixLocalCofactor n k) =
      sixNormLocalNum n i j k - sixLocalPrincipal n i j k * sixNormLocalCof n k := by
    unfold sixLocalNumerator sixNormLocalNum sixNormLocalCof sixNormalization sixBlockLen
    rw [mul_sub, taylor_mul, taylor_mul, taylor_mul, taylor_C, ← mul_assoc, ← mul_assoc, ← map_mul]
    have hsc : (1 / (∏ b : Fin 14, (((50 - 2 * sixOffset b) * n).factorial : ℚ))) *
        ((2 * ∏ b : Fin 14, (((50 - 2 * sixOffset b) * n).factorial : ℚ)) /
          (∏ a : Fin 5, ((sixZero a * n).factorial : ℚ) ^ 2)) =
        2 / (∏ a : Fin 5, ((sixZero a * n).factorial : ℚ) ^ 2) := by
      field_simp
    rw [hsc]
    ring
  rwa [heq] at hmul

private theorem taylor_prod_fin {ι : Type*} [DecidableEq ι] (x : ℚ)
    (s : Finset ι) (f : ι → ℚ[X]) :
    taylor x (∏ i ∈ s, f i) = ∏ i ∈ s, taylor x (f i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; rw [← C_1, taylor_C, C_1]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, taylor_mul, ih]

/-- All-prime-power weight of the normalized local numerator `Ñ_k` (`M₀ = 55 * n`). -/
theorem sixNormLocalNum_weighted (n p : ℕ) [Fact p.Prime] (hn : 0 < n)
    (i j : Fin (rank n)) (k : ℕ) :
    PolyWeighted p (sixNormLocalNum n i j k) 0 (Nat.log p (55 * n)) := by
  let S : ℤ := (Nat.log p (55 * n) : ℤ)
  have hS0 : 0 ≤ S := Int.natCast_nonneg _
  have hcenter : taylor (-(k : ℚ)) (X + C (70 * (n : ℚ) + 1)) =
      X + C (((70 * (n : ℤ) + 1 - (k : ℤ)) : ℤ) : ℚ) := by
    rw [map_add, taylor_X, taylor_C, add_assoc, ← C_add]
    congr 2; push_cast; ring
  have hmult : taylor (-(k : ℚ)) (centeredMultiplier n i.val j.val) =
      taylor (((sixCenter n : ℤ) - (k : ℤ) : ℤ) : ℚ) (evenBasis i.val) *
      taylor (((sixCenter n : ℤ) - (k : ℤ) : ℤ) : ℚ) (evenBasis j.val) := by
    unfold centeredMultiplier
    rw [taylor_apply, taylor_apply, taylor_apply, comp_assoc, mul_comp]
    have harg : (X + C (70 * (n : ℚ) + 1)).comp (X + C (-(k : ℚ))) =
        X + C (((sixCenter n : ℤ) - (k : ℤ) : ℤ) : ℚ) := by
      simp only [add_comp, X_comp, C_comp, add_assoc, ← C_add]
      congr 2; unfold sixCenter; push_cast; ring
    rw [harg]
  have hCprod : C (2 / (∏ a : Fin 5, ((sixZero a * n).factorial : ℚ) ^ 2)) =
      C (2 : ℚ) * ∏ a : Fin 5,
        (C (1 / ((sixZero a * n).factorial : ℚ)) * C (1 / ((sixZero a * n).factorial : ℚ))) := by
    have hinv : (∏ a : Fin 5, ((sixZero a * n).factorial : ℚ) ^ 2)⁻¹ =
        ∏ a : Fin 5, (1 / ((sixZero a * n).factorial : ℚ)) * (1 / ((sixZero a * n).factorial : ℚ)) := by
      rw [← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl; intro a _
      rw [one_div, sq, mul_inv]
    rw [div_eq_mul_inv, hinv, map_mul, map_prod]
    congr 1
    apply Finset.prod_congr rfl; intro a _
    rw [map_mul]
  have hrew : sixNormLocalNum n i j k =
      C (2 : ℚ) * (X + C (((70 * (n : ℤ) + 1 - (k : ℤ)) : ℤ) : ℚ)) *
      (∏ a : Fin 5,
        taylor (-(k : ℚ)) (normalizedRising 1 (sixZero a * n)) *
        taylor (-(k : ℚ)) (normalizedRising (140 * (n : ℤ) + 2 - (sixZero a * n : ℤ)) (sixZero a * n))) *
      (taylor (((sixCenter n : ℤ) - (k : ℤ) : ℤ) : ℚ) (evenBasis i.val) *
       taylor (((sixCenter n : ℤ) - (k : ℤ) : ℤ) : ℚ) (evenBasis j.val)) := by
    unfold sixNormLocalNum sixNumerator
    rw [taylor_mul, taylor_mul, taylor_prod_fin, hcenter, hmult, hCprod]
    have hprod_eq : (∏ a : Fin 5,
        (C (1 / ((sixZero a * n).factorial : ℚ)) * C (1 / ((sixZero a * n).factorial : ℚ)))) *
        (∏ a : Fin 5, taylor (-(k : ℚ))
          (rising 1 (sixZero a * n) *
            rising (140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ)) (sixZero a * n))) =
        ∏ a : Fin 5,
          taylor (-(k : ℚ)) (normalizedRising 1 (sixZero a * n)) *
          taylor (-(k : ℚ)) (normalizedRising (140 * (n : ℤ) + 2 - (sixZero a * n : ℤ)) (sixZero a * n)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro a _
      unfold normalizedRising
      rw [taylor_mul, taylor_mul, taylor_mul, taylor_C]
      have hc1 : ((1 : ℤ) : ℚ) = 1 := by norm_num
      have hc2 : ((140 * (n : ℤ) + 2 - (sixZero a * n : ℤ) : ℤ) : ℚ) =
          140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ) := by push_cast; ring
      rw [hc1, hc2]
      ring
    rw [← hprod_eq]
    ring
  rw [hrew]
  have h0 : PolyWeighted p (C (2 : ℚ)) 0 S :=
    polyWeighted_C (valAtLeast_natCast p 2)
  have h1 : PolyWeighted p (X + C (((70 * (n : ℤ) + 1 - (k : ℤ)) : ℤ) : ℚ)) 0 S :=
    polyWeighted_linear_int_slope _ S hS0
  have h2 : PolyWeighted p (∏ a : Fin 5,
      taylor (-(k : ℚ)) (normalizedRising 1 (sixZero a * n)) *
      taylor (-(k : ℚ)) (normalizedRising (140 * (n : ℤ) + 2 - (sixZero a * n : ℤ)) (sixZero a * n)))
      0 S := by
    have hprod := polyWeighted_prod (p := p) (Finset.univ : Finset (Fin 5))
      (fun a => taylor (-(k : ℚ)) (normalizedRising 1 (sixZero a * n)) *
        taylor (-(k : ℚ)) (normalizedRising (140 * (n : ℤ) + 2 - (sixZero a * n : ℤ)) (sixZero a * n)))
      (fun _ => 0) S (fun a _ => by
        have hza : sixZero a ≤ 43 := by fin_cases a <;> decide
        have hle : sixZero a * n ≤ 55 * n := by nlinarith
        have hA := normalizedRising_weighted_allPrimes p (55 * n) 1 (-(k : ℤ)) (sixZero a * n) hle
        have hB := normalizedRising_weighted_allPrimes p (55 * n)
          (140 * (n : ℤ) + 2 - (sixZero a * n : ℤ)) (-(k : ℤ)) (sixZero a * n) hle
        have hm := polyWeighted_mul hA hB
        exact polyWeighted_mono hm (by omega))
    exact polyWeighted_mono hprod (by simp)
  have hi : 2 * i.val ≤ 55 * n := by have := i.isLt; unfold rank at this; omega
  have hj : 2 * j.val ≤ 55 * n := by have := j.isLt; unfold rank at this; omega
  have h3 : PolyWeighted p (taylor (((sixCenter n : ℤ) - (k : ℤ) : ℤ) : ℚ) (evenBasis i.val) *
      taylor (((sixCenter n : ℤ) - (k : ℤ) : ℤ) : ℚ) (evenBasis j.val)) 0 S :=
    polyWeighted_mono
      (polyWeighted_mul
        (evenBasis_weighted_allPrimes p (55 * n) i.val hi _)
        (evenBasis_weighted_allPrimes p (55 * n) j.val hj _))
      (by omega)
  exact polyWeighted_mono (polyWeighted_mul (polyWeighted_mul (polyWeighted_mul h0 h1) h2) h3)
    (by omega)

private theorem sixPoleOrder_eq_block_count (n k : ℕ) :
    (∑ b : Fin 14,
      if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then (1 : ℕ) else 0) =
      sixPoleOrder n k := by
  unfold sixPoleOrder sixPoleList
  rw [list_count_flatMap, ← Fin.sum_univ_def]
  apply Finset.sum_congr rfl; intro b _
  have hmem : k ∈ (List.range (sixBlockLen n b + 1)).map (fun j => sixBlockStart n b + j) ↔
      sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b := by
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · rintro ⟨h1, h2⟩; exact ⟨k - sixBlockStart n b, by omega, by omega⟩
  symm
  change ((List.range (sixBlockLen n b + 1)).map (fun j => sixBlockStart n b + j)).count k = _
  split_ifs with h
  · exact List.count_eq_one_of_mem
      ((List.nodup_map_iff (fun _ _ h => Nat.add_left_cancel h)).mpr List.nodup_range)
      (hmem.mpr h)
  · exact List.count_eq_zero_of_not_mem (fun hk' => h (hmem.mp hk'))

/-- Exact block-wise factorization of `sixLocalCofactor n k`. -/
theorem sixLocalCofactor_eq_block_prod (n k : ℕ) (hk : k ∈ sixPoleSet n) :
    sixLocalCofactor n k =
      ∏ b : Fin 14,
        ∏ j ∈ (if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then
          (range (sixBlockLen n b + 1)).erase (k - sixBlockStart n b)
        else range (sixBlockLen n b + 1)),
          (X + C (((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) := by
  have hden_eq : (X + C (k : ℚ)) ^ sixPoleOrder n k *
      (∏ a ∈ (sixPoleSet n).erase k, (X + C (a : ℚ)) ^ sixPoleOrder n a) =
      sixDenominator n := by
    rw [six_denominator_powers]
    exact Finset.mul_prod_erase (sixPoleSet n) (fun a => (X + C (a : ℚ)) ^ sixPoleOrder n a) hk
  have hblock_split : ∀ b : Fin 14,
      rising (sixBlockStart n b : ℚ) (sixBlockLen n b + 1) =
        (if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then
          X + C (k : ℚ) else 1) *
        ∏ j ∈ (if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then
          (range (sixBlockLen n b + 1)).erase (k - sixBlockStart n b)
        else range (sixBlockLen n b + 1)),
          (X + C ((sixBlockStart n b : ℚ) + (j : ℚ))) := by
    intro b
    unfold rising
    split_ifs with hcond
    · have hmem : k - sixBlockStart n b ∈ range (sixBlockLen n b + 1) := by
        rw [mem_range]; omega
      rw [← Finset.mul_prod_erase _ _ hmem]
      congr 1; congr 1; congr 1
      rw [Nat.cast_sub hcond.1]; ring
    · simp
  have hprod_den : sixDenominator n =
      (X + C (k : ℚ)) ^ sixPoleOrder n k *
      ∏ b : Fin 14,
        ∏ j ∈ (if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then
          (range (sixBlockLen n b + 1)).erase (k - sixBlockStart n b)
        else range (sixBlockLen n b + 1)),
          (X + C ((sixBlockStart n b : ℚ) + (j : ℚ))) := by
    have h1 : sixDenominator n =
        ∏ b : Fin 14, rising (sixBlockStart n b : ℚ) (sixBlockLen n b + 1) := by
      unfold sixDenominator sixBlockStart sixBlockLen
      apply Finset.prod_congr rfl; intro b _
      congr 1; push_cast; ring
    rw [h1]
    have h2 : (∏ b : Fin 14, rising (sixBlockStart n b : ℚ) (sixBlockLen n b + 1)) =
        ∏ b : Fin 14,
          ((if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then
            X + C (k : ℚ) else 1) *
          ∏ j ∈ (if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then
            (range (sixBlockLen n b + 1)).erase (k - sixBlockStart n b)
          else range (sixBlockLen n b + 1)),
            (X + C ((sixBlockStart n b : ℚ) + (j : ℚ)))) :=
      Finset.prod_congr rfl (fun b _ => hblock_split b)
    rw [h2, Finset.prod_mul_distrib]
    congr 1
    have hite : (∏ b : Fin 14,
        if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then
          X + C (k : ℚ) else 1) =
        ∏ b : Fin 14, (X + C (k : ℚ)) ^
          (if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then 1 else 0) :=
      Finset.prod_congr rfl (fun b _ => by split_ifs <;> simp)
    rw [hite, Finset.prod_pow_eq_pow_sum, sixPoleOrder_eq_block_count]
  have hcancel : (∏ a ∈ (sixPoleSet n).erase k, (X + C (a : ℚ)) ^ sixPoleOrder n a) =
      ∏ b : Fin 14,
        ∏ j ∈ (if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then
          (range (sixBlockLen n b + 1)).erase (k - sixBlockStart n b)
        else range (sixBlockLen n b + 1)),
          (X + C ((sixBlockStart n b : ℚ) + (j : ℚ))) := by
    have hne : (X + C (k : ℚ)) ^ sixPoleOrder n k ≠ 0 :=
      pow_ne_zero _ (Polynomial.monic_X_add_C _).ne_zero
    apply mul_left_cancel₀ hne
    rw [hden_eq, hprod_den]
  unfold sixLocalCofactor
  rw [hcancel, taylor_prod_fin]
  apply Finset.prod_congr rfl; intro b _
  rw [taylor_prod_fin]
  apply Finset.prod_congr rfl; intro j _
  rw [map_add, taylor_X, taylor_C, add_assoc, ← C_add]
  congr 2; push_cast; ring

/-- Constant-term valuation upper bound & unit-normalized slope for `sixNormLocalCof n k`. -/
theorem sixNormLocalCof_bounds (n p : ℕ) [Fact p.Prime] (_hn : 0 < n) (k : ℕ)
    (hk : k ∈ sixPoleSet n) :
    (sixNormLocalCof n k).coeff 0 ≠ 0 ∧
    padicValRat p ((sixNormLocalCof n k).coeff 0) ≤
      ((14 - sixPoleOrder n k : ℕ) : ℤ) * (Nat.log p (55 * n) : ℤ) ∧
    PolyWeighted p (C (1 / (sixNormLocalCof n k).coeff 0) * sixNormLocalCof n k)
      0 (Nat.log p (55 * n)) := by
  let S : ℤ := (Nat.log p (55 * n) : ℤ)
  have hbnd := six_pole_address_bounds n k hk
  -- Factor `sixNormLocalCof` per block
  let s_b : Fin 14 → Finset ℕ := fun b =>
    if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then
      (range (sixBlockLen n b + 1)).erase (k - sixBlockStart n b)
    else range (sixBlockLen n b + 1)
  let C_b : Fin 14 → ℚ[X] := fun b =>
    C (1 / ((sixBlockLen n b).factorial : ℚ)) *
      ∏ j ∈ s_b b, (X + C (((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ))
  have hfact : sixNormLocalCof n k = ∏ b : Fin 14, C_b b := by
    unfold sixNormLocalCof
    rw [sixLocalCofactor_eq_block_prod n k hk]
    have hCprod : C (1 / (∏ b : Fin 14, ((sixBlockLen n b).factorial : ℚ))) =
        ∏ b : Fin 14, C (1 / ((sixBlockLen n b).factorial : ℚ)) := by
      rw [← map_prod]; congr 1
      rw [one_div, ← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl; intro b _; rw [one_div]
    rw [hCprod, ← Finset.prod_mul_distrib]
  -- Check each block's constant term and normalized weight
  have hblock_info : ∀ b : Fin 14,
      (C_b b).coeff 0 ≠ 0 ∧
      padicValRat p ((C_b b).coeff 0) ≤
        (if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then 0 else S) ∧
      PolyWeighted p (C (1 / (C_b b).coeff 0) * C_b b) 0 S := by
    intro b
    have hob : sixOffset b ≤ 11 := by fin_cases b <;> decide
    have hSb_bounds : 45 * n + 1 ≤ sixBlockStart n b ∧
        sixBlockStart n b + sixBlockLen n b ≤ 95 * n + 1 := by
      unfold sixBlockStart sixBlockLen
      have h0 : (45 + sixOffset b) * n = 45 * n + sixOffset b * n := by ring
      have h1 : sixOffset b * n ≤ 11 * n := Nat.mul_le_mul_right n hob
      have h2 : (50 - 2 * sixOffset b) * n + 2 * (sixOffset b * n) = 50 * n := by
        have : (50 - 2 * sixOffset b) + 2 * sixOffset b = 50 := by omega
        calc
          (50 - 2 * sixOffset b) * n + 2 * (sixOffset b * n)
              = ((50 - 2 * sixOffset b) + 2 * sixOffset b) * n := by ring
          _ = 50 * n := by rw [this]
      omega
    have hdist : ∀ j ∈ s_b b,
        ((sixBlockStart n b + j : ℤ) - (k : ℤ)) ≠ 0 ∧
        ((sixBlockStart n b + j : ℤ) - (k : ℤ)).natAbs ≤ 55 * n := by
      intro j hj
      dsimp [s_b] at hj
      split_ifs at hj with hcond
      · have hne := (Finset.mem_erase.mp hj).1
        have hlt := mem_range.mp (Finset.mem_erase.mp hj).2
        omega
      · have hlt := mem_range.mp hj
        omega
    have hcoeff0 : (C_b b).coeff 0 =
        (1 / ((sixBlockLen n b).factorial : ℚ)) *
          ∏ j ∈ s_b b, (((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ) := by
      dsimp [C_b]
      rw [Polynomial.coeff_zero_eq_eval_zero, eval_mul, eval_C, eval_prod]
      congr 1
      apply Finset.prod_congr rfl; intro j _; simp
    have hne0 : (C_b b).coeff 0 ≠ 0 := by
      rw [hcoeff0]
      apply mul_ne_zero (one_div_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _))
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact_mod_cast (hdist j hj).1
    -- Normalized weight of `C (1 / (C_b b).coeff 0) * C_b b`
    have hweight : PolyWeighted p (C (1 / (C_b b).coeff 0) * C_b b) 0 S := by
      have hrew : C (1 / (C_b b).coeff 0) * C_b b =
          ∏ j ∈ s_b b, (1 + C (1 / (((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) * X) := by
        dsimp [C_b]
        rw [hcoeff0, ← mul_assoc, ← map_mul]
        have hfac_ne : ((sixBlockLen n b).factorial : ℚ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero _
        have hprod_ne : (∏ j ∈ s_b b, (((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr (fun j hj => by exact_mod_cast (hdist j hj).1)
        have hsc : (1 / ((1 / ((sixBlockLen n b).factorial : ℚ)) *
            ∏ j ∈ s_b b, (((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ))) *
            (1 / ((sixBlockLen n b).factorial : ℚ)) =
            ∏ j ∈ s_b b, (1 / (((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) := by
          rw [Finset.prod_div_distrib, Finset.prod_const_one]
          field_simp
        rw [hsc, map_prod, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl; intro j hj
        have hne : (((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ) ≠ 0 := by
          exact_mod_cast (hdist j hj).1
        rw [mul_add, ← map_mul, one_div_mul_cancel hne, map_one, add_comm]
      rw [hrew]
      have hprod := polyWeighted_prod (p := p) (s_b b)
        (fun j => 1 + C (1 / (((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) * X)
        (fun _ => 0) S (fun j hj => by
          intro r
          cases r with
          | zero =>
            simp only [coeff_add, coeff_one_zero, coeff_C_mul, coeff_X_zero, mul_zero, add_zero,
              Nat.cast_zero, sub_zero]
            exact valAtLeast_one p
          | succ r =>
            cases r with
            | zero =>
              simp only [zero_add, coeff_add, coeff_one, show ¬ (1 : ℕ) = 0 by omega, ite_false,
                zero_add, coeff_C_mul, coeff_X_one, mul_one, Nat.cast_one, zero_sub]
              right
              rw [one_div, padicValRat.inv, padicValRat.of_int, padicValInt]
              have hd := hdist j hj
              have hlog := padicValNat_le_log p (Int.natAbs_pos.mpr hd.1) hd.2
              omega
            | succ r =>
              simp only [coeff_add, coeff_one, coeff_C_mul, coeff_X,
                show ¬ (r + 1 + 1 = 0) by omega, show ¬ (1 = r + 1 + 1) by omega,
                ite_false, mul_zero, add_zero]
              exact valAtLeast_zero p _)
      simpa using hprod
    -- Constant term valuation upper bound
    have hval : padicValRat p ((C_b b).coeff 0) ≤
        if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then 0 else S := by
      let a := sixBlockStart n b
      let L := sixBlockLen n b
      change padicValRat p ((C_b b).coeff 0) ≤ if a ≤ k ∧ k ≤ a + L then 0 else S
      have hfac_ne : (L.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero L
      by_cases hcond : a ≤ k ∧ k ≤ a + L
      · simp only [hcond, and_self, ite_true]
        -- Product equals `(-1)^(k - a) * (k - a)! * (a + L - k)!`
        have hprod_in : (∏ j ∈ (range (L + 1)).erase (k - a), (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
            (-1 : ℚ) ^ (k - a) * (((k - a).factorial : ℕ) : ℚ) *
              (((a + L - k).factorial : ℕ) : ℚ) := by
          have hsplit : (range (L + 1)).erase (k - a) =
              range (k - a) ∪ Finset.Ico (k - a + 1) (L + 1) := by
            ext j; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
            omega
          have hdisj : Disjoint (range (k - a)) (Finset.Ico (k - a + 1) (L + 1)) := by
            rw [Finset.disjoint_left]; intro j hj1 hj2
            rw [Finset.mem_range] at hj1; rw [Finset.mem_Ico] at hj2; omega
          rw [hsplit, Finset.prod_union hdisj]
          have hleft : (∏ j ∈ range (k - a), (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
              (-1 : ℚ) ^ (k - a) * (((k - a).factorial : ℕ) : ℚ) := by
            have hbij : (∏ j ∈ range (k - a), (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
                ∏ u ∈ range (k - a), (-(((u + 1 : ℕ) : ℚ))) := by
              apply Finset.prod_bij (fun j _ => k - a - 1 - j)
              · intro j hj; exact mem_range.mpr (by have := mem_range.mp hj; omega)
              · intro j₁ hj₁ j₂ hj₂ h; have := mem_range.mp hj₁; have := mem_range.mp hj₂; omega
              · intro u hu; exact ⟨k - a - 1 - u, mem_range.mpr (by have := mem_range.mp hu; omega),
                  by have := mem_range.mp hu; omega⟩
              · intro j hj
                have hjlt := mem_range.mp hj
                have h1 : k - a - 1 - j + 1 = k - a - j := by omega
                rw [h1, Nat.cast_sub (by omega : j ≤ k - a), Nat.cast_sub hcond.1]
                push_cast; ring
            rw [hbij]
            clear hbij hsplit hdisj
            induction (k - a) with
            | zero => simp
            | succ m ihm =>
              rw [Finset.prod_range_succ, ihm, pow_succ, Nat.factorial_succ]
              push_cast; ring
          have hright : (∏ j ∈ Finset.Ico (k - a + 1) (L + 1), (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
              (((a + L - k).factorial : ℕ) : ℚ) := by
            have hbij : (∏ j ∈ Finset.Ico (k - a + 1) (L + 1), (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
                ∏ u ∈ range (a + L - k), ((u + 1 : ℕ) : ℚ) := by
              apply Finset.prod_bij (fun j _ => j - (k - a + 1))
              · intro j hj; rw [Finset.mem_Ico] at hj; exact mem_range.mpr (by omega)
              · intro j₁ hj₁ j₂ hj₂ h
                rw [Finset.mem_Ico] at hj₁ hj₂; omega
              · intro u hu; rw [mem_range] at hu
                exact ⟨u + (k - a + 1), Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
              · intro j hj
                rw [Finset.mem_Ico] at hj
                have h1 : j - (k - a + 1) + 1 = a + j - k := by omega
                rw [h1, Nat.cast_sub (by omega : k ≤ a + j)]
                push_cast; ring
            rw [hbij]
            clear hbij hleft hsplit hdisj
            induction (a + L - k) with
            | zero => simp
            | succ m ihm =>
              rw [Finset.prod_range_succ, ihm, Nat.factorial_succ]
              push_cast; ring
          rw [hleft, hright]
        have hC0_eq : (C_b b).coeff 0 =
            (-1 : ℚ) ^ (k - a) / ((L.choose (k - a) : ℕ) : ℚ) := by
          rw [hcoeff0]
          have hs_eq : s_b b = (range (L + 1)).erase (k - a) := by
            change (if a ≤ k ∧ k ≤ a + L then (range (L + 1)).erase (k - a) else range (L + 1)) = _
            simp only [hcond, and_self, ite_true]
          rw [hs_eq, hprod_in]
          have hch : L.choose (k - a) * (k - a).factorial * (a + L - k).factorial = L.factorial := by
            have hsub : L - (k - a) = a + L - k := by omega
            have := Nat.choose_mul_factorial_mul_factorial (show k - a ≤ L by omega)
            rwa [hsub] at this
          have hch_ne : ((L.choose (k - a) : ℕ) : ℚ) ≠ 0 := by
            exact_mod_cast (Nat.choose_pos (show k - a ≤ L by omega)).ne'
          have hchQ : ((L.choose (k - a) : ℕ) : ℚ) * (((k - a).factorial : ℕ) : ℚ) *
              (((a + L - k).factorial : ℕ) : ℚ) = (L.factorial : ℚ) := by
            exact_mod_cast hch
          field_simp
          rw [← hchQ]
          ring
        rw [hC0_eq]
        have h1ne : (-1 : ℚ) ^ (k - a) ≠ 0 := pow_ne_zero _ (by norm_num)
        have hch_ne : ((L.choose (k - a) : ℕ) : ℚ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos (show k - a ≤ L by omega)).ne'
        have hv1 : padicValRat p ((-1 : ℚ) ^ (k - a)) = 0 := by
          rcases Nat.even_or_odd (k - a) with he | ho
          · rw [he.neg_one_pow, padicValRat.one]
          · rw [ho.neg_one_pow, padicValRat.neg, padicValRat.one]
        rw [padicValRat.div h1ne hch_ne, hv1, zero_sub, padicValRat.of_nat]
        omega
      · simp only [hcond, ↓reduceIte]
        have hs_eq : s_b b = range (L + 1) := by
          change (if a ≤ k ∧ k ≤ a + L then (range (L + 1)).erase (k - a) else range (L + 1)) = _
          simp only [hcond, ↓reduceIte]
        -- Helper: `∏_{j=0}^L (d + j) = (d + L)! / (d - 1)!`
        have hprod_shifted : ∀ d : ℕ, 1 ≤ d →
            (∏ j ∈ range (L + 1), ((d + j : ℕ) : ℚ)) =
              (((d + L).factorial : ℕ) : ℚ) / (((d - 1).factorial : ℕ) : ℚ) := by
          intro d hd1
          have hne : (((d - 1).factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
          rw [eq_div_iff hne]
          have hnat : (∏ j ∈ range (L + 1), (d + j)) * (d - 1).factorial = (d + L).factorial := by
            clear hne
            induction L with
            | zero =>
              simp only [zero_add, range_one, prod_singleton, add_zero]
              exact Nat.mul_factorial_pred (by omega : d ≠ 0)
            | succ m ihm =>
              rw [Finset.prod_range_succ]
              have heq : d + (m + 1) = (d + m) + 1 := by omega
              rw [heq, Nat.factorial_succ]
              calc
                (∏ x ∈ range (m + 1), (d + x)) * (d + m + 1) * (d - 1).factorial
                    = (d + m + 1) * ((∏ x ∈ range (m + 1), (d + x)) * (d - 1).factorial) := by ring
                _ = (d + m + 1) * (d + m).factorial := by rw [ihm]
          exact_mod_cast hnat
        rcases (show k < a ∨ a + L < k by omega) with hlt | hgt
        · -- `k < a`: `d = a - k ≥ 1`, `d + L = a + L - k ≤ 50n ≤ 55n`
          let d := a - k
          have hd1 : 1 ≤ d := by omega
          have hdL : d + L ≤ 55 * n := by omega
          have hpeq : (∏ j ∈ s_b b, (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
              (((d + L).factorial : ℕ) : ℚ) / (((d - 1).factorial : ℕ) : ℚ) := by
            rw [hs_eq, ← hprod_shifted d hd1]
            apply Finset.prod_congr rfl; intro j _
            rw [Nat.cast_add, Nat.cast_sub hlt.le]; push_cast; ring
          rw [hcoeff0, hpeq, one_div, mul_comm, ← div_eq_mul_inv, div_div]
          have hnum_ne : (((d + L).factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
          have hden1_ne : (((d - 1).factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
          rw [padicValRat.div hnum_ne (mul_ne_zero hden1_ne hfac_ne),
            padicValRat.mul hden1_ne hfac_ne,
            padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat]
          have hbound := offBlock_factorial_ratio_val_le p d L (55 * n) hd1 hdL
          omega
        · -- `a + L < k`: `d = k - (a + L) ≥ 1`, `d + L = k - a ≤ 50n ≤ 55n`
          let d := k - (a + L)
          have hd1 : 1 ≤ d := by omega
          have hdL : d + L ≤ 55 * n := by omega
          have hpeq : (∏ j ∈ s_b b, (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
              (-1 : ℚ) ^ (L + 1) *
                ((((d + L).factorial : ℕ) : ℚ) / (((d - 1).factorial : ℕ) : ℚ)) := by
            rw [hs_eq, ← hprod_shifted d hd1]
            have hbij : (∏ j ∈ range (L + 1), (((a + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
                ∏ u ∈ range (L + 1), (-1 : ℚ) * ((d + u : ℕ) : ℚ) := by
              apply Finset.prod_bij (fun j _ => L - j)
              · intro j hj; exact mem_range.mpr (by have := mem_range.mp hj; omega)
              · intro j₁ hj₁ j₂ hj₂ h; have := mem_range.mp hj₁; have := mem_range.mp hj₂; omega
              · intro u hu; exact ⟨L - u, mem_range.mpr (by have := mem_range.mp hu; omega),
                  by have := mem_range.mp hu; omega⟩
              · intro j hj
                have hjL : j ≤ L := Nat.lt_succ_iff.mp (mem_range.mp hj)
                rw [Nat.cast_add, Nat.cast_sub hgt.le, Nat.cast_sub hjL]
                push_cast; ring
            rw [hbij, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
          rw [hcoeff0, hpeq]
          have h1ne : (-1 : ℚ) ^ (L + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
          have hnum_ne : (((d + L).factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
          have hden1_ne : (((d - 1).factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
          have hv1 : padicValRat p ((-1 : ℚ) ^ (L + 1)) = 0 := by
            rcases Nat.even_or_odd (L + 1) with he | ho
            · rw [he.neg_one_pow, padicValRat.one]
            · rw [ho.neg_one_pow, padicValRat.neg, padicValRat.one]
          have hrew : (1 / (L.factorial : ℚ)) *
              ((-1 : ℚ) ^ (L + 1) * ((((d + L).factorial : ℕ) : ℚ) / (((d - 1).factorial : ℕ) : ℚ))) =
              (-1 : ℚ) ^ (L + 1) * ((((d + L).factorial : ℕ) : ℚ) /
                ((((d - 1).factorial : ℕ) : ℚ) * (L.factorial : ℚ))) := by ring
          rw [hrew, padicValRat.mul h1ne (div_ne_zero hnum_ne (mul_ne_zero hden1_ne hfac_ne)),
            hv1, zero_add, padicValRat.div hnum_ne (mul_ne_zero hden1_ne hfac_ne),
            padicValRat.mul hden1_ne hfac_ne,
            padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat]
          have hbound := offBlock_factorial_ratio_val_le p d L (55 * n) hd1 hdL
          omega
    exact ⟨hne0, hval, hweight⟩
  -- Combine all 14 blocks
  have hC0_prod : (sixNormLocalCof n k).coeff 0 = ∏ b : Fin 14, (C_b b).coeff 0 := by
    rw [hfact, Polynomial.coeff_zero_eq_eval_zero, eval_prod]
    apply Finset.prod_congr rfl; intro b _; rw [Polynomial.coeff_zero_eq_eval_zero]
  have hC0_ne : (sixNormLocalCof n k).coeff 0 ≠ 0 := by
    rw [hC0_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun b _ => (hblock_info b).1)
  have hcount_off : (∑ b : Fin 14,
      if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then (0 : ℤ) else S) =
      ((14 - sixPoleOrder n k : ℕ) : ℤ) * S := by
    have hcount_in := sixPoleOrder_eq_block_count n k
    have hord := six_pole_order_le n k
    have hsum14 : (∑ b : Fin 14,
        ((if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then (0 : ℤ) else 1) +
         (if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then (1 : ℤ) else 0))) =
        (14 : ℤ) := by
      have : ∀ b : Fin 14,
          (if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then (0 : ℤ) else 1) +
          (if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then (1 : ℤ) else 0) = 1 := by
        intro b; split_ifs <;> norm_num
      simp [this]
    have hoff1 : (∑ b : Fin 14,
        if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then (0 : ℤ) else 1) =
        ((14 - sixPoleOrder n k : ℕ) : ℤ) := by
      rw [Finset.sum_add_distrib] at hsum14
      have hinZ : (∑ b : Fin 14,
          if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then (1 : ℤ) else 0) =
          (sixPoleOrder n k : ℤ) := by
        have := congrArg (Nat.cast (R := ℤ)) hcount_in
        push_cast at this
        simpa [apply_ite] using this
      rw [Nat.cast_sub hord]
      push_cast at hsum14 ⊢
      linarith
    calc
      (∑ b : Fin 14,
          if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then (0 : ℤ) else S)
          = (∑ b : Fin 14,
              (if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then (0 : ℤ) else 1) * S) := by
            apply Finset.sum_congr rfl; intro b _; split_ifs <;> ring
      _ = (∑ b : Fin 14,
            if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then (0 : ℤ) else 1) * S := by
            rw [← Finset.sum_mul]
      _ = ((14 - sixPoleOrder n k : ℕ) : ℤ) * S := by rw [hoff1]
  have hC0_val : padicValRat p ((sixNormLocalCof n k).coeff 0) ≤
      ((14 - sixPoleOrder n k : ℕ) : ℤ) * S := by
    have hpadic_prod : ∀ s : Finset (Fin 14),
        padicValRat p (∏ b ∈ s, (C_b b).coeff 0) = ∑ b ∈ s, padicValRat p ((C_b b).coeff 0) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha,
          padicValRat.mul (hblock_info a).1
            (Finset.prod_ne_zero_iff.mpr (fun b _ => (hblock_info b).1)), ih]
    rw [hC0_prod, hpadic_prod Finset.univ, ← hcount_off]
    exact Finset.sum_le_sum (fun b _ => (hblock_info b).2.1)
  have hnorm_weight : PolyWeighted p
      (C (1 / (sixNormLocalCof n k).coeff 0) * sixNormLocalCof n k) 0 S := by
    have hprod_eq : C (1 / (sixNormLocalCof n k).coeff 0) * sixNormLocalCof n k =
        ∏ b : Fin 14, (C (1 / (C_b b).coeff 0) * C_b b) := by
      rw [hC0_prod, hfact]
      have hC : C (1 / ∏ b : Fin 14, (C_b b).coeff 0) =
          ∏ b : Fin 14, C (1 / (C_b b).coeff 0) := by
        rw [← map_prod]; congr 1
        rw [Finset.prod_div_distrib, Finset.prod_const_one]
      rw [hC, ← Finset.prod_mul_distrib]
    rw [hprod_eq]
    simpa using polyWeighted_prod (p := p) (Finset.univ : Finset (Fin 14))
      (fun b => C (1 / (C_b b).coeff 0) * C_b b) (fun _ => 0) S
      (fun b _ => (hblock_info b).2.2)
  exact ⟨hC0_ne, hC0_val, hnorm_weight⟩

/-! ## All-prime-power bounds on principal coefficients, `sixMatrix`, and `sixPrimitiveScalar` -/

theorem sixPrincipalCoefficients_valAtLeast_allPrimes (n p : ℕ) [Fact p.Prime] (hn : 0 < n)
    (i j : Fin (rank n)) (k : ℕ) (hk : k ∈ sixPoleSet n)
    (l : Fin (sixPoleOrder n k)) :
    ValAtLeast p (-((13 - l.val : ℕ) : ℤ) * (Nat.log p (55 * n) : ℤ))
      (sixPrincipalCoefficients n i j k l) := by
  let S : ℤ := (Nat.log p (55 * n) : ℤ)
  have hS0 : 0 ≤ S := Int.natCast_nonneg _
  obtain ⟨hC0_ne, hC0_val, hU_wt⟩ := sixNormLocalCof_bounds n p hn k hk
  let U : ℚ[X] := C (1 / (sixNormLocalCof n k).coeff 0) * sixNormLocalCof n k
  let Q : ℚ[X] := C ((sixNormLocalCof n k).coeff 0) * sixLocalPrincipal n i j k
  have hU0 : U.coeff 0 = 1 := by
    dsimp [U]; rw [coeff_C_mul, one_div_mul_cancel hC0_ne]
  have hdvd : X ^ sixPoleOrder n k ∣ sixNormLocalNum n i j k - Q * U := by
    have hQU : Q * U = sixLocalPrincipal n i j k * sixNormLocalCof n k := by
      dsimp [Q, U]
      have h1 : C ((sixNormLocalCof n k).coeff 0) * C (1 / (sixNormLocalCof n k).coeff 0) = 1 := by
        rw [← map_mul, mul_one_div_cancel hC0_ne, map_one]
      calc
        C ((sixNormLocalCof n k).coeff 0) * sixLocalPrincipal n i j k *
            (C (1 / (sixNormLocalCof n k).coeff 0) * sixNormLocalCof n k)
            = (C ((sixNormLocalCof n k).coeff 0) * C (1 / (sixNormLocalCof n k).coeff 0)) *
                (sixLocalPrincipal n i j k * sixNormLocalCof n k) := by ring
        _ = _ := by rw [h1, one_mul]
    rw [hQU]
    exact sixNormLocal_congruence n i j k hk
  let q := sixPoleOrder n k - (l.val + 1)
  have hqm : q < sixPoleOrder n k := by have := l.isLt; omega
  have hQval := truncated_division_weighted hU0 hU_wt (sixNormLocalNum_weighted n p hn i j k) hdvd q hqm
  have hcoeff : sixPrincipalCoefficients n i j k l =
      (1 / (sixNormLocalCof n k).coeff 0) * Q.coeff q := by
    dsimp [Q]
    rw [coeff_C_mul, ← mul_assoc, one_div_mul_cancel hC0_ne, one_mul, sixLocalPrincipal_coeff]
  rw [hcoeff]
  have hinv : ValAtLeast p (-(((14 - sixPoleOrder n k : ℕ) : ℤ) * S))
      (1 / (sixNormLocalCof n k).coeff 0) := by
    right
    rw [one_div, padicValRat.inv]
    linarith
  have hmul := valAtLeast_mul hinv hQval
  have hord := six_pole_order_le n k
  have hl := l.isLt
  have hexp : -((13 - l.val : ℕ) : ℤ) * S ≤
      -(((14 - sixPoleOrder n k : ℕ) : ℤ) * S) + -(S * (q : ℤ)) := by
    have hsum_nat : (14 - sixPoleOrder n k) + q = 13 - l.val := by dsimp [q]; omega
    have hsum_int : ((14 - sixPoleOrder n k : ℕ) : ℤ) + (q : ℤ) = ((13 - l.val : ℕ) : ℤ) := by
      exact_mod_cast hsum_nat
    nlinarith
  exact valAtLeast_mono hmul hexp

theorem harmonicCutoff_valAtLeast_allPrimes (p : ℕ) [Fact p.Prime]
    (s N M₀ : ℕ) (hNM : N ≤ M₀) :
    ValAtLeast p (-((s : ℤ) * (Nat.log p M₀ : ℤ))) (harmonicCutoff s N) := by
  unfold harmonicCutoff
  apply valAtLeast_sum
  intro j hj
  have hj1 : 1 ≤ j + 1 := by omega
  have hjM : j + 1 ≤ M₀ := by have := mem_range.mp hj; omega
  right
  have hj_ne : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [one_div, padicValRat.inv]
  have hcast : ((j : ℚ) + 1) = ((j + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [hcast]
  have hpow_val : padicValRat p (((j + 1 : ℕ) : ℚ) ^ s) = (s : ℤ) * (padicValNat p (j + 1) : ℤ) := by
    induction s with
    | zero => simp
    | succ s ih =>
      rw [pow_succ, padicValRat.mul (pow_ne_zero s hj_ne) hj_ne, ih, padicValRat.of_nat]
      push_cast; ring
  rw [hpow_val]
  have hlog : (padicValNat p (j + 1) : ℤ) ≤ (Nat.log p M₀ : ℤ) := by
    exact_mod_cast padicValNat_le_log p hj1 hjM
  nlinarith

/-- Entrywise Lemma 3 bound: every entry of `sixMatrix n` has `p`-adic Gauss valuation
at least `-18 * Nat.log p (55 * n)` for EVERY prime `p`. -/
theorem sixMatrix_entry_formalValAtLeast_allPrimes (n p : ℕ) [Fact p.Prime] (hn : 0 < n)
    (i j : Fin (rank n)) :
    FormalValAtLeast p (-(18 * (Nat.log p (55 * n) : ℤ))) (sixMatrix n i j) := by
  let S : ℤ := (Nat.log p (55 * n) : ℤ)
  have hS0 : 0 ≤ S := Int.natCast_nonneg _
  unfold sixMatrix
  apply formalValAtLeast_add
  · apply formalValAtLeast_C
    unfold sixMomentConstant
    apply valAtLeast_neg
    apply valAtLeast_sum; intro k hk
    apply valAtLeast_sum; intro l _
    have hbnd := six_pole_address_bounds n k hk
    have hpc := sixPrincipalCoefficients_valAtLeast_allPrimes n p hn i j k hk l
    have hch := valAtLeast_natCast p ((l.val + 4).choose 4)
    have hhc := harmonicCutoff_valAtLeast_allPrimes p (l.val + 5) (k - 40 * n - 1) (55 * n) (by omega)
    have hmul := valAtLeast_mul (valAtLeast_mul hpc hch) hhc
    have hl : l.val ≤ 13 := by have := l.isLt; have := six_pole_order_le n k; omega
    have hexp : -(18 * S) ≤
        -((13 - l.val : ℕ) : ℤ) * S + 0 + -(((l.val + 5 : ℕ) : ℤ) * S) := by
      have h18 : ((13 - l.val : ℕ) : ℤ) + ((l.val + 5 : ℕ) : ℤ) = 18 := by omega
      nlinarith
    exact valAtLeast_mono hmul hexp
  · apply formalValAtLeast_sum; intro s _
    apply formalValAtLeast_mono
      (formalValAtLeast_C_mul (a := -(18 * S)) (b := 0) ?_ (formalValAtLeast_X p s))
      (by omega)
    unfold sixZetaCoefficient sixOrderCoefficient
    have hch := valAtLeast_natCast p ((2 + 2 * s.val + 4).choose 4)
    have hsum : ValAtLeast p (-(18 * S))
        (∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
          if l.val = 2 + 2 * s.val then sixPrincipalCoefficients n i j k l else 0) := by
      apply valAtLeast_sum; intro k hk
      apply valAtLeast_sum; intro l _
      split_ifs
      · have hpc := sixPrincipalCoefficients_valAtLeast_allPrimes n p hn i j k hk l
        have hl : 13 - l.val ≤ 18 := by omega
        exact valAtLeast_mono hpc (by nlinarith)
      · exact valAtLeast_zero p _
    exact valAtLeast_mono (valAtLeast_mul hch hsum) (by omega)

/-- Determinant Lemma 3 bound: `(sixMatrix n).det` has Gauss valuation at least
`-18 * (15n) * Nat.log p (55n)` for EVERY prime `p`. -/
theorem sixMatrix_det_formalValAtLeast_allPrimes (n p : ℕ) [Fact p.Prime] :
    FormalValAtLeast p (-(18 * (rank n : ℤ) * (Nat.log p (55 * n) : ℤ))) (sixMatrix n).det := by
  by_cases hn : n = 0
  · subst hn
    have h1 : (sixMatrix 0).det = 1 := by
      have : rank 0 = 0 := rfl
      rw [Matrix.det_eq_one_of_card_eq_zero (by simp [rank])]
    rw [h1]
    simpa [rank] using formalValAtLeast_one p
  · have hdet := formalValAtLeast_det_uniform (sixMatrix n) (-(18 * (Nat.log p (55 * n) : ℤ)))
      (sixMatrix_entry_formalValAtLeast_allPrimes n p (Nat.pos_of_ne_zero hn))
    have heq : -(18 * (rank n : ℤ) * (Nat.log p (55 * n) : ℤ)) =
        (rank n : ℤ) * -(18 * (Nat.log p (55 * n) : ℤ)) := by ring
    exact formalValAtLeast_mono hdet heq.le

/-- **Lemma 3 (universal all-prime-power bound, sharp `M₀ = 55n`)**: for EVERY prime `p`
and EVERY `n : ℕ`, `-v_p(sixPrimitiveScalar n) ≤ 18 * (15n) * Nat.log p (55n)`. -/
theorem sixPrimitiveScalar_universal_bound_55 (n p : ℕ) [Fact p.Prime] :
    -padicValRat p (sixPrimitiveScalar n) ≤
      18 * (15 * (n : ℤ)) * (Nat.log p (55 * n) : ℤ) := by
  have hL := sixMatrix_det_formalValAtLeast_allPrimes n p
  have hnonpos : -(18 * (rank n : ℤ) * (Nat.log p (55 * n) : ℤ)) ≤ 0 :=
    neg_nonpos.mpr (by positivity)
  have hge := sixPrimitiveScalar_padicValRat_ge_of_formal_nonpos n p _ hnonpos hL
  have hrank : (rank n : ℤ) = 15 * (n : ℤ) := by unfold rank; push_cast; ring
  rw [hrank] at hge
  linarith

/-- **Lemma 3 (universal all-prime-power bound with `M₀ = 140n + 2`)**: for EVERY prime `p`
and EVERY `n : ℕ`, `-v_p(sixPrimitiveScalar n) ≤ 18 * (15n) * Nat.log p (140n + 2)`. -/
theorem sixPrimitiveScalar_universal_bound (n p : ℕ) [Fact p.Prime] :
    -padicValRat p (sixPrimitiveScalar n) ≤
      18 * (15 * (n : ℤ)) * (Nat.log p (140 * n + 2) : ℤ) := by
  have h1 := sixPrimitiveScalar_universal_bound_55 n p
  have hlog : Nat.log p (55 * n) ≤ Nat.log p (140 * n + 2) :=
    Nat.log_mono_right (by omega)
  have hlogZ : (Nat.log p (55 * n) : ℤ) ≤ (Nat.log p (140 * n + 2) : ℤ) := by
    exact_mod_cast hlog
  have hcoeff : (0 : ℤ) ≤ 18 * (15 * (n : ℤ)) := by positivity
  nlinarith

/-- **Large-prime vanishing (`p > 55n`)**: every entry of `sixMatrix n` is `p`-integral,
so `0 ≤ v_p(sixPrimitiveScalar n)` (i.e., `p` does not divide the denominator of `γ_n`). -/
theorem sixMatrix_large_prime_integral (n p : ℕ) [Fact p.Prime] (hp : 55 * n < p)
    (i j : Fin (rank n)) :
    FormalValAtLeast p 0 (sixMatrix n i j) := by
  by_cases hn : n = 0
  · subst hn; exact Fin.elim0 i
  · have h := sixMatrix_entry_formalValAtLeast_allPrimes n p (Nat.pos_of_ne_zero hn) i j
    have hlog : Nat.log p (55 * n) = 0 := Nat.log_eq_zero_iff.mpr (Or.inl hp)
    simpa [hlog] using h

theorem sixPrimitiveScalar_large_prime_integral (n p : ℕ) [Fact p.Prime] (hp : 55 * n < p) :
    -padicValRat p (sixPrimitiveScalar n) ≤ 0 := by
  have h := sixPrimitiveScalar_universal_bound_55 n p
  have hlog : Nat.log p (55 * n) = 0 := Nat.log_eq_zero_iff.mpr (Or.inl hp)
  simpa [hlog] using h

/-- Explicit LCM clearing (Lemma 3): `D_{M₀}^18 * (sixMatrix n i j)` has integer coefficients
for any `M₀ ≥ 55 * n` (in particular `M₀ = 55 * n` or `M₀ = 140 * n + 2`). -/
theorem sixMatrix_cleared_by_lcm_18 (n M₀ : ℕ) (hM : 55 * n ≤ M₀)
    (i j : Fin (rank n)) (m : Fin 6 →₀ ℕ) :
    let D : ℕ := (Finset.Icc 1 M₀).lcm id
    ∃ z : ℤ, ((D : ℚ) ^ 18) * (sixMatrix n i j).coeff m = (z : ℚ) := by
  intro D
  have hn : 0 < n := by have := i.isLt; unfold rank at this; omega
  let q : ℚ := ((D : ℚ) ^ 18) * (sixMatrix n i j).coeff m
  have hden1 : q.den = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have : Fact p.Prime := ⟨hp⟩
    have hneg : padicValRat p q < 0 := by
      have hq0 : q ≠ 0 := by
        intro h0; apply hne; simp [h0]
      have hpos : 0 < padicValNat p q.den :=
        one_le_padicValNat_of_dvd q.den_nz hpdvd
      rcases q.num_or_den_zero_padicVal hp with hnum0 | hden0
      · rw [padicValRat_def, hnum0]; omega
      · omega
    have hDne_nat : D ≠ 0 := by
      intro h0
      obtain ⟨x, hx, hx0⟩ := Finset.lcm_eq_zero_iff.mp h0
      have := (Finset.mem_Icc.mp hx).1
      dsimp at hx0
      omega
    have hD_val : (Nat.log p (55 * n) : ℤ) ≤ padicValRat p (D : ℚ) := by
      have hpow_le : p ^ Nat.log p (55 * n) ≤ M₀ :=
        (Nat.pow_log_le_self p (by omega : 55 * n ≠ 0)).trans hM
      have hpow_pos : 1 ≤ p ^ Nat.log p (55 * n) := Nat.one_le_pow _ _ hp.pos
      have hdvdD : p ^ Nat.log p (55 * n) ∣ D :=
        Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hpow_pos, hpow_le⟩)
      rw [padicValRat.of_nat]
      exact_mod_cast (padicValNat_dvd_iff_le hDne_nat).mp hdvdD
    have hD18 : ValAtLeast p (18 * (Nat.log p (55 * n) : ℤ)) ((D : ℚ) ^ 18) := by
      have hDne : (D : ℚ) ≠ 0 := by exact_mod_cast hDne_nat
      right
      have hpow : padicValRat p ((D : ℚ) ^ 18) = 18 * padicValRat p (D : ℚ) := by
        have hgen : ∀ k : ℕ, padicValRat p ((D : ℚ) ^ k) = (k : ℤ) * padicValRat p (D : ℚ) := by
          intro k; induction k with
          | zero => simp
          | succ k ih => rw [pow_succ, padicValRat.mul (pow_ne_zero k hDne) hDne, ih]; push_cast; ring
        exact_mod_cast hgen 18
      rw [hpow]; linarith
    have hc_val := sixMatrix_entry_formalValAtLeast_allPrimes n p hn i j m
    have hq_val : ValAtLeast p 0 q := by
      have hm := valAtLeast_mul hD18 hc_val
      exact valAtLeast_mono hm (by omega)
    rcases hq_val with hq0 | hge0
    · apply hne; simp [hq0]
    · omega
  refine ⟨q.num, ?_⟩
  change q = (q.num : ℚ)
  rw [← Rat.num_div_den q, hden1]
  simp

end OddZetaSix
