import OddZetaSix.SixIdentity
import OddZetaSix.SixConfluentHermite
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Local `p`-Adic Ring, Tail-Pole Stripping, and Confluent Binomial Blocks

For prime `p = 50n + 1`:
1. Defines the local ring `sixGateIntegralRing p` (`{q : ℚ | 0 ≤ padicValRat p q}`)
   and residue-field ring homomorphism `sixGateReduction p : sixGateIntegralRing p →+* ZMod p`.
2. Proves `p`-integrality of `sixNormalization n`, `evenBasis i` (`i < 15n`),
   all local cofactors, all principal coefficients `sixPrincipalCoefficients`,
   all zeta coefficients, and all non-singular harmonic terms.
3. Splits `MvPolynomial.eval q (sixMatrix n i j)` for `q ∈ Z_(p)^6` into a
   `Z_(p)`-regular remainder plus the singular sum supported solely on the
   `5n` tail poles `k_t = 90n + 2 + t` (`t : Fin (5n)`).
4. Strips the `(X - C p)^q` numerator factor (`q ∈ {0, 1, 2}`, with `m = q + 5`),
   constructs the truncated unit quotient `sixGateUnitSeries n t`, proves the
   exact finite binomial collapse into powers `p^(-9 + r + a + b)`, and certifies
   the three fixed `3 × 3` binomial block determinants `-50, -20, -1` are units mod `p`.
-/

noncomputable section
set_option autoImplicit false

namespace OddZetaSix

open Polynomial Finset

/-! ## Local ring `ℤ_(p)` and residue reduction `ℤ_(p) →+* ZMod p` -/

def sixGateIntegralRing (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {q : ℚ | 0 ≤ padicValRat p q}
  zero_mem' := by simp
  one_mem' := by simp
  neg_mem' {x} hx := by simpa only [Set.mem_ofPred_eq, padicValRat.neg] using hx
  add_mem' {x y} hx hy := by
    by_cases hxy : x + y = 0
    · simp [hxy]
    · exact le_trans (le_min hx hy) (padicValRat.min_le_padicValRat_add hxy)
  mul_mem' {x y} hx hy := by
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hy0 : y = 0
    · simp [hy0]
    change 0 ≤ padicValRat p (x * y)
    rw [padicValRat.mul hx0 hy0]
    exact add_nonneg hx hy

theorem sixGateIntegralRing_mem_iff (p : ℕ) [Fact p.Prime] (q : ℚ) :
    q ∈ sixGateIntegralRing p ↔ 0 ≤ padicValRat p q := Iff.rfl

theorem sixGateIntegralRing_den_valuation (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : q ∈ sixGateIntegralRing p) : padicValNat p q.den = 0 := by
  have hnonneg : 0 ≤ padicValRat p q := hq
  rcases q.num_or_den_zero_padicVal (Fact.out : p.Prime) with hn | hd
  · rw [padicValRat_def, hn] at hnonneg
    omega
  · exact hd

theorem sixGateIntegralRing_den_not_dvd (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : q ∈ sixGateIntegralRing p) : ¬ p ∣ q.den := by
  have hd := sixGateIntegralRing_den_valuation p q hq
  rcases padicValNat.eq_zero_iff.mp hd with hp | hz | hnd
  · exact False.elim ((Fact.out : p.Prime).ne_one hp)
  · exact False.elim (q.den_nz hz)
  · exact hnd

theorem sixGateIntegralRing_mem_of_den_not_dvd (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : ¬ p ∣ q.den) : q ∈ sixGateIntegralRing p := by
  change 0 ≤ padicValRat p q
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hq]
  simp only [Nat.cast_zero, sub_zero]
  exact Int.natCast_nonneg _

theorem sixGateIntegralRing_den_cast_ne_zero (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : q ∈ sixGateIntegralRing p) : (q.den : ZMod p) ≠ 0 := by
  simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using
    (sixGateIntegralRing_den_not_dvd p q hq)

def sixGateReduction (p : ℕ) [Fact p.Prime] : sixGateIntegralRing p →+* ZMod p where
  toFun q := ((q : ℚ) : ZMod p)
  map_zero' := by simp
  map_one' := by simp
  map_add' q r := Rat.cast_add_of_ne_zero
    (sixGateIntegralRing_den_cast_ne_zero p q q.property)
    (sixGateIntegralRing_den_cast_ne_zero p r r.property)
  map_mul' q r := Rat.cast_mul_of_ne_zero
    (sixGateIntegralRing_den_cast_ne_zero p q q.property)
    (sixGateIntegralRing_den_cast_ne_zero p r r.property)

@[simp]
theorem sixGateReduction_apply (p : ℕ) [Fact p.Prime] (q : sixGateIntegralRing p) :
    sixGateReduction p q = ((q : ℚ) : ZMod p) := rfl

theorem sixGateReduction_ne_zero_iff (p : ℕ) [Fact p.Prime] (q : sixGateIntegralRing p) :
    sixGateReduction p q ≠ 0 ↔ (q : ℚ) ≠ 0 ∧ padicValRat p (q : ℚ) = 0 := by
  have hd := sixGateIntegralRing_den_cast_ne_zero p q q.property
  have hdv := sixGateIntegralRing_den_valuation p q q.property
  rw [sixGateReduction_apply, Rat.cast_def, div_ne_zero_iff]
  change ((q : ℚ).num : ZMod p) ≠ 0 ∧ ((q : ℚ).den : ZMod p) ≠ 0 ↔ _
  simp only [hd, ne_eq, not_false_eq_true, and_true,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [padicValRat_def, hdv, Nat.cast_zero, sub_zero]
  constructor
  · intro hn
    refine ⟨fun hq => hn (by simp [hq]), ?_⟩
    exact_mod_cast padicValInt.eq_zero_of_not_dvd hn
  · rintro ⟨hq, hv⟩
    have hv' : padicValInt p (q : ℚ).num = 0 := by exact_mod_cast hv
    rcases padicValInt.eq_zero_iff.mp hv' with hp | hn | hnd
    · exact False.elim ((Fact.out : p.Prime).ne_one hp)
    · exact False.elim ((Rat.num_ne_zero.mpr hq) hn)
    · exact hnd

theorem sixGateIntegralRing_inv_of_unit (p : ℕ) [Fact p.Prime] (q : ℚ)
    (_hq : q ≠ 0) (hv : padicValRat p q = 0) : q⁻¹ ∈ sixGateIntegralRing p := by
  change 0 ≤ padicValRat p q⁻¹
  rw [padicValRat.inv, hv]
  omega

theorem sixGateIntegralRing_cast_add (p : ℕ) [Fact p.Prime] {x y : ℚ}
    (hx : x ∈ sixGateIntegralRing p) (hy : y ∈ sixGateIntegralRing p) :
    ((x + y : ℚ) : ZMod p) = (x : ZMod p) + (y : ZMod p) :=
  (sixGateReduction p).map_add ⟨x, hx⟩ ⟨y, hy⟩

theorem sixGateIntegralRing_cast_mul (p : ℕ) [Fact p.Prime] {x y : ℚ}
    (hx : x ∈ sixGateIntegralRing p) (hy : y ∈ sixGateIntegralRing p) :
    ((x * y : ℚ) : ZMod p) = (x : ZMod p) * (y : ZMod p) :=
  (sixGateReduction p).map_mul ⟨x, hx⟩ ⟨y, hy⟩

theorem sixGateIntegralRing_cast_pow (p : ℕ) [Fact p.Prime] {x : ℚ}
    (hx : x ∈ sixGateIntegralRing p) (e : ℕ) :
    ((x ^ e : ℚ) : ZMod p) = (x : ZMod p) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, pow_succ, sixGateIntegralRing_cast_mul p
      ((sixGateIntegralRing p).pow_mem hx e) hx, ih]

theorem sixGateReduction_mul_p_eq_zero (p : ℕ) [Fact p.Prime]
    (q : ℚ) (hq : q ∈ sixGateIntegralRing p) :
    (((p : ℚ) * q : ℚ) : ZMod p) = 0 := by
  rw [sixGateIntegralRing_cast_mul p (natCast_mem _ p) hq, Rat.cast_natCast,
    ZMod.natCast_self, zero_mul]

theorem sixGateReduction_p_pow_mul_eq_zero (p : ℕ) [Fact p.Prime] {e : ℕ} (he : 1 ≤ e)
    (q : ℚ) (hq : q ∈ sixGateIntegralRing p) :
    (((p : ℚ) ^ e * q : ℚ) : ZMod p) = 0 := by
  rw [sixGateIntegralRing_cast_mul p
      ((sixGateIntegralRing p).pow_mem (natCast_mem _ p) e) hq,
    sixGateIntegralRing_cast_pow p (natCast_mem _ p) e, Rat.cast_natCast,
    ZMod.natCast_self, zero_pow (by omega : e ≠ 0), zero_mul]

theorem sixGateIntegralRing_cast_sum {ι : Type*} (p : ℕ) [Fact p.Prime]
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ∈ sixGateIntegralRing p) :
    ((∑ i ∈ s, f i : ℚ) : ZMod p) = ∑ i ∈ s, (f i : ZMod p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      sixGateIntegralRing_cast_add p (hf a (mem_insert_self a s))
        ((sixGateIntegralRing p).sum_mem (fun b hb => hf b (mem_insert_of_mem hb))),
      ih (fun b hb => hf b (mem_insert_of_mem hb))]

theorem sixGateIntegralRing_cast_prod {ι : Type*} (p : ℕ) [Fact p.Prime]
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ∈ sixGateIntegralRing p) :
    ((∏ i ∈ s, f i : ℚ) : ZMod p) = ∏ i ∈ s, (f i : ZMod p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      sixGateIntegralRing_cast_mul p (hf a (mem_insert_self a s))
        ((sixGateIntegralRing p).prod_mem (fun b hb => hf b (mem_insert_of_mem hb))),
      ih (fun b hb => hf b (mem_insert_of_mem hb))]

/-! ## `p`-integrality of polynomials and Taylor shifts -/

def PolyInSubring (S : Subring ℚ) (P : ℚ[X]) : Prop := ∀ q : ℕ, P.coeff q ∈ S

theorem polyInSubring_C {S : Subring ℚ} {c : ℚ} (hc : c ∈ S) : PolyInSubring S (C c) := by
  intro q
  rw [coeff_C]
  split_ifs
  · exact hc
  · exact S.zero_mem

theorem polyInSubring_X {S : Subring ℚ} : PolyInSubring S (X : ℚ[X]) := by
  intro q
  rw [coeff_X]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

theorem polyInSubring_add {S : Subring ℚ} {P Q : ℚ[X]}
    (hP : PolyInSubring S P) (hQ : PolyInSubring S Q) : PolyInSubring S (P + Q) := by
  intro q; rw [coeff_add]; exact S.add_mem (hP q) (hQ q)

theorem polyInSubring_sub {S : Subring ℚ} {P Q : ℚ[X]}
    (hP : PolyInSubring S P) (hQ : PolyInSubring S Q) : PolyInSubring S (P - Q) := by
  intro q; rw [coeff_sub]; exact S.sub_mem (hP q) (hQ q)

theorem polyInSubring_mul {S : Subring ℚ} {P Q : ℚ[X]}
    (hP : PolyInSubring S P) (hQ : PolyInSubring S Q) : PolyInSubring S (P * Q) := by
  intro q
  rw [coeff_mul]
  exact S.sum_mem fun a _ => S.mul_mem (hP a.1) (hQ a.2)

theorem polyInSubring_pow {S : Subring ℚ} {P : ℚ[X]} (hP : PolyInSubring S P) (m : ℕ) :
    PolyInSubring S (P ^ m) := by
  induction m with
  | zero => intro q; rw [pow_zero, coeff_one]; split_ifs; exact S.one_mem; exact S.zero_mem
  | succ m ih => rw [pow_succ]; exact polyInSubring_mul ih hP

theorem polyInSubring_prod {ι : Type*} {S : Subring ℚ} (s : Finset ι) (f : ι → ℚ[X])
    (hf : ∀ i ∈ s, PolyInSubring S (f i)) : PolyInSubring S (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro q; rw [Finset.prod_empty, coeff_one]; split_ifs; exact S.one_mem; exact S.zero_mem
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact polyInSubring_mul (hf a (mem_insert_self a s))
      (ih fun b hb => hf b (mem_insert_of_mem hb))

theorem polyInSubring_taylor {S : Subring ℚ} {P : ℚ[X]} (hP : PolyInSubring S P)
    {r : ℚ} (hr : r ∈ S) : PolyInSubring S (taylor r P) := by
  rw [taylor_apply]
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_comp]
    -- Use explicit monomial sum instead so hp/hq need not split coefficients.
    clear hp hq
    rw [← add_comp, (p + q).as_sum_range_C_mul_X_pow]
    simp only [Polynomial.sum_comp, mul_comp, C_comp, pow_comp, X_comp]
    intro m
    rw [finsetSum_coeff]
    apply S.sum_mem
    intro k _
    exact (polyInSubring_mul (polyInSubring_C (hP k))
      (polyInSubring_pow (polyInSubring_add polyInSubring_X (polyInSubring_C hr)) k)) m
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp]
    have ha : a ∈ S := by simpa using hP n
    exact polyInSubring_mul (polyInSubring_C ha)
      (polyInSubring_pow (polyInSubring_add polyInSubring_X (polyInSubring_C hr)) n)

theorem polyInSubring_comp {S : Subring ℚ} {P Q : ℚ[X]}
    (hP : PolyInSubring S P) (hQ : PolyInSubring S Q) : PolyInSubring S (P.comp Q) := by
  rw [P.as_sum_range_C_mul_X_pow]
  simp only [Polynomial.sum_comp, mul_comp, C_comp, pow_comp, X_comp]
  intro m
  rw [finsetSum_coeff]
  apply S.sum_mem
  intro k _
  exact (polyInSubring_mul (polyInSubring_C (hP k)) (polyInSubring_pow hQ k)) m

/-! ## Normalization, basis, and pole-cofactor units at `p = 50n + 1` -/

private theorem gate_padic_prod {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ a ∈ s, f a ≠ 0) :
    padicValRat p (∏ a ∈ s, f a) = ∑ a ∈ s, padicValRat p (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValRat.mul (hf a (mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr (fun b hb => hf b (mem_insert_of_mem hb))),
      ih (fun b hb => hf b (mem_insert_of_mem hb))]

theorem six_factorial_padicValRat_zero (m p : ℕ) (hp : p.Prime) (hm : m < p) :
    padicValRat p (m.factorial : ℚ) = 0 := by
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]
  · rfl
  · exact fun h => (Nat.not_le_of_lt hm) (hp.dvd_factorial.mp h)

theorem sixGate_normalization_unit (n : ℕ) [Fact (gatePrime n).Prime] :
    sixNormalization n ≠ 0 ∧ padicValRat (gatePrime n) (sixNormalization n) = 0 := by
  have hp : (gatePrime n).Prime := Fact.out
  have h51 := gatePrime_ge_51 n hp
  refine ⟨sixNormalization_ne_zero n, ?_⟩
  have hf (m : ℕ) : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hnum : (∏ b : Fin 14, (((50 - 2 * sixOffset b) * n).factorial : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun _ _ => hf _)
  have hden : (∏ a : Fin 5, ((sixZero a * n).factorial : ℚ) ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun _ _ => pow_ne_zero _ (hf _))
  rw [sixNormalization, padicValRat.div (mul_ne_zero (by norm_num) hnum) hden,
    padicValRat.mul (by norm_num) hnum]
  have htwo : padicValRat (gatePrime n) 2 = 0 := by
    have h : padicValNat (gatePrime n) 2 = 0 :=
      padicValNat.eq_zero_of_not_dvd (gatePrime_not_dvd_two n hp)
    change padicValRat (gatePrime n) ((2 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, h]
    rfl
  rw [htwo, gate_padic_prod _ _ (fun _ _ => hf _),
    gate_padic_prod _ _ (fun _ _ => pow_ne_zero _ (hf _))]
  have hA : (∑ b : Fin 14, padicValRat (gatePrime n) (((50 - 2 * sixOffset b) * n).factorial : ℚ)) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    apply six_factorial_padicValRat_zero _ _ hp
    have : 50 - 2 * sixOffset b ≤ 50 := Nat.sub_le _ _
    unfold gatePrime
    nlinarith
  have hB : (∑ a : Fin 5, padicValRat (gatePrime n) (((sixZero a * n).factorial : ℚ) ^ 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    have hza : sixZero a ≤ 43 := by fin_cases a <;> decide
    rw [padicValRat.pow, six_factorial_padicValRat_zero _ _ hp (by unfold gatePrime; nlinarith),
      mul_zero]
  rw [hA, hB]
  norm_num

theorem sixGate_evenBasis_in_subring (n : ℕ) [Fact (gatePrime n).Prime] (i : Fin (rank n)) :
    PolyInSubring (sixGateIntegralRing (gatePrime n)) (evenBasis i.val) := by
  have hp : (gatePrime n).Prime := Fact.out
  cases h : i.val with
  | zero =>
    rw [evenBasis_zero]
    exact polyInSubring_C (sixGateIntegralRing _).one_mem
  | succ m =>
    rw [evenBasis_succ]
    have hlt : 2 * (m + 1) < gatePrime n := by
      have hi : i.val < 15 * n := i.isLt
      unfold gatePrime
      omega
    have hfac : padicValRat (gatePrime n) (((2 * (m + 1)).factorial : ℚ)) = 0 :=
      six_factorial_padicValRat_zero _ _ hp hlt
    have hinv : (((2 * (m + 1)).factorial : ℚ))⁻¹ ∈ sixGateIntegralRing (gatePrime n) :=
      sixGateIntegralRing_inv_of_unit _ _ (by exact_mod_cast Nat.factorial_ne_zero _) hfac
    have hsc : (2 : ℚ) / ((2 * (m + 1)).factorial : ℚ) ∈ sixGateIntegralRing (gatePrime n) := by
      rw [div_eq_mul_inv]
      exact (sixGateIntegralRing _).mul_mem (natCast_mem _ 2) hinv
    apply polyInSubring_mul (polyInSubring_C hsc)
    apply polyInSubring_mul (polyInSubring_pow polyInSubring_X 2)
    apply polyInSubring_prod
    intro j _
    exact polyInSubring_sub (polyInSubring_pow polyInSubring_X 2)
      (polyInSubring_C ((sixGateIntegralRing _).pow_mem
        ((sixGateIntegralRing _).add_mem (natCast_mem _ j) (sixGateIntegralRing _).one_mem) 2))

theorem sixGate_centeredMultiplier_in_subring (n : ℕ) [Fact (gatePrime n).Prime]
    (i j : Fin (rank n)) :
    PolyInSubring (sixGateIntegralRing (gatePrime n)) (centeredMultiplier n i.val j.val) := by
  apply polyInSubring_comp
  · exact polyInSubring_mul (sixGate_evenBasis_in_subring n i) (sixGate_evenBasis_in_subring n j)
  · exact polyInSubring_add polyInSubring_X
      (polyInSubring_C ((sixGateIntegralRing _).add_mem
        ((sixGateIntegralRing _).mul_mem (natCast_mem _ 70) (natCast_mem _ n))
        (sixGateIntegralRing _).one_mem))

/-- Mapping a `ℤ_(p)[X]` polynomial into `(ZMod p)[X]` via `sixGateReduction`. -/
def reducePoly (p : ℕ) [Fact p.Prime] (P : ℚ[X]) : (ZMod p)[X] :=
  ∑ k ∈ range (P.natDegree + 1), monomial k ((P.coeff k : ℚ) : ZMod p)

theorem reducePoly_coeff (p : ℕ) [Fact p.Prime] (P : ℚ[X]) (k : ℕ) :
    (reducePoly p P).coeff k = ((P.coeff k : ℚ) : ZMod p) := by
  unfold reducePoly
  rw [finsetSum_coeff]
  by_cases hk : k < P.natDegree + 1
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hbk; simp [coeff_monomial, hbk]
    · intro h; exact (h (mem_range.mpr hk)).elim
  · rw [Finset.sum_eq_zero]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), Rat.cast_zero]
    · intro b hb; simp [coeff_monomial, show b ≠ k by have := mem_range.mp hb; omega]

theorem reducePoly_add (p : ℕ) [Fact p.Prime] {P Q : ℚ[X]}
    (hP : PolyInSubring (sixGateIntegralRing p) P)
    (hQ : PolyInSubring (sixGateIntegralRing p) Q) :
    reducePoly p (P + Q) = reducePoly p P + reducePoly p Q := by
  ext k
  rw [coeff_add, reducePoly_coeff, reducePoly_coeff, reducePoly_coeff, coeff_add,
    sixGateIntegralRing_cast_add p (hP k) (hQ k)]

theorem reducePoly_mul (p : ℕ) [Fact p.Prime] {P Q : ℚ[X]}
    (hP : PolyInSubring (sixGateIntegralRing p) P)
    (hQ : PolyInSubring (sixGateIntegralRing p) Q) :
    reducePoly p (P * Q) = reducePoly p P * reducePoly p Q := by
  ext k
  rw [reducePoly_coeff, coeff_mul, coeff_mul,
    sixGateIntegralRing_cast_sum p (Finset.antidiagonal k)
      (fun a => P.coeff a.1 * Q.coeff a.2)
      (fun a _ => (sixGateIntegralRing p).mul_mem (hP a.1) (hQ a.2))]
  apply Finset.sum_congr rfl
  intro a _
  rw [sixGateIntegralRing_cast_mul p (hP a.1) (hQ a.2), reducePoly_coeff, reducePoly_coeff]

theorem reducePoly_C (p : ℕ) [Fact p.Prime] (c : ℚ) :
    reducePoly p (C c) = C ((c : ℚ) : ZMod p) := by
  ext k
  rw [reducePoly_coeff, coeff_C, coeff_C]
  split_ifs <;> simp

theorem reducePoly_zero (p : ℕ) [Fact p.Prime] : reducePoly p 0 = 0 := by
  rw [← map_zero C, reducePoly_C, Rat.cast_zero, map_zero]

theorem reducePoly_one (p : ℕ) [Fact p.Prime] : reducePoly p 1 = 1 := by
  rw [← map_one C, reducePoly_C, Rat.cast_one, map_one]

theorem reducePoly_X (p : ℕ) [Fact p.Prime] :
    reducePoly p (X : ℚ[X]) = X := by
  ext k
  rw [reducePoly_coeff, coeff_X, coeff_X]
  split_ifs <;> simp

theorem reducePoly_pow (p : ℕ) [Fact p.Prime] {P : ℚ[X]}
    (hP : PolyInSubring (sixGateIntegralRing p) P) (m : ℕ) :
    reducePoly p (P ^ m) = (reducePoly p P) ^ m := by
  induction m with
  | zero => simpa only [pow_zero] using reducePoly_one p
  | succ m ih =>
    rw [pow_succ, pow_succ, reducePoly_mul p (polyInSubring_pow hP m) hP, ih]

theorem reducePoly_prod {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℚ[X])
    (hf : ∀ i ∈ s, PolyInSubring (sixGateIntegralRing p) (f i)) :
    reducePoly p (∏ i ∈ s, f i) = ∏ i ∈ s, reducePoly p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using reducePoly_one p
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      reducePoly_mul p (hf a (mem_insert_self a s))
        (polyInSubring_prod s f (fun b hb => hf b (mem_insert_of_mem hb))),
      ih (fun b hb => hf b (mem_insert_of_mem hb))]

theorem reducePoly_taylor (p : ℕ) [Fact p.Prime] {P : ℚ[X]}
    (hP : PolyInSubring (sixGateIntegralRing p) P) {r : ℚ} (hr : r ∈ sixGateIntegralRing p) :
    reducePoly p (taylor r P) = taylor ((r : ℚ) : ZMod p) (reducePoly p P) := by
  rw [taylor_apply, taylor_apply]
  have h1 : P.comp (X + C r) = ∑ k ∈ range (P.natDegree + 1), C (P.coeff k) * (X + C r) ^ k := by
    conv_lhs => rw [P.as_sum_range_C_mul_X_pow]
    simp only [Polynomial.sum_comp, mul_comp, C_comp, pow_comp, X_comp]
  have h2 : (reducePoly p P).comp (X + C ((r : ℚ) : ZMod p)) =
      ∑ k ∈ range (P.natDegree + 1),
        C ((P.coeff k : ℚ) : ZMod p) * (X + C ((r : ℚ) : ZMod p)) ^ k := by
    unfold reducePoly
    simp only [Polynomial.sum_comp, ← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp]
  rw [h1, h2]
  have hterm (k : ℕ) : PolyInSubring (sixGateIntegralRing p) (C (P.coeff k) * (X + C r) ^ k) :=
    polyInSubring_mul (polyInSubring_C (hP k))
      (polyInSubring_pow (polyInSubring_add polyInSubring_X (polyInSubring_C hr)) k)
  -- Induction on range for sum
  have hsum_red : ∀ m : ℕ,
      reducePoly p (∑ k ∈ range m, C (P.coeff k) * (X + C r) ^ k) =
        ∑ k ∈ range m, C ((P.coeff k : ℚ) : ZMod p) * (X + C ((r : ℚ) : ZMod p)) ^ k := by
    intro m
    induction m with
    | zero => simpa only [Finset.range_zero, Finset.sum_empty] using reducePoly_zero p
    | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        reducePoly_add p
          (fun q => by rw [finsetSum_coeff]; exact (sixGateIntegralRing p).sum_mem (fun k _ => hterm k q))
          (hterm m),
        ih,
        reducePoly_mul p (polyInSubring_C (hP m))
          (polyInSubring_pow (polyInSubring_add polyInSubring_X (polyInSubring_C hr)) m),
        reducePoly_C,
        reducePoly_pow p (polyInSubring_add polyInSubring_X (polyInSubring_C hr)) m,
        reducePoly_add p polyInSubring_X (polyInSubring_C hr), reducePoly_X, reducePoly_C]
  exact hsum_red (P.natDegree + 1)

theorem reducePoly_evenBasis (n : ℕ) [Fact (gatePrime n).Prime] (i : Fin (rank n)) :
    reducePoly (gatePrime n) (evenBasis i.val) = gateEvenPoly n i := by
  have hp : (gatePrime n).Prime := Fact.out
  cases h : i.val with
  | zero =>
    rw [evenBasis_zero, reducePoly_one]
    simp [gateEvenPoly, gateEvenPolySq, gateBasisCoeff, gateMonicBasis, h]
  | succ m =>
    rw [evenBasis_succ]
    have hlt : 2 * (m + 1) < gatePrime n := by
      have hi : i.val < 15 * n := i.isLt
      unfold gatePrime
      omega
    have hfac : padicValRat (gatePrime n) (((2 * (m + 1)).factorial : ℚ)) = 0 :=
      six_factorial_padicValRat_zero _ _ hp hlt
    have hfac_ne : (((2 * (m + 1)).factorial : ℕ) : ZMod (gatePrime n)) ≠ 0 := by
      intro hz
      have hd := (ZMod.natCast_eq_zero_iff _ (gatePrime n)).mp hz
      exact (Nat.not_le_of_lt hlt) (hp.dvd_factorial.mp hd)
    have hsc : (2 : ℚ) / ((2 * (m + 1)).factorial : ℚ) ∈ sixGateIntegralRing (gatePrime n) := by
      rw [div_eq_mul_inv]
      exact (sixGateIntegralRing _).mul_mem (natCast_mem _ 2)
        (sixGateIntegralRing_inv_of_unit _ _ (by exact_mod_cast Nat.factorial_ne_zero _) hfac)
    have hprod_mem : PolyInSubring (sixGateIntegralRing (gatePrime n)) (evenBasisProduct m) := by
      apply polyInSubring_prod
      intro j _
      exact polyInSubring_sub (polyInSubring_pow polyInSubring_X 2)
        (polyInSubring_C ((sixGateIntegralRing _).pow_mem
          ((sixGateIntegralRing _).add_mem (natCast_mem _ j) (sixGateIntegralRing _).one_mem) 2))
    rw [reducePoly_mul _ (polyInSubring_C hsc)
        (polyInSubring_mul (polyInSubring_pow polyInSubring_X 2) hprod_mem),
      reducePoly_C,
      reducePoly_mul _ (polyInSubring_pow polyInSubring_X 2) hprod_mem,
      reducePoly_pow _ polyInSubring_X 2, reducePoly_X]
    have hcast_sc : (((2 : ℚ) / ((2 * (m + 1)).factorial : ℚ) : ℚ) : ZMod (gatePrime n)) =
        gateBasisCoeff n i := by
      unfold gateBasisCoeff
      rw [h]
      simp only [Nat.succ_ne_zero, ite_false]
      rw [Rat.cast_div_of_ne_zero (by norm_num) (by simpa using hfac_ne)]
      norm_num
    have hcast_prod : reducePoly (gatePrime n) (evenBasisProduct m) =
        ∏ j ∈ range m, (X ^ 2 - C ((((j : ZMod (gatePrime n)) + 1) ^ 2))) := by
      unfold evenBasisProduct
      rw [reducePoly_prod]
      · apply Finset.prod_congr rfl
        intro j _
        have hsub_eq : (X ^ 2 - C (((j : ℚ) + 1) ^ 2) : ℚ[X]) =
            X ^ 2 + C (-(((j : ℚ) + 1) ^ 2)) := by simp [sub_eq_add_neg]
        rw [hsub_eq, reducePoly_add _ (polyInSubring_pow polyInSubring_X 2)
            (polyInSubring_C ((sixGateIntegralRing _).neg_mem
              ((sixGateIntegralRing _).pow_mem
                ((sixGateIntegralRing _).add_mem (natCast_mem _ j) (sixGateIntegralRing _).one_mem) 2))),
          reducePoly_pow _ polyInSubring_X 2, reducePoly_X, reducePoly_C]
        have hjc : ((-(((j : ℚ) + 1) ^ 2) : ℚ) : ZMod (gatePrime n)) =
            -(((j : ZMod (gatePrime n)) + 1) ^ 2) := by
          have : (-(((j : ℚ) + 1) ^ 2) : ℚ) = (((-((j : ℤ) + 1) ^ 2 : ℤ) : ℚ)) := by push_cast; ring
          rw [this, Rat.cast_intCast]
          push_cast
          ring
        rw [hjc, map_neg, ← sub_eq_add_neg]
      · intro j _
        exact polyInSubring_sub (polyInSubring_pow polyInSubring_X 2)
          (polyInSubring_C ((sixGateIntegralRing _).pow_mem
            ((sixGateIntegralRing _).add_mem (natCast_mem _ j) (sixGateIntegralRing _).one_mem) 2))
    rw [hcast_sc, hcast_prod]
    simp only [gateEvenPoly, gateEvenPolySq, gateMonicBasis, h, mul_comp, C_comp, X_comp,
      Polynomial.prod_comp, sub_comp]

theorem sixGate_taylor_evenBasis_coeff_cast (n : ℕ) [Fact (gatePrime n).Prime]
    (i : Fin (rank n)) (t : Fin (5 * n)) (a : ℕ) :
    (((taylor (gateNode n t : ℚ) (evenBasis i.val)).coeff a : ℚ) : ZMod (gatePrime n)) =
      (taylor ((gateNode n t : ℤ) : ZMod (gatePrime n)) (gateEvenPoly n i)).coeff a := by
  rw [← reducePoly_coeff,
    reducePoly_taylor (gatePrime n) (sixGate_evenBasis_in_subring n i) (intCast_mem _ _),
    reducePoly_evenBasis n i, Rat.cast_intCast]

/-! ## Local principal polynomials, cofactors, and `p`-integrality at every pole -/

def sixLocalPrincipal (n : ℕ) (i j : Fin (rank n)) (k : ℕ) : ℚ[X] :=
  ∑ l : Fin (sixPoleOrder n k),
    monomial (sixPoleOrder n k - (l.val + 1)) (sixPrincipalCoefficients n i j k l)

def sixLocalCofactor (n k : ℕ) : ℚ[X] :=
  taylor (-(k : ℚ)) (∏ a ∈ (sixPoleSet n).erase k,
    (X + C (a : ℚ)) ^ sixPoleOrder n a)

def sixLocalNumerator (n : ℕ) (i j : Fin (rank n)) (k : ℕ) : ℚ[X] :=
  taylor (-(k : ℚ))
    (C (sixNormalization n) * sixNumerator n * centeredMultiplier n i.val j.val)

theorem taylor_at_negative_linear (k : ℕ) :
    taylor (-(k : ℚ)) (X + C (k : ℚ)) = X := by
  simp only [map_add, taylor_X, taylor_C, add_assoc, ← C_add, neg_add_cancel,
    C_0, add_zero]

private theorem shifted_other_complement_dvd (n k a l : ℕ)
    (hk : k ∈ sixPoleSet n) (hak : a ≠ k) :
    X ^ sixPoleOrder n k ∣ taylor (-(k : ℚ)) (sixPoleComplement n a l) := by
  have hmem : k ∈ (sixPoleSet n).erase a := mem_erase.mpr ⟨Ne.symm hak, hk⟩
  have hprod := Finset.dvd_prod_of_mem
    (fun b : ℕ => (X + C (b : ℚ)) ^ sixPoleOrder n b) hmem
  have hdiv : (X + C (k : ℚ)) ^ sixPoleOrder n k ∣ sixPoleComplement n a l :=
    dvd_mul_of_dvd_right hprod _
  have h := (taylorAlgHom (-(k : ℚ))).toRingHom.map_dvd hdiv
  change taylor (-(k : ℚ)) ((X + C (k : ℚ)) ^ sixPoleOrder n k) ∣
    taylor (-(k : ℚ)) (sixPoleComplement n a l) at h
  simpa only [taylor_pow, taylor_at_negative_linear] using h

private theorem shifted_own_block (n : ℕ) (i j : Fin (rank n)) (k : ℕ) :
    (∑ l : Fin (sixPoleOrder n k), taylor (-(k : ℚ))
      (C (sixPrincipalCoefficients n i j k l) * sixPoleComplement n k l.val)) =
      sixLocalPrincipal n i j k * sixLocalCofactor n k := by
  simp only [sixLocalPrincipal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  simp only [sixPoleComplement, taylor_mul, taylor_C, taylor_pow,
    taylor_at_negative_linear, sixLocalCofactor, ← C_mul_X_pow_eq_monomial]
  ring

theorem sixLocalPrincipal_congruence (n : ℕ) (i j : Fin (rank n)) (k : ℕ)
    (hk : k ∈ sixPoleSet n) :
    X ^ sixPoleOrder n k ∣
      sixLocalNumerator n i j k -
        sixLocalPrincipal n i j k * sixLocalCofactor n k := by
  have he := congrArg (taylor (-(k : ℚ))) (six_cleared_partial_fractions n i j)
  simp only [map_sum] at he
  rw [← Finset.sum_erase_add _ _ hk, shifted_own_block] at he
  change X ^ sixPoleOrder n k ∣
    taylor (-(k : ℚ)) (C (sixNormalization n) * sixNumerator n * centeredMultiplier n i.val j.val) - _
  rw [he, add_sub_cancel_right]
  apply Finset.dvd_sum
  intro a ha
  apply Finset.dvd_sum
  intro l _
  rw [taylor_mul, taylor_C]
  exact dvd_mul_of_dvd_right (shifted_other_complement_dvd n k a l.val hk (mem_erase.mp ha).1) _

theorem sixLocalPrincipal_coeff (n : ℕ) (i j : Fin (rank n)) (k : ℕ)
    (l : Fin (sixPoleOrder n k)) :
    (sixLocalPrincipal n i j k).coeff (sixPoleOrder n k - (l.val + 1)) =
      sixPrincipalCoefficients n i j k l := by
  unfold sixLocalPrincipal
  rw [finsetSum_coeff, Finset.sum_eq_single l]
  · simp
  · intro b _ hbl
    rw [coeff_monomial]
    have hne : sixPoleOrder n k - (b.val + 1) ≠ sixPoleOrder n k - (l.val + 1) := by
      have hb := b.isLt; have hl := l.isLt
      intro h; exact hbl (Fin.ext (by omega))
    simp [hne]
  · intro h; exact (h (mem_univ l)).elim

theorem sixGate_localCofactor_in_subring (n : ℕ) [Fact (gatePrime n).Prime] (k : ℕ) :
    PolyInSubring (sixGateIntegralRing (gatePrime n)) (sixLocalCofactor n k) := by
  unfold sixLocalCofactor
  apply polyInSubring_taylor _ ((sixGateIntegralRing _).neg_mem (natCast_mem _ k))
  apply polyInSubring_prod
  intro a _
  exact polyInSubring_pow (polyInSubring_add polyInSubring_X (polyInSubring_C (natCast_mem _ a))) _

theorem sixGate_localCofactor_zero_unit (n : ℕ) [Fact (gatePrime n).Prime]
    (k : ℕ) (hk : k ∈ sixPoleSet n) :
    (sixLocalCofactor n k).coeff 0 ≠ 0 ∧
      padicValRat (gatePrime n) ((sixLocalCofactor n k).coeff 0) = 0 := by
  have hp : (gatePrime n).Prime := Fact.out
  have hkb := six_pole_address_bounds n k hk
  have hval : (sixLocalCofactor n k).coeff 0 =
      ∏ a ∈ (sixPoleSet n).erase k, ((a : ℚ) - (k : ℚ)) ^ sixPoleOrder n a := by
    rw [sixLocalCofactor, taylor_coeff_zero, eval_prod]
    apply Finset.prod_congr rfl
    intro a _
    simp [sub_eq_add_neg, add_comm]
  rw [hval]
  have hterm (a : ℕ) (ha : a ∈ (sixPoleSet n).erase k) :
      ((a : ℚ) - (k : ℚ)) ^ sixPoleOrder n a ≠ 0 ∧
        padicValRat (gatePrime n) (((a : ℚ) - (k : ℚ)) ^ sixPoleOrder n a) = 0 := by
    have hak : a ≠ k := (mem_erase.mp ha).1
    have hab := six_pole_address_bounds n a (mem_erase.mp ha).2
    have hdiff_ne : (a : ℚ) - (k : ℚ) ≠ 0 := by
      intro h; exact hak (by exact_mod_cast sub_eq_zero.mp h)
    refine ⟨pow_ne_zero _ hdiff_ne, ?_⟩
    rw [padicValRat.pow]
    have hdiff_val : padicValRat (gatePrime n) ((a : ℚ) - (k : ℚ)) = 0 := by
      have hz : ((a : ℚ) - (k : ℚ)) = (((a : ℤ) - (k : ℤ) : ℤ) : ℚ) := by push_cast; rfl
      rw [hz, padicValRat.of_int]
      have hnd : ¬ ((gatePrime n : ℤ) ∣ (a : ℤ) - (k : ℤ)) := by
        intro hd
        have hnat : gatePrime n ∣ ((a : ℤ) - (k : ℤ)).natAbs := by
          exact_mod_cast Int.dvd_natAbs.mpr hd
        have hpos : 0 < ((a : ℤ) - (k : ℤ)).natAbs := Int.natAbs_pos.mpr (by omega)
        have hlt : ((a : ℤ) - (k : ℤ)).natAbs < gatePrime n := by
          unfold gatePrime; omega
        exact Nat.not_dvd_of_pos_of_lt hpos hlt hnat
      exact_mod_cast padicValInt.eq_zero_of_not_dvd hnd
    rw [hdiff_val, mul_zero]
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun a ha => (hterm a ha).1), ?_⟩
  rw [gate_padic_prod _ _ (fun a ha => (hterm a ha).1)]
  exact Finset.sum_eq_zero (fun a ha => (hterm a ha).2)

/-- Recursive truncated polynomial quotient: given `A, C ∈ S[X]` with `C(0)⁻¹ ∈ S`,
constructs `U ∈ S[X]` with `X^m ∣ A - C * U` and `U(0) = A(0) / C(0)`. -/
def truncatedQuotient (A C : ℚ[X]) : ℕ → ℚ[X]
  | 0 => 0
  | m + 1 =>
    let U := truncatedQuotient A C m
    U + monomial m (((A - C * U).coeff m) / (C.coeff 0))

theorem truncatedQuotient_dvd (A C : ℚ[X]) (hC0 : C.coeff 0 ≠ 0) :
    ∀ m : ℕ, X ^ m ∣ A - C * truncatedQuotient A C m := by
  intro m
  induction m with
  | zero => simp [truncatedQuotient]
  | succ m ih =>
    rw [Polynomial.X_pow_dvd_iff] at ih ⊢
    intro d hd
    dsimp only [truncatedQuotient]
    set U := truncatedQuotient A C m
    set c := (A - C * U).coeff m / C.coeff 0
    have hsplit : A - C * (U + monomial m c) = (A - C * U) - C * monomial m c := by ring
    rw [hsplit, coeff_sub, mul_comm C (monomial m c), ← C_mul_X_pow_eq_monomial,
      mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    by_cases hdm : d < m
    · rw [ih d hdm, ite_eq_right (by omega), mul_zero, sub_zero]
    · have hdeq : d = m := by omega
      subst hdeq
      rw [ite_eq_left le_rfl, Nat.sub_self, show c * C.coeff 0 = (A - C * U).coeff d by
        dsimp [c]; field_simp [hC0], sub_self]

theorem truncatedQuotient_in_subring {S : Subring ℚ} {A C : ℚ[X]}
    (hA : PolyInSubring S A) (hC : PolyInSubring S C)
    (hC0inv : (C.coeff 0)⁻¹ ∈ S) :
    ∀ m : ℕ, PolyInSubring S (truncatedQuotient A C m) := by
  intro m
  induction m with
  | zero => intro q; simp [truncatedQuotient, S.zero_mem]
  | succ m ih =>
    dsimp only [truncatedQuotient]
    apply polyInSubring_add ih
    intro q
    rw [coeff_monomial]
    split_ifs
    · rw [div_eq_mul_inv]
      exact S.mul_mem ((polyInSubring_sub hA (polyInSubring_mul hC ih)) m) hC0inv
    · exact S.zero_mem

theorem truncatedQuotient_coeff_zero (A C : ℚ[X]) {m : ℕ} (hm : 1 ≤ m) :
    (truncatedQuotient A C m).coeff 0 = A.coeff 0 / C.coeff 0 := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp [truncatedQuotient]
    | succ m =>
      dsimp only [truncatedQuotient]
      rw [coeff_add, coeff_monomial, ite_eq_right (by omega), add_zero]
      exact ih (by omega)

/-- Uniqueness of polynomial congruence mod `X^m` when `C.coeff 0 ≠ 0`. -/
theorem coeff_eq_of_X_pow_dvd_mul {C D : ℚ[X]} (hC0 : C.coeff 0 ≠ 0) {m : ℕ}
    (hdvd : X ^ m ∣ C * D) : ∀ d < m, D.coeff d = 0 := by
  rw [Polynomial.X_pow_dvd_iff] at hdvd
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hdm
    have h0 := hdvd d hdm
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => C.coeff i * D.coeff j),
      Finset.sum_range_succ'] at h0
    have hrest : (∑ k ∈ range d, C.coeff (k + 1) * D.coeff (d - (k + 1))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkd : k < d := mem_range.mp hk
      rw [ih (d - (k + 1)) (by omega) (by omega), mul_zero]
    rw [hrest, zero_add, Nat.sub_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left hC0

theorem sixGate_numerator_in_subring (n : ℕ) [Fact (gatePrime n).Prime] :
    PolyInSubring (sixGateIntegralRing (gatePrime n)) (sixNumerator n) := by
  unfold sixNumerator
  apply polyInSubring_mul
  · exact polyInSubring_add polyInSubring_X
      (polyInSubring_C ((sixGateIntegralRing _).add_mem
        ((sixGateIntegralRing _).mul_mem (natCast_mem _ 70) (natCast_mem _ n))
        (sixGateIntegralRing _).one_mem))
  · apply polyInSubring_prod
    intro a _
    apply polyInSubring_mul
    · apply polyInSubring_prod
      intro j _
      exact polyInSubring_add polyInSubring_X
        (polyInSubring_C ((sixGateIntegralRing _).add_mem (sixGateIntegralRing _).one_mem
          (natCast_mem _ j)))
    · apply polyInSubring_prod
      intro j _
      exact polyInSubring_add polyInSubring_X
        (polyInSubring_C ((sixGateIntegralRing _).add_mem
          ((sixGateIntegralRing _).sub_mem
            ((sixGateIntegralRing _).add_mem
              ((sixGateIntegralRing _).mul_mem (natCast_mem _ 140) (natCast_mem _ n))
              (natCast_mem _ 2))
            (natCast_mem _ (sixZero a * n)))
          (natCast_mem _ j)))

theorem sixGate_localNumerator_in_subring (n : ℕ) [Fact (gatePrime n).Prime]
    (i j : Fin (rank n)) (k : ℕ) :
    PolyInSubring (sixGateIntegralRing (gatePrime n)) (sixLocalNumerator n i j k) := by
  unfold sixLocalNumerator
  apply polyInSubring_taylor _ ((sixGateIntegralRing _).neg_mem (natCast_mem _ k))
  apply polyInSubring_mul
  · apply polyInSubring_mul
    · apply polyInSubring_C
      change 0 ≤ padicValRat (gatePrime n) (sixNormalization n)
      rw [(sixGate_normalization_unit n).2]
    · exact sixGate_numerator_in_subring n
  · exact sixGate_centeredMultiplier_in_subring n i j

theorem sixGate_principal_coeff_mem (n : ℕ) [Fact (gatePrime n).Prime]
    (i j : Fin (rank n)) (k : ℕ) (hk : k ∈ sixPoleSet n) (l : Fin (sixPoleOrder n k)) :
    sixPrincipalCoefficients n i j k l ∈ sixGateIntegralRing (gatePrime n) := by
  let S := sixGateIntegralRing (gatePrime n)
  let C := sixLocalCofactor n k
  let A := sixLocalNumerator n i j k
  let m := sixPoleOrder n k
  have hCu := sixGate_localCofactor_zero_unit n k hk
  have hC0inv : (C.coeff 0)⁻¹ ∈ S := sixGateIntegralRing_inv_of_unit _ _ hCu.1 hCu.2
  let U := truncatedQuotient A C m
  have hU_mem : PolyInSubring S U :=
    truncatedQuotient_in_subring (sixGate_localNumerator_in_subring n i j k)
      (sixGate_localCofactor_in_subring n k) hC0inv m
  have hdvd1 := sixLocalPrincipal_congruence n i j k hk
  have hdvd2 := truncatedQuotient_dvd A C hCu.1 m
  have hdiff : X ^ m ∣ C * (U - sixLocalPrincipal n i j k) := by
    have heq : C * (U - sixLocalPrincipal n i j k) =
        (A - sixLocalPrincipal n i j k * C) - (A - C * U) := by ring
    rw [heq]
    exact dvd_sub hdvd1 hdvd2
  have hcoeff := coeff_eq_of_X_pow_dvd_mul hCu.1 hdiff (m - (l.val + 1)) (by have := l.isLt; omega)
  rw [coeff_sub, sub_eq_zero, sixLocalPrincipal_coeff] at hcoeff
  rw [← hcoeff]
  exact hU_mem _

theorem sixGate_zeta_coeff_mem (n : ℕ) [Fact (gatePrime n).Prime]
    (i j : Fin (rank n)) (s : ℕ) :
    sixZetaCoefficient n i j s ∈ sixGateIntegralRing (gatePrime n) := by
  let S := sixGateIntegralRing (gatePrime n)
  unfold sixZetaCoefficient sixOrderCoefficient
  apply S.mul_mem (natCast_mem S _)
  apply S.sum_mem
  intro k hk
  apply S.sum_mem
  intro l _
  split_ifs
  · exact sixGate_principal_coeff_mem n i j k hk l
  · exact S.zero_mem

/-! ## Harmonic split: regular part in `ℤ_(p)` + singular sum on the `5n` tail poles -/

def harmonicRegularPart (p s m : ℕ) : ℚ :=
  ∑ t ∈ range m, if t + 1 = p then 0 else 1 / ((t : ℚ) + 1) ^ s

theorem harmonicCutoff_split_at_prime (p s m : ℕ) (hp : 0 < p) :
    harmonicCutoff s m = (if p ≤ m then 1 / (p : ℚ) ^ s else 0) +
      harmonicRegularPart p s m := by
  have hsum : (∑ t ∈ range m, if t + 1 = p then 1 / ((t : ℚ) + 1) ^ s else 0) =
      if p ≤ m then 1 / (p : ℚ) ^ s else 0 := by
    by_cases hpm : p ≤ m
    · rw [ite_eq_left hpm, Finset.sum_eq_single (p - 1)]
      · have he : p - 1 + 1 = p := by omega
        simp only [he, ite_true]
        rw [← Nat.cast_one, ← Nat.cast_add, he]
      · intro b _ hne; simp [show b + 1 ≠ p by omega]
      · intro hnot; exact (hnot (mem_range.mpr (by omega))).elim
    · rw [ite_eq_right hpm]
      apply Finset.sum_eq_zero
      intro b hb
      have hb := mem_range.mp hb
      simp [show b + 1 ≠ p by omega]
  rw [← hsum, harmonicRegularPart, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp

theorem harmonicRegularPart_mem (p s m : ℕ) [Fact p.Prime] (hm : m < 2 * p) :
    harmonicRegularPart p s m ∈ sixGateIntegralRing p := by
  have hp : p.Prime := Fact.out
  let S := sixGateIntegralRing p
  unfold harmonicRegularPart
  apply S.sum_mem
  intro t ht
  split_ifs with htp
  · exact S.zero_mem
  · have ht := mem_range.mp ht
    have hnd : ¬ p ∣ t + 1 := by
      rintro ⟨a, ha⟩
      have ha1 : 1 ≤ a := by nlinarith [hp.pos]
      have ha2 : a < 2 := by nlinarith [hp.pos]
      have : a = 1 := by omega
      subst this
      omega
    have hval : padicValRat p (((t : ℚ) + 1) ^ s) = 0 := by
      have hcast : ((t : ℚ) + 1) ^ s = (((t + 1) ^ s : ℕ) : ℚ) := by push_cast; rfl
      rw [hcast, padicValRat.of_nat]
      have hnd' : ¬ p ∣ (t + 1) ^ s := fun hd => hnd (hp.dvd_of_dvd_pow hd)
      exact_mod_cast padicValNat.eq_zero_of_not_dvd hnd'
    rw [one_div]
    exact sixGateIntegralRing_inv_of_unit p _ (by positivity) hval

theorem sixGateTailPole_mem (n : ℕ) (t : Fin (5 * n)) :
    gateTailPole n t ∈ sixPoleSet n := by
  simp only [sixPoleSet, List.mem_toFinset, sixPoleList, List.mem_flatMap,
    List.mem_finRange, true_and, List.mem_map, List.mem_range]
  refine ⟨0, 45 * n + 1 + t.val, ?_, ?_⟩
  · have ht := t.isLt
    change 45 * n + 1 + t.val < (50 - 2 * 0) * n + 1
    omega
  · unfold gateTailPole
    change (45 + 0) * n + 1 + (45 * n + 1 + t.val) = 90 * n + 2 + t.val
    omega

/-- The singular harmonic sum supported solely on the `5n` tail poles `k_t = 90n + 2 + t`. -/
def sixSingularEntry (n : ℕ) (i j : Fin (rank n)) : ℚ :=
  -(∑ t : Fin (5 * n), ∑ l : Fin (sixPoleOrder n (gateTailPole n t)),
    sixPrincipalCoefficients n i j (gateTailPole n t) l * ((l.val + 4).choose 4 : ℚ) *
      (1 / (gatePrime n : ℚ) ^ (l.val + 5)))

/-- For any `p`-integral rational specialization `q : Fin 6 → ℚ`, the difference
between `eval q (sixMatrix n i j)` and `sixSingularEntry n i j` is `p`-integral. -/
theorem sixMatrix_eval_sub_singular_mem (n : ℕ) [Fact (gatePrime n).Prime]
    (q : Fin 6 → ℚ) (hq : ∀ s : Fin 6, q s ∈ sixGateIntegralRing (gatePrime n))
    (i j : Fin (rank n)) :
    MvPolynomial.eval q (sixMatrix n i j) - sixSingularEntry n i j ∈
      sixGateIntegralRing (gatePrime n) := by
  have hp : (gatePrime n).Prime := Fact.out
  let S := sixGateIntegralRing (gatePrime n)
  have heval : MvPolynomial.eval q (sixMatrix n i j) =
      sixMomentConstant n i j +
        ∑ s : Fin 6, sixZetaCoefficient n i j (2 + 2 * s.val) * q s := by
    simp [sixMatrix, affineEntry]
  rw [heval]
  have hzeta : (∑ s : Fin 6, sixZetaCoefficient n i j (2 + 2 * s.val) * q s) ∈ S :=
    S.sum_mem fun s _ => S.mul_mem (sixGate_zeta_coeff_mem n i j _) (hq s)
  have hconst_diff : sixMomentConstant n i j - sixSingularEntry n i j ∈ S := by
    unfold sixMomentConstant sixSingularEntry
    have hsplit : (∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
        sixPrincipalCoefficients n i j k l * ((l.val + 4).choose 4 : ℚ) *
          harmonicCutoff (l.val + 5) (k - 40 * n - 1)) =
      (∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
        sixPrincipalCoefficients n i j k l * ((l.val + 4).choose 4 : ℚ) *
          (if gatePrime n ≤ k - 40 * n - 1 then 1 / (gatePrime n : ℚ) ^ (l.val + 5) else 0)) +
      (∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
        sixPrincipalCoefficients n i j k l * ((l.val + 4).choose 4 : ℚ) *
          harmonicRegularPart (gatePrime n) (l.val + 5) (k - 40 * n - 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l _
      rw [harmonicCutoff_split_at_prime (gatePrime n) (l.val + 5) (k - 40 * n - 1) hp.pos]
      ring
    have hsing_eq : (∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
        sixPrincipalCoefficients n i j k l * ((l.val + 4).choose 4 : ℚ) *
          (if gatePrime n ≤ k - 40 * n - 1 then 1 / (gatePrime n : ℚ) ^ (l.val + 5) else 0)) =
      ∑ t : Fin (5 * n), ∑ l : Fin (sixPoleOrder n (gateTailPole n t)),
        sixPrincipalCoefficients n i j (gateTailPole n t) l * ((l.val + 4).choose 4 : ℚ) *
          (1 / (gatePrime n : ℚ) ^ (l.val + 5)) := by
      have hfilt : (∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
          sixPrincipalCoefficients n i j k l * ((l.val + 4).choose 4 : ℚ) *
            (if gatePrime n ≤ k - 40 * n - 1 then 1 / (gatePrime n : ℚ) ^ (l.val + 5) else 0)) =
        ∑ k ∈ (sixPoleSet n).filter (fun k => gatePrime n ≤ k - 40 * n - 1),
          ∑ l : Fin (sixPoleOrder n k),
            sixPrincipalCoefficients n i j k l * ((l.val + 4).choose 4 : ℚ) *
              (1 / (gatePrime n : ℚ) ^ (l.val + 5)) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hcond : gatePrime n ≤ k - 40 * n - 1
        · simp [hcond]
        · simp [hcond]
      rw [hfilt]
      symm
      apply Finset.sum_bij (fun (t : Fin (5 * n)) _ => gateTailPole n t)
      · intro t _
        rw [Finset.mem_filter]
        refine ⟨sixGateTailPole_mem n t, ?_⟩
        unfold gateTailPole gatePrime
        omega
      · intro t₁ _ t₂ _ heq
        apply Fin.ext
        unfold gateTailPole at heq
        omega
      · intro k hk
        rw [Finset.mem_filter] at hk
        have hb := six_pole_address_bounds n k hk.1
        have hge : 90 * n + 2 ≤ k := by
          have h2 := hk.2
          unfold gatePrime at h2
          omega
        refine ⟨⟨k - (90 * n + 2), by omega⟩, Finset.mem_univ _, ?_⟩
        unfold gateTailPole
        dsimp
        omega
      · intro t _
        rfl
    rw [hsplit, hsing_eq]
    have hcancel : -(
        (∑ t : Fin (5 * n), ∑ l : Fin (sixPoleOrder n (gateTailPole n t)),
          sixPrincipalCoefficients n i j (gateTailPole n t) l * ((l.val + 4).choose 4 : ℚ) *
            (1 / (gatePrime n : ℚ) ^ (l.val + 5))) +
        (∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
          sixPrincipalCoefficients n i j k l * ((l.val + 4).choose 4 : ℚ) *
            harmonicRegularPart (gatePrime n) (l.val + 5) (k - 40 * n - 1))) -
      -(∑ t : Fin (5 * n), ∑ l : Fin (sixPoleOrder n (gateTailPole n t)),
          sixPrincipalCoefficients n i j (gateTailPole n t) l * ((l.val + 4).choose 4 : ℚ) *
            (1 / (gatePrime n : ℚ) ^ (l.val + 5))) =
      -(∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
        sixPrincipalCoefficients n i j k l * ((l.val + 4).choose 4 : ℚ) *
          harmonicRegularPart (gatePrime n) (l.val + 5) (k - 40 * n - 1)) := by ring
    rw [hcancel]
    apply S.neg_mem
    apply S.sum_mem
    intro k hk
    apply S.sum_mem
    intro l _
    apply S.mul_mem
    · exact S.mul_mem (sixGate_principal_coeff_mem n i j k hk l) (natCast_mem S _)
    · apply harmonicRegularPart_mem
      have hb := six_pole_address_bounds n k hk
      unfold gatePrime
      omega
  have hadd : sixMomentConstant n i j +
      (∑ s : Fin 6, sixZetaCoefficient n i j (2 + 2 * s.val) * q s) -
      sixSingularEntry n i j =
      (sixMomentConstant n i j - sixSingularEntry n i j) +
      (∑ s : Fin 6, sixZetaCoefficient n i j (2 + 2 * s.val) * q s) := by ring
  rw [hadd]
  exact S.add_mem hconst_diff hzeta

/-! ## Tail pole order / zero-count matching (`m - q = 5`) and numerator stripping -/

/-- Exact left-root multiplicity `q ∈ {0, 1, 2}` at tail pole `k_t = 90n + 2 + t`. -/
def sixGateTailZeroCount (n : ℕ) (t : Fin (5 * n)) : Fin 3 :=
  if t.val < n then 2 else if t.val < 3 * n then 1 else 0

private theorem tail_interval_count (a d k : ℕ) :
    ((List.range (d + 1)).map (fun j => a + j)).count k =
      if a ≤ k ∧ k ≤ a + d then 1 else 0 := by
  have hmem : k ∈ (List.range (d + 1)).map (fun j => a + j) ↔ a ≤ k ∧ k ≤ a + d := by
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · rintro ⟨hk, hd⟩; exact ⟨k - a, by omega, by omega⟩
  split_ifs with h
  · exact List.count_eq_one_of_mem
      ((List.nodup_map_iff (fun _ _ h => Nat.add_left_cancel h)).mpr List.nodup_range)
      (hmem.mpr h)
  · exact List.count_eq_zero_of_not_mem (fun hk => h (hmem.mp hk))

/-- Every tail pole satisfies `m(k_t) = q(k_t) + 5` (`B - 4 = 5`). -/
theorem sixGateTailOrder_eq (n : ℕ) (t : Fin (5 * n)) :
    sixPoleOrder n (gateTailPole n t) = (sixGateTailZeroCount n t).val + 5 := by
  have ht := t.isLt
  have hn : 0 < n := by omega
  unfold sixPoleOrder sixPoleList
  rw [list_count_flatMap]
  have hsum : ((List.finRange 14).map fun b =>
      ((List.range ((50 - 2 * sixOffset b) * n + 1)).map
        fun j => (45 + sixOffset b) * n + 1 + j).count (gateTailPole n t)).sum =
      ∑ b : Fin 14, if t.val < (5 - sixOffset b) * n then 1 else 0 := by
    rw [← Fin.sum_univ_def]
    apply Finset.sum_congr rfl
    intro b _
    rw [tail_interval_count]
    fin_cases b <;>
      (dsimp [sixOffset, gateTailPole]
       exact if_congr ⟨fun h => by omega, fun h => by omega⟩ rfl rfl)
  rw [hsum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, sixOffset, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero, sixGateTailZeroCount]
  norm_num only
  by_cases h1 : t.val < n
  · have h3 : t.val < 3 * n := by omega
    have h0 : ¬ t.val < 0 := by omega
    simp [h1, h3, ht, h0]
  · by_cases h2 : t.val < 3 * n
    · have h0 : ¬ t.val < 0 := by omega
      simp [h1, h2, ht, h0]
    · have h0 : ¬ t.val < 0 := by omega
      simp [h1, h2, ht, h0]

/-- Stripping the single `(X - C p)` factor from `taylor (-k) (rising 1 m)` when `k - p ∈ [1, m]`. -/
def risingStrippedAt (m k p : ℕ) : ℚ[X] :=
  ∏ j ∈ (range m).erase (k - p - 1), (X + C ((1 : ℚ) + j - k))

private theorem taylor_prod {ι : Type*} [DecidableEq ι] (r : ℚ) (s : Finset ι) (f : ι → ℚ[X]) :
    taylor r (∏ i ∈ s, f i) = ∏ i ∈ s, taylor r (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [← C_1, taylor_C, C_1]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, taylor_mul, ih]

theorem taylor_rising_one (m k : ℕ) :
    taylor (-(k : ℚ)) (rising 1 m) = ∏ j ∈ range m, (X + C ((1 : ℚ) + j - k)) := by
  unfold rising
  rw [taylor_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [map_add, taylor_X, taylor_C, add_assoc, ← C_add]
  congr 2
  ring

theorem taylor_rising_one_strip (m k p : ℕ) (h1 : p + 1 ≤ k) (h2 : k - p ≤ m) :
    taylor (-(k : ℚ)) (rising 1 m) = (X - C (p : ℚ)) * risingStrippedAt m k p := by
  rw [taylor_rising_one, risingStrippedAt]
  have hmem : k - p - 1 ∈ range m := by simp only [mem_range]; omega
  rw [← Finset.mul_prod_erase (range m) _ hmem]
  congr 1
  have hcast : (1 : ℚ) + ((k - p - 1 : ℕ) : ℚ) - (k : ℚ) = -(p : ℚ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k - p), Nat.cast_sub (by omega : p ≤ k), Nat.cast_one]
    ring
  rw [hcast, map_neg, ← sub_eq_add_neg]

theorem risingStrippedAt_in_subring (p : ℕ) [Fact p.Prime] (m k : ℕ) :
    PolyInSubring (sixGateIntegralRing p) (risingStrippedAt m k p) := by
  unfold risingStrippedAt
  apply polyInSubring_prod
  intro j _
  exact polyInSubring_add polyInSubring_X
    (polyInSubring_C ((sixGateIntegralRing p).sub_mem
      ((sixGateIntegralRing p).add_mem (sixGateIntegralRing p).one_mem (natCast_mem _ j))
      (natCast_mem _ k)))

/-- Stripped local numerator factor `Ñ_t(w)` satisfying
`taylor (-k_t) (C (sixNormalization n) * sixNumerator n) = (X - C p)^q * Ñ_t(w)`. -/
def sixGateStrippedNum (n : ℕ) (t : Fin (5 * n)) : ℚ[X] :=
  let k := gateTailPole n t
  let p := gatePrime n
  C (sixNormalization n) *
    (X + C ((70 * (n : ℚ) + 1) - (k : ℚ))) *
    (∏ a : Fin 5,
      (if k - p ≤ sixZero a * n then risingStrippedAt (sixZero a * n) k p
       else taylor (-(k : ℚ)) (rising 1 (sixZero a * n))) *
      taylor (-(k : ℚ)) (rising (140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ)) (sixZero a * n)))

theorem sixGate_taylor_numerator_strip (n : ℕ) (t : Fin (5 * n)) :
    taylor (-(gateTailPole n t : ℚ)) (C (sixNormalization n) * sixNumerator n) =
      (X - C (gatePrime n : ℚ)) ^ (sixGateTailZeroCount n t).val * sixGateStrippedNum n t := by
  have ht := t.isLt
  have hn : 0 < n := by omega
  let k := gateTailPole n t
  let p := gatePrime n
  have hkp1 : p + 1 ≤ k := by dsimp [k, p, gateTailPole, gatePrime]; omega
  unfold sixNumerator sixGateStrippedNum
  rw [taylor_mul, taylor_mul, taylor_C, taylor_prod]
  have hcenter : taylor (-(k : ℚ)) (X + C (70 * (n : ℚ) + 1)) =
      X + C ((70 * (n : ℚ) + 1) - (k : ℚ)) := by
    rw [map_add, taylor_X, taylor_C, add_assoc, ← C_add]
    congr 2; ring
  rw [hcenter]
  have hprod_mul : (∏ a : Fin 5, taylor (-(k : ℚ))
      (rising 1 (sixZero a * n) *
        rising (140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ)) (sixZero a * n))) =
      ∏ a : Fin 5,
        taylor (-(k : ℚ)) (rising 1 (sixZero a * n)) *
          taylor (-(k : ℚ)) (rising (140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ)) (sixZero a * n)) := by
    apply Finset.prod_congr rfl
    intro a _
    exact taylor_mul _ _ _
  rw [hprod_mul]
  have hprod : (∏ a : Fin 5,
      taylor (-(k : ℚ)) (rising 1 (sixZero a * n)) *
        taylor (-(k : ℚ)) (rising (140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ)) (sixZero a * n))) =
      (X - C (p : ℚ)) ^ (sixGateTailZeroCount n t).val *
        ∏ a : Fin 5,
          (if k - p ≤ sixZero a * n then risingStrippedAt (sixZero a * n) k p
           else taylor (-(k : ℚ)) (rising 1 (sixZero a * n))) *
          taylor (-(k : ℚ)) (rising (140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ)) (sixZero a * n)) := by
    have hsplit : (∏ a : Fin 5,
        taylor (-(k : ℚ)) (rising 1 (sixZero a * n)) *
          taylor (-(k : ℚ)) (rising (140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ)) (sixZero a * n))) =
        (∏ a : Fin 5, if k - p ≤ sixZero a * n then (X - C (p : ℚ)) else 1) *
        (∏ a : Fin 5,
          (if k - p ≤ sixZero a * n then risingStrippedAt (sixZero a * n) k p
           else taylor (-(k : ℚ)) (rising 1 (sixZero a * n))) *
          taylor (-(k : ℚ)) (rising (140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ)) (sixZero a * n))) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro a _
      by_cases hcond : k - p ≤ sixZero a * n
      · simp only [hcond, ite_true]
        rw [← mul_assoc, ← taylor_rising_one_strip (sixZero a * n) k p hkp1 hcond]
      · simp only [hcond, ite_false, one_mul]
    rw [hsplit]
    congr 1
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, sixZero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, mul_one, sixGateTailZeroCount]
    dsimp [k, p, gateTailPole, gatePrime]
    by_cases h1 : t.val < n
    · simp only [h1, ite_true]
      have hc0 : ¬ (90 * n + 2 + t.val - (50 * n + 1) ≤ 40 * n) := by omega
      have hc1 : 90 * n + 2 + t.val - (50 * n + 1) ≤ 41 * n := by omega
      have hc2 : 90 * n + 2 + t.val - (50 * n + 1) ≤ 43 * n := by omega
      simp [hc0, hc1, hc2, pow_two]
    · by_cases h2 : t.val < 3 * n
      · simp only [h1, h2, ite_false, ite_true]
        have hc0 : ¬ (90 * n + 2 + t.val - (50 * n + 1) ≤ 40 * n) := by omega
        have hc1 : ¬ (90 * n + 2 + t.val - (50 * n + 1) ≤ 41 * n) := by omega
        have hc2 : 90 * n + 2 + t.val - (50 * n + 1) ≤ 43 * n := by omega
        simp [hc0, hc1, hc2]
      · simp only [h1, h2, ite_false]
        have hc0 : ¬ (90 * n + 2 + t.val - (50 * n + 1) ≤ 40 * n) := by omega
        have hc1 : ¬ (90 * n + 2 + t.val - (50 * n + 1) ≤ 41 * n) := by omega
        have hc2 : ¬ (90 * n + 2 + t.val - (50 * n + 1) ≤ 43 * n) := by omega
        simp [hc0, hc1, hc2]
  rw [hprod]
  ring

theorem sixGateStrippedNum_in_subring (n : ℕ) [Fact (gatePrime n).Prime] (t : Fin (5 * n)) :
    PolyInSubring (sixGateIntegralRing (gatePrime n)) (sixGateStrippedNum n t) := by
  let S := sixGateIntegralRing (gatePrime n)
  unfold sixGateStrippedNum
  apply polyInSubring_mul
  · apply polyInSubring_mul
    · apply polyInSubring_C
      change 0 ≤ padicValRat (gatePrime n) (sixNormalization n)
      rw [(sixGate_normalization_unit n).2]
    · exact polyInSubring_add polyInSubring_X
        (polyInSubring_C (S.sub_mem
          (S.add_mem (S.mul_mem (natCast_mem S 70) (natCast_mem S n)) S.one_mem)
          (natCast_mem S _)))
  · apply polyInSubring_prod
    intro a _
    apply polyInSubring_mul
    · split_ifs
      · exact risingStrippedAt_in_subring _ _ _
      · apply polyInSubring_taylor _ (S.neg_mem (natCast_mem S _))
        apply polyInSubring_prod
        intro j _
        exact polyInSubring_add polyInSubring_X
          (polyInSubring_C (S.add_mem S.one_mem (natCast_mem S j)))
    · apply polyInSubring_taylor _ (S.neg_mem (natCast_mem S _))
      apply polyInSubring_prod
      intro j _
      exact polyInSubring_add polyInSubring_X
        (polyInSubring_C (S.add_mem
          (S.sub_mem (S.add_mem (S.mul_mem (natCast_mem S 140) (natCast_mem S n))
            (natCast_mem S 2)) (natCast_mem S (sixZero a * n)))
          (natCast_mem S j)))

private theorem int_unit_of_not_dvd (p : ℕ) [Fact p.Prime] (z : ℤ) (hnd : ¬ (p : ℤ) ∣ z) :
    (z : ℚ) ≠ 0 ∧ padicValRat p (z : ℚ) = 0 := by
  refine ⟨fun hz => ?_, ?_⟩
  · have h0 : z = 0 := by exact_mod_cast hz
    exact hnd (by rw [h0]; exact dvd_zero _)
  · rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd hnd

private theorem gate_unit_mul (p : ℕ) [Fact p.Prime] {x y : ℚ}
    (hx : x ≠ 0 ∧ padicValRat p x = 0) (hy : y ≠ 0 ∧ padicValRat p y = 0) :
    x * y ≠ 0 ∧ padicValRat p (x * y) = 0 := by
  refine ⟨mul_ne_zero hx.1 hy.1, ?_⟩
  rw [padicValRat.mul hx.1 hy.1, hx.2, hy.2, add_zero]

private theorem gate_unit_prod {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, f i ≠ 0 ∧ padicValRat p (f i) = 0) :
    (∏ i ∈ s, f i) ≠ 0 ∧ padicValRat p (∏ i ∈ s, f i) = 0 := by
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun i hi => (hf i hi).1), ?_⟩
  rw [gate_padic_prod s f (fun i hi => (hf i hi).1)]
  exact Finset.sum_eq_zero (fun i hi => (hf i hi).2)

private theorem coeff_zero_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    (∏ i ∈ s, f i).coeff 0 = ∏ i ∈ s, (f i).coeff 0 := by
  simp only [Polynomial.coeff_zero_eq_eval_zero, eval_prod]

theorem sixGateStrippedNum_zero_unit (n : ℕ) [Fact (gatePrime n).Prime] (t : Fin (5 * n)) :
    (sixGateStrippedNum n t).coeff 0 ≠ 0 ∧
      padicValRat (gatePrime n) ((sixGateStrippedNum n t).coeff 0) = 0 := by
  have hp : (gatePrime n).Prime := Fact.out
  have ht := t.isLt
  have hn := gatePrime_pos_index n hp
  let k := gateTailPole n t
  let p := gatePrime n
  have hcoeff0 : (sixGateStrippedNum n t).coeff 0 =
      sixNormalization n * ((70 * (n : ℚ) + 1) - (k : ℚ)) *
      ∏ a : Fin 5,
        ((if k - p ≤ sixZero a * n then (risingStrippedAt (sixZero a * n) k p).coeff 0
          else (taylor (-(k : ℚ)) (rising 1 (sixZero a * n))).coeff 0) *
         (taylor (-(k : ℚ)) (rising (140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ))
            (sixZero a * n))).coeff 0) := by
    unfold sixGateStrippedNum
    rw [mul_coeff_zero, mul_coeff_zero, coeff_C_zero, coeff_add, coeff_X_zero, coeff_C_zero,
      zero_add, coeff_zero_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro a _
    rw [mul_coeff_zero]
    split_ifs <;> rfl
  rw [hcoeff0]
  apply gate_unit_mul p
  · apply gate_unit_mul p (sixGate_normalization_unit n)
    have hcenter_eq : (70 * (n : ℚ) + 1) - (k : ℚ) =
        ((-((20 * n + 1 + t.val : ℕ) : ℤ) : ℤ) : ℚ) := by
      dsimp [k, gateTailPole]; push_cast; ring
    rw [hcenter_eq]
    apply int_unit_of_not_dvd p
    intro hd
    have hnat : p ∣ 20 * n + 1 + t.val := by
      have h1 := Int.dvd_natAbs.mpr hd
      rw [Int.natAbs_neg, Int.natAbs_natCast] at h1
      exact Int.natCast_dvd_natCast.mp h1
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by dsimp [p, gatePrime]; omega) hnat
  · apply gate_unit_prod p
    intro a _
    have hza : sixZero a ≤ 43 := by fin_cases a <;> decide
    have hza_mul : sixZero a * n ≤ 43 * n := Nat.mul_le_mul_right n hza
    apply gate_unit_mul p
    · split_ifs with hcond
      · rw [Polynomial.coeff_zero_eq_eval_zero, risingStrippedAt, eval_prod]
        apply gate_unit_prod p
        intro j hj
        simp only [eval_add, eval_X, eval_C, zero_add]
        have hjlt : j < sixZero a * n := mem_range.mp (mem_erase.mp hj).2
        have hjne : j ≠ k - p - 1 := (mem_erase.mp hj).1
        have heq : (1 : ℚ) + (j : ℚ) - (k : ℚ) = (((1 + (j : ℤ) - (k : ℤ)) : ℤ) : ℚ) := by
          push_cast; ring
        rw [heq]
        apply int_unit_of_not_dvd p
        intro hd
        have hnat : p ∣ k - (1 + j) := by
          have := Int.dvd_natAbs.mpr hd
          have hpos : 1 + j < k := by dsimp [k, gateTailPole]; omega
          have habs : (1 + (j : ℤ) - (k : ℤ)).natAbs = k - (1 + j) := by omega
          rw [habs] at this
          exact Int.natCast_dvd_natCast.mp this
        obtain ⟨c, hc⟩ := hnat
        have h1 : 1 ≤ c := by
          have : 0 < k - (1 + j) := by dsimp [k, gateTailPole]; omega
          nlinarith [hp.pos]
        have h2 : c < 2 := by
          have : k - (1 + j) < 2 * p := by dsimp [k, p, gateTailPole, gatePrime]; omega
          nlinarith [hp.pos]
        have hc1 : c = 1 := by omega
        subst hc1
        dsimp [k, p, gateTailPole, gatePrime] at hc hjne
        omega
      · rw [taylor_rising_one, Polynomial.coeff_zero_eq_eval_zero, eval_prod]
        apply gate_unit_prod p
        intro j hj
        simp only [eval_add, eval_X, eval_C, zero_add]
        have hjlt : j < sixZero a * n := mem_range.mp hj
        have heq : (1 : ℚ) + (j : ℚ) - (k : ℚ) = (((1 + (j : ℤ) - (k : ℤ)) : ℤ) : ℚ) := by
          push_cast; ring
        rw [heq]
        apply int_unit_of_not_dvd p
        intro hd
        have hnat : p ∣ k - (1 + j) := by
          have := Int.dvd_natAbs.mpr hd
          have hpos : 1 + j < k := by dsimp [k, gateTailPole]; omega
          have habs : (1 + (j : ℤ) - (k : ℤ)).natAbs = k - (1 + j) := by omega
          rw [habs] at this
          exact Int.natCast_dvd_natCast.mp this
        obtain ⟨c, hc⟩ := hnat
        have h1 : 1 ≤ c := by
          have : 0 < k - (1 + j) := by dsimp [k, gateTailPole]; omega
          nlinarith [hp.pos]
        have h2 : c < 2 := by
          have : k - (1 + j) < 2 * p := by dsimp [k, p, gateTailPole, gatePrime]; omega
          nlinarith [hp.pos]
        have hc1 : c = 1 := by omega
        subst hc1
        omega
    · rw [taylor_coeff_zero, rising, eval_prod]
      apply gate_unit_prod p
      intro j hj
      simp only [eval_add, eval_X, eval_C]
      have hjlt : j < sixZero a * n := mem_range.mp hj
      have hza_mul : sixZero a * n ≤ 43 * n := Nat.mul_le_mul_right n hza
      have heq : -(k : ℚ) + (140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ) + (j : ℚ)) =
          (((140 * n + 2 - sixZero a * n + j - k : ℕ) : ℤ) : ℚ) := by
        have hge : sixZero a * n ≤ 140 * n + 2 := by omega
        have hge2 : k ≤ 140 * n + 2 - sixZero a * n + j := by
          dsimp [k, gateTailPole]; omega
        rw [Int.cast_natCast, Nat.cast_sub hge2, Nat.cast_add, Nat.cast_sub hge]
        push_cast; ring
      rw [heq]
      apply int_unit_of_not_dvd p
      intro hd
      have hnat : p ∣ 140 * n + 2 - sixZero a * n + j - k := Int.natCast_dvd_natCast.mp hd
      have hpos : 0 < 140 * n + 2 - sixZero a * n + j - k := by
        dsimp [k, gateTailPole]; omega
      have hlt : 140 * n + 2 - sixZero a * n + j - k < p := by
        dsimp [k, p, gateTailPole, gatePrime]; omega
      exact Nat.not_dvd_of_pos_of_lt hpos hlt hnat

/-! ## Local unit quotient `U_t(w)` and exact finite binomial collapse -/

/-- Local truncated unit series `U_t(w)` satisfying
`X^m ∣ sixGateStrippedNum n t - sixLocalCofactor n k_t * U_t`. -/
def sixGateUnitSeries (n : ℕ) (t : Fin (5 * n)) : ℚ[X] :=
  truncatedQuotient (sixGateStrippedNum n t) (sixLocalCofactor n (gateTailPole n t))
    (sixPoleOrder n (gateTailPole n t))

theorem sixGateUnitSeries_in_subring (n : ℕ) [Fact (gatePrime n).Prime] (t : Fin (5 * n)) :
    PolyInSubring (sixGateIntegralRing (gatePrime n)) (sixGateUnitSeries n t) := by
  have hk := sixGateTailPole_mem n t
  have hCu := sixGate_localCofactor_zero_unit n (gateTailPole n t) hk
  exact truncatedQuotient_in_subring (sixGateStrippedNum_in_subring n t)
    (sixGate_localCofactor_in_subring n (gateTailPole n t))
    (sixGateIntegralRing_inv_of_unit _ _ hCu.1 hCu.2) _

theorem sixGateUnitSeries_zero_unit (n : ℕ) [Fact (gatePrime n).Prime] (t : Fin (5 * n)) :
    (sixGateUnitSeries n t).coeff 0 ≠ 0 ∧
      padicValRat (gatePrime n) ((sixGateUnitSeries n t).coeff 0) = 0 := by
  have hk := sixGateTailPole_mem n t
  have hm : 1 ≤ sixPoleOrder n (gateTailPole n t) := six_pole_order_positive n _ hk
  rw [sixGateUnitSeries, truncatedQuotient_coeff_zero _ _ hm]
  have hN := sixGateStrippedNum_zero_unit n t
  have hC := sixGate_localCofactor_zero_unit n (gateTailPole n t) hk
  refine ⟨div_ne_zero hN.1 hC.1, ?_⟩
  rw [padicValRat.div hN.1 hC.1, hN.2, hC.2, sub_zero]

theorem taylor_centeredMultiplier_eq (n : ℕ) (i j : Fin (rank n)) (t : Fin (5 * n)) :
    taylor (-(gateTailPole n t : ℚ)) (centeredMultiplier n i.val j.val) =
      taylor (gateNode n t : ℚ) (evenBasis i.val) *
        taylor (gateNode n t : ℚ) (evenBasis j.val) := by
  unfold centeredMultiplier
  rw [taylor_apply, taylor_apply, taylor_apply, comp_assoc, mul_comp]
  have harg : (X + C (70 * (n : ℚ) + 1)).comp (X + C (-(gateTailPole n t : ℚ))) =
      X + C (gateNode n t : ℚ) := by
    simp only [add_comp, X_comp, C_comp, add_assoc, ← C_add]
    congr 2
    unfold gateNode sixCenter
    push_cast
    ring
  rw [harg]

/-- Congruence identifying `sixLocalPrincipal n i j k_t` mod `X^m` with
`(X - C p)^q * U_t(w) * E_i(x_t + w) * E_j(x_t + w)`. -/
theorem sixLocalPrincipal_coeff_eq_stripped (n : ℕ) [Fact (gatePrime n).Prime]
    (i j : Fin (rank n)) (t : Fin (5 * n)) (d : ℕ)
    (hd : d < sixPoleOrder n (gateTailPole n t)) :
    (sixLocalPrincipal n i j (gateTailPole n t)).coeff d =
      ((X - C (gatePrime n : ℚ)) ^ (sixGateTailZeroCount n t).val *
        (sixGateUnitSeries n t *
          taylor (gateNode n t : ℚ) (evenBasis i.val) *
          taylor (gateNode n t : ℚ) (evenBasis j.val))).coeff d := by
  have hk := sixGateTailPole_mem n t
  have hCu := sixGate_localCofactor_zero_unit n (gateTailPole n t) hk
  let k := gateTailPole n t
  let m := sixPoleOrder n k
  let Cf := sixLocalCofactor n k
  let Qp := (X - C (gatePrime n : ℚ)) ^ (sixGateTailZeroCount n t).val
  let G := sixGateUnitSeries n t * taylor (gateNode n t : ℚ) (evenBasis i.val) *
      taylor (gateNode n t : ℚ) (evenBasis j.val)
  have hdvd1 := sixLocalPrincipal_congruence n i j k hk
  have hdvdU : X ^ m ∣ sixGateStrippedNum n t - Cf * sixGateUnitSeries n t :=
    truncatedQuotient_dvd _ _ hCu.1 m
  have hnum_eq : sixLocalNumerator n i j k =
      Qp * sixGateStrippedNum n t *
        (taylor (gateNode n t : ℚ) (evenBasis i.val) *
          taylor (gateNode n t : ℚ) (evenBasis j.val)) := by
    unfold sixLocalNumerator
    rw [taylor_mul, sixGate_taylor_numerator_strip n t, taylor_centeredMultiplier_eq n i j t]
  have hdvd2 : X ^ m ∣ sixLocalNumerator n i j k - Cf * (Qp * G) := by
    rw [hnum_eq]
    have hfac : Qp * sixGateStrippedNum n t *
          (taylor (gateNode n t : ℚ) (evenBasis i.val) *
            taylor (gateNode n t : ℚ) (evenBasis j.val)) - Cf * (Qp * G) =
        (sixGateStrippedNum n t - Cf * sixGateUnitSeries n t) *
          (Qp * (taylor (gateNode n t : ℚ) (evenBasis i.val) *
            taylor (gateNode n t : ℚ) (evenBasis j.val))) := by
      dsimp [G]; ring
    rw [hfac]
    exact dvd_mul_of_dvd_left hdvdU _
  have hdiff : X ^ m ∣ Cf * (sixLocalPrincipal n i j k - Qp * G) := by
    have heq : Cf * (sixLocalPrincipal n i j k - Qp * G) =
        (sixLocalNumerator n i j k - Cf * (Qp * G)) -
        (sixLocalNumerator n i j k - sixLocalPrincipal n i j k * Cf) := by ring
    rw [heq]
    exact dvd_sub hdvd2 hdvd1
  have h0 := coeff_eq_of_X_pow_dvd_mul hCu.1 hdiff d hd
  rw [coeff_sub, sub_eq_zero] at h0
  exact h0

/-- The 18-case finite binomial identity collapsing `(w - p)^q` against `choose(l+3, 4) p^{-(l+4)}`. -/
theorem sixGate_binomial_sum_eq (q : Fin 3) (s : ℕ) (hs : s < q.val + 5) :
    (∑ a ∈ range (q.val + 1),
      if a + s < q.val + 5 then
        (-1 : ℚ) ^ (q.val - a) * (q.val.choose a : ℚ) *
          ((q.val + 5 - (a + s) + 3).choose 4 : ℚ)
      else 0) =
      (-1 : ℚ) ^ q.val * ((8 - s).choose (q.val + 4 - s) : ℚ) := by
  fin_cases q
  · dsimp at hs ⊢
    interval_cases s <;> norm_num [Finset.sum_range_succ, Nat.choose]
  · dsimp at hs ⊢
    interval_cases s <;> norm_num [Finset.sum_range_succ, Nat.choose]
  · dsimp at hs ⊢
    interval_cases s <;> norm_num [Finset.sum_range_succ, Nat.choose]

private theorem coeff_X_sub_C_pow (p : ℚ) (q a : ℕ) :
    ((X - C p) ^ q).coeff a = if a ≤ q then (-p) ^ (q - a) * (q.choose a : ℚ) else 0 := by
  rw [sub_eq_add_neg, add_pow, finsetSum_coeff]
  have hterm : ∀ b : ℕ, (X ^ b * (-C p) ^ (q - b) * (q.choose b : ℚ[X])).coeff a =
      if b = a then (-p) ^ (q - b) * (q.choose b : ℚ) else 0 := by
    intro b
    have heq : X ^ b * (-C p) ^ (q - b) * (q.choose b : ℚ[X]) =
        C ((-p) ^ (q - b) * (q.choose b : ℚ)) * X ^ b := by
      simp only [map_mul, map_pow, map_neg, map_natCast]
      ring
    rw [heq, coeff_C_mul, coeff_X_pow]
    by_cases hba : b = a
    · subst hba; simp
    · have hab : a ≠ b := Ne.symm hba
      simp [hba, hab]
  simp_rw [hterm]
  by_cases ha : a ≤ q
  · simp only [ha, ite_true]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba; simp [hba]
    · intro h; exact (h (mem_range.mpr (by omega))).elim
  · simp only [ha, ite_false]
    apply Finset.sum_eq_zero
    intro b hb
    have hba : b ≠ a := by have := mem_range.mp hb; omega
    simp [hba]

/-- Exact algebraic collapse of the singular harmonic sum at tail pole `k_t` into
powers `p^(-9 + s)` weighted by `(-1)^(q+1) choose(8-s, m-1-s) [w^s](U_t E_i E_j)`. -/
theorem sixSingularEntry_eq_collapsed (n : ℕ) [Fact (gatePrime n).Prime]
    (i j : Fin (rank n)) :
    sixSingularEntry n i j =
      ∑ t : Fin (5 * n),
        ∑ s ∈ range (sixPoleOrder n (gateTailPole n t)),
          (-1 : ℚ) ^ ((sixGateTailZeroCount n t).val + 1) *
            ((8 - s).choose (sixPoleOrder n (gateTailPole n t) - 1 - s) : ℚ) *
            (sixGateUnitSeries n t *
              taylor (gateNode n t : ℚ) (evenBasis i.val) *
              taylor (gateNode n t : ℚ) (evenBasis j.val)).coeff s *
            (gatePrime n : ℚ) ^ (-(9 : ℤ) + (s : ℤ)) := by
  have hp : (gatePrime n).Prime := Fact.out
  have hpne : (gatePrime n : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold sixSingularEntry
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  let k := gateTailPole n t
  let q := sixGateTailZeroCount n t
  let m := sixPoleOrder n k
  have hm : m = q.val + 5 := sixGateTailOrder_eq n t
  let G := sixGateUnitSeries n t *
      taylor (gateNode n t : ℚ) (evenBasis i.val) *
      taylor (gateNode n t : ℚ) (evenBasis j.val)
  let p : ℚ := (gatePrime n : ℚ)
  -- Reindex l ∈ Fin m to d = m - (l + 1) ∈ range m
  have hreindex : (∑ l : Fin m,
      sixPrincipalCoefficients n i j k l * ((l.val + 4).choose 4 : ℚ) *
        (1 / p ^ (l.val + 5))) =
      ∑ d ∈ range m,
        ((X - C p) ^ q.val * G).coeff d * ((m - d + 3).choose 4 : ℚ) *
          (1 / p ^ (m - d + 4)) := by
    apply Finset.sum_bij (fun (l : Fin m) _ => m - 1 - l.val)
    · intro l _; exact mem_range.mpr (by have := l.isLt; omega)
    · intro l₁ _ l₂ _ heq
      ext; have := l₁.isLt; have := l₂.isLt; omega
    · intro d hd
      have hdm : d < m := mem_range.mp hd
      exact ⟨⟨m - 1 - d, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
    · intro l _
      have hl := l.isLt
      have hdm : m - 1 - l.val < m := by omega
      have hcoeff : sixPrincipalCoefficients n i j k l =
          ((X - C p) ^ q.val * G).coeff (m - 1 - l.val) := by
        have h1 := sixLocalPrincipal_coeff n i j k l
        have hidx : m - (l.val + 1) = m - 1 - l.val := by omega
        rw [hidx] at h1
        rw [← h1]
        exact sixLocalPrincipal_coeff_eq_stripped n i j t (m - 1 - l.val) hdm
      have h4 : l.val + 4 = m - (m - 1 - l.val) + 3 := by omega
      have h5 : l.val + 5 = m - (m - 1 - l.val) + 4 := by omega
      rw [hcoeff, h4, h5]
  rw [hreindex]
  -- Expand coeff d of ((X - C p)^q * G)
  have hexpand : (∑ d ∈ range m,
      ((X - C p) ^ q.val * G).coeff d * ((m - d + 3).choose 4 : ℚ) * (1 / p ^ (m - d + 4))) =
      ∑ d ∈ range m, ∑ a ∈ range (q.val + 1),
        if a ≤ d then
          (-p) ^ (q.val - a) * (q.val.choose a : ℚ) * G.coeff (d - a) *
            ((m - d + 3).choose 4 : ℚ) * (1 / p ^ (m - d + 4))
        else 0 := by
    apply Finset.sum_congr rfl
    intro d _
    have hcm : ((X - C p) ^ q.val * G).coeff d =
        ∑ a ∈ range (d + 1), ((X - C p) ^ q.val).coeff a * G.coeff (d - a) := by
      rw [coeff_mul]
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => ((X - C p) ^ q.val).coeff a * G.coeff b) d
    rw [hcm]
    simp_rw [coeff_X_sub_C_pow]
    have hswap : (∑ a ∈ range (d + 1),
        (if a ≤ q.val then (-p) ^ (q.val - a) * (q.val.choose a : ℚ) else 0) * G.coeff (d - a)) =
        ∑ a ∈ range (q.val + 1),
          if a ≤ d then (-p) ^ (q.val - a) * (q.val.choose a : ℚ) * G.coeff (d - a) else 0 := by
      -- Both equal sum over a ∈ range (min (d+1) (q+1))
      have hL : (∑ a ∈ range (d + 1),
          (if a ≤ q.val then (-p) ^ (q.val - a) * (q.val.choose a : ℚ) else 0) * G.coeff (d - a)) =
          ∑ a ∈ (range (d + 1)).filter (fun a => a ≤ q.val),
            (-p) ^ (q.val - a) * (q.val.choose a : ℚ) * G.coeff (d - a) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a _; split_ifs <;> simp
      have hR : (∑ a ∈ range (q.val + 1),
          if a ≤ d then (-p) ^ (q.val - a) * (q.val.choose a : ℚ) * G.coeff (d - a) else 0) =
          ∑ a ∈ (range (q.val + 1)).filter (fun a => a ≤ d),
            (-p) ^ (q.val - a) * (q.val.choose a : ℚ) * G.coeff (d - a) := by
        rw [Finset.sum_filter]
      rw [hL, hR]
      congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hswap, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  rw [hexpand, Finset.sum_comm]
  -- Change inner variable d = a + s (s = d - a < m)
  have hreidx2 : (∑ a ∈ range (q.val + 1), ∑ d ∈ range m,
      if a ≤ d then
        (-p) ^ (q.val - a) * (q.val.choose a : ℚ) * G.coeff (d - a) *
          ((m - d + 3).choose 4 : ℚ) * (1 / p ^ (m - d + 4))
      else 0) =
      ∑ s ∈ range m, ∑ a ∈ range (q.val + 1),
        if a + s < m then
          (-1 : ℚ) ^ (q.val - a) * (q.val.choose a : ℚ) *
            ((m - (a + s) + 3).choose 4 : ℚ) * G.coeff s * p ^ (-(9 : ℤ) + (s : ℤ))
        else 0 := by
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    have haq : a ≤ q.val := Nat.lt_succ_iff.mp (mem_range.mp ha)
    have hL : (∑ d ∈ range m,
        if a ≤ d then
          (-p) ^ (q.val - a) * (q.val.choose a : ℚ) * G.coeff (d - a) *
            ((m - d + 3).choose 4 : ℚ) * (1 / p ^ (m - d + 4))
        else 0) =
        ∑ d ∈ (range m).filter (fun d => a ≤ d),
          (-p) ^ (q.val - a) * (q.val.choose a : ℚ) * G.coeff (d - a) *
            ((m - d + 3).choose 4 : ℚ) * (1 / p ^ (m - d + 4)) := by
      rw [Finset.sum_filter]
    have hR : (∑ s ∈ range m,
        if a + s < m then
          (-1 : ℚ) ^ (q.val - a) * (q.val.choose a : ℚ) *
            ((m - (a + s) + 3).choose 4 : ℚ) * G.coeff s * p ^ (-(9 : ℤ) + (s : ℤ))
        else 0) =
        ∑ s ∈ (range m).filter (fun s => a + s < m),
          (-1 : ℚ) ^ (q.val - a) * (q.val.choose a : ℚ) *
            ((m - (a + s) + 3).choose 4 : ℚ) * G.coeff s * p ^ (-(9 : ℤ) + (s : ℤ)) := by
      rw [Finset.sum_filter]
    rw [hL, hR]
    apply Finset.sum_bij (fun d _ => d - a)
    · intro d hd
      rw [Finset.mem_filter, Finset.mem_range] at hd ⊢
      omega
    · intro d₁ hd₁ d₂ hd₂ heq
      rw [Finset.mem_filter] at hd₁ hd₂
      omega
    · intro s hs
      rw [Finset.mem_filter, Finset.mem_range] at hs
      refine ⟨a + s, ?_, by omega⟩
      rw [Finset.mem_filter, Finset.mem_range]
      omega
    · intro d hd
      rw [Finset.mem_filter, Finset.mem_range] at hd
      have hdas : a + (d - a) = d := by omega
      rw [hdas]
      have hnegp : (-p) ^ (q.val - a) = (-1 : ℚ) ^ (q.val - a) * p ^ (q.val - a) := by
        rw [← mul_pow, neg_one_mul]
      rw [hnegp]
      have hp_pow : p ^ (q.val - a) * (1 / p ^ (m - d + 4)) = p ^ (-(9 : ℤ) + ((d - a : ℕ) : ℤ)) := by
        rw [one_div, ← zpow_natCast p (q.val - a), ← zpow_natCast p (m - d + 4),
          ← zpow_neg, ← zpow_add₀ hpne]
        congr 1
        have : (q.val - a : ℤ) + -((m - d + 4 : ℕ) : ℤ) = -(9 : ℤ) + ((d - a : ℕ) : ℤ) := by
          omega
        exact_mod_cast this
      calc
        (-1 : ℚ) ^ (q.val - a) * p ^ (q.val - a) * (q.val.choose a : ℚ) * G.coeff (d - a) *
            ((m - d + 3).choose 4 : ℚ) * (1 / p ^ (m - d + 4))
            = (-1 : ℚ) ^ (q.val - a) * (q.val.choose a : ℚ) * ((m - d + 3).choose 4 : ℚ) *
                G.coeff (d - a) * (p ^ (q.val - a) * (1 / p ^ (m - d + 4))) := by ring
        _ = _ := by rw [hp_pow]
  rw [hreidx2, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hsm : s < m := mem_range.mp hs
  have hfactor : (∑ a ∈ range (q.val + 1),
      if a + s < m then
        (-1 : ℚ) ^ (q.val - a) * (q.val.choose a : ℚ) *
          ((m - (a + s) + 3).choose 4 : ℚ) * G.coeff s * p ^ (-(9 : ℤ) + (s : ℤ))
      else 0) =
      (∑ a ∈ range (q.val + 1),
        if a + s < m then
          (-1 : ℚ) ^ (q.val - a) * (q.val.choose a : ℚ) * ((m - (a + s) + 3).choose 4 : ℚ)
        else 0) * (G.coeff s * p ^ (-(9 : ℤ) + (s : ℤ))) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  rw [hfactor]
  have hbin := sixGate_binomial_sum_eq q s (by omega)
  have hbin' : (∑ a ∈ range (q.val + 1),
      if a + s < m then
        (-1 : ℚ) ^ (q.val - a) * (q.val.choose a : ℚ) * ((m - (a + s) + 3).choose 4 : ℚ)
      else 0) = (-1 : ℚ) ^ q.val * ((8 - s).choose (m - 1 - s) : ℚ) := by
    simpa only [hm, show q.val + 5 - 1 - s = q.val + 4 - s by omega] using hbin
  rw [hbin', pow_succ]
  ring

/-! ## The three fixed `3 × 3` binomial blocks (determinants `-50`, `-20`, `-1`) -/

def sixGateBlock (q : Fin 3) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun a b => ((8 - a.val - b.val).choose (q.val + 4 - a.val - b.val) : ℤ)

theorem sixGateBlock_det_0 : (sixGateBlock 0).det = -50 := by
  rw [Matrix.det_fin_three]
  decide

theorem sixGateBlock_det_1 : (sixGateBlock 1).det = -20 := by
  rw [Matrix.det_fin_three]
  decide

theorem sixGateBlock_det_2 : (sixGateBlock 2).det = -1 := by
  rw [Matrix.det_fin_three]
  decide

/-- All three `3 × 3` binomial blocks are invertible in `ZMod (50n + 1)` with zero
bad primes excluded (since `50n + 1 ≥ 51` is prime, hence coprime to `2` and `5`). -/
theorem sixGateBlock_det_zmod_ne_zero (n : ℕ) [Fact (gatePrime n).Prime] (q : Fin 3) :
    ((sixGateBlock q).map (Int.castRingHom (ZMod (gatePrime n)))).det ≠ 0 := by
  change ((Int.castRingHom (ZMod (gatePrime n))).mapMatrix (sixGateBlock q)).det ≠ 0
  rw [← RingHom.map_det]
  have h2 := gatePrime_two_ne_zero n
  have h5 := gatePrime_five_ne_zero n
  fin_cases q
  · change (Int.castRingHom (ZMod (gatePrime n))) (sixGateBlock 0).det ≠ 0
    rw [sixGateBlock_det_0]
    change ((-50 : ℤ) : ZMod (gatePrime n)) ≠ 0
    simp only [Int.cast_neg, Int.cast_ofNat, neg_ne_zero]
    have : (50 : ZMod (gatePrime n)) = 2 * 5 * 5 := by norm_num
    rw [this]
    exact mul_ne_zero (mul_ne_zero h2 h5) h5
  · change (Int.castRingHom (ZMod (gatePrime n))) (sixGateBlock 1).det ≠ 0
    rw [sixGateBlock_det_1]
    change ((-20 : ℤ) : ZMod (gatePrime n)) ≠ 0
    simp only [Int.cast_neg, Int.cast_ofNat, neg_ne_zero]
    have : (20 : ZMod (gatePrime n)) = 2 * 2 * 5 := by norm_num
    rw [this]
    exact mul_ne_zero (mul_ne_zero h2 h2) h5
  · change (Int.castRingHom (ZMod (gatePrime n))) (sixGateBlock 2).det ≠ 0
    rw [sixGateBlock_det_2]
    change ((-1 : ℤ) : ZMod (gatePrime n)) ≠ 0
    simp

end OddZetaSix

