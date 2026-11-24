import OddZetaSix.EvenBasis
import OddZetaSix.SixFunctional
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Int.GCD

/-!
# Stage 2A (File 1): Lemma 2 Taylor Estimates, Congruence-Class Shifts, and Binomial Weights

Proves the local Taylor estimates for `evenBasis i` (`zeta6_irrationality_proof.tex`, Lemma 2 &
eq. (7)) plus the all-prime-power weighted Taylor bound used by Lemma 3 (`SixSmallPrimes.lean`):

1. Zero-safe `p`-adic valuation floors `ValAtLeast` and linear-slope polynomial weights
   `PolyWeighted` (handling Mathlib's `padicValRat p 0 = 0` cleanly).
2. Exact polynomial identity `evenBasis i = normalizedRising (1 - i) (2i) + normalizedRising (-i) (2i)`.
3. **Lemma 2 (eq. (5))**: for any prime `p` with `2i < p^2` and any `x : ℤ`,
   `ValAtLeast p (max 0 (r - ⌊2i/p⌋)) (p^r * taylorCoeff (evenBasis i) x r)` and its
   `q`-shifted corollary.
4. **Eq. (7)**: congruence-class shift `p^a E_i^[a](x) = ∑_{j=a}^{2i} choose(j,a) ((x-z)/p)^(j-a) p^j E_i^[j](z)`
   with integer coefficients when `p ∣ x - z`, plus reflection parity
   `p^a E_i^[a](-x) = (-1)^a p^a E_i^[a](x)`.
5. **All-prime-power Vandermonde bound**: for any prime `p`, any `M₀`, and any `m ≤ M₀`,
   `PolyWeighted p (taylor x (normalizedRising a m)) 0 (Nat.log p M₀)`.
-/

noncomputable section
set_option autoImplicit false

namespace OddZetaSix

open Polynomial Finset

/-! ## Zero-safe `p`-adic valuation floors and linear-slope polynomial weights -/

/-- Zero-safe `p`-adic valuation lower bound (`0` satisfies every floor). -/
def ValAtLeast (p : ℕ) (a : ℤ) (x : ℚ) : Prop :=
  x = 0 ∨ a ≤ padicValRat p x

theorem valAtLeast_zero (p : ℕ) (a : ℤ) : ValAtLeast p a 0 := Or.inl rfl

theorem valAtLeast_of_ne_zero {p : ℕ} {a : ℤ} {x : ℚ}
    (h : ValAtLeast p a x) (hx : x ≠ 0) : a ≤ padicValRat p x :=
  h.resolve_left hx

theorem valAtLeast_mono {p : ℕ} {a b : ℤ} {x : ℚ}
    (h : ValAtLeast p a x) (hab : b ≤ a) : ValAtLeast p b x :=
  h.elim Or.inl (fun hx => Or.inr (hab.trans hx))

theorem valAtLeast_max {p : ℕ} {a b : ℤ} {x : ℚ}
    (ha : ValAtLeast p a x) (hb : ValAtLeast p b x) : ValAtLeast p (max a b) x := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr (max_le (ha.resolve_left hx) (hb.resolve_left hx))

theorem valAtLeast_neg {p : ℕ} {a : ℤ} {x : ℚ}
    (h : ValAtLeast p a x) : ValAtLeast p a (-x) := by
  rcases h with rfl | h
  · simpa using valAtLeast_zero p a
  · exact Or.inr (by simpa using h)

theorem valAtLeast_intCast (p : ℕ) [Fact p.Prime] (z : ℤ) : ValAtLeast p 0 (z : ℚ) := by
  by_cases hz : z = 0
  · subst hz; exact Or.inl (by simp)
  · right
    rw [padicValRat.of_int]
    exact Int.natCast_nonneg _

theorem valAtLeast_natCast (p : ℕ) [Fact p.Prime] (k : ℕ) : ValAtLeast p 0 (k : ℚ) := by
  simpa using valAtLeast_intCast p (k : ℤ)

theorem valAtLeast_one (p : ℕ) [Fact p.Prime] : ValAtLeast p 0 (1 : ℚ) :=
  Or.inr (by simp)

theorem valAtLeast_add {p : ℕ} [Fact p.Prime] {a : ℤ} {x y : ℚ}
    (hx : ValAtLeast p a x) (hy : ValAtLeast p a y) : ValAtLeast p a (x + y) := by
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  rcases hx with rfl | hx
  · simpa using hy
  rcases hy with rfl | hy
  · exact Or.inr (by simpa using hx)
  exact Or.inr ((le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy))

theorem valAtLeast_sub {p : ℕ} [Fact p.Prime] {a : ℤ} {x y : ℚ}
    (hx : ValAtLeast p a x) (hy : ValAtLeast p a y) : ValAtLeast p a (x - y) := by
  simpa only [sub_eq_add_neg] using valAtLeast_add hx (valAtLeast_neg hy)

theorem valAtLeast_mul {p : ℕ} [Fact p.Prime] {a b : ℤ} {x y : ℚ}
    (hx : ValAtLeast p a x) (hy : ValAtLeast p b y) : ValAtLeast p (a + b) (x * y) := by
  by_cases hx0 : x = 0
  · simp [hx0, valAtLeast_zero]
  by_cases hy0 : y = 0
  · simp [hy0, valAtLeast_zero]
  right
  rw [padicValRat.mul hx0 hy0]
  exact add_le_add (hx.resolve_left hx0) (hy.resolve_left hy0)

theorem valAtLeast_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → ℚ) (a : ℤ) (hf : ∀ i ∈ s, ValAtLeast p a (f i)) :
    ValAtLeast p a (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valAtLeast_zero p a
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact valAtLeast_add (hf i (mem_insert_self _ _))
      (ih (fun j hj => hf j (mem_insert_of_mem hj)))

theorem valAtLeast_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → ℚ) (a : ι → ℤ) (hf : ∀ i ∈ s, ValAtLeast p (a i) (f i)) :
    ValAtLeast p (∑ i ∈ s, a i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valAtLeast_one p
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact valAtLeast_mul (hf i (mem_insert_self _ _))
      (ih (fun j hj => hf j (mem_insert_of_mem hj)))

theorem valAtLeast_p_pow_mul {p : ℕ} [Fact p.Prime] {a : ℤ} {x : ℚ}
    (r : ℕ) (hx : ValAtLeast p a x) :
    ValAtLeast p ((r : ℤ) + a) ((p : ℚ) ^ r * x) := by
  have hp : p.Prime := Fact.out
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpr_eq : padicValRat p ((p : ℚ) ^ r) = (r : ℤ) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ, padicValRat.mul (pow_ne_zero r hpne) hpne, ih,
        padicValRat.self hp.one_lt]
      push_cast; ring
  exact valAtLeast_mul (Or.inr hpr_eq.ge) hx

/-- Linear-slope coefficient valuation bound: `coeff r` has `p`-adic valuation `≥ a - slope * r`. -/
def PolyWeighted (p : ℕ) (P : ℚ[X]) (a slope : ℤ) : Prop :=
  ∀ r : ℕ, ValAtLeast p (a - slope * (r : ℤ)) (P.coeff r)

theorem polyWeighted_mono {p : ℕ} {P : ℚ[X]} {a b slope : ℤ}
    (h : PolyWeighted p P a slope) (hab : b ≤ a) : PolyWeighted p P b slope :=
  fun r => valAtLeast_mono (h r) (by omega)

theorem polyWeighted_C {p : ℕ} {a slope : ℤ} {x : ℚ} (hx : ValAtLeast p a x) :
    PolyWeighted p (C x) a slope := by
  intro r
  by_cases hr : r = 0
  · subst hr; simpa using hx
  · rw [coeff_C]; simp [hr, valAtLeast_zero]

theorem polyWeighted_one (p : ℕ) [Fact p.Prime] (slope : ℤ) : PolyWeighted p 1 0 slope := by
  simpa using (polyWeighted_C (slope := slope) (valAtLeast_one p))

theorem polyWeighted_add {p : ℕ} [Fact p.Prime] {P Q : ℚ[X]} {a slope : ℤ}
    (hP : PolyWeighted p P a slope) (hQ : PolyWeighted p Q a slope) :
    PolyWeighted p (P + Q) a slope := by
  intro r; rw [coeff_add]; exact valAtLeast_add (hP r) (hQ r)

theorem polyWeighted_mul {p : ℕ} [Fact p.Prime] {P Q : ℚ[X]} {a b slope : ℤ}
    (hP : PolyWeighted p P a slope) (hQ : PolyWeighted p Q b slope) :
    PolyWeighted p (P * Q) (a + b) slope := by
  intro r
  rw [coeff_mul]
  apply valAtLeast_sum
  intro x hx
  have hxr : (x.1 : ℤ) + (x.2 : ℤ) = (r : ℤ) := by
    exact_mod_cast Finset.mem_antidiagonal.mp hx
  have hm := valAtLeast_mul (hP x.1) (hQ x.2)
  have heq : a + b - slope * (r : ℤ) = (a - slope * (x.1 : ℤ)) + (b - slope * (x.2 : ℤ)) := by
    rw [← hxr]; ring
  exact valAtLeast_mono hm heq.le

theorem polyWeighted_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → ℚ[X]) (a slope : ℤ) (hf : ∀ i ∈ s, PolyWeighted p (f i) a slope) :
    PolyWeighted p (∑ i ∈ s, f i) a slope := by
  intro r
  rw [finsetSum_coeff]
  exact valAtLeast_sum s (fun i => (f i).coeff r) _ (fun i hi => hf i hi r)

theorem polyWeighted_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → ℚ[X]) (a : ι → ℤ) (slope : ℤ)
    (hf : ∀ i ∈ s, PolyWeighted p (f i) (a i) slope) :
    PolyWeighted p (∏ i ∈ s, f i) (∑ i ∈ s, a i) slope := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polyWeighted_one p slope
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact polyWeighted_mul (hf i (mem_insert_self _ _))
      (ih (fun j hj => hf j (mem_insert_of_mem hj)))

theorem polyWeighted_linear_int {p : ℕ} [Fact p.Prime] (c : ℤ) :
    PolyWeighted p (X + C (c : ℚ)) (if (p : ℤ) ∣ c then 1 else 0) 1 := by
  intro r
  cases r with
  | zero =>
    simp only [coeff_add, coeff_X_zero, coeff_C_zero, zero_add, Nat.cast_zero, mul_zero, sub_zero]
    split_ifs with hd
    · by_cases hc : c = 0
      · subst hc; exact Or.inl (by simp)
      · right
        rw [padicValRat.of_int, padicValInt]
        have h1 : 1 ≤ padicValNat p c.natAbs :=
          one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hc)
            (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd))
        exact_mod_cast h1
    · exact valAtLeast_intCast p c
  | succ r =>
    cases r with
    | zero =>
      simp only [zero_add, coeff_add, coeff_X_one, coeff_C_succ, add_zero, Nat.cast_one, mul_one]
      apply valAtLeast_mono (valAtLeast_one p)
      split_ifs <;> omega
    | succ r =>
      have hne : (1 : ℕ) ≠ r + 1 + 1 := by omega
      simp only [coeff_add, coeff_X, coeff_C_succ, hne, ite_false, add_zero]
      exact valAtLeast_zero p _

theorem polyWeighted_linear_int_slope {p : ℕ} [Fact p.Prime] (c : ℤ) (slope : ℤ) (hs : 0 ≤ slope) :
    PolyWeighted p (X + C (c : ℚ)) 0 slope := by
  intro r
  cases r with
  | zero =>
    simp only [coeff_add, coeff_X_zero, coeff_C_zero, zero_add, Nat.cast_zero, mul_zero, sub_zero]
    exact valAtLeast_intCast p c
  | succ r =>
    cases r with
    | zero =>
      simp only [zero_add, coeff_add, coeff_X_one, coeff_C_succ, add_zero, Nat.cast_one, mul_one]
      exact valAtLeast_mono (valAtLeast_one p) (by omega)
    | succ r =>
      have hne : (1 : ℕ) ≠ r + 1 + 1 := by omega
      simp only [coeff_add, coeff_X, coeff_C_succ, hne, ite_false, add_zero]
      exact valAtLeast_zero p _

/-! ## Taylor coefficient notation and normalized rising polynomials -/

/-- The `r`-th Taylor coefficient `P^[r](x)` of `P ∈ ℚ[X]` around `x ∈ ℚ`. -/
def taylorCoeff (P : ℚ[X]) (x : ℚ) (r : ℕ) : ℚ :=
  (taylor x P).coeff r

/-- A consecutive integer root block divided by its length factorial. -/
def normalizedRising (a : ℤ) (m : ℕ) : ℚ[X] :=
  C (1 / (m.factorial : ℚ)) * rising (a : ℚ) m

private theorem taylor_prod_finset {ι : Type*} [DecidableEq ι] (x : ℚ)
    (s : Finset ι) (f : ι → ℚ[X]) :
    taylor x (∏ i ∈ s, f i) = ∏ i ∈ s, taylor x (f i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; rw [← C_1, taylor_C, C_1]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, taylor_mul, ih]

theorem taylor_rising_int (a x : ℤ) (m : ℕ) :
    taylor (x : ℚ) (rising (a : ℚ) m) =
      ∏ j ∈ range m, (X + C (((a + x + (j : ℤ)) : ℤ) : ℚ)) := by
  unfold rising
  rw [taylor_prod_finset]
  apply Finset.prod_congr rfl
  intro j _
  rw [map_add, taylor_X, taylor_C, add_assoc, ← C_add]
  congr 2
  push_cast
  ring

/-- Polynomial identity expressing `evenBasis i` (`i > 0`) as the sum of two adjacent
normalized rising blocks of length `2i`. -/
theorem evenBasis_eq_normalizedRising (i : ℕ) (hi : 0 < i) :
    evenBasis i = normalizedRising (1 - (i : ℤ)) (2 * i) + normalizedRising (-(i : ℤ)) (2 * i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  rw [evenBasis_succ, normalizedRising, normalizedRising, ← mul_add]
  have hprod_eq : ∀ k : ℕ,
      (∏ j ∈ range (2 * k + 1), (X + C ((j : ℚ) - (k : ℚ)))) =
        X * evenBasisProduct k := by
    intro k
    induction k with
    | zero => simp [evenBasisProduct]
    | succ k ih =>
      have hsplit : (∏ j ∈ range (2 * (k + 1) + 1), (X + C ((j : ℚ) - ((k + 1 : ℕ) : ℚ)))) =
          (X + C (-((k + 1 : ℕ) : ℚ))) *
            (∏ j ∈ range (2 * k + 1), (X + C ((j : ℚ) - (k : ℚ)))) *
            (X + C (((k + 1 : ℕ) : ℚ))) := by
        rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega, prod_range_succ]
        congr 1
        · rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, prod_range_succ']
          rw [mul_comm]
          congr 1
          · simp
          · apply Finset.prod_congr rfl
            intro j _
            congr 2
            push_cast
            ring
        · congr 2
          push_cast
          ring
      rw [hsplit, ih]
      conv_rhs => rw [evenBasisProduct, prod_range_succ, ← evenBasisProduct]
      have hdiff : (X + C (-((k + 1 : ℕ) : ℚ))) * (X + C (((k + 1 : ℕ) : ℚ))) =
          X ^ 2 - C (((k : ℚ) + 1) ^ 2) := by
        simp only [map_neg, map_pow, map_add, map_natCast, map_one]
        push_cast
        ring
      calc
        (X + C (-((k + 1 : ℕ) : ℚ))) * (X * evenBasisProduct k) * (X + C (((k + 1 : ℕ) : ℚ)))
            = ((X + C (-((k + 1 : ℕ) : ℚ))) * (X + C (((k + 1 : ℕ) : ℚ)))) *
                (X * evenBasisProduct k) := by ring
        _ = (X ^ 2 - C (((k : ℚ) + 1) ^ 2)) * (X * evenBasisProduct k) := by rw [hdiff]
        _ = X * (evenBasisProduct k * (X ^ 2 - C (((k : ℚ) + 1) ^ 2))) := by ring
  have hr1 : rising ((1 - ((m + 1 : ℕ) : ℤ) : ℤ) : ℚ) (2 * (m + 1)) =
      (X * evenBasisProduct m) * (X + C ((m : ℚ) + 1)) := by
    unfold rising
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, prod_range_succ, ← hprod_eq m]
    congr 1
    · apply Finset.prod_congr rfl
      intro j _
      congr 2
      push_cast; ring
    · congr 2
      push_cast; ring
  have hr2 : rising ((-((m + 1 : ℕ) : ℤ) : ℤ) : ℚ) (2 * (m + 1)) =
      (X - C ((m : ℚ) + 1)) * (X * evenBasisProduct m) := by
    unfold rising
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, prod_range_succ', ← hprod_eq m]
    rw [mul_comm]
    congr 1
    · rw [sub_eq_add_neg, ← map_neg]
      congr 2
      push_cast; ring
    · apply Finset.prod_congr rfl
      intro j _
      congr 2
      push_cast; ring
  rw [hr1, hr2]
  have h2 : C ((2 : ℚ) / ((2 * (m + 1)).factorial : ℚ)) =
      C (1 / ((2 * (m + 1)).factorial : ℚ)) * C 2 := by
    rw [← map_mul]; congr 1; ring
  rw [h2]
  have hsum : (X * evenBasisProduct m) * (X + C ((m : ℚ) + 1)) +
      (X - C ((m : ℚ) + 1)) * (X * evenBasisProduct m) =
      C (2 : ℚ) * (X ^ 2 * evenBasisProduct m) := by
    have : C (2 : ℚ) = (2 : ℚ[X]) := map_ofNat C 2
    rw [this]; ring
  rw [hsum]
  ring

/-! ## Lemma 2: Taylor estimates for `p^2 > 2i` -/

/-- Any `m` consecutive integers contain at least `⌊m / p⌋` multiples of `p`. -/
theorem consecutive_multiples_lower (p : ℕ) (hp : 0 < p) (b : ℤ) (m : ℕ) :
    ((m / p : ℕ) : ℤ) ≤ ∑ j ∈ range m, (if (p : ℤ) ∣ b + (j : ℤ) then (1 : ℤ) else 0) := by
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  let k : ℕ := m / p
  have hkp : k * p ≤ m := Nat.div_mul_le_self m p
  have hstep : ∀ q : ℕ, ∃ j ∈ Finset.Ico (q * p) ((q + 1) * p), (p : ℤ) ∣ b + (j : ℤ) := by
    intro q
    let r : ℤ := (b + ((q * p : ℕ) : ℤ)) % (p : ℤ)
    have hr0 : 0 ≤ r := Int.emod_nonneg _ hpZ.ne'
    have hrlt : r < (p : ℤ) := Int.emod_lt_of_pos _ hpZ
    let d : ℕ := if r = 0 then 0 else (p - r.toNat)
    have hdlt : d < p := by
      dsimp [d]
      split_ifs with h0
      · exact hp
      · have hpos : 0 < r.toNat := by omega
        omega
    refine ⟨q * p + d, Finset.mem_Ico.mpr ⟨by omega, by nlinarith⟩, ?_⟩
    have hdiv : (p : ℤ) ∣ b + ((q * p : ℕ) : ℤ) + (d : ℤ) := by
      dsimp [d]
      split_ifs with h0
      · simp only [Nat.cast_zero, add_zero]
        exact Int.dvd_of_emod_eq_zero h0
      · have hmod : (b + ((q * p : ℕ) : ℤ) + ((p - r.toNat : ℕ) : ℤ)) % (p : ℤ) = 0 := by
          have hr_eq : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
          have hsub : ((p - r.toNat : ℕ) : ℤ) = (p : ℤ) - r := by
            rw [Nat.cast_sub (by omega : r.toNat ≤ p), hr_eq]
          rw [hsub]
          have h1 : b + ((q * p : ℕ) : ℤ) + ((p : ℤ) - r) =
              ((b + ((q * p : ℕ) : ℤ)) / (p : ℤ) + 1) * (p : ℤ) := by
            have hdivmod := Int.mul_ediv_add_emod (b + ((q * p : ℕ) : ℤ)) (p : ℤ)
            dsimp [r]
            push_cast at hdivmod ⊢
            linarith
          rw [h1]
          exact Int.mul_emod_left _ _
        exact Int.dvd_of_emod_eq_zero hmod
    simpa [Nat.cast_add, add_assoc] using hdiv
  have hsub : (∑ q ∈ range k, ∑ j ∈ Finset.Ico (q * p) ((q + 1) * p),
      (if (p : ℤ) ∣ b + (j : ℤ) then (1 : ℤ) else 0)) ≤
      ∑ j ∈ range m, (if (p : ℤ) ∣ b + (j : ℤ) then (1 : ℤ) else 0) := by
    have hpart : ∀ n : ℕ, (∑ q ∈ range n, ∑ j ∈ Finset.Ico (q * p) ((q + 1) * p),
        (if (p : ℤ) ∣ b + (j : ℤ) then (1 : ℤ) else 0)) =
        ∑ j ∈ range (n * p), (if (p : ℤ) ∣ b + (j : ℤ) then (1 : ℤ) else 0) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih, ← Nat.Ico_zero_eq_range, ← Nat.Ico_zero_eq_range]
        rw [Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by nlinarith)]
    rw [hpart k]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkp)
      (fun j _ _ => by split_ifs <;> norm_num)
  have hblock : ∀ q ∈ range k, (1 : ℤ) ≤ ∑ j ∈ Finset.Ico (q * p) ((q + 1) * p),
      (if (p : ℤ) ∣ b + (j : ℤ) then (1 : ℤ) else 0) := by
    intro q _
    obtain ⟨j₀, hj₀, hdiv⟩ := hstep q
    have hle := Finset.single_le_sum
      (f := fun j : ℕ => if (p : ℤ) ∣ b + (j : ℤ) then (1 : ℤ) else 0)
      (s := Finset.Ico (q * p) ((q + 1) * p))
      (fun j _ => by split_ifs <;> norm_num) hj₀
    simpa [hdiv] using hle
  calc
    (k : ℤ) = ∑ _q ∈ range k, (1 : ℤ) := by simp
    _ ≤ ∑ q ∈ range k, ∑ j ∈ Finset.Ico (q * p) ((q + 1) * p),
        (if (p : ℤ) ∣ b + (j : ℤ) then (1 : ℤ) else 0) := Finset.sum_le_sum hblock
    _ ≤ _ := hsub

/-- Legendre valuation of `m!` when `m < p^2`: `v_p(m!) = ⌊m / p⌋`. -/
theorem padicValRat_factorial_lt_sq (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m < p ^ 2) :
    padicValRat p (m.factorial : ℚ) = ((m / p : ℕ) : ℤ) := by
  by_cases hm0 : m = 0
  · simp [hm0]
  · rw [padicValRat.of_nat, padicValNat_factorial (Nat.log_lt_of_lt_pow hm0 hm)]
    norm_num [show Finset.Ico 1 2 = ({1} : Finset ℕ) by decide]

theorem normalizedRising_unit_slope (p : ℕ) [Fact p.Prime]
    (a x : ℤ) (m : ℕ) (hm : m < p ^ 2) :
    PolyWeighted p (taylor (x : ℚ) (normalizedRising a m)) 0 1 := by
  have hp : p.Prime := Fact.out
  rw [normalizedRising, taylor_mul, taylor_C, taylor_rising_int]
  have hfac : ValAtLeast p (-((m / p : ℕ) : ℤ)) (1 / (m.factorial : ℚ)) := by
    right
    rw [one_div, padicValRat.inv, padicValRat_factorial_lt_sq p m hm]
  have hprod := polyWeighted_prod (range m)
    (fun j => X + C (((a + x + (j : ℤ)) : ℤ) : ℚ))
    (fun j => if (p : ℤ) ∣ a + x + (j : ℤ) then 1 else 0) 1
    (fun j _ => polyWeighted_linear_int (a + x + (j : ℤ)))
  have hmul := polyWeighted_mul (polyWeighted_C (slope := 1) hfac) hprod
  have hcnt := consecutive_multiples_lower p hp.pos (a + x) m
  exact polyWeighted_mono hmul (by omega)

theorem normalizedRising_flat_floor (p : ℕ) [Fact p.Prime]
    (a x : ℤ) (m : ℕ) (hm : m < p ^ 2) :
    PolyWeighted p (taylor (x : ℚ) (normalizedRising a m)) (-((m / p : ℕ) : ℤ)) 0 := by
  rw [normalizedRising, taylor_mul, taylor_C, taylor_rising_int]
  have hfac : ValAtLeast p (-((m / p : ℕ) : ℤ)) (1 / (m.factorial : ℚ)) := by
    right
    rw [one_div, padicValRat.inv, padicValRat_factorial_lt_sq p m hm]
  have hprod := polyWeighted_prod (p := p) (range m)
    (fun j => X + C (((a + x + (j : ℤ)) : ℤ) : ℚ))
    (fun _ => 0) 0
    (fun j _ => polyWeighted_linear_int_slope (a + x + (j : ℤ)) 0 le_rfl)
  simpa using polyWeighted_mul (polyWeighted_C (slope := 0) hfac) hprod

/-- **Lemma 2 (zero-safe form, eq. (5))**: for any prime `p`, `2i < p^2`, `x : ℤ`, `r : ℕ`,
`p^r E_i^[r](x)` has `p`-adic valuation at least `max(0, r - ⌊2i/p⌋)`. -/
theorem valAtLeast_p_pow_evenBasis_taylor (p : ℕ) [Fact p.Prime]
    (i : ℕ) (hi : 2 * i < p ^ 2) (x : ℤ) (r : ℕ) :
    ValAtLeast p (max 0 ((r : ℤ) - ((2 * i / p : ℕ) : ℤ)))
      ((p : ℚ) ^ r * taylorCoeff (evenBasis i) (x : ℚ) r) := by
  by_cases hi0 : i = 0
  · subst hi0
    unfold taylorCoeff
    rw [evenBasis_zero, ← C_1, taylor_C, C_1, coeff_one]
    by_cases hr : r = 0
    · subst hr; simpa using valAtLeast_one p
    · simp [hr, valAtLeast_zero]
  · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    have h1 : ValAtLeast p (-(r : ℤ)) (taylorCoeff (evenBasis i) (x : ℚ) r) := by
      unfold taylorCoeff
      rw [evenBasis_eq_normalizedRising i hipos, map_add, coeff_add]
      have hA := normalizedRising_unit_slope p (1 - (i : ℤ)) x (2 * i) hi r
      have hB := normalizedRising_unit_slope p (-(i : ℤ)) x (2 * i) hi r
      simpa using valAtLeast_add hA hB
    have h2 : ValAtLeast p (-((2 * i / p : ℕ) : ℤ)) (taylorCoeff (evenBasis i) (x : ℚ) r) := by
      unfold taylorCoeff
      rw [evenBasis_eq_normalizedRising i hipos, map_add, coeff_add]
      have hA := normalizedRising_flat_floor p (1 - (i : ℤ)) x (2 * i) hi r
      have hB := normalizedRising_flat_floor p (-(i : ℤ)) x (2 * i) hi r
      simpa using valAtLeast_add hA hB
    have hp1 : ValAtLeast p 0 ((p : ℚ) ^ r * taylorCoeff (evenBasis i) (x : ℚ) r) := by
      have h := valAtLeast_p_pow_mul (p := p) r h1
      exact valAtLeast_mono h (by omega)
    have hp2 : ValAtLeast p ((r : ℤ) - ((2 * i / p : ℕ) : ℤ))
        ((p : ℚ) ^ r * taylorCoeff (evenBasis i) (x : ℚ) r) := by
      have h := valAtLeast_p_pow_mul (p := p) r h2
      exact valAtLeast_mono h (by omega)
    exact valAtLeast_max hp1 hp2

/-- **Lemma 2 (`padicValRat` form)** for nonzero Taylor coefficients. -/
theorem padicValRat_p_pow_evenBasis_taylor_ge (p : ℕ) [Fact p.Prime]
    (i : ℕ) (hi : 2 * i < p ^ 2) (x : ℤ) (r : ℕ)
    (hne : taylorCoeff (evenBasis i) (x : ℚ) r ≠ 0) :
    max 0 ((r : ℤ) - ((2 * i / p : ℕ) : ℤ)) ≤
      padicValRat p ((p : ℚ) ^ r * taylorCoeff (evenBasis i) (x : ℚ) r) := by
  have hp : p.Prime := Fact.out
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  exact valAtLeast_of_ne_zero (valAtLeast_p_pow_evenBasis_taylor p i hi x r)
    (mul_ne_zero (pow_ne_zero r hpne) hne)

/-- **Lemma 2 (`q`-shifted row-scaling form, zero-safe)**: multiplying row `i` by
`p ^ (⌊2i/p⌋ - q)_+` gives valuation at least `(r - q)_+`. -/
theorem valAtLeast_p_pow_evenBasis_taylor_shift (p : ℕ) [Fact p.Prime]
    (i q : ℕ) (hi : 2 * i < p ^ 2) (x : ℤ) (r : ℕ) :
    ValAtLeast p ((r - q : ℕ) : ℤ)
      ((p : ℚ) ^ (2 * i / p - q) * ((p : ℚ) ^ r * taylorCoeff (evenBasis i) (x : ℚ) r)) := by
  have h := valAtLeast_p_pow_mul (p := p) (2 * i / p - q)
    (valAtLeast_p_pow_evenBasis_taylor p i hi x r)
  apply valAtLeast_mono h
  omega

/-- **Lemma 2 (`q`-shifted `padicValRat` form)** for nonzero Taylor coefficients. -/
theorem padicValRat_p_pow_evenBasis_taylor_shift_ge (p : ℕ) [Fact p.Prime]
    (i q : ℕ) (hi : 2 * i < p ^ 2) (x : ℤ) (r : ℕ)
    (hne : taylorCoeff (evenBasis i) (x : ℚ) r ≠ 0) :
    ((r - q : ℕ) : ℤ) ≤
      padicValRat p ((p : ℚ) ^ r * taylorCoeff (evenBasis i) (x : ℚ) r) +
        ((2 * i / p - q : ℕ) : ℤ) := by
  have h := padicValRat_p_pow_evenBasis_taylor_ge p i hi x r hne
  omega

/-! ## Eq. (7): Congruence-class Taylor shift and reflection parity -/

private theorem coeff_X_add_C_pow (c : ℚ) (j a : ℕ) :
    ((X + C c) ^ j).coeff a = if a ≤ j then (j.choose a : ℚ) * c ^ (j - a) else 0 := by
  rw [add_pow, finsetSum_coeff]
  have hterm : ∀ b : ℕ, (X ^ b * C c ^ (j - b) * (j.choose b : ℚ[X])).coeff a =
      if b = a then (j.choose b : ℚ) * c ^ (j - b) else 0 := by
    intro b
    have heq : X ^ b * C c ^ (j - b) * (j.choose b : ℚ[X]) =
        C ((j.choose b : ℚ) * c ^ (j - b)) * X ^ b := by
      simp only [map_mul, map_pow, map_natCast]
      ring
    rw [heq, coeff_C_mul, coeff_X_pow]
    by_cases hba : b = a
    · subst hba; simp
    · have hab : a ≠ b := Ne.symm hba
      simp [hba, hab]
  simp_rw [hterm]
  by_cases ha : a ≤ j
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

/-- General Taylor re-expansion of `P^[a](x)` in terms of `P^[j](z)` (`a ≤ j ≤ D`). -/
theorem taylorCoeff_shift (P : ℚ[X]) (D : ℕ) (hdeg : P.natDegree ≤ D)
    (x z : ℚ) (a : ℕ) :
    taylorCoeff P x a =
      ∑ j ∈ Finset.Icc a D, (j.choose a : ℚ) * (x - z) ^ (j - a) * taylorCoeff P z j := by
  unfold taylorCoeff
  have hshift : taylor x P = taylor (x - z) (taylor z P) := by
    rw [taylor_taylor, sub_add_cancel]
  rw [hshift]
  have hdegz : (taylor z P).natDegree ≤ D := by
    rw [taylor_apply]
    exact natDegree_comp_le.trans (by
      have h1 : (X + C z).natDegree = 1 := natDegree_X_add_C z
      rw [h1, mul_one]; exact hdeg)
  have hexp : taylor z P = ∑ j ∈ range (D + 1), C ((taylor z P).coeff j) * X ^ j := by
    ext k
    rw [finsetSum_coeff]
    by_cases hk : k ≤ D
    · rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk
        rw [coeff_C_mul, coeff_X_pow, ite_eq_right (fun h => (hjk h.symm).elim), mul_zero]
      · intro h; exact (h (mem_range.mpr (by omega))).elim
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      have hjk : j ≠ k := by have := mem_range.mp hj; omega
      rw [coeff_C_mul, coeff_X_pow, ite_eq_right (fun h => (hjk h.symm).elim), mul_zero]
  conv_lhs => rw [hexp]
  rw [map_sum, finsetSum_coeff]
  have hterm : ∀ j ∈ range (D + 1),
      (taylor (x - z) (C ((taylor z P).coeff j) * X ^ j)).coeff a =
        if a ≤ j then (j.choose a : ℚ) * (x - z) ^ (j - a) * (taylor z P).coeff j else 0 := by
    intro j _
    rw [taylor_mul, taylor_C, taylor_pow, taylor_X, coeff_C_mul, coeff_X_add_C_pow]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

theorem evenBasis_natDegree_le (i : ℕ) : (evenBasis i).natDegree ≤ 2 * i := by
  cases i with
  | zero => simp [evenBasis_zero]
  | succ m =>
    rw [evenBasis_succ]
    refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
    have h1 : (X ^ 2 : ℚ[X]).natDegree ≤ 2 := by simp
    have h2 : (evenBasisProduct m).natDegree ≤ 2 * m := by
      unfold evenBasisProduct
      refine (natDegree_prod_le _ _).trans ?_
      have hterm : ∀ j ∈ range m, (X ^ 2 - C (((j : ℚ) + 1) ^ 2)).natDegree ≤ 2 := by
        intro j _
        exact (natDegree_sub_le _ _).trans (by simp)
      exact (Finset.sum_le_sum hterm).trans (by simp [mul_comm])
    omega

/-- **Eq. (7)**: scaled congruence-class Taylor shift for `evenBasis i`. -/
theorem p_pow_taylorCoeff_evenBasis_shift (p : ℕ) (hp : p ≠ 0)
    (i : ℕ) (x z : ℚ) (a : ℕ) :
    (p : ℚ) ^ a * taylorCoeff (evenBasis i) x a =
      ∑ j ∈ Finset.Icc a (2 * i),
        (j.choose a : ℚ) * ((x - z) / (p : ℚ)) ^ (j - a) *
          ((p : ℚ) ^ j * taylorCoeff (evenBasis i) z j) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  rw [taylorCoeff_shift (evenBasis i) (2 * i) (evenBasis_natDegree_le i) x z a, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have haj : a ≤ j := (Finset.mem_Icc.mp hj).1
  have hpow : (p : ℚ) ^ a * (x - z) ^ (j - a) =
      ((x - z) / (p : ℚ)) ^ (j - a) * (p : ℚ) ^ j := by
    rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero (j - a) hpq)]
    have : (p : ℚ) ^ a * (p : ℚ) ^ (j - a) = (p : ℚ) ^ j := by
      rw [← pow_add, Nat.add_sub_of_le haj]
    calc
      (p : ℚ) ^ a * (x - z) ^ (j - a) * (p : ℚ) ^ (j - a)
          = ((p : ℚ) ^ a * (p : ℚ) ^ (j - a)) * (x - z) ^ (j - a) := by ring
      _ = (p : ℚ) ^ j * (x - z) ^ (j - a) := by rw [this]
      _ = (x - z) ^ (j - a) * (p : ℚ) ^ j := by ring
  calc
    (p : ℚ) ^ a * ((j.choose a : ℚ) * (x - z) ^ (j - a) * taylorCoeff (evenBasis i) z j)
        = (j.choose a : ℚ) * ((p : ℚ) ^ a * (x - z) ^ (j - a)) * taylorCoeff (evenBasis i) z j := by ring
    _ = (j.choose a : ℚ) * (((x - z) / (p : ℚ)) ^ (j - a) * (p : ℚ) ^ j) *
          taylorCoeff (evenBasis i) z j := by rw [hpow]
    _ = _ := by ring

/-- When `x ≡ z (mod p)`, every shift coefficient `choose(j, a) * ((x - z) / p)^(j - a)` is an integer. -/
theorem shift_coeff_int_of_dvd {p : ℕ} (hp : p ≠ 0) {x z : ℤ}
    (hdvd : (p : ℤ) ∣ x - z) (j a : ℕ) :
    ∃ m : ℤ, (j.choose a : ℚ) * (((x : ℚ) - (z : ℚ)) / (p : ℚ)) ^ (j - a) = (m : ℚ) := by
  obtain ⟨k, hk⟩ := hdvd
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hdiv : ((x : ℚ) - (z : ℚ)) / (p : ℚ) = (k : ℚ) := by
    have hq : (x : ℚ) - (z : ℚ) = (p : ℚ) * (k : ℚ) := by exact_mod_cast hk
    rw [hq, mul_div_cancel_left₀ _ hpq]
  refine ⟨(j.choose a : ℤ) * k ^ (j - a), ?_⟩
  rw [hdiv]
  push_cast
  ring

/-- Reflection invariance of `evenBasis i`: `E_i(-X) = E_i(X)`. -/
theorem evenBasis_comp_neg (i : ℕ) : (evenBasis i).comp (-X) = evenBasis i := by
  cases i with
  | zero => simp [evenBasis_zero]
  | succ m =>
    rw [evenBasis_succ]
    simp only [mul_comp, C_comp, pow_comp, X_comp, even_two.neg_pow]
    congr 2
    unfold evenBasisProduct
    rw [Polynomial.prod_comp]
    apply Finset.prod_congr rfl
    intro j _
    simp only [sub_comp, pow_comp, X_comp, C_comp, even_two.neg_pow]

/-- Reflection parity of Taylor coefficients: `E_i^[a](-x) = (-1)^a E_i^[a](x)`. -/
theorem taylorCoeff_evenBasis_neg (i : ℕ) (x : ℚ) (a : ℕ) :
    taylorCoeff (evenBasis i) (-x) a = (-1 : ℚ) ^ a * taylorCoeff (evenBasis i) x a := by
  unfold taylorCoeff
  have hcomp : taylor (-x) (evenBasis i) = (taylor x (evenBasis i)).comp (-X) := by
    rw [taylor_apply, taylor_apply, comp_assoc]
    have harg : (X + C x).comp (-X) = (-X).comp (X + C (-x)) := by
      simp only [add_comp, X_comp, C_comp, neg_comp, map_neg]
      ring
    rw [harg, ← comp_assoc, evenBasis_comp_neg i]
  rw [hcomp]
  have hneg : ∀ Q : ℚ[X], (Q.comp (-X)).coeff a = (-1 : ℚ) ^ a * Q.coeff a := by
    intro Q
    rw [Q.as_sum_range_C_mul_X_pow]
    simp only [Polynomial.sum_comp, mul_comp, C_comp, pow_comp, X_comp, finsetSum_coeff]
    have hterm : ∀ k : ℕ, (C (Q.coeff k) * (-X) ^ k).coeff a =
        (-1 : ℚ) ^ a * (C (Q.coeff k) * X ^ k).coeff a := by
      intro k
      have hpow : (-X : ℚ[X]) ^ k = C ((-1 : ℚ) ^ k) * X ^ k := by
        rw [neg_eq_neg_one_mul, mul_pow, ← C_1, ← map_neg, ← map_pow]
      rw [hpow, ← mul_assoc, ← map_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow]
      by_cases hka : a = k
      · subst hka; simp; ring
      · simp [hka]
    simp_rw [hterm]
    rw [← Finset.mul_sum, ← finsetSum_coeff, ← Q.as_sum_range_C_mul_X_pow]
  exact hneg (taylor x (evenBasis i))

theorem p_pow_taylorCoeff_evenBasis_neg (p : ℕ) (i : ℕ) (x : ℚ) (a : ℕ) :
    (p : ℚ) ^ a * taylorCoeff (evenBasis i) (-x) a =
      (-1 : ℚ) ^ a * ((p : ℚ) ^ a * taylorCoeff (evenBasis i) x a) := by
  rw [taylorCoeff_evenBasis_neg]
  ring

/-! ## All-prime-power Vandermonde binomial bound (foundation for Lemma 3) -/

/-- Falling-factorial binomial polynomial `binom(X, m) ∈ ℚ[X]`. -/
def binomPoly (m : ℕ) : ℚ[X] :=
  C (1 / (m.factorial : ℚ)) * ∏ j ∈ range m, (X - C (j : ℚ))

theorem binomPoly_zero : binomPoly 0 = 1 := by
  simp [binomPoly]

theorem binomPoly_succ (m : ℕ) :
    binomPoly (m + 1) = C (1 / ((m + 1 : ℕ) : ℚ)) * (X - C (m : ℚ)) * binomPoly m := by
  unfold binomPoly
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  have hfac : C (1 / ((((m + 1) * m.factorial : ℕ) : ℚ))) =
      C (1 / ((m + 1 : ℕ) : ℚ)) * C (1 / (m.factorial : ℚ)) := by
    rw [← map_mul]; congr 1; push_cast; field_simp
  rw [hfac]
  ring

/-- `binomPoly m` takes integer values at every integer `A : ℤ`. -/
theorem binomPoly_eval_int (A : ℤ) (m : ℕ) :
    ∃ z : ℤ, (binomPoly m).eval (A : ℚ) = (z : ℚ) := by
  cases m with
  | zero => exact ⟨1, by simp [binomPoly_zero]⟩
  | succ m =>
    by_cases hA : 0 ≤ A
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hA
      refine ⟨(n.choose (m + 1) : ℤ), ?_⟩
      unfold binomPoly
      rw [eval_mul, eval_C, eval_prod]
      have hdesc : (∏ j ∈ range (m + 1), (((n : ℤ) : ℚ) - (j : ℚ))) =
          ((n.descFactorial (m + 1) : ℕ) : ℚ) := by
        induction (m + 1) with
        | zero => simp
        | succ k ihk =>
          rw [Finset.prod_range_succ, Nat.descFactorial_succ, ihk]
          by_cases hkn : k ≤ n
          · rw [Nat.cast_mul, Nat.cast_sub hkn, Int.cast_natCast]; ring
          · have h0 : n.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
            simp [h0]
      have heval : (∏ j ∈ range (m + 1), eval ((n : ℤ) : ℚ) (X - C (j : ℚ))) =
          ((n.descFactorial (m + 1) : ℕ) : ℚ) := by
        simpa only [eval_sub, eval_X, eval_C] using hdesc
      rw [heval, Nat.descFactorial_eq_factorial_mul_choose]
      have hfac : (((m + 1).factorial : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (m + 1)
      push_cast
      field_simp
    · obtain ⟨n, hAn⟩ : ∃ n : ℕ, A = -((n + 1 : ℕ) : ℤ) :=
        ⟨(-A - 1).toNat, by omega⟩
      subst hAn
      refine ⟨(-1 : ℤ) ^ (m + 1) * (((n + m + 1).choose (m + 1) : ℕ) : ℤ), ?_⟩
      unfold binomPoly
      rw [eval_mul, eval_C, eval_prod]
      have hasc : (∏ j ∈ range (m + 1), ((-((n + 1 : ℕ) : ℤ) : ℚ) - (j : ℚ))) =
          (-1 : ℚ) ^ (m + 1) * (((n + 1).ascFactorial (m + 1) : ℕ) : ℚ) := by
        induction (m + 1) with
        | zero => simp
        | succ k ihk =>
          rw [Finset.prod_range_succ, Nat.ascFactorial_succ, ihk, pow_succ]
          push_cast
          ring
      have heval : (∏ j ∈ range (m + 1), eval (((-((n + 1 : ℕ) : ℤ) : ℤ) : ℚ)) (X - C (j : ℚ))) =
          (-1 : ℚ) ^ (m + 1) * (((n + 1).ascFactorial (m + 1) : ℕ) : ℚ) := by
        simpa only [eval_sub, eval_X, eval_C, Int.cast_neg, Int.cast_natCast] using hasc
      have hdesc_succ : ∀ a k : ℕ, (a + 1).descFactorial (k + 1) = (a + 1) * a.descFactorial k := by
        intro a k
        induction k with
        | zero => simp
        | succ k ihk =>
          rw [Nat.descFactorial_succ, ihk, Nat.descFactorial_succ]
          have : a + 1 - (k + 1) = a - k := by omega
          rw [this]; ring
      have hasc_eq : ∀ k : ℕ, (n + 1).ascFactorial k = (n + k).descFactorial k := by
        intro k
        induction k with
        | zero => simp
        | succ k ihk =>
          rw [Nat.ascFactorial_succ, ihk]
          have h1 : (n + (k + 1)).descFactorial (k + 1) = (n + k + 1) * (n + k).descFactorial k := by
            simpa [Nat.add_assoc] using hdesc_succ (n + k) k
          rw [h1]
          ring
      rw [heval, hasc_eq (m + 1), Nat.descFactorial_eq_factorial_mul_choose,
        show n + (m + 1) = n + m + 1 by omega]
      have hfac : (((m + 1).factorial : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (m + 1)
      push_cast
      field_simp

/-- Polynomial Vandermonde identity: `binom(X + A, m) = ∑_{j=0}^m binom(A, m - j) * binom(X, j)`. -/
theorem taylor_binomPoly (A : ℚ) (m : ℕ) :
    taylor A (binomPoly m) =
      ∑ j ∈ range (m + 1), C ((binomPoly (m - j)).eval A) * binomPoly j := by
  induction m with
  | zero => simp [binomPoly_zero]
  | succ m ih =>
    have hmul_lhs : C ((m + 1 : ℕ) : ℚ) * taylor A (binomPoly (m + 1)) =
        (X + C (A - (m : ℚ))) * taylor A (binomPoly m) := by
      rw [binomPoly_succ, taylor_mul, taylor_mul, taylor_C, map_sub, taylor_X, taylor_C]
      have h1 : C ((m + 1 : ℕ) : ℚ) * C (1 / ((m + 1 : ℕ) : ℚ)) = 1 := by
        rw [← map_mul, mul_one_div_cancel (by positivity), map_one]
      have h2 : X + C A - C (m : ℚ) = X + C (A - (m : ℚ)) := by
        rw [add_sub_assoc, ← map_sub]
      rw [h2, ← mul_assoc, ← mul_assoc, h1, one_mul]
    have hstep_X : ∀ j : ℕ, (X - C (j : ℚ)) * binomPoly j =
        C ((j + 1 : ℕ) : ℚ) * binomPoly (j + 1) := by
      intro j
      rw [binomPoly_succ, ← mul_assoc, ← mul_assoc, ← map_mul,
        mul_one_div_cancel (by positivity), map_one, one_mul]
    have hstep_A : ∀ k : ℕ, (A - (k : ℚ)) * (binomPoly k).eval A =
        ((k + 1 : ℕ) : ℚ) * (binomPoly (k + 1)).eval A := by
      intro k
      have := congrArg (eval A) (hstep_X k)
      simpa only [eval_mul, eval_sub, eval_X, eval_C] using this
    have hmul_rhs : (X + C (A - (m : ℚ))) *
        (∑ j ∈ range (m + 1), C ((binomPoly (m - j)).eval A) * binomPoly j) =
        C ((m + 1 : ℕ) : ℚ) *
          ∑ j ∈ range (m + 2), C ((binomPoly (m + 1 - j)).eval A) * binomPoly j := by
      rw [Finset.mul_sum]
      have hsplit : ∀ j ∈ range (m + 1),
          (X + C (A - (m : ℚ))) * (C ((binomPoly (m - j)).eval A) * binomPoly j) =
            C (((j + 1 : ℕ) : ℚ) * (binomPoly (m - j)).eval A) * binomPoly (j + 1) +
            C (((m - j + 1 : ℕ) : ℚ) * (binomPoly (m - j + 1)).eval A) * binomPoly j := by
        intro j hj
        have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
        have hlin : X + C (A - (m : ℚ)) = (X - C (j : ℚ)) + C (A - ((m - j : ℕ) : ℚ)) := by
          have hA : A - (m : ℚ) = -(j : ℚ) + (A - ((m - j : ℕ) : ℚ)) := by
            rw [Nat.cast_sub hjm]; ring
          rw [hA, map_add, map_neg]; ring
        rw [hlin, add_mul]
        congr 1
        · calc
            (X - C (j : ℚ)) * (C ((binomPoly (m - j)).eval A) * binomPoly j)
                = C ((binomPoly (m - j)).eval A) * ((X - C (j : ℚ)) * binomPoly j) := by ring
            _ = C ((binomPoly (m - j)).eval A) * (C ((j + 1 : ℕ) : ℚ) * binomPoly (j + 1)) := by
                  rw [hstep_X j]
            _ = _ := by rw [← mul_assoc, ← map_mul, mul_comm ((binomPoly _).eval A)]
        · rw [← mul_assoc, ← map_mul, hstep_A (m - j)]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      have hS1 : (∑ j ∈ range (m + 1),
          C (((j + 1 : ℕ) : ℚ) * (binomPoly (m - j)).eval A) * binomPoly (j + 1)) =
          ∑ j ∈ range (m + 2),
            C ((j : ℚ) * (binomPoly (m + 1 - j)).eval A) * binomPoly j := by
        symm
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_mul, map_zero, add_zero]
        apply Finset.sum_congr rfl
        intro j _
        simp only [show m + 1 - (j + 1) = m - j by omega]
      have hS2 : (∑ j ∈ range (m + 1),
          C (((m - j + 1 : ℕ) : ℚ) * (binomPoly (m - j + 1)).eval A) * binomPoly j) =
          ∑ j ∈ range (m + 2),
            C (((m + 1 - j : ℕ) : ℚ) * (binomPoly (m + 1 - j)).eval A) * binomPoly j := by
        symm
        rw [Finset.sum_range_succ]
        simp only [Nat.sub_self, Nat.cast_zero, zero_mul, map_zero, add_zero]
        apply Finset.sum_congr rfl
        intro j hj
        have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
        simp only [show m + 1 - j = m - j + 1 by omega]
      rw [hS1, hS2, ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ m + 1 := Nat.lt_succ_iff.mp (mem_range.mp hj)
      rw [← add_mul, ← map_add, ← mul_assoc, ← map_mul]
      congr 2
      rw [Nat.cast_sub hjle]
      push_cast
      ring
    have hmne : C (((m + 1 : ℕ) : ℚ)) ≠ (0 : ℚ[X]) :=
      C_ne_zero.mpr (by positivity)
    apply mul_left_cancel₀ hmne
    rw [hmul_lhs, ih, hmul_rhs]

/-- Reciprocal-denominator factorization of `binomPoly j` for `j ≥ 1`:
`binom(X, j) = ((-1)^(j-1)/j) * X * ∏_{k=1}^{j-1} (1 - X/k)`. -/
theorem binomPoly_eq_inv_prod (j : ℕ) (hj : 1 ≤ j) :
    binomPoly j = C ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * X *
      ∏ k ∈ Finset.Ico 1 j, (1 - C (1 / (k : ℚ)) * X) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  induction m with
  | zero => simp [binomPoly]
  | succ m ih =>
    rw [binomPoly_succ, ih (by omega)]
    rw [show Finset.Ico 1 (m + 2) = insert (m + 1) (Finset.Ico 1 (m + 1)) by
      ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega]
    rw [Finset.prod_insert (by simp)]
    have hfac : X - C ((m + 1 : ℕ) : ℚ) =
        C (-((m + 1 : ℕ) : ℚ)) * (1 - C (1 / ((m + 1 : ℕ) : ℚ)) * X) := by
      have hmne : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      rw [mul_sub, mul_one, ← mul_assoc, ← map_mul]
      have h1 : -((m + 1 : ℕ) : ℚ) * (1 / ((m + 1 : ℕ) : ℚ)) = -1 := by field_simp
      rw [h1]
      simp only [C_neg, C_1]
      ring
    rw [hfac]
    have hsc : C (1 / ((m + 2 : ℕ) : ℚ)) * C (-((m + 1 : ℕ) : ℚ)) *
        C ((-1 : ℚ) ^ m / ((m + 1 : ℕ) : ℚ)) =
        C ((-1 : ℚ) ^ (m + 1) / ((m + 2 : ℕ) : ℚ)) := by
      rw [← map_mul, ← map_mul]
      congr 1
      have hmne : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      rw [pow_succ]
      field_simp
    calc
      C (1 / ((m + 2 : ℕ) : ℚ)) *
          (C (-((m + 1 : ℕ) : ℚ)) * (1 - C (1 / ((m + 1 : ℕ) : ℚ)) * X)) *
          (C ((-1 : ℚ) ^ m / ((m + 1 : ℕ) : ℚ)) * X *
            ∏ k ∈ Finset.Ico 1 (m + 1), (1 - C (1 / (k : ℚ)) * X))
          = (C (1 / ((m + 2 : ℕ) : ℚ)) * C (-((m + 1 : ℕ) : ℚ)) *
              C ((-1 : ℚ) ^ m / ((m + 1 : ℕ) : ℚ))) * X *
            ((1 - C (1 / ((m + 1 : ℕ) : ℚ)) * X) *
              ∏ k ∈ Finset.Ico 1 (m + 1), (1 - C (1 / (k : ℚ)) * X)) := by ring
      _ = _ := by rw [hsc]; rfl

theorem padicValNat_le_log (p : ℕ) [Fact p.Prime] {k M : ℕ} (hk0 : 0 < k) (hkM : k ≤ M) :
    padicValNat p k ≤ Nat.log p M := by
  have hp : p.Prime := Fact.out
  have hdvd : p ^ padicValNat p k ∣ k := pow_padicValNat_dvd
  have hle : p ^ padicValNat p k ≤ k := Nat.le_of_dvd hk0 hdvd
  exact Nat.le_log_of_pow_le hp.one_lt (hle.trans hkM)

/-- Every `binomPoly j` (`j ≤ M₀`) has linear-slope weight `Nat.log p M₀` for **every** prime `p`. -/
theorem binomPoly_weighted_allPrimes (p : ℕ) [Fact p.Prime] (M₀ j : ℕ) (hj : j ≤ M₀) :
    PolyWeighted p (binomPoly j) 0 (Nat.log p M₀) := by
  by_cases hj0 : j = 0
  · subst hj0; rw [binomPoly_zero]; exact polyWeighted_one p _
  · have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj0
    rw [binomPoly_eq_inv_prod j hj1]
    have hfront : PolyWeighted p (C ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * X) 0 (Nat.log p M₀) := by
      intro r
      cases r with
      | zero => simp [valAtLeast_zero]
      | succ r =>
        cases r with
        | zero =>
          simp only [zero_add, coeff_C_mul, coeff_X_one, mul_one, Nat.cast_one, zero_sub]
          right
          have h1 : (-1 : ℚ) ^ (j - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
          have h2 : (j : ℚ) ≠ 0 := by exact_mod_cast hj0
          have hv1 : padicValRat p ((-1 : ℚ) ^ (j - 1)) = 0 := by
            rcases Nat.even_or_odd (j - 1) with he | ho
            · rw [he.neg_one_pow, padicValRat.one]
            · rw [ho.neg_one_pow, padicValRat.neg, padicValRat.one]
          rw [padicValRat.div h1 h2, hv1, zero_sub, padicValRat.of_nat]
          have hlog := padicValNat_le_log p hj1 hj
          omega
        | succ r =>
          simp only [coeff_C_mul, coeff_X, show ¬ (1 = r + 1 + 1) by omega, ite_false, mul_zero]
          exact valAtLeast_zero p _
    have hlin : ∀ k ∈ Finset.Ico 1 j,
        PolyWeighted p (1 - C (1 / (k : ℚ)) * X) 0 (Nat.log p M₀) := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
      have hkM : k ≤ M₀ := ((Finset.mem_Ico.mp hk).2.le).trans hj
      intro r
      cases r with
      | zero =>
        simp only [coeff_sub, coeff_one_zero, coeff_C_mul, coeff_X_zero, mul_zero, sub_zero,
          Nat.cast_zero, mul_zero]
        exact valAtLeast_one p
      | succ r =>
        cases r with
        | zero =>
          simp only [zero_add, coeff_sub, coeff_one,
            show ¬ (1 : ℕ) = 0 by omega, ite_false, zero_sub,
            coeff_C_mul, coeff_X_one, mul_one, Nat.cast_one]
          right
          rw [padicValRat.neg, one_div, padicValRat.inv, padicValRat.of_nat]
          have hlog := padicValNat_le_log p hk1 hkM
          omega
        | succ r =>
          simp only [coeff_sub, coeff_one, coeff_C_mul, coeff_X,
            show ¬ (r + 1 + 1 = 0) by omega, show ¬ (1 = r + 1 + 1) by omega,
            ite_false, mul_zero, sub_zero]
          exact valAtLeast_zero p _
    have hprod := polyWeighted_prod (Finset.Ico 1 j)
      (fun k => 1 - C (1 / (k : ℚ)) * X) (fun _ => 0) (Nat.log p M₀) hlin
    simpa using polyWeighted_mul hfront hprod

/-- **All-prime-power weighted Taylor bound**: for EVERY prime `p` (no `p^2 > m` assumption)
and every `m ≤ M₀`, `taylor x (normalizedRising a m)` has slope `Nat.log p M₀`. -/
theorem normalizedRising_weighted_allPrimes (p : ℕ) [Fact p.Prime]
    (M₀ : ℕ) (a x : ℤ) (m : ℕ) (hm : m ≤ M₀) :
    PolyWeighted p (taylor (x : ℚ) (normalizedRising a m)) 0 (Nat.log p M₀) := by
  have heq : taylor (x : ℚ) (normalizedRising a m) =
      taylor (((a + x + (m : ℤ) - 1 : ℤ) : ℚ)) (binomPoly m) := by
    rw [normalizedRising, taylor_mul, taylor_C, taylor_rising_int, binomPoly, taylor_mul, taylor_C,
      taylor_prod_finset]
    congr 1
    -- Reindex `j ∈ range m` by `m - 1 - j`
    apply Finset.prod_bij (fun j _ => m - 1 - j)
    · intro j hj; exact mem_range.mpr (by have := mem_range.mp hj; omega)
    · intro j₁ hj₁ j₂ hj₂ h; have := mem_range.mp hj₁; have := mem_range.mp hj₂; omega
    · intro j hj; exact ⟨m - 1 - j, mem_range.mpr (by have := mem_range.mp hj; omega), by
        have := mem_range.mp hj; omega⟩
    · intro j hj
      have hjm : j < m := mem_range.mp hj
      rw [map_sub, taylor_X, taylor_C, add_sub_assoc, ← map_sub]
      congr 2
      rw [Nat.cast_sub (by omega : j ≤ m - 1), Nat.cast_sub (by omega : 1 ≤ m)]
      push_cast
      ring
  rw [heq, taylor_binomPoly]
  apply polyWeighted_sum
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  obtain ⟨z, hz⟩ := binomPoly_eval_int (a + x + (m : ℤ) - 1) (m - j)
  rw [hz]
  simpa using polyWeighted_mul (polyWeighted_C (slope := Nat.log p M₀) (valAtLeast_intCast p z))
    (binomPoly_weighted_allPrimes p M₀ j (hjm.trans hm))

/-- Corollary: `evenBasis i` (`2i ≤ M₀`) has slope `Nat.log p M₀` for **every** prime `p`. -/
theorem evenBasis_weighted_allPrimes (p : ℕ) [Fact p.Prime]
    (M₀ i : ℕ) (hi : 2 * i ≤ M₀) (x : ℤ) :
    PolyWeighted p (taylor (x : ℚ) (evenBasis i)) 0 (Nat.log p M₀) := by
  by_cases hi0 : i = 0
  · subst hi0
    rw [evenBasis_zero, ← C_1, taylor_C, C_1]
    exact polyWeighted_one p _
  · rw [evenBasis_eq_normalizedRising i (Nat.pos_of_ne_zero hi0), map_add]
    exact polyWeighted_add
      (normalizedRising_weighted_allPrimes p M₀ (1 - (i : ℤ)) x (2 * i) hi)
      (normalizedRising_weighted_allPrimes p M₀ (-(i : ℤ)) x (2 * i) hi)

end OddZetaSix
