import OddZetaSix.SixFolded

/-!
# Stage 2A (File 4): `Y * W * Yᵀ` Factorization, Local Slot Costs `B_{k,a}` / `B_+(c)`, and Master Prime Bounds

For `n ≥ 1` and prime `p` with `140 * n + 2 < p ^ 2` (automatically `p ≥ 13`, odd, and
`2 * rank n < p ^ 2`):

1. Rewrites `sixMatrix n` via reflection pairing on the upper half-lattice
   `k ∈ [70n + 1, 95n + 1]` (`25n + 1` sites, `14` jet slots each) as an exact
   block-diagonal factorization `sixMatrix n = Y_C * W * Y_Cᵀ` with
   `Y_{i, (t, a)} = p^a * E_i^[a](c_n - k_t)`.
2. Proves the refined local slot cost bound (`zeta6_irrationality_proof.tex`, §2.1 eq. (6)):
   - `d' = min d N_z` when `N_d = 0` (no denominator aliases) and `d' = d` when `N_d > 0`;
   - even-order harmonic cancellation indicator `I_ℓ` (`0` when left/right cutoffs have equal
     multiples of `p`);
   - central factor `X + c_n` estimated safely as an integral polynomial;
   - `2 * v_p^G(W_{t, (a, b)}) ≥ -(B_{t, a} + B_{t, b})` and `B_{t, a} ≤ 18`.
3. Proves the coarse periodic cost `B_+(c) = (4 + #poles(c) - #zeros(c) - v_fact)_+`
   depends only on the folded residue class `c : Fin (p / 2 + 1)`, satisfies `B_+(c) ≤ 18`,
   and dominates `B_{t, a}` uniformly.
4. Connects to `SixFolded` to export the two Stage 2A master prime bounds:
   - `sixPrimitiveScalar_folded_joint_bound` (for mid/high primes `p / (nL) ≥ 7 / 100`);
   - `sixPrimitiveScalar_periodic_coarse_bound` (for slim periodic small-prime range,
     directly giving `-v_p(γ_n) ≤ (2 * (15n) / p + 5) * ∑ c, B_+(c)`).
-/

noncomputable section
set_option autoImplicit false

namespace OddZetaSix

open Polynomial Finset

/-! ## Residue-class pole/zero counts and factorial valuation for `p^2 > 140n + 2` -/

/-- Exact `p`-adic valuation of `sixNormalization n` when `p^2 > 140n + 2` (and `p > 2`). -/
def sixFactVal (n p : ℕ) : ℤ :=
  (∑ b : Fin 14, ((sixBlockLen n b / p : ℕ) : ℤ)) -
    2 * ∑ a : Fin 5, ((sixZero a * n / p : ℕ) : ℤ)

theorem padicValRat_sixNormalization_eq (n p : ℕ) [Fact p.Prime]
    (hn : 0 < n) (hsq : 140 * n + 2 < p ^ 2) :
    padicValRat p (sixNormalization n) = sixFactVal n p := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 < p := by nlinarith
  have h2ne : (2 : ℚ) ≠ 0 := by norm_num
  have h2val : padicValRat p (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    exact_mod_cast padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by norm_num) hp2)
  have hnum_ne : (∏ b : Fin 14, ((sixBlockLen n b).factorial : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun b _ => by exact_mod_cast Nat.factorial_ne_zero _)
  have hden_ne : (∏ a : Fin 5, ((sixZero a * n).factorial : ℚ) ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun a _ => pow_ne_zero 2 (by exact_mod_cast Nat.factorial_ne_zero _))
  have hpadic_prod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℚ),
      (∀ i ∈ s, f i ≠ 0) → padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
    intro ι s f hf
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        padicValRat.mul (hf a (mem_insert_self _ _))
          (Finset.prod_ne_zero_iff.mpr (fun b hb => hf b (mem_insert_of_mem hb))),
        ih (fun b hb => hf b (mem_insert_of_mem hb))]
  have hpadic_num : padicValRat p (∏ b : Fin 14, ((sixBlockLen n b).factorial : ℚ)) =
      ∑ b : Fin 14, padicValRat p ((sixBlockLen n b).factorial : ℚ) :=
    hpadic_prod Finset.univ (fun b : Fin 14 => ((sixBlockLen n b).factorial : ℚ))
      (fun b _ => by exact_mod_cast Nat.factorial_ne_zero _)
  have hpadic_den : padicValRat p (∏ a : Fin 5, ((sixZero a * n).factorial : ℚ) ^ 2) =
      ∑ a : Fin 5, padicValRat p (((sixZero a * n).factorial : ℚ) ^ 2) :=
    hpadic_prod Finset.univ (fun a : Fin 5 => ((sixZero a * n).factorial : ℚ) ^ 2)
      (fun a _ => pow_ne_zero 2 (by exact_mod_cast Nat.factorial_ne_zero _))
  unfold sixNormalization sixFactVal
  change padicValRat p ((2 * ∏ b : Fin 14, ((sixBlockLen n b).factorial : ℚ)) /
      (∏ a : Fin 5, ((sixZero a * n).factorial : ℚ) ^ 2)) = _
  rw [padicValRat.div (mul_ne_zero h2ne hnum_ne) hden_ne,
    padicValRat.mul h2ne hnum_ne, h2val, zero_add, hpadic_num, hpadic_den]
  congr 1
  · apply Finset.sum_congr rfl; intro b _
    have hob : sixOffset b ≤ 11 := by fin_cases b <;> decide
    have hlt : sixBlockLen n b < p ^ 2 := by
      unfold sixBlockLen
      have : (50 - 2 * sixOffset b) * n ≤ 50 * n := Nat.mul_le_mul_right n (by omega)
      omega
    exact padicValRat_factorial_lt_sq p (sixBlockLen n b) hlt
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    have hza : sixZero a ≤ 43 := by fin_cases a <;> decide
    have hlt : sixZero a * n < p ^ 2 := by
      have : sixZero a * n ≤ 43 * n := Nat.mul_le_mul_right n hza
      omega
    have hne : ((sixZero a * n).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [sq, padicValRat.mul hne hne, padicValRat_factorial_lt_sq p (sixZero a * n) hlt]
    ring

/-- Number of denominator factors congruent to `c_n - c (mod p)` across all 14 blocks. -/
def sixPoleClassCount (n p : ℕ) (c : ℤ) : ℕ :=
  ∑ b : Fin 14,
    ((range (sixBlockLen n b + 1)).filter
      (fun j : ℕ => (p : ℤ) ∣ ((sixBlockStart n b : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c)).card

/-- Number of numerator rising factors congruent to `c_n - c (mod p)` across all 10 blocks
(excluding the single central factor `X + c_n`). -/
def sixZeroClassCount (n p : ℕ) (c : ℤ) : ℕ :=
  ∑ a : Fin 5,
    (((range (sixZero a * n)).filter
        (fun j : ℕ => (p : ℤ) ∣ ((1 : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c)).card +
     ((range (sixZero a * n)).filter
        (fun j : ℕ => (p : ℤ) ∣ (((140 * n + 2 - sixZero a * n + j : ℕ) : ℤ) - (sixCenter n : ℤ)) + c)).card)

/-- `sixPoleClassCount` is invariant modulo `p`. -/
theorem sixPoleClassCount_mod (n p : ℕ) {c₁ c₂ : ℤ} (h : (p : ℤ) ∣ c₁ - c₂) :
    sixPoleClassCount n p c₁ = sixPoleClassCount n p c₂ := by
  unfold sixPoleClassCount
  apply Finset.sum_congr rfl; intro b _
  congr 1; ext j
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro _
  constructor
  · intro hd
    have heq : ((sixBlockStart n b : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c₂ =
        (((sixBlockStart n b : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c₁) - (c₁ - c₂) := by ring
    rw [heq]; exact dvd_sub hd h
  · intro hd
    have heq : ((sixBlockStart n b : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c₁ =
        (((sixBlockStart n b : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c₂) + (c₁ - c₂) := by ring
    rw [heq]; exact dvd_add hd h

/-- `sixPoleClassCount` is even under `c ↦ -c` (by reflection symmetry of each block). -/
theorem sixPoleClassCount_neg (n p : ℕ) (c : ℤ) :
    sixPoleClassCount n p (-c) = sixPoleClassCount n p c := by
  unfold sixPoleClassCount
  apply Finset.sum_congr rfl; intro b _
  have hob : sixOffset b ≤ 11 := by fin_cases b <;> decide
  have hsym : ∀ j ≤ sixBlockLen n b,
      ((sixBlockStart n b : ℤ) + ((sixBlockLen n b - j : ℕ) : ℤ) - (sixCenter n : ℤ)) + (-c) =
        -(((sixBlockStart n b : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c) := by
    intro j hj
    have hsub : ((sixBlockLen n b - j : ℕ) : ℤ) = (sixBlockLen n b : ℤ) - (j : ℤ) := Nat.cast_sub hj
    rw [hsub]
    unfold sixBlockStart sixBlockLen sixCenter
    have h1 : (50 - 2 * sixOffset b) * n + 2 * (sixOffset b * n) = 50 * n := by
      have : (50 - 2 * sixOffset b) + 2 * sixOffset b = 50 := by omega
      calc
        (50 - 2 * sixOffset b) * n + 2 * (sixOffset b * n)
            = ((50 - 2 * sixOffset b) + 2 * sixOffset b) * n := by ring
        _ = 50 * n := by rw [this]
    have h2 : (45 + sixOffset b) * n = 45 * n + sixOffset b * n := by ring
    omega
  apply Finset.card_bij (fun j _ => sixBlockLen n b - j)
  · intro j hj
    rw [Finset.mem_filter, mem_range] at hj ⊢
    have hjle : j ≤ sixBlockLen n b := by omega
    refine ⟨by omega, ?_⟩
    have h := hsym j hjle
    have hsym2 : ((sixBlockStart n b : ℤ) + ((sixBlockLen n b - j : ℕ) : ℤ) - (sixCenter n : ℤ)) + c =
        -(((sixBlockStart n b : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + (-c)) := by linarith
    rw [hsym2]
    exact dvd_neg.mpr hj.2
  · intro j₁ hj₁ j₂ hj₂ heq
    rw [Finset.mem_filter, mem_range] at hj₁ hj₂; omega
  · intro j hj
    rw [Finset.mem_filter, mem_range] at hj
    have hjle : j ≤ sixBlockLen n b := by omega
    refine ⟨sixBlockLen n b - j, ?_, by omega⟩
    rw [Finset.mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    rw [hsym j hjle]
    exact dvd_neg.mpr hj.2

/-- `sixZeroClassCount` is invariant modulo `p`. -/
theorem sixZeroClassCount_mod (n p : ℕ) {c₁ c₂ : ℤ} (h : (p : ℤ) ∣ c₁ - c₂) :
    sixZeroClassCount n p c₁ = sixZeroClassCount n p c₂ := by
  unfold sixZeroClassCount
  apply Finset.sum_congr rfl; intro a _
  congr 1
  · congr 1; ext j
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    constructor
    · intro hd
      have heq : ((1 : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c₂ =
          (((1 : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c₁) - (c₁ - c₂) := by ring
      rw [heq]; exact dvd_sub hd h
    · intro hd
      have heq : ((1 : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c₁ =
          (((1 : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c₂) + (c₁ - c₂) := by ring
      rw [heq]; exact dvd_add hd h
  · congr 1; ext j
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    constructor
    · intro hd
      have heq : (((140 * n + 2 - sixZero a * n + j : ℕ) : ℤ) - (sixCenter n : ℤ)) + c₂ =
          ((((140 * n + 2 - sixZero a * n + j : ℕ) : ℤ) - (sixCenter n : ℤ)) + c₁) - (c₁ - c₂) := by ring
      rw [heq]; exact dvd_sub hd h
    · intro hd
      have heq : (((140 * n + 2 - sixZero a * n + j : ℕ) : ℤ) - (sixCenter n : ℤ)) + c₁ =
          ((((140 * n + 2 - sixZero a * n + j : ℕ) : ℤ) - (sixCenter n : ℤ)) + c₂) + (c₁ - c₂) := by ring
      rw [heq]; exact dvd_add hd h

/-- `sixZeroClassCount` is even under `c ↦ -c` (reflection swaps left and right zero blocks). -/
theorem sixZeroClassCount_neg (n p : ℕ) (c : ℤ) :
    sixZeroClassCount n p (-c) = sixZeroClassCount n p c := by
  unfold sixZeroClassCount
  apply Finset.sum_congr rfl; intro a _
  have hza : sixZero a ≤ 43 := by fin_cases a <;> decide
  have hza_le : sixZero a * n ≤ 140 * n + 2 := by nlinarith
  have hswap : ∀ c₀ : ℤ,
      ((range (sixZero a * n)).filter
        (fun j : ℕ => (p : ℤ) ∣ ((1 : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + (-c₀))).card =
      ((range (sixZero a * n)).filter
        (fun j : ℕ => (p : ℤ) ∣ (((140 * n + 2 - sixZero a * n + j : ℕ) : ℤ) - (sixCenter n : ℤ)) + c₀)).card := by
    intro c₀
    apply Finset.card_bij (fun j _ => sixZero a * n - 1 - j)
    · intro j hj
      rw [Finset.mem_filter, mem_range] at hj ⊢
      refine ⟨by omega, ?_⟩
      have heq : (((140 * n + 2 - sixZero a * n + (sixZero a * n - 1 - j) : ℕ) : ℤ) -
          (sixCenter n : ℤ)) + c₀ = -(((1 : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + (-c₀)) := by
        unfold sixCenter
        have hnat : 140 * n + 2 - sixZero a * n + (sixZero a * n - 1 - j) + (1 + j) = 140 * n + 2 := by
          omega
        omega
      rw [heq]
      exact dvd_neg.mpr hj.2
    · intro j₁ hj₁ j₂ hj₂ heq
      rw [Finset.mem_filter, mem_range] at hj₁ hj₂; omega
    · intro j hj
      rw [Finset.mem_filter, mem_range] at hj
      refine ⟨sixZero a * n - 1 - j, ?_, by omega⟩
      rw [Finset.mem_filter, mem_range]
      refine ⟨by omega, ?_⟩
      have heq : ((1 : ℤ) + ((sixZero a * n - 1 - j : ℕ) : ℤ) - (sixCenter n : ℤ)) + (-c₀) =
          -((((140 * n + 2 - sixZero a * n + j : ℕ) : ℤ) - (sixCenter n : ℤ)) + c₀) := by
        unfold sixCenter
        have hnat : 140 * n + 2 - sixZero a * n + j + (1 + (sixZero a * n - 1 - j)) = 140 * n + 2 := by
          omega
        omega
      rw [heq]
      exact dvd_neg.mpr hj.2
  have h1 := hswap c
  have h2 := hswap (-c)
  rw [neg_neg] at h2
  omega

/-- Both class counts depend ONLY on the folded residue class `foldMod p hp c`. -/
theorem sixPoleClassCount_foldMod (n p : ℕ) (hp : 0 < p) (c : ℤ) :
    sixPoleClassCount n p c = sixPoleClassCount n p ((foldMod p hp c).val : ℤ) := by
  have hdvd := foldMod_congruence p hp c
  have h1 := sixPoleClassCount_mod n p hdvd
  unfold foldSign at h1
  split_ifs at h1
  · simpa using h1
  · simpa [sixPoleClassCount_neg] using h1

theorem sixZeroClassCount_foldMod (n p : ℕ) (hp : 0 < p) (c : ℤ) :
    sixZeroClassCount n p c = sixZeroClassCount n p ((foldMod p hp c).val : ℤ) := by
  have hdvd := foldMod_congruence p hp c
  have h1 := sixZeroClassCount_mod n p hdvd
  unfold foldSign at h1
  split_ifs at h1
  · simpa using h1
  · simpa [sixZeroClassCount_neg] using h1

/-- Any `L + 1` consecutive integers contain at most `L / p + 1` multiples of `p`. -/
private theorem consecutive_multiples_upper (p : ℕ) (hp : 0 < p) (b : ℤ) (L : ℕ) :
    ((range (L + 1)).filter (fun j : ℕ => (p : ℤ) ∣ b + (j : ℤ))).card ≤ L / p + 1 := by
  -- Map each multiple `j` to `j / p ∈ range (L / p + 1)`; distinct multiples in the same residue class differ by ≥ p
  have hinj : ∀ j₁ ∈ (range (L + 1)).filter (fun j : ℕ => (p : ℤ) ∣ b + (j : ℤ)),
      ∀ j₂ ∈ (range (L + 1)).filter (fun j : ℕ => (p : ℤ) ∣ b + (j : ℤ)),
      j₁ / p = j₂ / p → j₁ = j₂ := by
    intro j₁ hj₁ j₂ hj₂ hdiv
    have hd1 := (Finset.mem_filter.mp hj₁).2
    have hd2 := (Finset.mem_filter.mp hj₂).2
    have hdiff : (p : ℤ) ∣ (j₁ : ℤ) - (j₂ : ℤ) := by
      have : (j₁ : ℤ) - (j₂ : ℤ) = (b + (j₁ : ℤ)) - (b + (j₂ : ℤ)) := by ring
      rw [this]; exact dvd_sub hd1 hd2
    have h1 := Nat.div_add_mod j₁ p
    have h2 := Nat.div_add_mod j₂ p
    have hm1 : j₁ % p < p := Nat.mod_lt j₁ hp
    have hm2 : j₂ % p < p := Nat.mod_lt j₂ hp
    have hsub : (j₁ : ℤ) - (j₂ : ℤ) = ((j₁ % p : ℕ) : ℤ) - ((j₂ % p : ℕ) : ℤ) := by
      have h1Z : (p : ℤ) * ((j₁ / p : ℕ) : ℤ) + ((j₁ % p : ℕ) : ℤ) = (j₁ : ℤ) := by
        exact_mod_cast h1
      have h2Z : (p : ℤ) * ((j₂ / p : ℕ) : ℤ) + ((j₂ % p : ℕ) : ℤ) = (j₂ : ℤ) := by
        exact_mod_cast h2
      rw [hdiv] at h1Z
      linarith
    have hmp1 : ((j₁ % p : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast hm1
    have hmp2 : ((j₂ % p : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast hm2
    have hmp1' : (0 : ℤ) ≤ ((j₁ % p : ℕ) : ℤ) := Nat.cast_nonneg _
    have hmp2' : (0 : ℤ) ≤ ((j₂ % p : ℕ) : ℤ) := Nat.cast_nonneg _
    obtain ⟨t, ht⟩ := hdiff
    have ht0 : t = 0 := by nlinarith
    rw [ht0, mul_zero] at ht
    omega
  have himg : ((range (L + 1)).filter (fun j : ℕ => (p : ℤ) ∣ b + (j : ℤ))).image (· / p) ⊆
      range (L / p + 1) := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    have hjL : j ≤ L := Nat.lt_succ_iff.mp (mem_range.mp (Finset.mem_filter.mp hj).1)
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hjL))
  calc
    ((range (L + 1)).filter (fun j : ℕ => (p : ℤ) ∣ b + (j : ℤ))).card
        = (((range (L + 1)).filter (fun j : ℕ => (p : ℤ) ∣ b + (j : ℤ))).image (· / p)).card :=
          (Finset.card_image_of_injOn (fun j₁ hj₁ j₂ hj₂ h => hinj j₁ hj₁ j₂ hj₂ h)).symm
    _ ≤ (range (L / p + 1)).card := Finset.card_le_card himg
    _ = L / p + 1 := Finset.card_range _

/-- Coarse periodic cost `B_+(c) = max(0, 4 + #poles(c) - #zeros(c) - v_fact)` on folded class `c`. -/
def sixCoarsePeriodicCost (n p : ℕ) (c : Fin (p / 2 + 1)) : ℕ :=
  (4 + (sixPoleClassCount n p (c.val : ℤ) : ℤ) -
    (sixZeroClassCount n p (c.val : ℤ) : ℤ) - sixFactVal n p).toNat

/-- Unconditional upper bound `B_+(c) ≤ 18` for every folded class `c`. -/
theorem sixCoarsePeriodicCost_le_18 (n p : ℕ) (hp : 0 < p) (c : Fin (p / 2 + 1)) :
    sixCoarsePeriodicCost n p c ≤ 18 := by
  unfold sixCoarsePeriodicCost
  have hpoles : (sixPoleClassCount n p (c.val : ℤ) : ℤ) ≤
      (∑ b : Fin 14, ((sixBlockLen n b / p : ℕ) : ℤ)) + 14 := by
    unfold sixPoleClassCount
    push_cast
    have h14 : (∑ _b : Fin 14, (1 : ℤ)) = 14 := by simp
    rw [← h14, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro b _
    have hup := consecutive_multiples_upper p hp
      ((sixBlockStart n b : ℤ) - (sixCenter n : ℤ) + (c.val : ℤ)) (sixBlockLen n b)
    have hrew : ((range (sixBlockLen n b + 1)).filter
        (fun j : ℕ => (p : ℤ) ∣ ((sixBlockStart n b : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + (c.val : ℤ))).card =
        ((range (sixBlockLen n b + 1)).filter
          (fun j : ℕ => (p : ℤ) ∣ ((sixBlockStart n b : ℤ) - (sixCenter n : ℤ) + (c.val : ℤ)) + (j : ℤ))).card := by
      congr 1; ext j
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro _; constructor <;> intro h <;> (convert h using 1; ring)
    rw [hrew]
    exact_mod_cast hup
  have hzeros : 2 * (∑ a : Fin 5, ((sixZero a * n / p : ℕ) : ℤ)) ≤
      (sixZeroClassCount n p (c.val : ℤ) : ℤ) := by
    unfold sixZeroClassCount
    rw [Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_le_sum; intro a _
    rw [Nat.cast_add]
    have hL := consecutive_multiples_lower p hp (1 - (sixCenter n : ℤ) + (c.val : ℤ)) (sixZero a * n)
    have hR := consecutive_multiples_lower p hp
      (((140 * n + 2 - sixZero a * n : ℕ) : ℤ) - (sixCenter n : ℤ) + (c.val : ℤ)) (sixZero a * n)
    have hcnt : ∀ (b₀ : ℤ) (m : ℕ),
        (∑ j ∈ range m, if (p : ℤ) ∣ b₀ + (j : ℤ) then (1 : ℤ) else 0) =
        (((range m).filter (fun j : ℕ => (p : ℤ) ∣ b₀ + (j : ℤ))).card : ℤ) := by
      intro b₀ m
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hL' : ((sixZero a * n / p : ℕ) : ℤ) ≤
        (((range (sixZero a * n)).filter
          (fun j : ℕ => (p : ℤ) ∣ ((1 : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + (c.val : ℤ))).card : ℤ) := by
      rw [hcnt] at hL
      convert hL using 2
      congr 1; ext j
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro _; constructor <;> intro h <;> (convert h using 1; ring)
    have hR' : ((sixZero a * n / p : ℕ) : ℤ) ≤
        (((range (sixZero a * n)).filter
          (fun j : ℕ => (p : ℤ) ∣ (((140 * n + 2 - sixZero a * n + j : ℕ) : ℤ) - (sixCenter n : ℤ)) + (c.val : ℤ))).card : ℤ) := by
      rw [hcnt] at hR
      convert hR using 2
      congr 1; ext j
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro _; constructor <;> intro h <;> (convert h using 1; push_cast; ring)
    linarith
  unfold sixFactVal
  omega

/-! ## Local regular factor `Q_k`, refined slot costs `C_{k, r}` / `B_{k, a}` (eq. (6)) -/

/-- Multiplier-free local numerator `N_base(w) = taylor (-k) (C γ_norm * sixNumerator n)`. -/
def sixBaseLocalNum (n k : ℕ) : ℚ[X] :=
  taylor (-(k : ℚ)) (C (sixNormalization n) * sixNumerator n)

/-- Local regular quotient `Q_k(w) = N_base(w) / C_k(w) mod w^m`, independent of `(i, j)`. -/
def sixLocalRegularFactor (n k : ℕ) : ℚ[X] :=
  truncatedQuotient (sixBaseLocalNum n k) (sixLocalCofactor n k) (sixPoleOrder n k)

/-- Count `N_d` of nonzero denominator aliases (`u ∈ block_b \ {k}` with `p ∣ u - k`). -/
def sixDenomAliasCount (n p k : ℕ) : ℕ :=
  sixPoleClassCount n p ((sixCenter n : ℤ) - (k : ℤ)) - sixPoleOrder n k

/-- Count `N_z` of numerator rising aliases (`u ∈ zero_block` with `p ∣ u - k`). -/
def sixNumAliasCount (n p k : ℕ) : ℕ :=
  sixZeroClassCount n p ((sixCenter n : ℤ) - (k : ℤ))

/-- Constant-term valuation `v = v_fact + N_z - N_d` of the local regular factor (with central
factor estimated conservatively as an integral polynomial). -/
def sixSiteBaseVal (n p k : ℕ) : ℤ :=
  sixFactVal n p + (sixNumAliasCount n p k : ℤ) - (sixDenomAliasCount n p k : ℤ)

/-- Effective derivative-order loss `d'`: `min d N_z` if `N_d = 0`, else `d`. -/
def sixEffectiveOrderLoss (n p k d : ℕ) : ℕ :=
  if sixDenomAliasCount n p k = 0 then min d (sixNumAliasCount n p k) else d

/-- Paired harmonic denominator indicator `I_ℓ` (`ℓ = l + 1`):
- for `l` even (`ℓ` odd): `1` iff `p ≤ k - 40n - 1`;
- for `l` odd (`ℓ` even): `1` iff `(k' - 40n - 1) / p < (k - 40n - 1) / p`. -/
def sixHarmonicIndicator (n p k l : ℕ) : ℕ :=
  if Even l then
    if 1 ≤ (k - 40 * n - 1) / p then 1 else 0
  else
    if (sixReflectedPole n k - 40 * n - 1) / p < (k - 40 * n - 1) / p then 1 else 0

/-- Refined combined-order cost `C_{k, r}` from eq. (6) of `zeta6_irrationality_proof.tex`. -/
def sixRefinedOrderCost (n p k r : ℕ) : ℕ :=
  ((range (sixPoleOrder n k)).filter (fun l => r ≤ sixPoleOrder n k - 1 - l)).sup fun l =>
    let d := sixPoleOrder n k - 1 - l - r
    let d' := sixEffectiveOrderLoss n p k d
    let I := sixHarmonicIndicator n p k l
    ((r : ℤ) - sixSiteBaseVal n p k + (d' : ℤ) + ((l + 5 : ℕ) : ℤ) * (I : ℤ)).toNat

/-- Refined single-slot cost `B_{k, a} = max_{r ≥ a} C_{k, r}` from eq. (6). -/
def sixRefinedSlotCost (n p k a : ℕ) : ℕ :=
  ((range (sixPoleOrder n k)).filter (fun r => a ≤ r)).sup fun r =>
    sixRefinedOrderCost n p k r

theorem sixPoleOrder_le_poleClassCount (n p k : ℕ) :
    sixPoleOrder n k ≤ sixPoleClassCount n p ((sixCenter n : ℤ) - (k : ℤ)) := by
  have hord : sixPoleOrder n k =
      ∑ b : Fin 14,
        if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then 1 else 0 := by
    unfold sixPoleOrder sixPoleList
    rw [list_count_flatMap, ← Fin.sum_univ_def]
    apply Finset.sum_congr rfl; intro b _
    have hmem : k ∈ (List.range (sixBlockLen n b + 1)).map (fun j => sixBlockStart n b + j) ↔
        sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b := by
      simp only [List.mem_map, List.mem_range]
      constructor
      · rintro ⟨j, hj, rfl⟩; omega
      · rintro ⟨h1, h2⟩; exact ⟨k - sixBlockStart n b, by omega, by omega⟩
    change ((List.range (sixBlockLen n b + 1)).map (fun j => sixBlockStart n b + j)).count k = _
    split_ifs with h
    · exact List.count_eq_one_of_mem
        ((List.nodup_map_iff (fun _ _ h => Nat.add_left_cancel h)).mpr List.nodup_range)
        (hmem.mpr h)
    · exact List.count_eq_zero_of_not_mem (fun hk' => h (hmem.mp hk'))
  rw [hord]
  unfold sixPoleClassCount
  apply Finset.sum_le_sum; intro b _
  split_ifs with hcond
  · have hmem : k - sixBlockStart n b ∈ (range (sixBlockLen n b + 1)).filter
        (fun j : ℕ => (p : ℤ) ∣ ((sixBlockStart n b : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) +
          ((sixCenter n : ℤ) - (k : ℤ))) := by
      rw [Finset.mem_filter, mem_range]
      refine ⟨by omega, ?_⟩
      have h0 : ((sixBlockStart n b : ℤ) + ((k - sixBlockStart n b : ℕ) : ℤ) - (sixCenter n : ℤ)) +
          ((sixCenter n : ℤ) - (k : ℤ)) = 0 := by
        rw [Nat.cast_sub hcond.1]; ring
      rw [h0]; exact dvd_zero _
    exact Finset.card_pos.mpr ⟨k - sixBlockStart n b, hmem⟩
  · exact Nat.zero_le _

/-- Refined slot cost `B_{k, a}` is always dominated by the coarse periodic cost `B_+(foldMod(c_n - k))`. -/
theorem sixRefinedSlotCost_le_coarse (n p k a : ℕ) (hp : 0 < p) :
    sixRefinedSlotCost n p k a ≤
      sixCoarsePeriodicCost n p (foldMod p hp ((sixCenter n : ℤ) - (k : ℤ))) := by
  unfold sixRefinedSlotCost
  rw [Finset.sup_le_iff]
  intro r _
  unfold sixRefinedOrderCost
  rw [Finset.sup_le_iff]
  intro l hl
  have hrl : r ≤ sixPoleOrder n k - 1 - l := (Finset.mem_filter.mp hl).2
  have hl_lt : l < sixPoleOrder n k := mem_range.mp (Finset.mem_filter.mp hl).1
  unfold sixCoarsePeriodicCost
  rw [← sixPoleClassCount_foldMod n p hp, ← sixZeroClassCount_foldMod n p hp]
  have hd'_le : sixEffectiveOrderLoss n p k (sixPoleOrder n k - 1 - l - r) ≤
      sixPoleOrder n k - 1 - l - r := by
    unfold sixEffectiveOrderLoss
    split_ifs
    · exact Nat.min_le_left _ _
    · exact le_rfl
  have hI_le : sixHarmonicIndicator n p k l ≤ 1 := by
    unfold sixHarmonicIndicator
    split_ifs <;> omega
  have hord_le := sixPoleOrder_le_poleClassCount n p k
  unfold sixSiteBaseVal sixDenomAliasCount sixNumAliasCount
  have hmul_le : ((l + 5 : ℕ) : ℤ) * (sixHarmonicIndicator n p k l : ℤ) ≤ ((l + 5 : ℕ) : ℤ) := by
    have : (sixHarmonicIndicator n p k l : ℤ) ≤ 1 := by exact_mod_cast hI_le
    nlinarith
  dsimp only
  have hsub_cast : ((sixPoleClassCount n p ((sixCenter n : ℤ) - (k : ℤ)) - sixPoleOrder n k : ℕ) : ℤ) =
      (sixPoleClassCount n p ((sixCenter n : ℤ) - (k : ℤ)) : ℤ) - (sixPoleOrder n k : ℤ) :=
    Nat.cast_sub hord_le
  rw [hsub_cast]
  omega

theorem sixRefinedSlotCost_le_18 (n p k a : ℕ) (hp : 0 < p) :
    sixRefinedSlotCost n p k a ≤ 18 :=
  (sixRefinedSlotCost_le_coarse n p k a hp).trans (sixCoarsePeriodicCost_le_18 n p hp _)

/-! ## Valuation of the local regular factor `Q_k.coeff d` -/

/-- Key local numerator bound: for `p^2 > 140n + 2`, every `d`-th coefficient of
`sixBaseLocalNum n k` has valuation at least `v_fact + N_z - min d N_z`. -/
theorem sixBaseLocalNum_coeff_valAtLeast (n p : ℕ) [Fact p.Prime] (hn : 0 < n)
    (hsq : 140 * n + 2 < p ^ 2) (k : ℕ) (hk : k ∈ sixPoleSet n) (d : ℕ) :
    ValAtLeast p (sixFactVal n p + (sixNumAliasCount n p k : ℤ) -
      (min d (sixNumAliasCount n p k) : ℤ))
      ((sixBaseLocalNum n k).coeff d) := by
  have hp : p.Prime := Fact.out
  have hbnd := six_pole_address_bounds n k hk
  -- General lemma: multiplying `∏_{x ∈ s} (X + c_x)` where `c_x ∈ ℤ` has `coeff d` valuation `≥ #(p ∣ c_x) - min d #(p ∣ c_x)`
  have hlin_prod : ∀ {ι : Type} (s : Finset ι) (c : ι → ℤ),
      ∀ e : ℕ, ValAtLeast p ((((s.filter (fun x => (p : ℤ) ∣ c x)).card - e : ℕ) : ℤ))
        ((∏ x ∈ s, (X + C (c x : ℚ))).coeff e) := by
    intro ι s c
    classical
    induction s using Finset.induction_on with
    | empty =>
      intro e
      simp only [Finset.filter_empty, Finset.card_empty, Nat.zero_sub, Nat.cast_zero,
        Finset.prod_empty, coeff_one]
      split_ifs
      · exact valAtLeast_one p
      · exact valAtLeast_zero p 0
    | @insert a s ha ih =>
      intro e
      rw [Finset.prod_insert ha, coeff_mul]
      apply valAtLeast_sum
      intro uv huv
      have heq : uv.1 + uv.2 = e := Finset.mem_antidiagonal.mp huv
      have hcard : ((insert a s).filter (fun x => (p : ℤ) ∣ c x)).card =
          (if (p : ℤ) ∣ c a then 1 else 0) + (s.filter (fun x => (p : ℤ) ∣ c x)).card := by
        rw [Finset.filter_insert]
        split_ifs with hda
        · rw [Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.mp h).1)]; omega
        · omega
      cases h1 : uv.1 with
      | zero =>
        have huv2 : uv.2 = e := by omega
        rw [huv2, coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
        have hca : ValAtLeast p (if (p : ℤ) ∣ c a then 1 else 0) (c a : ℚ) := by
          split_ifs with hd
          · by_cases hc0 : c a = 0
            · rw [hc0]; exact Or.inl (by simp)
            · right
              rw [padicValRat.of_int, padicValInt]
              exact_mod_cast one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hc0)
                (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd))
          · exact valAtLeast_intCast p (c a)
        exact valAtLeast_mono (valAtLeast_mul hca (ih e)) (by
          rw [hcard]; by_cases hda : (p : ℤ) ∣ c a <;> simp only [hda, ite_true, ite_false] <;> omega)
      | succ u1 =>
        cases u1 with
        | zero =>
          have huv2 : uv.2 = e - 1 := by omega
          rw [huv2]
          simp only [zero_add, coeff_add, coeff_X_one, coeff_C_succ, add_zero, one_mul]
          exact valAtLeast_mono (ih (e - 1)) (by
            rw [hcard]; by_cases hda : (p : ℤ) ∣ c a <;> simp only [hda, ite_true, ite_false] <;> omega)
        | succ u1' =>
          have hne : (1 : ℕ) ≠ u1' + 1 + 1 := by omega
          simp only [coeff_add, coeff_X, coeff_C_succ, hne, ite_false, add_zero, zero_mul]
          exact valAtLeast_zero p _
  -- Apply to the 10 rising blocks in `sixNumerator n`
  have hnorm_val : ValAtLeast p (sixFactVal n p) (sixNormalization n) := by
    right; exact (padicValRat_sixNormalization_eq n p hn hsq).ge
  have hrew : sixBaseLocalNum n k =
      C (sixNormalization n) *
      (X + C (((70 * (n : ℤ) + 1 - (k : ℤ)) : ℤ) : ℚ)) *
      (∏ a : Fin 5,
        (∏ j ∈ range (sixZero a * n), (X + C (((1 + (j : ℤ) - (k : ℤ)) : ℤ) : ℚ))) *
        (∏ j ∈ range (sixZero a * n),
          (X + C ((((140 * n + 2 - sixZero a * n + j : ℕ) : ℤ) - (k : ℤ) : ℤ) : ℚ)))) := by
    unfold sixBaseLocalNum sixNumerator
    rw [taylor_mul, taylor_C, taylor_mul]
    have h1 : taylor (-(k : ℚ)) (X + C (70 * (n : ℚ) + 1)) =
        X + C (((70 * (n : ℤ) + 1 - (k : ℤ)) : ℤ) : ℚ) := by
      rw [map_add, taylor_X, taylor_C, add_assoc, ← C_add]; congr 2; push_cast; ring
    have hprod_t : ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ℚ[X]),
        taylor (-(k : ℚ)) (∏ i ∈ s, f i) = ∏ i ∈ s, taylor (-(k : ℚ)) (f i) := by
      intro ι _ s f
      induction s using Finset.induction_on with
      | empty => simp only [Finset.prod_empty]; rw [← C_1, taylor_C, C_1]
      | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, taylor_mul, ih]
    have hprod_a := hprod_t (Finset.univ : Finset (Fin 5))
      (fun a => rising 1 (sixZero a * n) * rising (140 * (n : ℚ) + 2 - ((sixZero a * n : ℕ) : ℚ)) (sixZero a * n))
    rw [h1, hprod_a, ← mul_assoc]
    congr 1
    apply Finset.prod_congr rfl; intro a _
    rw [taylor_mul, rising, rising, hprod_t (range _), hprod_t (range _)]
    congr 1
    · apply Finset.prod_congr rfl; intro j _
      rw [map_add, taylor_X, taylor_C, add_assoc, ← C_add]; congr 2; push_cast; ring
    · apply Finset.prod_congr rfl; intro j _
      rw [map_add, taylor_X, taylor_C, add_assoc, ← C_add]; congr 2
      have hza : sixZero a ≤ 43 := by fin_cases a <;> decide
      have hle : sixZero a * n ≤ 140 * n + 2 := by nlinarith
      rw [Nat.cast_add, Nat.cast_sub hle]; push_cast; ring
  -- Combine the 10 blocks as one product over a sigma finset
  let idxSet : Finset (Fin 5 × Bool × ℕ) :=
    Finset.univ.biUnion (fun a : Fin 5 =>
      ((range (sixZero a * n)).image (fun j => (a, false, j))) ∪
      ((range (sixZero a * n)).image (fun j => (a, true, j))))
  let c_idx : Fin 5 × Bool × ℕ → ℤ := fun x =>
    if !x.2.1 then (1 + (x.2.2 : ℤ) - (k : ℤ))
    else (((140 * n + 2 - sixZero x.1 * n + x.2.2 : ℕ) : ℤ) - (k : ℤ))
  have hprod_idx : (∏ a : Fin 5,
      (∏ j ∈ range (sixZero a * n), (X + C (((1 + (j : ℤ) - (k : ℤ)) : ℤ) : ℚ))) *
      (∏ j ∈ range (sixZero a * n),
        (X + C ((((140 * n + 2 - sixZero a * n + j : ℕ) : ℤ) - (k : ℤ) : ℤ) : ℚ)))) =
      ∏ x ∈ idxSet, (X + C (c_idx x : ℚ)) := by
    dsimp [idxSet]
    rw [Finset.prod_biUnion]
    · apply Finset.prod_congr rfl; intro a _
      rw [Finset.prod_union]
      · rw [Finset.prod_image (fun _ _ _ _ h => by injection h with _ h2; injection h2),
            Finset.prod_image (fun _ _ _ _ h => by injection h with _ h2; injection h2)]
        rfl
      · rw [Finset.disjoint_left]; intro x hx1 hx2
        obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp hx1
        obtain ⟨j₂, _, h⟩ := Finset.mem_image.mp hx2
        injection h with _ h2; injection h2 with h3; cases h3
    · intro a₁ _ a₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_union, Finset.mem_image] at hx1 hx2
      rcases hx1 with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
        rcases hx2 with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;>
        exact hne (congrArg Prod.fst h).symm
  have hcard_idx : (idxSet.filter (fun x => (p : ℤ) ∣ c_idx x)).card = sixNumAliasCount n p k := by
    dsimp [idxSet]
    rw [Finset.filter_biUnion, Finset.card_biUnion]
    · unfold sixNumAliasCount sixZeroClassCount
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.filter_union, Finset.card_union_of_disjoint]
      · congr 1
        · rw [Finset.filter_image, Finset.card_image_of_injective _
            (fun _ _ h => by injection h with _ h2; injection h2)]
          congr 1; ext j
          simp only [Finset.mem_filter, and_congr_right_iff]
          intro _; dsimp [c_idx]; constructor <;> intro h <;> (convert h using 1; ring)
        · rw [Finset.filter_image, Finset.card_image_of_injective _
            (fun _ _ h => by injection h with _ h2; injection h2)]
          congr 1; ext j
          simp only [Finset.mem_filter, and_congr_right_iff]
          intro _; dsimp [c_idx]; constructor <;> intro h <;> (convert h using 1; ring)
      · rw [Finset.disjoint_left]; intro x hx1 hx2
        have h1 := (Finset.mem_filter.mp hx1).1
        have h2 := (Finset.mem_filter.mp hx2).1
        obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨j₂, _, h⟩ := Finset.mem_image.mp h2
        injection h with _ h2'; injection h2' with h3; cases h3
    · intro a₁ _ a₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]; intro x hx1 hx2
      have h1 := (Finset.mem_filter.mp hx1).1
      have h2 := (Finset.mem_filter.mp hx2).1
      simp only [Finset.mem_union, Finset.mem_image] at h1 h2
      rcases h1 with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
        rcases h2 with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;>
        exact hne (congrArg Prod.fst h).symm
  rw [hrew, hprod_idx, mul_assoc, coeff_C_mul]
  have hmul_poly : ValAtLeast p (((sixNumAliasCount n p k - d : ℕ) : ℤ))
      (((X + C (((70 * (n : ℤ) + 1 - (k : ℤ)) : ℤ) : ℚ)) *
        ∏ x ∈ idxSet, (X + C (c_idx x : ℚ))).coeff d) := by
    rw [coeff_mul]
    apply valAtLeast_sum; intro uv huv
    have huv_eq : uv.1 + uv.2 = d := Finset.mem_antidiagonal.mp huv
    have hc1 := polyWeighted_linear_int_slope (p := p) (70 * (n : ℤ) + 1 - (k : ℤ)) 0 le_rfl uv.1
    have hc2 := hlin_prod idxSet c_idx uv.2
    rw [hcard_idx] at hc2
    exact valAtLeast_mono (valAtLeast_mul hc1 hc2) (by omega)
  exact valAtLeast_mono (valAtLeast_mul hnorm_val hmul_poly) (by omega)

/-- Exact constant-term valuation `v_p(sixLocalCofactor n k) = N_d` and slope-1 weight
for `p^2 > 140n + 2`. -/
theorem sixLocalCofactor_val_eq_aliasCount (n p : ℕ) [Fact p.Prime] (_hn : 0 < n)
    (hsq : 140 * n + 2 < p ^ 2) (k : ℕ) (hk : k ∈ sixPoleSet n) :
    (sixLocalCofactor n k).coeff 0 ≠ 0 ∧
    padicValRat p ((sixLocalCofactor n k).coeff 0) = (sixDenomAliasCount n p k : ℤ) ∧
    PolyWeighted p (sixLocalCofactor n k) (sixDenomAliasCount n p k : ℤ) 1 ∧
    PolyWeighted p (sixLocalCofactor n k) 0 0 := by
  have hp : p.Prime := Fact.out
  have hbnd := six_pole_address_bounds n k hk
  let s_b : Fin 14 → Finset ℕ := fun b =>
    if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then
      (range (sixBlockLen n b + 1)).erase (k - sixBlockStart n b)
    else range (sixBlockLen n b + 1)
  have hrew : sixLocalCofactor n k =
      ∏ b : Fin 14, ∏ j ∈ s_b b, (X + C (((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) :=
    sixLocalCofactor_eq_block_prod n k hk
  have hdist : ∀ (b : Fin 14), ∀ j ∈ s_b b,
      ((sixBlockStart n b + j : ℤ) - (k : ℤ)) ≠ 0 ∧
      ((sixBlockStart n b + j : ℤ) - (k : ℤ)).natAbs < p ^ 2 := by
    intro b j hj
    have hob : sixOffset b ≤ 11 := by fin_cases b <;> decide
    have hSb : 45 * n + 1 ≤ sixBlockStart n b ∧ sixBlockStart n b + sixBlockLen n b ≤ 95 * n + 1 := by
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
    dsimp [s_b] at hj
    split_ifs at hj with hcond
    · have hne := (Finset.mem_erase.mp hj).1
      have hlt := mem_range.mp (Finset.mem_erase.mp hj).2
      omega
    · have hlt := mem_range.mp hj
      omega
  have hval_lin : ∀ (b : Fin 14), ∀ j ∈ s_b b,
      padicValRat p ((((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)) =
        if (p : ℤ) ∣ (sixBlockStart n b + j : ℤ) - (k : ℤ) then 1 else 0 := by
    intro b j hj
    have hd := hdist b j hj
    rw [padicValRat.of_int, padicValInt]
    split_ifs with hdvd
    · have h1 : 1 ≤ padicValNat p ((sixBlockStart n b + j : ℤ) - (k : ℤ)).natAbs :=
        one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hd.1)
          (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdvd))
      have hlt2 : padicValNat p ((sixBlockStart n b + j : ℤ) - (k : ℤ)).natAbs < 2 := by
        by_contra hge
        push Not at hge
        have hp2dvd : p ^ 2 ∣ ((sixBlockStart n b + j : ℤ) - (k : ℤ)).natAbs :=
          (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hd.1)).mpr hge
        have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hd.1) hp2dvd
        omega
      omega
    · have hnd : ¬ p ∣ ((sixBlockStart n b + j : ℤ) - (k : ℤ)).natAbs := fun h =>
        hdvd (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
      exact_mod_cast padicValNat.eq_zero_of_not_dvd hnd
  have hsum_eq : (∑ b : Fin 14, ∑ j ∈ s_b b,
      (if (p : ℤ) ∣ (sixBlockStart n b + j : ℤ) - (k : ℤ) then (1 : ℤ) else 0)) =
      (sixDenomAliasCount n p k : ℤ) := by
    have hord_le := sixPoleOrder_le_poleClassCount n p k
    unfold sixDenomAliasCount
    rw [Nat.cast_sub hord_le]
    unfold sixPoleClassCount
    have hord_sum : (sixPoleOrder n k : ℤ) = ∑ b : Fin 14,
        if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then (1 : ℤ) else 0 := by
      have hord_nat : sixPoleOrder n k = ∑ b : Fin 14,
          if sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b then (1 : ℕ) else 0 := by
        unfold sixPoleOrder sixPoleList
        rw [list_count_flatMap, ← Fin.sum_univ_def]
        apply Finset.sum_congr rfl; intro b _
        have hmem : k ∈ (List.range (sixBlockLen n b + 1)).map (fun j => sixBlockStart n b + j) ↔
            sixBlockStart n b ≤ k ∧ k ≤ sixBlockStart n b + sixBlockLen n b := by
          simp only [List.mem_map, List.mem_range]
          constructor
          · rintro ⟨j, hj, rfl⟩; omega
          · rintro ⟨h1, h2⟩; exact ⟨k - sixBlockStart n b, by omega, by omega⟩
        change ((List.range (sixBlockLen n b + 1)).map (fun j => sixBlockStart n b + j)).count k = _
        split_ifs with h
        · exact List.count_eq_one_of_mem
            ((List.nodup_map_iff (fun _ _ h => Nat.add_left_cancel h)).mpr List.nodup_range)
            (hmem.mpr h)
        · exact List.count_eq_zero_of_not_mem (fun hk' => h (hmem.mp hk'))
      have := congrArg (Nat.cast (R := ℤ)) hord_nat
      push_cast at this
      simpa [apply_ite] using this
    rw [hord_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro b _
    have hfull : (((range (sixBlockLen n b + 1)).filter
        (fun j : ℕ => (p : ℤ) ∣ ((sixBlockStart n b : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) +
          ((sixCenter n : ℤ) - (k : ℤ)))).card : ℤ) =
        ∑ j ∈ range (sixBlockLen n b + 1),
          if (p : ℤ) ∣ (sixBlockStart n b + j : ℤ) - (k : ℤ) then (1 : ℤ) else 0 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1; congr 1; ext j
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro _; constructor <;> intro h <;> (convert h using 1; ring)
    rw [hfull]
    dsimp [s_b]
    split_ifs with hcond
    · have hmem : k - sixBlockStart n b ∈ range (sixBlockLen n b + 1) :=
        mem_range.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ hmem]
      have h0 : (sixBlockStart n b + ((k - sixBlockStart n b : ℕ) : ℤ)) - (k : ℤ) = 0 := by
        rw [Nat.cast_sub hcond.1]; ring
      rw [h0]
      simp
    · ring
  have hcoeff0 : (sixLocalCofactor n k).coeff 0 =
      ∏ b : Fin 14, ∏ j ∈ s_b b, (((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ) := by
    rw [hrew, Polynomial.coeff_zero_eq_eval_zero, eval_prod]
    apply Finset.prod_congr rfl; intro b _
    rw [eval_prod]
    apply Finset.prod_congr rfl; intro j _; simp
  have hne0 : (sixLocalCofactor n k).coeff 0 ≠ 0 := by
    rw [hcoeff0]
    exact Finset.prod_ne_zero_iff.mpr (fun b _ =>
      Finset.prod_ne_zero_iff.mpr (fun j hj => by exact_mod_cast (hdist b j hj).1))
  have hval0 : padicValRat p ((sixLocalCofactor n k).coeff 0) = (sixDenomAliasCount n p k : ℤ) := by
    have hpadic_prod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℚ),
        (∀ i ∈ s, f i ≠ 0) → padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
      intro ι s f hf
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha,
          padicValRat.mul (hf a (mem_insert_self _ _))
            (Finset.prod_ne_zero_iff.mpr (fun b hb => hf b (mem_insert_of_mem hb))),
          ih (fun b hb => hf b (mem_insert_of_mem hb))]
    have houter := hpadic_prod (Finset.univ : Finset (Fin 14))
      (fun b => ∏ j ∈ s_b b, (((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ))
      (fun b _ => Finset.prod_ne_zero_iff.mpr (fun j hj => by exact_mod_cast (hdist b j hj).1))
    rw [hcoeff0, houter, ← hsum_eq]
    apply Finset.sum_congr rfl; intro b _
    rw [hpadic_prod (s_b b) _ (fun j hj => by exact_mod_cast (hdist b j hj).1)]
    exact Finset.sum_congr rfl (fun j hj => hval_lin b j hj)
  have hwt1 : PolyWeighted p (sixLocalCofactor n k) (sixDenomAliasCount n p k : ℤ) 1 := by
    rw [hrew, ← hsum_eq]
    exact polyWeighted_prod (p := p) Finset.univ _ _ 1 (fun b _ =>
      polyWeighted_prod (p := p) (s_b b) _ _ 1 (fun j _ => polyWeighted_linear_int _))
  have hwt0 : PolyWeighted p (sixLocalCofactor n k) 0 0 := by
    rw [hrew]
    have houter := polyWeighted_prod (p := p) (Finset.univ : Finset (Fin 14))
      (fun b => ∏ j ∈ s_b b, (X + C (((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ)))
      (fun _ => (0 : ℤ)) 0 (fun b _ => by
        have hinner := polyWeighted_prod (p := p) (s_b b)
          (fun j => X + C (((sixBlockStart n b + j : ℤ) - (k : ℤ) : ℤ) : ℚ))
          (fun _ => (0 : ℤ)) 0
          (fun j _ => polyWeighted_linear_int_slope _ 0 le_rfl)
        rwa [Finset.sum_const_zero] at hinner)
    rwa [Finset.sum_const_zero] at houter
  exact ⟨hne0, hval0, hwt1, hwt0⟩

/-- **Local regular-factor valuation bound (§2.1)**: for `p^2 > 140n + 2` and `d < m(k)`,
`Q_k.coeff d` has valuation at least `v - d'` (`d' = min d N_z` if `N_d = 0`, else `d`). -/
theorem sixLocalRegularFactor_coeff_valAtLeast (n p : ℕ) [Fact p.Prime] (hn : 0 < n)
    (hsq : 140 * n + 2 < p ^ 2) (k : ℕ) (hk : k ∈ sixPoleSet n)
    (d : ℕ) (hd : d < sixPoleOrder n k) :
    ValAtLeast p (sixSiteBaseVal n p k - (sixEffectiveOrderLoss n p k d : ℤ))
      ((sixLocalRegularFactor n k).coeff d) := by
  obtain ⟨hC0_ne, hC0_val, hC_wt1, hC_wt0⟩ := sixLocalCofactor_val_eq_aliasCount n p hn hsq k hk
  have hdvd : X ^ sixPoleOrder n k ∣
      sixBaseLocalNum n k - sixLocalCofactor n k * sixLocalRegularFactor n k :=
    truncatedQuotient_dvd _ _ hC0_ne _
  unfold sixSiteBaseVal sixEffectiveOrderLoss
  by_cases hNd : sixDenomAliasCount n p k = 0
  · -- Case 1: `N_d = 0` (no denominator aliases); strong induction on `d`
    simp only [hNd, Nat.cast_zero, sub_zero, ite_true]
    rw [hNd] at hC0_val
    induction d using Nat.strong_induction_on with
    | h d ih =>
      have hzero : (sixBaseLocalNum n k - sixLocalCofactor n k * sixLocalRegularFactor n k).coeff d = 0 := by
        obtain ⟨R, hR⟩ := hdvd
        rw [hR, coeff_X_pow_mul']
        simp [show ¬ (sixPoleOrder n k ≤ d) by omega]
      rw [coeff_sub, sub_eq_zero, mul_comm, coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun a b => (sixLocalRegularFactor n k).coeff a * (sixLocalCofactor n k).coeff b),
        Finset.sum_range_succ, Nat.sub_self] at hzero
      have hQd : (sixLocalRegularFactor n k).coeff d =
          (1 / (sixLocalCofactor n k).coeff 0) *
            ((sixBaseLocalNum n k).coeff d -
              ∑ j ∈ range d, (sixLocalRegularFactor n k).coeff j * (sixLocalCofactor n k).coeff (d - j)) := by
        field_simp [hC0_ne]
        linarith
      rw [hQd]
      have hinv : ValAtLeast p 0 (1 / (sixLocalCofactor n k).coeff 0) := by
        right; rw [one_div, padicValRat.inv, hC0_val]; norm_num
      have hN := sixBaseLocalNum_coeff_valAtLeast n p hn hsq k hk d
      have hsum : ValAtLeast p (sixFactVal n p + (sixNumAliasCount n p k : ℤ) -
          (min d (sixNumAliasCount n p k) : ℤ))
          (∑ j ∈ range d, (sixLocalRegularFactor n k).coeff j * (sixLocalCofactor n k).coeff (d - j)) := by
        apply valAtLeast_sum; intro j hj
        have hjd : j < d := mem_range.mp hj
        have hQj := ih j hjd (hjd.trans hd)
        have hCj := hC_wt0 (d - j)
        exact valAtLeast_mono (valAtLeast_mul hQj hCj) (by
          have : min j (sixNumAliasCount n p k) ≤ min d (sixNumAliasCount n p k) :=
            min_le_min_right _ hjd.le
          omega)
      simpa using valAtLeast_mul hinv (valAtLeast_sub hN hsum)
  · -- Case 2: `N_d > 0`; use `truncated_division_weighted` at slope `1`
    simp only [hNd, ite_false]
    let cN : ℤ := sixFactVal n p + (sixNumAliasCount n p k : ℤ)
    let U : ℚ[X] := C (1 / (sixLocalCofactor n k).coeff 0) * sixLocalCofactor n k
    let p_pow : ℚ := (p : ℚ) ^ (-cN)
    have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hU0 : U.coeff 0 = 1 := by dsimp [U]; rw [coeff_C_mul, one_div_mul_cancel hC0_ne]
    have hU_wt : PolyWeighted p U 0 1 := by
      have hinv : ValAtLeast p (-(sixDenomAliasCount n p k : ℤ)) (1 / (sixLocalCofactor n k).coeff 0) := by
        right; rw [one_div, padicValRat.inv, hC0_val]
      have hm := polyWeighted_mul (polyWeighted_C (slope := 1) hinv) hC_wt1
      have h0 : -(sixDenomAliasCount n p k : ℤ) + (sixDenomAliasCount n p k : ℤ) = 0 := by ring
      rwa [h0] at hm
    -- Shift `N` by `p^(-cN)` to bring its base to `0`
    have hpz_val : ∀ z : ℤ, padicValRat p ((p : ℚ) ^ z) = z := by
      intro z
      have hp : p.Prime := Fact.out
      cases z with
      | ofNat k =>
        rw [Int.ofNat_eq_natCast, zpow_natCast]
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ, padicValRat.mul (pow_ne_zero k hpne) hpne, ih, padicValRat.self hp.one_lt]
          push_cast; ring
      | negSucc k =>
        rw [zpow_negSucc, padicValRat.inv]
        have hpos : padicValRat p ((p : ℚ) ^ (k + 1)) = ((k + 1 : ℕ) : ℤ) := by
          induction (k + 1) with
          | zero => simp
          | succ m ihm =>
            rw [pow_succ, padicValRat.mul (pow_ne_zero m hpne) hpne, ihm, padicValRat.self hp.one_lt]
            push_cast; ring
        rw [hpos]; omega
    let N' : ℚ[X] := C p_pow * sixBaseLocalNum n k
    let Q' : ℚ[X] := C (p_pow * (sixLocalCofactor n k).coeff 0) * sixLocalRegularFactor n k
    have hN'_wt : PolyWeighted p N' 0 1 := by
      intro r
      dsimp [N']
      rw [coeff_C_mul]
      have h1 : ValAtLeast p (-cN) p_pow := Or.inr (hpz_val (-cN)).ge
      have h2 := sixBaseLocalNum_coeff_valAtLeast n p hn hsq k hk r
      exact valAtLeast_mono (valAtLeast_mul h1 h2) (by
        have : min r (sixNumAliasCount n p k) ≤ r := Nat.min_le_left _ _
        dsimp [cN]; omega)
    have hdvd' : X ^ sixPoleOrder n k ∣ N' - Q' * U := by
      have heq : N' - Q' * U = C p_pow * (sixBaseLocalNum n k - sixLocalCofactor n k * sixLocalRegularFactor n k) := by
        dsimp [N', Q', U]
        have h1 : C (p_pow * (sixLocalCofactor n k).coeff 0) * C (1 / (sixLocalCofactor n k).coeff 0) = C p_pow := by
          rw [← map_mul]; congr 1; field_simp [hC0_ne]
        calc
          C p_pow * sixBaseLocalNum n k -
              C (p_pow * (sixLocalCofactor n k).coeff 0) * sixLocalRegularFactor n k *
                (C (1 / (sixLocalCofactor n k).coeff 0) * sixLocalCofactor n k)
              = C p_pow * sixBaseLocalNum n k -
                  (C (p_pow * (sixLocalCofactor n k).coeff 0) * C (1 / (sixLocalCofactor n k).coeff 0)) *
                    (sixLocalCofactor n k * sixLocalRegularFactor n k) := by ring
          _ = C p_pow * (sixBaseLocalNum n k - sixLocalCofactor n k * sixLocalRegularFactor n k) := by
                rw [h1]; ring
      rw [heq]
      exact dvd_mul_of_dvd_right hdvd _
    have hQ'd := truncated_division_weighted hU0 hU_wt hN'_wt hdvd' d hd
    have hQd_eq : (sixLocalRegularFactor n k).coeff d =
        ((p : ℚ) ^ cN / (sixLocalCofactor n k).coeff 0) * Q'.coeff d := by
      dsimp [Q', p_pow]
      rw [coeff_C_mul, ← mul_assoc]
      have h1 : ((p : ℚ) ^ cN / (sixLocalCofactor n k).coeff 0) * ((p : ℚ) ^ (-cN) * (sixLocalCofactor n k).coeff 0) = 1 := by
        have hpc : (p : ℚ) ^ cN * (p : ℚ) ^ (-cN) = 1 := by rw [← zpow_add₀ hpne, add_neg_cancel, zpow_zero]
        field_simp [hC0_ne]
        exact hpc
      rw [h1, one_mul]
    rw [hQd_eq]
    have hsc : ValAtLeast p (cN - (sixDenomAliasCount n p k : ℤ))
        ((p : ℚ) ^ cN / (sixLocalCofactor n k).coeff 0) := by
      right
      rw [padicValRat.div (zpow_ne_zero cN hpne) hC0_ne, hpz_val cN, hC0_val]
    exact valAtLeast_mono (valAtLeast_mul hsc hQ'd) (by dsimp [cN]; omega)

/-! ## Paired polynomial packets, `Y * W * Yᵀ` factorization, and Stage 2A master theorems -/

/-- Single-pole polynomial packet multiplying `sixPrincipalCoefficients n i j k l`. -/
def sixPolePacket (n k l : ℕ) : SixPolynomial :=
  MvPolynomial.C (((l + 4).choose 4 : ℚ) * (-harmonicCutoff (l + 5) (k - 40 * n - 1))) +
    ∑ s : Fin 6, if l = 2 + 2 * s.val then
      MvPolynomial.C (((l + 4).choose 4 : ℚ)) * MvPolynomial.X s else 0

/-- Reflection-paired polynomial packet for `k ≥ c_n` (unpaired at the fixed center `k = c_n`). -/
def sixPairedPacket (n k l : ℕ) : SixPolynomial :=
  if k = sixCenter n then
    if Even l then sixPolePacket n k l else 0
  else
    sixPolePacket n k l + MvPolynomial.C ((-1 : ℚ) ^ l) * sixPolePacket n (sixReflectedPole n k) l

/-- Valuation lower bound on `sixPairedPacket n k l` matching indicator `sixHarmonicIndicator n p k l`. -/
theorem sixPairedPacket_formalValAtLeast (n p : ℕ) [Fact p.Prime] (hn : 0 < n)
    (hsq : 140 * n + 2 < p ^ 2) (k : ℕ) (hk : k ∈ sixPoleSet n) (hkc : sixCenter n ≤ k) (l : ℕ) :
    FormalValAtLeast p (-(((l + 5 : ℕ) : ℤ) * (sixHarmonicIndicator n p k l : ℤ)))
      (sixPairedPacket n k l) := by
  have hp : p.Prime := Fact.out
  have hbnd := six_pole_address_bounds n k hk
  have hk_ref_le : sixReflectedPole n k ≤ k := by
    unfold sixReflectedPole sixCenter at *; omega
  have hharm_term : ∀ j : ℕ, 1 ≤ j → j < p ^ 2 →
      ValAtLeast p (if p ∣ j then -((l + 5 : ℕ) : ℤ) else 0) (1 / (j : ℚ) ^ (l + 5)) := by
    intro j hj1 hjlt
    have hjne : (j : ℚ) ≠ 0 := by positivity
    have hpow_val : padicValRat p ((j : ℚ) ^ (l + 5)) =
        ((l + 5 : ℕ) : ℤ) * (padicValNat p j : ℤ) := by
      induction (l + 5) with
      | zero => simp
      | succ m ihm =>
        rw [pow_succ, padicValRat.mul (pow_ne_zero m hjne) hjne, ihm, padicValRat.of_nat]
        push_cast; ring
    right
    rw [one_div, padicValRat.inv, hpow_val]
    split_ifs with hdvd
    · have hlt2 : padicValNat p j < 2 := by
        by_contra hge; push Not at hge
        have := Nat.le_of_dvd (by omega) ((padicValNat_dvd_iff_le (by omega)).mpr hge)
        omega
      have hle1 : (padicValNat p j : ℤ) ≤ 1 := by omega
      nlinarith
    · rw [padicValNat.eq_zero_of_not_dvd hdvd]; simp
  have hharm_le : ∀ N : ℕ, N < p ^ 2 →
      ValAtLeast p (if 1 ≤ N / p then -((l + 5 : ℕ) : ℤ) else 0) (harmonicCutoff (l + 5) N) := by
    intro N hNlt
    unfold harmonicCutoff
    apply valAtLeast_sum; intro j hj
    have hjN : j + 1 ≤ N := by have := mem_range.mp hj; omega
    have h1 := hharm_term (j + 1) (by omega) (hjN.trans_lt hNlt)
    have hcast : ((j : ℚ) + 1) = ((j + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [hcast]
    apply valAtLeast_mono h1
    by_cases hdiv : 1 ≤ N / p
    · by_cases hd : p ∣ j + 1 <;> simp only [hdiv, hd, ite_true, ite_false] <;> omega
    · by_cases hd : p ∣ j + 1
      · exfalso
        have hle : p ≤ j + 1 := Nat.le_of_dvd (by omega) hd
        have : 1 ≤ N / p := Nat.div_pos (hle.trans hjN) hp.pos
        omega
      · simp only [hdiv, hd, ite_false]; exact le_rfl
  unfold sixPairedPacket sixHarmonicIndicator
  by_cases hkc_eq : k = sixCenter n
  · simp only [hkc_eq, ite_true]
    by_cases hev : Even l
    · simp only [hev, ite_true]
      unfold sixPolePacket
      apply formalValAtLeast_add
      · apply formalValAtLeast_C
        have hch := valAtLeast_natCast p ((l + 4).choose 4)
        have hhc := valAtLeast_neg (hharm_le (sixCenter n - 40 * n - 1) (by unfold sixCenter; omega))
        have hm := valAtLeast_mul hch hhc
        exact valAtLeast_mono hm (by split_ifs <;> simp)
      · apply formalValAtLeast_sum; intro s _
        by_cases hs : l = 2 + 2 * s.val
        · simp only [hs, ite_true]
          exact formalValAtLeast_mono
            (formalValAtLeast_C_mul (valAtLeast_natCast p _) (formalValAtLeast_X p s))
            (by split_ifs <;> omega)
        · simp only [hs, ite_false]
          exact formalValAtLeast_zero p _
    · simp only [hev, ite_false]
      exact formalValAtLeast_zero p _
  · simp only [hkc_eq, ite_false]
    by_cases hev : Even l
    · simp only [hev, ite_true]
      have h1 : FormalValAtLeast p (-(((l + 5 : ℕ) : ℤ) * (if 1 ≤ (k - 40 * n - 1) / p then 1 else 0 : ℕ)))
          (sixPolePacket n k l) := by
        unfold sixPolePacket
        apply formalValAtLeast_add
        · apply formalValAtLeast_C
          have hm := valAtLeast_mul (valAtLeast_natCast p ((l + 4).choose 4))
            (valAtLeast_neg (hharm_le (k - 40 * n - 1) (by omega)))
          exact valAtLeast_mono hm (by split_ifs <;> simp)
        · apply formalValAtLeast_sum; intro s _
          by_cases hs : l = 2 + 2 * s.val
          · simp only [hs, ite_true]
            exact formalValAtLeast_mono
              (formalValAtLeast_C_mul (valAtLeast_natCast p _) (formalValAtLeast_X p s))
              (by split_ifs <;> omega)
          · simp only [hs, ite_false]
            exact formalValAtLeast_zero p _
      have h2 : FormalValAtLeast p (-(((l + 5 : ℕ) : ℤ) * (if 1 ≤ (k - 40 * n - 1) / p then 1 else 0 : ℕ)))
          (sixPolePacket n (sixReflectedPole n k) l) := by
        unfold sixPolePacket
        apply formalValAtLeast_add
        · apply formalValAtLeast_C
          have hdiv_le : (sixReflectedPole n k - 40 * n - 1) / p ≤ (k - 40 * n - 1) / p :=
            Nat.div_le_div_right (by omega)
          have hm := valAtLeast_mul (valAtLeast_natCast p ((l + 4).choose 4))
            (valAtLeast_neg (hharm_le (sixReflectedPole n k - 40 * n - 1) (by omega)))
          exact valAtLeast_mono hm (by split_ifs <;> omega)
        · apply formalValAtLeast_sum; intro s _
          by_cases hs : l = 2 + 2 * s.val
          · simp only [hs, ite_true]
            exact formalValAtLeast_mono
              (formalValAtLeast_C_mul (valAtLeast_natCast p _) (formalValAtLeast_X p s))
              (by split_ifs <;> omega)
          · simp only [hs, ite_false]
            exact formalValAtLeast_zero p _
      rw [hev.neg_one_pow, map_one, one_mul]
      exact formalValAtLeast_add h1 h2
    · simp only [hev, ite_false]
      have hodd : Odd l := Nat.not_even_iff_odd.mp hev
      rw [hodd.neg_one_pow]
      -- When `l` is odd, all `X s` terms vanish (`l ≠ 2 + 2s`), leaving only the harmonic difference!
      have hdiff_eq : sixPolePacket n k l + MvPolynomial.C (-1 : ℚ) * sixPolePacket n (sixReflectedPole n k) l =
          MvPolynomial.C (-(((l + 4).choose 4 : ℚ) *
            (harmonicCutoff (l + 5) (k - 40 * n - 1) -
              harmonicCutoff (l + 5) (sixReflectedPole n k - 40 * n - 1)))) := by
        unfold sixPolePacket
        have hnoX : (∑ s : Fin 6, if l = 2 + 2 * s.val then
            MvPolynomial.C (((l + 4).choose 4 : ℚ)) * MvPolynomial.X s else 0) = 0 := by
          apply Finset.sum_eq_zero; intro s _
          have hne : l ≠ 2 + 2 * s.val := by
            obtain ⟨t, rfl⟩ := hodd; omega
          simp [hne]
        rw [hnoX, add_zero, add_zero, ← map_mul, ← map_add]
        congr 1; ring
      rw [hdiff_eq]
      apply formalValAtLeast_C
      apply valAtLeast_neg
      have hch := valAtLeast_natCast p ((l + 4).choose 4)
      have hNle : sixReflectedPole n k - 40 * n - 1 ≤ k - 40 * n - 1 := by omega
      have hsub_harm : harmonicCutoff (l + 5) (k - 40 * n - 1) -
          harmonicCutoff (l + 5) (sixReflectedPole n k - 40 * n - 1) =
          ∑ j ∈ Finset.Ico (sixReflectedPole n k - 40 * n - 1) (k - 40 * n - 1),
            1 / ((j : ℚ) + 1) ^ (l + 5) := by
        unfold harmonicCutoff
        rw [← Nat.Ico_zero_eq_range, ← Nat.Ico_zero_eq_range,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le _) hNle]
        ring
      rw [hsub_harm]
      have hsum_val : ValAtLeast p
          (-(((l + 5 : ℕ) : ℤ) *
            (if (sixReflectedPole n k - 40 * n - 1) / p < (k - 40 * n - 1) / p then (1 : ℕ) else 0 : ℤ)))
          (∑ j ∈ Finset.Ico (sixReflectedPole n k - 40 * n - 1) (k - 40 * n - 1),
            1 / ((j : ℚ) + 1) ^ (l + 5)) := by
        apply valAtLeast_sum; intro j hj
        rw [Finset.mem_Ico] at hj
        have h1 := hharm_term (j + 1) (by omega) (by omega)
        have hcast : ((j : ℚ) + 1) = ((j + 1 : ℕ) : ℚ) := by push_cast; ring
        rw [hcast]
        apply valAtLeast_mono h1
        by_cases hlt : (sixReflectedPole n k - 40 * n - 1) / p < (k - 40 * n - 1) / p
        · by_cases hd : p ∣ j + 1 <;> simp only [hlt, hd, ite_true, ite_false] <;> omega
        · by_cases hd : p ∣ j + 1
          · exfalso
            obtain ⟨q, hq⟩ := hd
            have hq_gt : (sixReflectedPole n k - 40 * n - 1) / p < q := by
              have : sixReflectedPole n k - 40 * n - 1 < q * p := by nlinarith
              exact (Nat.div_lt_iff_lt_mul hp.pos).mpr (by nlinarith)
            have hq_le : q ≤ (k - 40 * n - 1) / p := by
              have : q * p ≤ k - 40 * n - 1 := by nlinarith
              exact (Nat.le_div_iff_mul_le hp.pos).mpr (by nlinarith)
            omega
          · simp only [hlt, hd, ite_false]; exact le_rfl
      simpa using valAtLeast_mul hch hsum_val

/-! ## Exact column indexing `(t, a) ∈ Fin (25n + 1) × Fin 14` and `Y * W * Yᵀ` identity -/

/-- Total number of slot columns across the `25n + 1` upper-half poles (`14` slots each). -/
def sixSlotCount (n : ℕ) : ℕ := (25 * n + 1) * 14

/-- Canonical bijection `Fin (25n + 1) × Fin 14 ≃ Fin (sixSlotCount n)`. -/
def sixSlotEquiv (n : ℕ) : Fin (25 * n + 1) × Fin 14 ≃ Fin (sixSlotCount n) where
  toFun p := ⟨14 * p.1.val + p.2.val, by unfold sixSlotCount; have := p.1.isLt; have := p.2.isLt; omega⟩
  invFun u := (⟨u.val / 14, by unfold sixSlotCount at u; have := u.isLt; omega⟩,
               ⟨u.val % 14, Nat.mod_lt _ (by decide)⟩)
  left_inv p := by ext <;> (dsimp; have := p.2.isLt; omega)
  right_inv u := by ext; dsimp; omega

/-- Pole address `k_t = 70n + 1 + t` for `t : Fin (25n + 1)`. -/
def sixHalfPole (n : ℕ) (t : Fin (25 * n + 1)) : ℕ := sixCenter n + t.val

/-- Centered coordinate `x_u = c_n - k_t = -t` for slot `u`. -/
def sixSlotCenter (n : ℕ) (u : Fin (sixSlotCount n)) : ℤ :=
  -((sixSlotEquiv n).symm u).1.val

/-- Jet order `a_u ∈ {0, ..., 13}` for slot `u`. -/
def sixSlotDeg (n : ℕ) (u : Fin (sixSlotCount n)) : ℕ :=
  ((sixSlotEquiv n).symm u).2.val

/-- Refined slot cost `B_u = sixRefinedSlotCost n p k_t a_u`. -/
def sixSlotCost (n p : ℕ) (u : Fin (sixSlotCount n)) : ℕ :=
  let ta := (sixSlotEquiv n).symm u
  sixRefinedSlotCost n p (sixHalfPole n ta.1) ta.2.val

/-- Block-diagonal paired weight matrix `W` indexed by `Fin (sixSlotCount n)`. -/
def sixSlotWeightMatrix (n p : ℕ) :
    Matrix (Fin (sixSlotCount n)) (Fin (sixSlotCount n)) SixPolynomial :=
  fun u v =>
    let ta := (sixSlotEquiv n).symm u
    let sb := (sixSlotEquiv n).symm v
    if ta.1 = sb.1 then
      let k := sixHalfPole n ta.1
      let m := sixPoleOrder n k
      let a := ta.2.val
      let b := sb.2.val
      ∑ l : Fin m,
        if a + b ≤ m - 1 - l.val then
          MvPolynomial.C ((sixLocalRegularFactor n k).coeff (m - 1 - l.val - (a + b)) /
            (p : ℚ) ^ (a + b)) * sixPairedPacket n k l.val
        else 0
    else 0

theorem sixHalfPole_mem (n : ℕ) (_hn : 0 < n) (t : Fin (25 * n + 1)) :
    sixHalfPole n t ∈ sixPoleSet n := by
  have ht := t.isLt
  unfold sixPoleSet sixPoleList
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_map, List.mem_range]
  refine ⟨0, 25 * n + t.val, ?_, ?_⟩
  · dsimp [sixOffset]; omega
  · dsimp [sixOffset, sixHalfPole, sixCenter]; omega

/-- **Exact `Y * W * Yᵀ` factorization of `sixMatrix n`** for any `n ≥ 1` and `p > 0`. -/
theorem sixMatrix_eq_evalJet_mul_weight (n p : ℕ) (hn : 0 < n) (hp : 0 < p) :
    sixMatrix n =
      (evalJetMatrix p (rank n) (sixSlotCount n) (sixSlotCenter n) (sixSlotDeg n)).map MvPolynomial.C *
      sixSlotWeightMatrix n p *
      ((evalJetMatrix p (rank n) (sixSlotCount n) (sixSlotCenter n) (sixSlotDeg n)).map MvPolynomial.C).transpose := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  -- Step 1: express `sixMatrix n i j` as sum of `sixPrincipalCoefficients * sixPolePacket`
  have hmat_pole : ∀ i j : Fin (rank n),
      sixMatrix n i j =
        ∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
          MvPolynomial.C (sixPrincipalCoefficients n i j k l) * sixPolePacket n k l.val := by
    intro i j
    unfold sixMatrix affineEntry sixPolePacket sixMomentConstant sixZetaCoefficient sixOrderCoefficient
    simp_rw [mul_add, Finset.sum_add_distrib]
    congr 1
    · simp only [← map_mul, ← map_sum]
      congr 1
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro k _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro l _; ring
    · have hswap : (∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k), ∑ s : Fin 6,
          MvPolynomial.C (sixPrincipalCoefficients n i j k l) *
            (if l.val = 2 + 2 * s.val then MvPolynomial.C (((l.val + 4).choose 4 : ℚ)) * MvPolynomial.X s else 0)) =
          ∑ s : Fin 6, ∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
            if l.val = 2 + 2 * s.val then
              MvPolynomial.C (sixPrincipalCoefficients n i j k l * (((2 + 2 * s.val + 4).choose 4 : ℚ))) * MvPolynomial.X s
            else 0 := by
        calc
          _ = ∑ k ∈ sixPoleSet n, ∑ s : Fin 6, ∑ l : Fin (sixPoleOrder n k),
                MvPolynomial.C (sixPrincipalCoefficients n i j k l) *
                  (if l.val = 2 + 2 * s.val then MvPolynomial.C (((l.val + 4).choose 4 : ℚ)) * MvPolynomial.X s else 0) := by
                apply Finset.sum_congr rfl; intro k _; exact Finset.sum_comm
          _ = ∑ s : Fin 6, ∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
                MvPolynomial.C (sixPrincipalCoefficients n i j k l) *
                  (if l.val = 2 + 2 * s.val then MvPolynomial.C (((l.val + 4).choose 4 : ℚ)) * MvPolynomial.X s else 0) :=
                Finset.sum_comm
          _ = _ := by
                apply Finset.sum_congr rfl; intro s _
                apply Finset.sum_congr rfl; intro k _
                apply Finset.sum_congr rfl; intro l _
                split_ifs with hl
                · rw [hl, ← mul_assoc, ← map_mul]
                · simp
      simp_rw [Finset.mul_sum]
      rw [hswap]
      apply Finset.sum_congr rfl; intro s _
      rw [map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro k _
      rw [map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro l _
      split_ifs <;> simp [map_mul, mul_comm]
  -- Step 2: fold the pole sum onto `t : Fin (25 * n + 1)` using reflection symmetry
  have hmat_half : ∀ i j : Fin (rank n),
      sixMatrix n i j =
        ∑ t : Fin (25 * n + 1), ∑ l : Fin (sixPoleOrder n (sixHalfPole n t)),
          MvPolynomial.C (sixPrincipalCoefficients n i j (sixHalfPole n t) l) *
            sixPairedPacket n (sixHalfPole n t) l.val := by
    intro i j
    rw [hmat_pole i j]
    -- Partition `sixPoleSet n` into `< c_n`, `= c_n`, `> c_n`
    let S_lt := (sixPoleSet n).filter (fun k => k < sixCenter n)
    let S_ge := (sixPoleSet n).filter (fun k => sixCenter n ≤ k)
    have hsplit : (∑ k ∈ sixPoleSet n, ∑ l : Fin (sixPoleOrder n k),
        MvPolynomial.C (sixPrincipalCoefficients n i j k l) * sixPolePacket n k l.val) =
        (∑ k ∈ S_ge, ∑ l : Fin (sixPoleOrder n k),
          MvPolynomial.C (sixPrincipalCoefficients n i j k l) * sixPolePacket n k l.val) +
        (∑ k ∈ S_lt, ∑ l : Fin (sixPoleOrder n k),
          MvPolynomial.C (sixPrincipalCoefficients n i j k l) * sixPolePacket n k l.val) := by
      have h := Finset.sum_filter_add_sum_filter_not (sixPoleSet n) (fun k => sixCenter n ≤ k)
        (fun k => ∑ l : Fin (sixPoleOrder n k),
          MvPolynomial.C (sixPrincipalCoefficients n i j k l) * sixPolePacket n k l.val)
      simpa only [not_le] using h.symm
    -- Reindex `S_lt` to `S_gt := S_ge.erase (sixCenter n)` via `sixReflectedPole n`
    have hlt_eq : (∑ k ∈ S_lt, ∑ l : Fin (sixPoleOrder n k),
        MvPolynomial.C (sixPrincipalCoefficients n i j k l) * sixPolePacket n k l.val) =
        ∑ k ∈ S_ge, if k = sixCenter n then 0 else
          ∑ l : Fin (sixPoleOrder n k),
            MvPolynomial.C (sixPrincipalCoefficients n i j k l) *
              (MvPolynomial.C ((-1 : ℚ) ^ l.val) * sixPolePacket n (sixReflectedPole n k) l.val) := by
      symm
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
      apply Finset.sum_bij (fun k _ => sixReflectedPole n k)
      · intro k hk
        rw [Finset.mem_filter] at hk
        have hkge := Finset.mem_filter.mp hk.1
        rw [Finset.mem_filter]
        refine ⟨(six_pole_mem_reflection n k).mpr hkge.1, ?_⟩
        unfold sixReflectedPole sixCenter at *; omega
      · intro k₁ hk₁ k₂ hk₂ heq
        unfold sixReflectedPole at heq
        have hb1 := six_pole_address_bounds n k₁ (Finset.mem_filter.mp (Finset.mem_filter.mp hk₁).1).1
        have hb2 := six_pole_address_bounds n k₂ (Finset.mem_filter.mp (Finset.mem_filter.mp hk₂).1).1
        omega
      · intro k hk
        rw [Finset.mem_filter] at hk
        have hb := six_pole_address_bounds n k hk.1
        refine ⟨sixReflectedPole n k, ?_, six_pole_reflection_involutive n k hk.1⟩
        rw [Finset.mem_filter, Finset.mem_filter]
        refine ⟨⟨(six_pole_mem_reflection n k).mpr hk.1, ?_⟩, ?_⟩
        · unfold sixReflectedPole sixCenter at *; omega
        · unfold sixReflectedPole sixCenter at *; omega
      · intro k hk
        have hkmem : k ∈ sixPoleSet n := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1
        have hord := six_pole_order_reflection n k
        apply Fintype.sum_equiv (finCongr hord.symm)
        intro l
        have href := six_principal_coefficients_reflection n i j k hkmem l
        simp only [finCongr_apply, Fin.val_cast]
        rw [href, map_mul]
        have hsq1 : (MvPolynomial.C ((-1 : ℚ) ^ l.val) : SixPolynomial) *
            MvPolynomial.C ((-1 : ℚ) ^ l.val) = 1 := by
          rw [← map_mul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, map_one]
        calc
          MvPolynomial.C ((-1 : ℚ) ^ l.val) *
              MvPolynomial.C (sixPrincipalCoefficients n i j (sixReflectedPole n k) (l.cast hord.symm)) *
              (MvPolynomial.C ((-1 : ℚ) ^ l.val) * sixPolePacket n (sixReflectedPole n k) l.val)
              = (MvPolynomial.C ((-1 : ℚ) ^ l.val) * MvPolynomial.C ((-1 : ℚ) ^ l.val)) *
                  (MvPolynomial.C (sixPrincipalCoefficients n i j (sixReflectedPole n k) (l.cast hord.symm)) *
                    sixPolePacket n (sixReflectedPole n k) l.val) := by ring
          _ = MvPolynomial.C (sixPrincipalCoefficients n i j (sixReflectedPole n k) (l.cast hord.symm)) *
                sixPolePacket n (sixReflectedPole n k) l.val := by rw [hsq1, one_mul]
    rw [hsplit, hlt_eq, ← Finset.sum_add_distrib]
    -- Reindex `S_ge` by `t : Fin (25 * n + 1)` via `sixHalfPole n t`
    symm
    apply Finset.sum_bij (fun (t : Fin (25 * n + 1)) _ => sixHalfPole n t)
    · intro t _
      rw [Finset.mem_filter]
      exact ⟨sixHalfPole_mem n hn t, by unfold sixHalfPole; omega⟩
    · intro t₁ _ t₂ _ heq
      ext; unfold sixHalfPole at heq; omega
    · intro k hk
      rw [Finset.mem_filter] at hk
      have hb := six_pole_address_bounds n k hk.1
      refine ⟨⟨k - sixCenter n, by unfold sixCenter at *; omega⟩, Finset.mem_univ _, ?_⟩
      unfold sixHalfPole; dsimp; omega
    · intro t _
      by_cases hkc : sixHalfPole n t = sixCenter n
      · unfold sixPairedPacket
        simp only [hkc, ite_true, add_zero]
        apply Finset.sum_congr rfl; intro l _
        by_cases hev : Even l.val
        · simp [hev]
        · simp only [hev, ite_false, mul_zero]
          have hodd : Odd l.val := Nat.not_even_iff_odd.mp hev
          have href := six_principal_coefficients_reflection n i j (sixHalfPole n t)
            (sixHalfPole_mem n hn t) l
          have hfix : sixReflectedPole n (sixHalfPole n t) = sixHalfPole n t := by
            rw [hkc]; unfold sixReflectedPole sixCenter; omega
          have hfix_coef : ∀ (k₁ k₂ : ℕ) (hk : k₁ = k₂)
              (l₁ : Fin (sixPoleOrder n k₁)) (l₂ : Fin (sixPoleOrder n k₂)),
              l₁.val = l₂.val →
              sixPrincipalCoefficients n i j k₁ l₁ = sixPrincipalCoefficients n i j k₂ l₂ := by
            rintro k₁ _ rfl l₁ l₂ hval; congr 1; exact Fin.ext hval
          have hcoef0 : sixPrincipalCoefficients n i j (sixHalfPole n t) l = 0 := by
            have h1 : sixPrincipalCoefficients n i j (sixHalfPole n t) l =
                -sixPrincipalCoefficients n i j (sixHalfPole n t) l := by
              rw [hodd.neg_one_pow, neg_one_mul,
                hfix_coef _ _ hfix (l.cast _) l (Fin.val_cast _ _)] at href
              exact href
            linarith
          simp [hcoef0]
      · unfold sixPairedPacket
        simp only [hkc, ite_false]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro l _
        rw [mul_add]
  -- Step 3: express `sixPrincipalCoefficients n i j k l` via `sixLocalRegularFactor` and `evenBasis` Taylor jets
  have hpc_expand : ∀ (i j : Fin (rank n)) (t : Fin (25 * n + 1))
      (l : Fin (sixPoleOrder n (sixHalfPole n t))),
      sixPrincipalCoefficients n i j (sixHalfPole n t) l =
        ∑ a : Fin 14, ∑ b : Fin 14,
          (if a.val + b.val ≤ sixPoleOrder n (sixHalfPole n t) - 1 - l.val then
            (sixLocalRegularFactor n (sixHalfPole n t)).coeff
              (sixPoleOrder n (sixHalfPole n t) - 1 - l.val - (a.val + b.val)) /
              (p : ℚ) ^ (a.val + b.val)
          else 0) *
          ((p : ℚ) ^ a.val * taylorCoeff (evenBasis i.val) (-(t.val : ℤ) : ℚ) a.val) *
          ((p : ℚ) ^ b.val * taylorCoeff (evenBasis j.val) (-(t.val : ℤ) : ℚ) b.val) := by
    intro i j t l
    let k := sixHalfPole n t
    let m := sixPoleOrder n k
    have hk := sixHalfPole_mem n hn t
    have hm14 : m ≤ 14 := six_pole_order_le n k
    have hC0_ne : (sixLocalCofactor n k).coeff 0 ≠ 0 := by
      rw [sixLocalCofactor_eq_block_prod n k hk, Polynomial.coeff_zero_eq_eval_zero, eval_prod]
      apply Finset.prod_ne_zero_iff.mpr; intro b _
      rw [eval_prod]
      apply Finset.prod_ne_zero_iff.mpr; intro u hu
      simp only [eval_add, eval_X, eval_C, zero_add]
      split_ifs at hu with hcond
      · have hne := (Finset.mem_erase.mp hu).1
        have hlt := mem_range.mp (Finset.mem_erase.mp hu).2
        have : (sixBlockStart n b + u : ℤ) - (k : ℤ) ≠ 0 := by omega
        exact_mod_cast this
      · have hlt := mem_range.mp hu
        have : (sixBlockStart n b + u : ℤ) - (k : ℤ) ≠ 0 := by omega
        exact_mod_cast this
    -- Congruence `sixLocalPrincipal ≡ sixLocalRegularFactor * E_i * E_j (mod X^m)`
    have hq_eq : (sixLocalPrincipal n i j k).coeff (m - 1 - l.val) =
        (sixLocalRegularFactor n k *
          (taylor (-(t.val : ℤ) : ℚ) (evenBasis i.val) *
           taylor (-(t.val : ℤ) : ℚ) (evenBasis j.val))).coeff (m - 1 - l.val) := by
      have hdvd1 := sixLocalPrincipal_congruence n i j k hk
      have hdvdQ := truncatedQuotient_dvd (sixBaseLocalNum n k) (sixLocalCofactor n k) hC0_ne m
      have hmult_eq : taylor (-(k : ℚ)) (centeredMultiplier n i.val j.val) =
          taylor (-(t.val : ℤ) : ℚ) (evenBasis i.val) *
          taylor (-(t.val : ℤ) : ℚ) (evenBasis j.val) := by
        unfold centeredMultiplier
        rw [taylor_apply, taylor_apply, taylor_apply, comp_assoc, mul_comp]
        have harg : (X + C (70 * (n : ℚ) + 1)).comp (X + C (-(k : ℚ))) =
            X + C (-(t.val : ℤ) : ℚ) := by
          simp only [add_comp, X_comp, C_comp, add_assoc, ← C_add]
          congr 2; dsimp [k, sixHalfPole, sixCenter]; push_cast; ring
        rw [harg]
      have hnum_eq : sixLocalNumerator n i j k =
          sixBaseLocalNum n k *
            (taylor (-(t.val : ℤ) : ℚ) (evenBasis i.val) *
             taylor (-(t.val : ℤ) : ℚ) (evenBasis j.val)) := by
        unfold sixLocalNumerator sixBaseLocalNum
        rw [taylor_mul, hmult_eq]
      have hdvd2 : X ^ m ∣ sixLocalCofactor n k *
          (sixLocalPrincipal n i j k -
            sixLocalRegularFactor n k *
              (taylor (-(t.val : ℤ) : ℚ) (evenBasis i.val) *
               taylor (-(t.val : ℤ) : ℚ) (evenBasis j.val))) := by
        have heq : sixLocalCofactor n k *
            (sixLocalPrincipal n i j k -
              sixLocalRegularFactor n k *
                (taylor (-(t.val : ℤ) : ℚ) (evenBasis i.val) *
                 taylor (-(t.val : ℤ) : ℚ) (evenBasis j.val))) =
            (sixBaseLocalNum n k - sixLocalCofactor n k * sixLocalRegularFactor n k) *
              (taylor (-(t.val : ℤ) : ℚ) (evenBasis i.val) *
               taylor (-(t.val : ℤ) : ℚ) (evenBasis j.val)) -
            (sixLocalNumerator n i j k - sixLocalPrincipal n i j k * sixLocalCofactor n k) := by
          rw [hnum_eq]; ring
        rw [heq]
        exact dvd_sub (dvd_mul_of_dvd_left hdvdQ _) hdvd1
      have hlt_m : l.val < m := l.isLt
      have hdm : m - 1 - l.val < m := by omega
      have h0 := coeff_eq_of_X_pow_dvd_mul hC0_ne hdvd2 (m - 1 - l.val) hdm
      rw [coeff_sub, sub_eq_zero] at h0
      exact h0
    have hpc_eq : sixPrincipalCoefficients n i j k l =
        (sixLocalPrincipal n i j k).coeff (m - 1 - l.val) := by
      have h := sixLocalPrincipal_coeff n i j k l
      have hidx : m - (l.val + 1) = m - 1 - l.val := by omega
      rw [hidx] at h
      exact h.symm
    rw [hpc_eq, hq_eq]
    -- Expand triple convolution `(Q * (E_i * E_j)).coeff d`
    let d := m - 1 - l.val
    have hlt_m : l.val < m := l.isLt
    have hd14 : d < 14 := by omega
    have hconv : (sixLocalRegularFactor n k *
        (taylor (-(t.val : ℤ) : ℚ) (evenBasis i.val) *
         taylor (-(t.val : ℤ) : ℚ) (evenBasis j.val))).coeff d =
        ∑ a : Fin 14, ∑ b : Fin 14,
          if a.val + b.val ≤ d then
            (sixLocalRegularFactor n k).coeff (d - (a.val + b.val)) *
              taylorCoeff (evenBasis i.val) (-(t.val : ℤ) : ℚ) a.val *
              taylorCoeff (evenBasis j.val) (-(t.val : ℤ) : ℚ) b.val
          else 0 := by
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun u v => (sixLocalRegularFactor n k).coeff u *
          (taylor (-(t.val : ℤ) : ℚ) (evenBasis i.val) *
           taylor (-(t.val : ℤ) : ℚ) (evenBasis j.val)).coeff v)]
      -- Reindex `u ∈ range (d + 1)` by `r = d - u`
      have hrev : (∑ u ∈ range (d + 1), (sixLocalRegularFactor n k).coeff u *
          (taylor (-(t.val : ℤ) : ℚ) (evenBasis i.val) *
           taylor (-(t.val : ℤ) : ℚ) (evenBasis j.val)).coeff (d - u)) =
          ∑ r ∈ range (d + 1), (sixLocalRegularFactor n k).coeff (d - r) *
            ∑ a ∈ range (r + 1),
              taylorCoeff (evenBasis i.val) (-(t.val : ℤ) : ℚ) a *
              taylorCoeff (evenBasis j.val) (-(t.val : ℤ) : ℚ) (r - a) := by
        apply Finset.sum_bij (fun u _ => d - u)
        · intro u hu; exact mem_range.mpr (by have := mem_range.mp hu; omega)
        · intro u₁ hu₁ u₂ hu₂ h; have := mem_range.mp hu₁; have := mem_range.mp hu₂; omega
        · intro r hr; exact ⟨d - r, mem_range.mpr (by have := mem_range.mp hr; omega),
            by have := mem_range.mp hr; omega⟩
        · intro u hu
          have hud : u ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hu)
          rw [show d - (d - u) = u by omega, coeff_mul]
          congr 1
          exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => taylorCoeff (evenBasis i.val) (-(t.val : ℤ) : ℚ) a *
              taylorCoeff (evenBasis j.val) (-(t.val : ℤ) : ℚ) b) (d - u)
      rw [hrev]
      simp_rw [Finset.mul_sum]
      -- Reindex `(r, a)` with `a ≤ r ≤ d` to `(a, b) : Fin 14 × Fin 14` with `a + b ≤ d`
      symm
      rw [← Fintype.sum_prod_type', ← Finset.sum_filter]
      trans (∑ ra ∈ (range (d + 1)).sigma (fun r => range (r + 1)),
          (sixLocalRegularFactor n k).coeff (d - ra.1) *
            (taylorCoeff (evenBasis i.val) (-(t.val : ℤ) : ℚ) ra.2 *
             taylorCoeff (evenBasis j.val) (-(t.val : ℤ) : ℚ) (ra.1 - ra.2)))
      · apply Finset.sum_bij (fun (ab : Fin 14 × Fin 14) _ =>
          (⟨ab.1.val + ab.2.val, ab.1.val⟩ : Σ _r : ℕ, ℕ))
        · intro ab hab
          have hle := (Finset.mem_filter.mp hab).2
          rw [Finset.mem_sigma]
          dsimp only
          exact ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩
        · intro ab₁ _ ab₂ _ h
          have h1 : ab₁.1.val + ab₁.2.val = ab₂.1.val + ab₂.2.val := congrArg Sigma.fst h
          have h2 : ab₁.1.val = ab₂.1.val := by
            have := congrArg Sigma.snd h
            simpa using this
          exact Prod.ext (Fin.ext h2) (Fin.ext (by omega))
        · intro ra hra
          rw [Finset.mem_sigma, mem_range, mem_range] at hra
          refine ⟨(⟨ra.2, by omega⟩, ⟨ra.1 - ra.2, by omega⟩), ?_, ?_⟩
          · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by dsimp; omega⟩
          · ext
            · dsimp; omega
            · dsimp; exact HEq.rfl
        · intro ab hab
          dsimp only
          rw [show ab.1.val + ab.2.val - ab.1.val = ab.2.val by omega]
          ring
      · exact Finset.sum_sigma (range (d + 1)) (fun r => range (r + 1)) _
    rw [hconv]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    split_ifs
    · have hpa : (p : ℚ) ^ a.val ≠ 0 := pow_ne_zero _ hpq
      have hpb : (p : ℚ) ^ b.val ≠ 0 := pow_ne_zero _ hpq
      rw [pow_add]
      field_simp
      dsimp only [d, m, k]
      ring
    · ring
  -- Step 4: assemble into `Y * W * Yᵀ`
  apply Matrix.ext; intro i j
  rw [hmat_half i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  -- Reindex `u, v : Fin (sixSlotCount n)` by `sixSlotEquiv n`
  have hreindex : (∑ v : Fin (sixSlotCount n), ∑ u : Fin (sixSlotCount n),
      MvPolynomial.C (evalJetMatrix p (rank n) (sixSlotCount n) (sixSlotCenter n) (sixSlotDeg n) i u) *
      sixSlotWeightMatrix n p u v *
      MvPolynomial.C (evalJetMatrix p (rank n) (sixSlotCount n) (sixSlotCenter n) (sixSlotDeg n) j v)) =
      ∑ t : Fin (25 * n + 1), ∑ b : Fin 14, ∑ a : Fin 14,
        MvPolynomial.C (evalJetMatrix p (rank n) (sixSlotCount n) (sixSlotCenter n) (sixSlotDeg n) i
          (sixSlotEquiv n (t, a))) *
        sixSlotWeightMatrix n p (sixSlotEquiv n (t, a)) (sixSlotEquiv n (t, b)) *
        MvPolynomial.C (evalJetMatrix p (rank n) (sixSlotCount n) (sixSlotCenter n) (sixSlotDeg n) j
          (sixSlotEquiv n (t, b))) := by
    rw [← Equiv.sum_comp (sixSlotEquiv n), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro t _
    apply Finset.sum_congr rfl; intro b _
    rw [← Equiv.sum_comp (sixSlotEquiv n), Fintype.sum_prod_type, Finset.sum_eq_single t]
    · intro t' _ hne
      apply Finset.sum_eq_zero; intro a _
      unfold sixSlotWeightMatrix
      simp [Equiv.symm_apply_apply, hne]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [hreindex]
  apply Finset.sum_congr rfl; intro t _
  simp_rw [hpc_expand i j t, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro a _
  unfold sixSlotWeightMatrix evalJetMatrix sixSlotCenter sixSlotDeg
  simp only [Equiv.symm_apply_apply, ite_true, Finset.mul_sum, Finset.sum_mul]
  apply Fintype.sum_equiv (finCongr (by rw [Equiv.symm_apply_apply]))
  intro l
  simp only [finCongr_apply, Fin.val_cast]
  have hcast_t : (((-(t.val : ℤ)) : ℤ) : ℚ) = -(t.val : ℚ) := by push_cast; ring
  have hcast_t' : (-(t.val : ℤ) : ℚ) = -(t.val : ℚ) := by push_cast; ring
  rw [hcast_t, hcast_t']
  split_ifs
  · simp only [map_mul]
    ring
  · simp

/-- Doubled Gauss valuation bound on `sixSlotWeightMatrix n p`:
`2 * v_p^G(W u v) ≥ -(B u + B v)`. -/
theorem sixSlotWeightMatrix_doubled_bound (n p : ℕ) [Fact p.Prime] (hn : 0 < n)
    (hsq : 140 * n + 2 < p ^ 2) (u v : Fin (sixSlotCount n)) :
    DoubledFormalValAtLeast p (-((sixSlotCost n p u + sixSlotCost n p v : ℕ) : ℤ))
      (sixSlotWeightMatrix n p u v) := by
  have hp : p.Prime := Fact.out
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold sixSlotWeightMatrix
  dsimp only
  split_ifs with ht
  · let ta := (sixSlotEquiv n).symm u
    let sb := (sixSlotEquiv n).symm v
    let k := sixHalfPole n ta.1
    let m := sixPoleOrder n k
    let a := ta.2.val
    let b := sb.2.val
    have hk := sixHalfPole_mem n hn ta.1
    have hkc : sixCenter n ≤ k := by unfold k sixHalfPole; omega
    -- Show `FormalValAtLeast p (-C_{k, a + b}) (W u v)`, then double!
    have hformal : FormalValAtLeast p (-(sixRefinedOrderCost n p k (a + b) : ℤ))
        (∑ l : Fin m,
          if a + b ≤ m - 1 - l.val then
            MvPolynomial.C ((sixLocalRegularFactor n k).coeff (m - 1 - l.val - (a + b)) /
              (p : ℚ) ^ (a + b)) * sixPairedPacket n k l.val
          else 0) := by
      apply formalValAtLeast_sum; intro l _
      split_ifs with hle
      · let d := m - 1 - l.val - (a + b)
        have hdm : d < m := by have := l.isLt; omega
        have hQ := sixLocalRegularFactor_coeff_valAtLeast n p hn hsq k hk d hdm
        have hpow_val : padicValRat p ((p : ℚ) ^ (a + b)) = ((a + b : ℕ) : ℤ) := by
          induction (a + b) with
          | zero => simp
          | succ r ihr =>
            rw [pow_succ, padicValRat.mul (pow_ne_zero r hpne) hpne, ihr, padicValRat.self hp.one_lt]
            push_cast; ring
        have hdiv : ValAtLeast p
            (sixSiteBaseVal n p k - (sixEffectiveOrderLoss n p k d : ℤ) - ((a + b : ℕ) : ℤ))
            ((sixLocalRegularFactor n k).coeff d / (p : ℚ) ^ (a + b)) := by
          by_cases hq0 : (sixLocalRegularFactor n k).coeff d = 0
          · rw [hq0, zero_div]; exact valAtLeast_zero p _
          · right
            have hval := hQ.resolve_left hq0
            rw [padicValRat.div hq0 (pow_ne_zero _ hpne), hpow_val]
            linarith
        have hpkt := sixPairedPacket_formalValAtLeast n p hn hsq k hk hkc l.val
        have hprod := formalValAtLeast_C_mul hdiv hpkt
        -- Compare with `sixRefinedOrderCost n p k (a + b)`
        have hle_sup : ((a + b : ℕ) : ℤ) - sixSiteBaseVal n p k +
            (sixEffectiveOrderLoss n p k d : ℤ) +
            ((l.val + 5 : ℕ) : ℤ) * (sixHarmonicIndicator n p k l.val : ℤ) ≤
            (sixRefinedOrderCost n p k (a + b) : ℤ) := by
          have hl_mem : l.val ∈ (range m).filter (fun l' => a + b ≤ m - 1 - l') :=
            Finset.mem_filter.mpr ⟨mem_range.mpr l.isLt, hle⟩
          have hsup := Finset.le_sup (f := fun l' =>
            (((a + b : ℕ) : ℤ) - sixSiteBaseVal n p k +
              (sixEffectiveOrderLoss n p k (m - 1 - l' - (a + b)) : ℤ) +
              ((l' + 5 : ℕ) : ℤ) * (sixHarmonicIndicator n p k l' : ℤ)).toNat) hl_mem
          have hsupZ : ((((a + b : ℕ) : ℤ) - sixSiteBaseVal n p k +
              (sixEffectiveOrderLoss n p k d : ℤ) +
              ((l.val + 5 : ℕ) : ℤ) * (sixHarmonicIndicator n p k l.val : ℤ)).toNat : ℤ) ≤
              (sixRefinedOrderCost n p k (a + b) : ℤ) := by
            exact_mod_cast hsup
          omega
        exact formalValAtLeast_mono hprod (by linarith)
      · exact formalValAtLeast_zero p _
    have hdoub := doubledFormalValAtLeast_of_formal hformal
    apply doubledFormalValAtLeast_mono hdoub
    -- Verify `2 * C_{k, a + b} ≤ B_{k, a} + B_{k, b}` (or `W u v = 0` if `a + b ≥ m`)
    by_cases hab : a + b < m
    · have hle_a : sixRefinedOrderCost n p k (a + b) ≤ sixSlotCost n p u := by
        unfold sixSlotCost sixRefinedSlotCost
        change sixRefinedOrderCost n p k (a + b) ≤
          ((range m).filter (fun r => a ≤ r)).sup (fun r => sixRefinedOrderCost n p k r)
        exact Finset.le_sup (f := fun r => sixRefinedOrderCost n p k r)
          (Finset.mem_filter.mpr ⟨mem_range.mpr hab, by omega⟩)
      have hle_b : sixRefinedOrderCost n p k (a + b) ≤ sixSlotCost n p v := by
        unfold sixSlotCost sixRefinedSlotCost
        change sixRefinedOrderCost n p k (a + b) ≤
          ((range (sixPoleOrder n (sixHalfPole n sb.1))).filter (fun r => b ≤ r)).sup
            (fun r => sixRefinedOrderCost n p (sixHalfPole n sb.1) r)
        rw [← ht]
        exact Finset.le_sup (f := fun r => sixRefinedOrderCost n p k r)
          (Finset.mem_filter.mpr ⟨mem_range.mpr hab, by omega⟩)
      omega
    · -- When `a + b ≥ m`, every `l : Fin m` fails `a + b ≤ m - 1 - l.val`, so `C_{k, a+b} = 0`!
      have hC0 : sixRefinedOrderCost n p k (a + b) = 0 := by
        unfold sixRefinedOrderCost
        have hemp : (range m).filter (fun l => a + b ≤ m - 1 - l) = ∅ := by
          ext l; simp only [Finset.mem_filter, mem_range, Finset.notMem_empty, iff_false]
          omega
        change ((range m).filter (fun l => a + b ≤ m - 1 - l)).sup _ = 0
        rw [hemp, Finset.sup_empty]; rfl
      rw [hC0]; omega
  · exact doubledFormalValAtLeast_zero p _

/-! ## Stage 2A Master Prime-Valuation Interfaces -/

/-- **Stage 2A Master Theorem 1 (Folded Joint Bound)** for mid/high primes (`p^2 > 140n + 2`):
for any `q : ℕ`, bounds `-v_p(sixPrimitiveScalar n)` by `2 * rowPenalty + ∑_{j=1}^{18} min(15n, cap_j)`. -/
theorem sixPrimitiveScalar_folded_joint_bound (n p : ℕ) [Fact p.Prime]
    (hn : 0 < n) (hsq : 140 * n + 2 < p ^ 2) (q : ℕ) :
    let hp := (Fact.out : p.Prime).pos;
    let clsSet : Fin (p / 2 + 1) → Finset (Fin (sixSlotCount n)) :=
      fun c => Finset.univ.filter (fun u => foldMod p hp (sixSlotCenter n u) = c);
    let slotPairs : Finset (Fin (p / 2 + 1) × Fin (sixSlotCount n)) :=
      Finset.univ.filter (fun cr => cr.2.val < (clsSet cr.1).card);
    let inc : Fin (p / 2 + 1) × Fin (sixSlotCount n) → ℤ := fun cr =>
      (nthDescWeight (clsSet cr.1) (sixSlotCost n p) cr.2.val : ℤ) -
        2 * ((cr.2.val - q : ℕ) : ℤ);
    -padicValRat p (sixPrimitiveScalar n) ≤
      2 * (sixRowPenalty (rank n) p q : ℤ) +
        ∑ j ∈ Finset.Icc 1 18,
          (min (rank n) (slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℤ) := by
  intro hp clsSet slotPairs inc
  have h2h : 2 * rank n < p ^ 2 := by unfold rank; omega
  have hformal := folded_joint_formalValAtLeast (p := p) h2h
    (sixSlotCenter n) (sixSlotDeg n) (sixSlotWeightMatrix n p) (sixSlotCost n p)
    (fun u => sixRefinedSlotCost_le_18 n p _ _ hp)
    (sixSlotWeightMatrix_doubled_bound n p hn hsq) q
  rw [← sixMatrix_eq_evalJet_mul_weight n p hn hp] at hformal
  have hnonpos : -(2 * (sixRowPenalty (rank n) p q : ℤ) +
      ∑ j ∈ Finset.Icc 1 18,
        (min (rank n) (slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℤ)) ≤ 0 := by
    have h1 : (0 : ℤ) ≤ 2 * (sixRowPenalty (rank n) p q : ℤ) := by positivity
    have h2 : (0 : ℤ) ≤ ∑ j ∈ Finset.Icc 1 18,
        (min (rank n) (slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℤ) :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    linarith
  have hge := sixPrimitiveScalar_padicValRat_ge_of_formal_nonpos n p _ hnonpos hformal
  linarith

/-- **Stage 2A Master Theorem 1b (Unfolded Bound)** for primes with `p^2 > 140n + 2`. -/
theorem sixPrimitiveScalar_unfolded_bound (n p : ℕ) [Fact p.Prime]
    (hn : 0 < n) (hsq : 140 * n + 2 < p ^ 2) (q : ℕ) :
    let inc : Fin (sixSlotCount n) → ℤ := fun u =>
      (sixSlotCost n p u : ℤ) - 2 * ((sixSlotDeg n u - q : ℕ) : ℤ);
    -padicValRat p (sixPrimitiveScalar n) ≤
      2 * (sixRowPenalty (rank n) p q : ℤ) +
        ∑ j ∈ Finset.Icc 1 18,
          (min (rank n) ((Finset.univ : Finset (Fin (sixSlotCount n))).filter
            (fun u => (j : ℤ) ≤ inc u)).card : ℤ) := by
  intro inc
  have hp := (Fact.out : p.Prime).pos
  have h2h : 2 * rank n < p ^ 2 := by unfold rank; omega
  have hformal := unfolded_formalValAtLeast (p := p) h2h
    (sixSlotCenter n) (sixSlotDeg n) (sixSlotWeightMatrix n p) (sixSlotCost n p)
    (fun u => sixRefinedSlotCost_le_18 n p _ _ hp)
    (sixSlotWeightMatrix_doubled_bound n p hn hsq) q
  rw [← sixMatrix_eq_evalJet_mul_weight n p hn hp] at hformal
  have hnonpos : -(2 * (sixRowPenalty (rank n) p q : ℤ) +
      ∑ j ∈ Finset.Icc 1 18,
        (min (rank n) ((Finset.univ : Finset (Fin (sixSlotCount n))).filter
          (fun u => (j : ℤ) ≤ inc u)).card : ℤ)) ≤ 0 := by
    have h1 : (0 : ℤ) ≤ 2 * (sixRowPenalty (rank n) p q : ℤ) := by positivity
    have h2 : (0 : ℤ) ≤ ∑ j ∈ Finset.Icc 1 18,
        (min (rank n) ((Finset.univ : Finset (Fin (sixSlotCount n))).filter
          (fun u => (j : ℤ) ≤ inc u)).card : ℤ) :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    linarith
  have hge := sixPrimitiveScalar_padicValRat_ge_of_formal_nonpos n p _ hnonpos hformal
  linarith

/-- **Stage 2A Master Theorem 2 (Coarse Periodic Single-Line Bound)** for the slim periodic
small-prime range (`√(140n + 2) < p < (7/100) * 50n`):
`-v_p(sixPrimitiveScalar n) ≤ (⌊2h / p⌋ + 5) * ∑_{c=0}^{(p-1)/2} B_+(c)`. -/
theorem sixPrimitiveScalar_periodic_coarse_bound (n p : ℕ) [Fact p.Prime]
    (hn : 0 < n) (hsq : 140 * n + 2 < p ^ 2) :
    -padicValRat p (sixPrimitiveScalar n) ≤
      ((2 * rank n / p + 5 : ℕ) : ℤ) *
        ∑ c : Fin (p / 2 + 1), (sixCoarsePeriodicCost n p c : ℤ) := by
  have hp := (Fact.out : p.Prime).pos
  have h2h : 2 * rank n < p ^ 2 := by unfold rank; omega
  have hdom : ∀ u : Fin (sixSlotCount n),
      sixSlotCost n p u ≤ sixCoarsePeriodicCost n p (foldMod p hp (sixSlotCenter n u)) := by
    intro u
    unfold sixSlotCost sixSlotCenter
    have heq : (sixCenter n : ℤ) - (sixHalfPole n ((sixSlotEquiv n).symm u).1 : ℤ) =
        -(((sixSlotEquiv n).symm u).1.val : ℤ) := by
      unfold sixHalfPole; push_cast; ring
    rw [← heq]
    exact sixRefinedSlotCost_le_coarse n p _ _ hp
  have hformal := folded_periodic_coarse_formalValAtLeast (p := p) h2h
    (sixSlotCenter n) (sixSlotDeg n) (sixSlotWeightMatrix n p) (sixSlotCost n p)
    (sixCoarsePeriodicCost n p) hdom
    (fun c => sixCoarsePeriodicCost_le_18 n p hp c)
    (sixSlotWeightMatrix_doubled_bound n p hn hsq)
  rw [← sixMatrix_eq_evalJet_mul_weight n p hn hp] at hformal
  have hnonpos : -(((2 * rank n / p + 5 : ℕ) : ℤ) *
      ∑ c : Fin (p / 2 + 1), (sixCoarsePeriodicCost n p c : ℤ)) ≤ 0 := by
    apply neg_nonpos.mpr
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => by positivity))
  have hge := sixPrimitiveScalar_padicValRat_ge_of_formal_nonpos n p _ hnonpos hformal
  linarith

end OddZetaSix
