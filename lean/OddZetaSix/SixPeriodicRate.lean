import OddZetaSix.SixFoldedCertCore
import OddZetaSix.SixLocalSlots
import OddZetaSix.SixPNTBridge
import OddZetaSix.PeriodicData.Shard0
import OddZetaSix.PeriodicData.Shard1
import OddZetaSix.PeriodicData.Shard2
import OddZetaSix.PeriodicData.Shard3
import OddZetaSix.PeriodicData.Shard4
import OddZetaSix.PeriodicData.Shard5
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Periodic Small-Prime Rate Bound (`ε n < p ≤ 3.5 n`, `C₀ ≤ 552/1000`)

Certifies the exact periodic coarse cost bound on `(1/10000) * n < p ≤ (7/2) * n`:
1. Exact discrete count lemma: for every prime `p` with `p^2 > 140n + 2` and every
   checked `PeriodicPiece` containing `τ = (n % p) / p`,
   `∑ c : Fin (p / 2 + 1), sixCoarsePeriodicCost n p c ≤ (p / 2) * (a0 + a1 * τ) + 486`.
2. Combines `sixPrimitiveScalar_periodic_coarse_bound` with the 12-period pure-rational
   left-endpoint weight `t⁻² + (6 t³)⁻¹` and the 3-line telescoping tail bound for
   `k ∈ [12, 10000)`.
3. Assembles the 6 certified periodic shards (`PeriodicData.Shard0`..`Shard5`, 1,808 pieces
   covering `[0, 1]`) and proves
   `sixPeriodicBand_rate_le : ∀ δ > 0, ∀ᶠ n in atTop, sixBandPrimeCost n (1/10000) (7/2) / sixNorm n ≤ 552 / 1000 + δ`.

Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

noncomputable section
set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix

open Finset Filter MeasureTheory
open OddZetaSix.CertCore
open scoped BigOperators

/-! ## Elementary integer interval-multiples count and ceiling-division helpers -/

/-- Exact number of integers `j ∈ range (L + 1)` with `p ∣ a + j`:
equals `⌊(a + L) / p⌋ - ⌊(a - 1) / p⌋` using Euclidean `Int.ediv`. -/
theorem range_multiples_card_eq_ediv (p : ℕ) (hp : 0 < p) (a : ℤ) (L : ℕ) :
    (((Finset.range (L + 1)).filter (fun j : ℕ => (p : ℤ) ∣ a + (j : ℤ))).card : ℤ) =
      (a + (L : ℤ)) / (p : ℤ) - (a - 1) / (p : ℤ) := by
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have hcard : ((Finset.range (L + 1)).filter (fun j : ℕ => (p : ℤ) ∣ a + (j : ℤ))).card =
      (Finset.Ioc ((a - 1) / (p : ℤ)) ((a + (L : ℤ)) / (p : ℤ))).card := by
    apply Finset.card_bij (fun (j : ℕ) _ => (a + (j : ℤ)) / (p : ℤ))
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨q, hq⟩ := hj.2
      have hdiv : (a + (j : ℤ)) / (p : ℤ) = q := by
        rw [hq, Int.mul_ediv_cancel_left q hpZ.ne']
      rw [Finset.mem_Ioc, hdiv]
      constructor
      · exact (Int.ediv_lt_iff_lt_mul hpZ).mpr (by linarith)
      · exact (Int.le_ediv_iff_mul_le hpZ).mpr (by linarith)
    · intro j₁ hj₁ j₂ hj₂ hEq
      obtain ⟨q₁, hq₁⟩ := (Finset.mem_filter.mp hj₁).2
      obtain ⟨q₂, hq₂⟩ := (Finset.mem_filter.mp hj₂).2
      rw [hq₁, hq₂, Int.mul_ediv_cancel_left q₁ hpZ.ne',
        Int.mul_ediv_cancel_left q₂ hpZ.ne'] at hEq
      subst hEq
      omega
    · intro q hq
      rw [Finset.mem_Ioc] at hq
      have h1 : a - 1 < q * (p : ℤ) := (Int.ediv_lt_iff_lt_mul hpZ).mp hq.1
      have h2 : q * (p : ℤ) ≤ a + (L : ℤ) := (Int.le_ediv_iff_mul_le hpZ).mp hq.2
      refine ⟨(q * (p : ℤ) - a).toNat, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        refine ⟨q, ?_⟩
        have hnn : 0 ≤ q * (p : ℤ) - a := by omega
        have hto : (((q * (p : ℤ) - a).toNat : ℕ) : ℤ) = q * (p : ℤ) - a := Int.toNat_of_nonneg hnn
        rw [hto]; ring
      · have hnn : 0 ≤ q * (p : ℤ) - a := by omega
        have hto : (((q * (p : ℤ) - a).toNat : ℕ) : ℤ) = q * (p : ℤ) - a := Int.toNat_of_nonneg hnn
        have heq : a + (((q * (p : ℤ) - a).toNat : ℕ) : ℤ) = (p : ℤ) * q := by rw [hto]; ring
        rw [heq, Int.mul_ediv_cancel_left q hpZ.ne']
  rw [hcard, Int.card_Ioc]
  have hle : (a - 1) / (p : ℤ) ≤ (a + (L : ℤ)) / (p : ℤ) :=
    Int.ediv_le_ediv hpZ (by omega)
  omega

/-- Exact symmetric block count `#{j ∈ [0, 2A] : p ∣ -A + j + c} = ⌊(c + A)/p⌋ - ⌊(c - A - 1)/p⌋`. -/
def symBlockMultCount (p A : ℕ) (c : ℤ) : ℤ :=
  (c + (A : ℤ)) / (p : ℤ) - (c - (A : ℤ) - 1) / (p : ℤ)

/-- `sixPoleClassCount n p c` equals the weighted sum of `symBlockMultCount p (r * n) c`
over the 8 pole radii. -/
theorem sixPoleClassCount_eq_symBlocks (n p : ℕ) (hp : 0 < p) (c : ℤ) :
    (sixPoleClassCount n p c : ℤ) =
      symBlockMultCount p (14 * n) c + 2 * symBlockMultCount p (16 * n) c +
      symBlockMultCount p (17 * n) c + symBlockMultCount p (19 * n) c +
      2 * symBlockMultCount p (20 * n) c + symBlockMultCount p (21 * n) c +
      symBlockMultCount p (23 * n) c + 5 * symBlockMultCount p (25 * n) c := by
  unfold sixPoleClassCount
  rw [Nat.cast_sum]
  have hterm : ∀ b : Fin 14,
      (((Finset.range (sixBlockLen n b + 1)).filter
        (fun j : ℕ => (p : ℤ) ∣ ((sixBlockStart n b : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c)).card : ℤ) =
        symBlockMultCount p ((25 - sixOffset b) * n) c := by
    intro b
    have hob : sixOffset b ≤ 11 := by fin_cases b <;> decide
    have hL : sixBlockLen n b = 2 * ((25 - sixOffset b) * n) := by
      unfold sixBlockLen
      have : 50 - 2 * sixOffset b = 2 * (25 - sixOffset b) := by omega
      rw [this]; ring
    have hstart : (sixBlockStart n b : ℤ) - (sixCenter n : ℤ) = -(((25 - sixOffset b) * n : ℕ) : ℤ) := by
      unfold sixBlockStart sixCenter
      have : (45 + sixOffset b) + (25 - sixOffset b) = 70 := by omega
      have hmul : (45 + sixOffset b) * n + (25 - sixOffset b) * n = 70 * n := by
        calc _ = ((45 + sixOffset b) + (25 - sixOffset b)) * n := by ring
             _ = 70 * n := by rw [this]
      omega
    have hfilt : (Finset.range (sixBlockLen n b + 1)).filter
        (fun j : ℕ => (p : ℤ) ∣ ((sixBlockStart n b : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c) =
        (Finset.range (sixBlockLen n b + 1)).filter
          (fun j : ℕ => (p : ℤ) ∣ (c - (((25 - sixOffset b) * n : ℕ) : ℤ)) + (j : ℤ)) := by
      ext j; simp only [Finset.mem_filter, and_congr_right_iff]
      intro _; rw [show ((sixBlockStart n b : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c =
        (c - (((25 - sixOffset b) * n : ℕ) : ℤ)) + (j : ℤ) by linarith]
    rw [hfilt, range_multiples_card_eq_ediv p hp]
    unfold symBlockMultCount
    rw [hL]; push_cast; ring_nf
  simp_rw [hterm]
  rw [Fin.sum_univ_def]
  simp only [List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, sixOffset, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num; ring

/-- `sixZeroClassCount n p c` equals `5 * symBlock(70n) - (symBlock(27n) + symBlock(29n) + 3 * symBlock(30n))`
EXACTLY for every `n, p, c`! -/
theorem sixZeroClassCount_eq_symBlocks (n p : ℕ) (hp : 0 < p) (c : ℤ) :
    (sixZeroClassCount n p c : ℤ) =
      5 * symBlockMultCount p (70 * n) c -
      (symBlockMultCount p (27 * n) c + symBlockMultCount p (29 * n) c +
        3 * symBlockMultCount p (30 * n) c) := by
  unfold sixZeroClassCount
  rw [Nat.cast_sum]
  have hterm : ∀ a : Fin 5,
      ((((Finset.range (sixZero a * n)).filter
          (fun j : ℕ => (p : ℤ) ∣ ((1 : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c)).card +
        ((Finset.range (sixZero a * n)).filter
          (fun j : ℕ => (p : ℤ) ∣ (((140 * n + 2 - sixZero a * n + j : ℕ) : ℤ) -
            (sixCenter n : ℤ)) + c)).card : ℕ) : ℤ) =
        symBlockMultCount p (70 * n) c - symBlockMultCount p ((70 - sixZero a) * n) c := by
    intro a
    by_cases hn0 : n = 0
    · subst hn0; unfold symBlockMultCount; simp
    have hza : sixZero a ≤ 43 := by fin_cases a <;> decide
    have hza_pos : 0 < sixZero a := by fin_cases a <;> decide
    have hlen : 0 < sixZero a * n := Nat.mul_pos hza_pos (Nat.pos_of_ne_zero hn0)
    have hL_eq : sixZero a * n = (sixZero a * n - 1) + 1 := by omega
    rw [Nat.cast_add]
    have hf1 : (Finset.range (sixZero a * n)).filter
        (fun j : ℕ => (p : ℤ) ∣ ((1 : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c) =
        (Finset.range ((sixZero a * n - 1) + 1)).filter
          (fun j : ℕ => (p : ℤ) ∣ (c - ((70 * n : ℕ) : ℤ)) + (j : ℤ)) := by
      conv_lhs => rw [hL_eq]
      ext j; simp only [Finset.mem_filter, and_congr_right_iff]
      intro _; unfold sixCenter; push_cast
      constructor <;> intro h <;> (convert h using 1; ring)
    have hsub70 : 140 * n + 2 - sixZero a * n = 70 * n + 1 + ((70 - sixZero a) * n + 1) := by
      have : sixZero a * n + (70 - sixZero a) * n = 70 * n := by
        calc _ = (sixZero a + (70 - sixZero a)) * n := by ring
             _ = 70 * n := by rw [Nat.add_sub_of_le (by omega)]
      omega
    have hf2 : (Finset.range (sixZero a * n)).filter
        (fun j : ℕ => (p : ℤ) ∣ (((140 * n + 2 - sixZero a * n + j : ℕ) : ℤ) - (sixCenter n : ℤ)) + c) =
        (Finset.range ((sixZero a * n - 1) + 1)).filter
          (fun j : ℕ => (p : ℤ) ∣ (c + (((70 - sixZero a) * n : ℕ) : ℤ) + 1) + (j : ℤ)) := by
      rw [hsub70]
      conv_lhs => rw [hL_eq]
      ext j; simp only [Finset.mem_filter, and_congr_right_iff]
      intro _; unfold sixCenter; push_cast
      constructor <;> intro h <;> (convert h using 1; ring)
    rw [hf1, hf2, range_multiples_card_eq_ediv p hp, range_multiples_card_eq_ediv p hp]
    unfold symBlockMultCount
    have h70 : ((sixZero a * n : ℕ) : ℤ) + (((70 - sixZero a) * n : ℕ) : ℤ) = ((70 * n : ℕ) : ℤ) := by
      have : sixZero a * n + (70 - sixZero a) * n = 70 * n := by
        calc _ = (sixZero a + (70 - sixZero a)) * n := by ring
             _ = 70 * n := by rw [Nat.add_sub_of_le (by omega)]
      exact_mod_cast this
    push_cast at h70
    have he1 : c - ((70 * n : ℕ) : ℤ) + ((sixZero a * n - 1 : ℕ) : ℤ) =
        c - (((70 - sixZero a) * n : ℕ) : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ sixZero a * n)]; push_cast; linarith
    have he2 : c + (((70 - sixZero a) * n : ℕ) : ℤ) + 1 + ((sixZero a * n - 1 : ℕ) : ℤ) =
        c + ((70 * n : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ sixZero a * n)]; push_cast; linarith
    have he3 : c + (((70 - sixZero a) * n : ℕ) : ℤ) + 1 - 1 =
        c + (((70 - sixZero a) * n : ℕ) : ℤ) := by ring
    rw [he1, he2, he3]
    ring
  simp_rw [hterm]
  rw [Fin.sum_univ_def]
  simp only [List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, sixZero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num; ring

/-- `sixFactVal n p` in terms of `n = k * p + r` (`r = n % p`). -/
theorem sixFactVal_eq_mod (n p : ℕ) (hp : 0 < p) :
    sixFactVal n p =
      ((28 * (n % p) / p : ℕ) : ℤ) + 2 * ((32 * (n % p) / p : ℕ) : ℤ) +
      ((34 * (n % p) / p : ℕ) : ℤ) + ((38 * (n % p) / p : ℕ) : ℤ) +
      2 * ((40 * (n % p) / p : ℕ) : ℤ) + ((42 * (n % p) / p : ℕ) : ℤ) +
      ((46 * (n % p) / p : ℕ) : ℤ) + 5 * ((50 * (n % p) / p : ℕ) : ℤ) -
      2 * (3 * ((40 * (n % p) / p : ℕ) : ℤ) + ((41 * (n % p) / p : ℕ) : ℤ) + ((43 * (n % p) / p : ℕ) : ℤ)) +
      (174 : ℤ) * ((n / p : ℕ) : ℤ) := by
  have hdiv : ∀ m : ℤ, 0 ≤ m → m * (n : ℤ) / (p : ℤ) =
      m * ((n : ℤ) / (p : ℤ)) + m * ((n : ℤ) % (p : ℤ)) / (p : ℤ) := by
    intro m hm
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    have hsplit : k * n = k * (n % p) + (k * (n / p)) * p := by
      have := Nat.div_add_mod n p; nlinarith
    have hnat : ((k * n / p : ℕ) : ℤ) = (k : ℤ) * ((n / p : ℕ) : ℤ) + ((k * (n % p) / p : ℕ) : ℤ) := by
      rw [hsplit, Nat.add_mul_div_right _ _ hp]; push_cast; ring
    simpa [Int.natCast_ediv, Int.natCast_emod, Nat.cast_mul] using hnat
  unfold sixFactVal sixBlockLen
  rw [Fin.sum_univ_def, Fin.sum_univ_def]
  simp only [List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, sixOffset, sixZero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  rw [hdiv 28 (by norm_num), hdiv 32 (by norm_num), hdiv 34 (by norm_num), hdiv 38 (by norm_num),
    hdiv 40 (by norm_num), hdiv 42 (by norm_num), hdiv 46 (by norm_num), hdiv 50 (by norm_num),
    hdiv 41 (by norm_num), hdiv 43 (by norm_num)]
  ring

/-- Key period-1 cancellation: `symBlockMultCount p (rad * n) c = 2 * rad * (n / p) + symBlockMultCount p (rad * (n % p)) c`. -/
theorem symBlockMultCount_mod (p rad n : ℕ) (hp : 0 < p) (c : ℤ) :
    symBlockMultCount p (rad * n) c =
      2 * (rad : ℤ) * (n / p : ℤ) + symBlockMultCount p (rad * (n % p)) c := by
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have hsplit : ((rad * n : ℕ) : ℤ) = ((rad * (n % p) : ℕ) : ℤ) + ((rad * (n / p) : ℕ) : ℤ) * (p : ℤ) := by
    have := Nat.div_add_mod n p
    have : rad * n = rad * (n % p) + (rad * (n / p)) * p := by nlinarith
    exact_mod_cast this
  unfold symBlockMultCount
  rw [hsplit]
  have h1 : (c + (((rad * (n % p) : ℕ) : ℤ) + ((rad * (n / p) : ℕ) : ℤ) * (p : ℤ))) / (p : ℤ) =
      (c + ((rad * (n % p) : ℕ) : ℤ)) / (p : ℤ) + ((rad * (n / p) : ℕ) : ℤ) := by
    rw [← add_assoc, Int.add_mul_ediv_right _ _ hpZ.ne']
  have h2 : (c - (((rad * (n % p) : ℕ) : ℤ) + ((rad * (n / p) : ℕ) : ℤ) * (p : ℤ)) - 1) / (p : ℤ) =
      (c - ((rad * (n % p) : ℕ) : ℤ) - 1) / (p : ℤ) - ((rad * (n / p) : ℕ) : ℤ) := by
    have heq : c - (((rad * (n % p) : ℕ) : ℤ) + ((rad * (n / p) : ℕ) : ℤ) * (p : ℤ)) - 1 =
        (c - ((rad * (n % p) : ℕ) : ℤ) - 1) + (-((rad * (n / p) : ℕ) : ℤ)) * (p : ℤ) := by ring
    rw [heq, Int.add_mul_ediv_right _ _ hpZ.ne']
    ring
  rw [h1, h2]
  push_cast; ring

/-- Exact `periodicDelta` evaluation for any radius `rad`, integer `r_n = n % p`,
and `c` strictly between `0` and `p / 2` avoiding the folded line `L_rad(r_n / p)`. -/
theorem symBlockMultCount_eq_periodicDelta (p rad rn q2 pos g : ℕ) (hp : 0 < p) (c : ℕ)
    (hc0 : 0 < c) (hchalf : 2 * c < p)
    (hq2_lo : q2 * p ≤ 2 * rad * rn) (hq2_hi : 2 * rad * rn ≤ (q2 + 1) * p)
    (hside : let line := periodicLine2 rad q2;
      (g ≤ pos → 2 * (c : ℤ) < line.1 * (p : ℤ) + line.2 * (rn : ℤ)) ∧
      (¬ g ≤ pos → line.1 * (p : ℤ) + line.2 * (rn : ℤ) < 2 * (c : ℤ))) :
    symBlockMultCount p (rad * rn) (c : ℤ) = periodicDelta q2 pos g := by
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  let q : ℕ := q2 / 2
  unfold symBlockMultCount periodicDelta
  have hq2_split : q2 = 2 * q + q2 % 2 := (Nat.div_add_mod q2 2).symm
  have hq2_loZ : (q2 : ℤ) * (p : ℤ) ≤ 2 * (rad : ℤ) * (rn : ℤ) := by exact_mod_cast hq2_lo
  have hq2_hiZ : 2 * (rad : ℤ) * (rn : ℤ) ≤ ((q2 : ℤ) + 1) * (p : ℤ) := by exact_mod_cast hq2_hi
  have hediv : ∀ (x z : ℤ), z * (p : ℤ) ≤ x → x < (z + 1) * (p : ℤ) → x / (p : ℤ) = z := by
    intro x z hlo hhi
    have h1 : z ≤ x / (p : ℤ) := (Int.le_ediv_iff_mul_le hpZ).mpr hlo
    have h2 : x / (p : ℤ) < z + 1 := (Int.ediv_lt_iff_lt_mul hpZ).mpr hhi
    omega
  by_cases hev : q2 % 2 = 0
  · simp only [hev, beq_self_eq_true, ite_true]
    have hq2_eq : (q2 : ℤ) = 2 * (q : ℤ) := by omega
    have hline : periodicLine2 rad q2 = (-2 * (q : ℤ), 2 * (rad : ℤ)) := by
      unfold periodicLine2; simp [hev, q]
    have hq_lo : (q : ℤ) * (p : ℤ) ≤ (rad : ℤ) * (rn : ℤ) := by nlinarith
    have hq_hi : 2 * ((rad : ℤ) * (rn : ℤ)) ≤ (2 * (q : ℤ) + 1) * (p : ℤ) := by nlinarith
    have h1 : ((c : ℤ) + ((rad * rn : ℕ) : ℤ)) / (p : ℤ) = (q : ℤ) :=
      hediv _ _ (by push_cast; nlinarith) (by push_cast; nlinarith)
    split_ifs with hgp
    · have hlt := hside.1 hgp
      rw [hline] at hlt; dsimp only at hlt
      have h2 : ((c : ℤ) - ((rad * rn : ℕ) : ℤ) - 1) / (p : ℤ) = -(q : ℤ) - 1 :=
        hediv _ _ (by push_cast; nlinarith) (by push_cast; nlinarith)
      rw [h1, h2]; ring
    · have hgt := hside.2 hgp
      rw [hline] at hgt; dsimp only at hgt
      have h2 : ((c : ℤ) - ((rad * rn : ℕ) : ℤ) - 1) / (p : ℤ) = -(q : ℤ) :=
        hediv _ _ (by push_cast; nlinarith) (by push_cast; nlinarith)
      rw [h1, h2]; ring
  · have hodd : q2 % 2 = 1 := by omega
    simp only [hodd, show (1 == 0) = false from rfl, Bool.false_eq_true, ite_false]
    have hq2_eq : (q2 : ℤ) = 2 * (q : ℤ) + 1 := by omega
    have hline : periodicLine2 rad q2 = (2 * ((q + 1 : ℕ) : ℤ), -2 * (rad : ℤ)) := by
      unfold periodicLine2; simp [hodd, q]
    have hq_lo : (2 * (q : ℤ) + 1) * (p : ℤ) ≤ 2 * ((rad : ℤ) * (rn : ℤ)) := by nlinarith
    have hq_hi : (rad : ℤ) * (rn : ℤ) ≤ ((q : ℤ) + 1) * (p : ℤ) := by nlinarith
    have h2 : ((c : ℤ) - ((rad * rn : ℕ) : ℤ) - 1) / (p : ℤ) = -(q : ℤ) - 1 :=
      hediv _ _ (by push_cast; nlinarith) (by push_cast; nlinarith)
    split_ifs with hgp
    · have hlt := hside.1 hgp
      rw [hline] at hlt; dsimp only at hlt; push_cast at hlt
      have h1 : ((c : ℤ) + ((rad * rn : ℕ) : ℤ)) / (p : ℤ) = (q : ℤ) :=
        hediv _ _ (by push_cast; nlinarith) (by push_cast; nlinarith)
      rw [h1, h2]; ring
    · have hgt := hside.2 hgp
      rw [hline] at hgt; dsimp only at hgt; push_cast at hgt
      have h1 : ((c : ℤ) + ((rad * rn : ℕ) : ℤ)) / (p : ℤ) = (q : ℤ) + 1 :=
        hediv _ _ (by push_cast; nlinarith) (by push_cast; nlinarith)
      rw [h1, h2]; ring

/-- Ceiling division soundness in `ℝ`: `(num : ℝ) / den ≤ ceilDiv num den`. -/
theorem div_le_ceilDiv_real (num den : ℕ) (hden : 0 < den) :
    (num : ℝ) / (den : ℝ) ≤ (ceilDiv num den : ℝ) := by
  unfold ceilDiv
  simp only [hden.ne', ite_false]
  have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  rw [div_le_iff₀ hdenR]
  have hnat : num ≤ ((num + den - 1) / den) * den := by
    have hdm := Nat.div_add_mod (num + den - 1) den
    rw [mul_comm] at hdm
    have hmod : (num + den - 1) % den < den := Nat.mod_lt _ hden
    omega
  exact_mod_cast hnat

/-- Number of natural numbers `c` strictly inside an open real interval `(A, B)` is at most `B - A + 1`. -/
theorem nat_open_interval_card_le (A B : ℝ) (hAB : A ≤ B) (s : Finset ℕ)
    (hs : ∀ c ∈ s, A < (c : ℝ) ∧ (c : ℝ) < B) :
    (s.card : ℝ) ≤ B - A + 1 := by
  by_cases hemp : s = ∅
  · subst hemp; simp; linarith
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
  let lo := s.min' hne
  let hi := s.max' hne
  have hle : lo ≤ hi := Finset.min'_le s hi (Finset.max'_mem s hne)
  have hsub : s ⊆ Finset.Icc lo hi := fun c hc =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le s c hc, Finset.le_max' s c hc⟩
  have hcard : s.card ≤ hi - lo + 1 := by
    have h1 := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h1
    omega
  have hlo := (hs lo (Finset.min'_mem s hne)).1
  have hhi := (hs hi (Finset.max'_mem s hne)).2
  have hcardR : (s.card : ℝ) ≤ (hi : ℝ) - (lo : ℝ) + 1 := by
    have : (s.card : ℝ) ≤ ((hi - lo + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    rwa [Nat.cast_add, Nat.cast_sub hle, Nat.cast_one] at this
  linarith

/-! ## Extracting verified invariants from `checkPeriodicPiece p = true` -/

theorem affLE_sound {ln ld rn rd : ℕ} {c0 c1 d0 d1 : ℤ} {x : ℝ}
    (hld : 0 < ld) (hrd : 0 < rd)
    (hlo : (ln : ℝ) / (ld : ℝ) ≤ x) (hhi : x ≤ (rn : ℝ) / (rd : ℝ))
    (h : affLE ln ld rn rd c0 c1 d0 d1 = true) :
    (c0 : ℝ) + (c1 : ℝ) * x ≤ (d0 : ℝ) + (d1 : ℝ) * x := by
  unfold affLE at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hldR : (0 : ℝ) < (ld : ℝ) := by exact_mod_cast hld
  have hrdR : (0 : ℝ) < (rd : ℝ) := by exact_mod_cast hrd
  have hL : (c0 : ℝ) + (c1 : ℝ) * ((ln : ℝ) / (ld : ℝ)) ≤ (d0 : ℝ) + (d1 : ℝ) * ((ln : ℝ) / (ld : ℝ)) := by
    have h1 : (c0 : ℝ) * (ld : ℝ) + (c1 : ℝ) * (ln : ℝ) ≤ (d0 : ℝ) * (ld : ℝ) + (d1 : ℝ) * (ln : ℝ) := by
      exact_mod_cast h.1
    have := div_le_div_of_nonneg_right h1 hldR.le
    field_simp [hldR.ne'] at this ⊢
    linarith
  have hR : (c0 : ℝ) + (c1 : ℝ) * ((rn : ℝ) / (rd : ℝ)) ≤ (d0 : ℝ) + (d1 : ℝ) * ((rn : ℝ) / (rd : ℝ)) := by
    have h2 : (c0 : ℝ) * (rd : ℝ) + (c1 : ℝ) * (rn : ℝ) ≤ (d0 : ℝ) * (rd : ℝ) + (d1 : ℝ) * (rn : ℝ) := by
      exact_mod_cast h.2
    have := div_le_div_of_nonneg_right h2 hrdR.le
    field_simp [hrdR.ne'] at this ⊢
    linarith
  by_cases hslope : (c1 : ℝ) ≤ (d1 : ℝ)
  · nlinarith
  · nlinarith

theorem periodicFloorOk_sound {m q ln ld rn rd : ℕ} {x : ℝ}
    (hld : 0 < ld) (hrd : 0 < rd)
    (hlo : (ln : ℝ) / (ld : ℝ) ≤ x) (hhi : x ≤ (rn : ℝ) / (rd : ℝ))
    (h : periodicFloorOk m q ln ld rn rd = true) :
    (q : ℝ) ≤ (m : ℝ) * x ∧ (m : ℝ) * x ≤ ((q + 1 : ℕ) : ℝ) := by
  unfold periodicFloorOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hldR : (0 : ℝ) < (ld : ℝ) := by exact_mod_cast hld
  have hrdR : (0 : ℝ) < (rd : ℝ) := by exact_mod_cast hrd
  have h1 : (q : ℝ) ≤ (m : ℝ) * ((ln : ℝ) / (ld : ℝ)) := by
    have : (q : ℝ) * (ld : ℝ) ≤ (m : ℝ) * (ln : ℝ) := by exact_mod_cast h.1
    rw [← mul_div_assoc, le_div_iff₀ hldR]; exact this
  have h2 : (m : ℝ) * ((rn : ℝ) / (rd : ℝ)) ≤ ((q + 1 : ℕ) : ℝ) := by
    have : (m : ℝ) * (rn : ℝ) ≤ ((q + 1 : ℕ) : ℝ) * (rd : ℝ) := by exact_mod_cast h.2
    rw [← mul_div_assoc, div_le_iff₀ hrdR]; exact this
  exact ⟨h1.trans (mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg m)),
    (mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg m)).trans h2⟩

theorem affIntCeil_sound {a0 a1 : ℤ} {ln ld rn rd D : ℕ}
    (hld : 0 < ld) (hrd : 0 < rd) (hlt : ln * rd < rn * ld) (hD : 0 < D)
    (hnnL : 0 ≤ a0 * (ld : ℤ) + a1 * (ln : ℤ))
    (hnnR : 0 ≤ a0 * (rd : ℤ) + a1 * (rn : ℤ)) :
    (∫ x in ((ln : ℝ) / (ld : ℝ))..((rn : ℝ) / (rd : ℝ)), (a0 : ℝ) + (a1 : ℝ) * x) ≤
      (affIntCeil a0 a1 ln ld rn rd D : ℝ) / (D : ℝ) := by
  have hldR : (0 : ℝ) < (ld : ℝ) := by exact_mod_cast hld
  have hrdR : (0 : ℝ) < (rd : ℝ) := by exact_mod_cast hrd
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  let l : ℝ := (ln : ℝ) / (ld : ℝ)
  let r : ℝ := (rn : ℝ) / (rd : ℝ)
  have hint : (∫ x in l..r, (a0 : ℝ) + (a1 : ℝ) * x) =
      (r - l) * ((a0 : ℝ) + (a1 : ℝ) * ((l + r) / 2)) := by
    have h1 : (∫ x in l..r, (a0 : ℝ) + (a1 : ℝ) * x) =
        (∫ _x in l..r, (a0 : ℝ)) + (a1 : ℝ) * (∫ x in l..r, x) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_const_mul]
    rw [h1, intervalIntegral.integral_const, smul_eq_mul, integral_id]
    ring
  rw [hint]
  let dx : ℤ := (rn : ℤ) * (ld : ℤ) - (ln : ℤ) * (rd : ℤ)
  let sum2 : ℤ := 2 * a0 * (ld : ℤ) * (rd : ℤ) +
    a1 * ((ln : ℤ) * (rd : ℤ) + (rn : ℤ) * (ld : ℤ))
  let num : ℤ := dx * sum2
  let den : ℕ := 2 * (ld * rd) * (ld * rd)
  have hden_pos : 0 < den := by dsimp [den]; positivity
  have hdx_pos : 0 < dx := by dsimp [dx]; omega
  have hsum2_nn : 0 ≤ sum2 := by
    have : sum2 = (rd : ℤ) * (a0 * (ld : ℤ) + a1 * (ln : ℤ)) +
        (ld : ℤ) * (a0 * (rd : ℤ) + a1 * (rn : ℤ)) := by dsimp [sum2]; ring
    rw [this]; positivity
  have hnum_nn : 0 ≤ num := mul_nonneg hdx_pos.le hsum2_nn
  have heq : (r - l) * ((a0 : ℝ) + (a1 : ℝ) * ((l + r) / 2)) =
      ((num.toNat : ℕ) : ℝ) / (den : ℝ) := by
    have hnum_cast : ((num.toNat : ℕ) : ℝ) = (num : ℝ) := by
      have : (num.toNat : ℤ) = num := Int.toNat_of_nonneg hnum_nn
      exact_mod_cast this
    rw [hnum_cast]
    dsimp [l, r, num, dx, sum2, den]
    push_cast
    field_simp [hldR.ne', hrdR.ne']
  rw [heq]
  unfold affIntCeil
  change ((num.toNat : ℕ) : ℝ) / (den : ℝ) ≤
    ((if num ≤ 0 then 0 else ceilDiv (num.toNat * D) den : ℕ) : ℝ) / (D : ℝ)
  split_ifs with h0
  · have : num.toNat = 0 := by omega
    simp [this]
  · have hc := div_le_ceilDiv_real (num.toNat * D) den hden_pos
    rw [le_div_iff₀ hDR]
    calc
      ((num.toNat : ℕ) : ℝ) / (den : ℝ) * (D : ℝ)
          = (((num.toNat * D : ℕ) : ℝ)) / (den : ℝ) := by push_cast; ring
      _ ≤ (ceilDiv (num.toNat * D) den : ℝ) := hc

/-- Substitution of `x = 1 / t` on `[1/y, 1/x]`:
`∫ u in (1/y)..(1/x), g u = ∫ t in x..y, g (1/t) / t^2`. -/
theorem integral_inv_sub (g : ℝ → ℝ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hg : ContinuousOn g (Set.Icc (1 / y) (1 / x))) :
    (∫ u in (1 / y)..(1 / x), g u) = ∫ t in x..y, g (1 / t) * (1 / t ^ 2) := by
  have hy : 0 < y := hx.trans_le hxy
  have hderiv : ∀ t ∈ Set.uIcc x y, HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    have ht0 : t ≠ 0 := (hx.trans_le ht.1).ne'
    exact hasDerivAt_inv ht0
  have hcont_d : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.uIcc x y) := by
    rw [Set.uIcc_of_le hxy]
    intro t ht
    have ht0 : t ≠ 0 := (hx.trans_le ht.1).ne'
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    fun_prop (disch := assumption)
  have hcont_g : ContinuousOn g ((fun s : ℝ => s⁻¹) '' Set.uIcc x y) := by
    apply hg.mono
    rintro _ ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le hxy] at ht
    have htpos : 0 < t := hx.trans_le ht.1
    exact ⟨by rw [one_div]; exact inv_anti₀ htpos ht.2,
           by rw [one_div]; exact inv_anti₀ hx ht.1⟩
  have hsub := intervalIntegral.integral_comp_mul_deriv' (a := x) (b := y)
    (f := fun s : ℝ => s⁻¹) (f' := fun t : ℝ => -(t ^ 2)⁻¹) (g := g)
    hderiv hcont_d hcont_g
  rw [intervalIntegral.integral_symm y⁻¹ x⁻¹] at hsub
  dsimp only [Function.comp_def] at hsub
  simp only [one_div]
  have hneg : (∫ t in x..y, g t⁻¹ * (t ^ 2)⁻¹) = -(∫ t in x..y, g t⁻¹ * -(t ^ 2)⁻¹) := by
    rw [← intervalIntegral.integral_neg]
    congr 1; ext t; ring
  rw [hneg, hsub, neg_neg]

/-- Standalone algebraic identity for `periodic12Ceil_sound` (keeps elaborator context tiny). -/
private theorem periodic12Ceil_prod_eq (a0 a1 : ℤ) (k uln uld rn rd : ℕ)
    (huld : 0 < uld) (hrd : 0 < rd) (hxn : 0 < k * uld + uln) :
    let tlo : ℝ := (k : ℝ) + (uln : ℝ) / (uld : ℝ)
    let xn : ℕ := k * uld + uln
    let dx : ℤ := (rn : ℤ) * (uld : ℤ) - (uln : ℤ) * (rd : ℤ)
    let sum2 : ℤ := 2 * a0 * (uld : ℤ) * (rd : ℤ) +
      a1 * ((uln : ℤ) * (rd : ℤ) + (rn : ℤ) * (uld : ℤ))
    let numI : ℤ := dx * sum2
    let denI : ℕ := 2 * (uld * rd) * (uld * rd)
    let wNum : ℕ := 6 * uld * uld * xn + uld * uld * uld
    let wDen : ℕ := 6 * xn * xn * xn
    (1 / tlo ^ 2 + 1 / (6 * tlo ^ 3)) *
      (((rn : ℝ) / (rd : ℝ) - (uln : ℝ) / (uld : ℝ)) *
        ((a0 : ℝ) + (a1 : ℝ) * (((uln : ℝ) / (uld : ℝ) + (rn : ℝ) / (rd : ℝ)) / 2))) =
      ((numI : ℝ) * (wNum : ℝ)) / ((denI * wDen : ℕ) : ℝ) := by
  intro tlo xn dx sum2 numI denI wNum wDen
  have huldR : (0 : ℝ) < (uld : ℝ) := by exact_mod_cast huld
  have hrdR : (0 : ℝ) < (rd : ℝ) := by exact_mod_cast hrd
  have hxnR : (0 : ℝ) < (xn : ℝ) := by exact_mod_cast hxn
  have htlo_frac : tlo = (xn : ℝ) / (uld : ℝ) := by
    dsimp [tlo, xn]; push_cast; field_simp [huldR.ne']
  rw [htlo_frac]
  dsimp [numI, dx, sum2, denI, wNum, wDen]
  push_cast
  field_simp [hxnR.ne', huldR.ne', hrdR.ne']

/-- Pure one-step term of `periodic12Ceil` after clipping `(uln, uld)`. -/
private def periodic12Step (a0 a1 : ℤ) (k uln uld rn rd : ℕ) : ℕ :=
  let xn : ℕ := k * uld + uln
  let dx : ℤ := (rn : ℤ) * (uld : ℤ) - (uln : ℤ) * (rd : ℤ)
  let sum2 : ℤ := 2 * a0 * (uld : ℤ) * (rd : ℤ) +
    a1 * ((uln : ℤ) * (rd : ℤ) + (rn : ℤ) * (uld : ℤ))
  let numI : ℤ := dx * sum2
  let denI : ℕ := 2 * (uld * rd) * (uld * rd)
  let wNum : ℕ := 6 * uld * uld * xn + uld * uld * uld
  let wDen : ℕ := 6 * xn * xn * xn
  if numI ≤ 0 then 0 else ceilDiv (numI.toNat * wNum * certDen) (denI * wDen)

/-- Isolated arithmetic ceiling step for one `k < 12` term of `periodic12Ceil` (avoids `if`-unfolding blowup). -/
private theorem periodic12Ceil_ceil_step (a0 a1 : ℤ) (k uln uld rn rd : ℕ)
    (huld : 0 < uld) (hrd : 0 < rd) (hxn : 0 < k * uld + uln) :
    let tlo : ℝ := (k : ℝ) + (uln : ℝ) / (uld : ℝ)
    (1 / tlo ^ 2 + 1 / (6 * tlo ^ 3)) *
      (((rn : ℝ) / (rd : ℝ) - (uln : ℝ) / (uld : ℝ)) *
        ((a0 : ℝ) + (a1 : ℝ) * (((uln : ℝ) / (uld : ℝ) + (rn : ℝ) / (rd : ℝ)) / 2))) ≤
      (periodic12Step a0 a1 k uln uld rn rd : ℝ) / (certDen : ℝ) := by
  intro tlo
  have hDR : (0 : ℝ) < (certDen : ℝ) := by unfold certDen; norm_num
  unfold periodic12Step
  dsimp only
  let xn : ℕ := k * uld + uln
  let dx : ℤ := (rn : ℤ) * (uld : ℤ) - (uln : ℤ) * (rd : ℤ)
  let sum2 : ℤ := 2 * a0 * (uld : ℤ) * (rd : ℤ) +
    a1 * ((uln : ℤ) * (rd : ℤ) + (rn : ℤ) * (uld : ℤ))
  let numI : ℤ := dx * sum2
  let denI : ℕ := 2 * (uld * rd) * (uld * rd)
  let wNum : ℕ := 6 * uld * uld * xn + uld * uld * uld
  let wDen : ℕ := 6 * xn * xn * xn
  have hden_pos : 0 < denI * wDen := by dsimp [denI, wDen]; positivity
  rw [periodic12Ceil_prod_eq a0 a1 k uln uld rn rd huld hrd hxn]
  change (numI : ℝ) * (wNum : ℝ) / ((denI * wDen : ℕ) : ℝ) ≤
    ((if numI ≤ 0 then 0 else ceilDiv (numI.toNat * wNum * certDen) (denI * wDen) : ℕ) : ℝ) / (certDen : ℝ)
  split_ifs with hnum0
  · have hle0 : (numI : ℝ) ≤ 0 := by exact_mod_cast hnum0
    have hnonpos : (numI : ℝ) * (wNum : ℝ) / ((denI * wDen : ℕ) : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hle0 (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    exact hnonpos.trans (by simp)
  · have hnum_nn : 0 ≤ numI := by omega
    have hnum_cast : ((numI.toNat : ℕ) : ℝ) = (numI : ℝ) := by
      have : (numI.toNat : ℤ) = numI := Int.toNat_of_nonneg hnum_nn
      exact_mod_cast this
    rw [← hnum_cast, le_div_iff₀ hDR]
    have hc := div_le_ceilDiv_real (numI.toNat * wNum * certDen) (denI * wDen) hden_pos
    calc
      ((numI.toNat : ℕ) : ℝ) * (wNum : ℝ) / ((denI * wDen : ℕ) : ℝ) * (certDen : ℝ)
          = ((numI.toNat * wNum * certDen : ℕ) : ℝ) / ((denI * wDen : ℕ) : ℝ) := by
        push_cast; ring
      _ ≤ (ceilDiv (numI.toNat * wNum * certDen) (denI * wDen) : ℝ) := hc

/-- Upper bound for one piece's 12-period weighted `x`-integral via `periodic12Ceil`. -/
theorem periodic12Ceil_sound (p : PeriodicPiece)
    (hld : 0 < p.ld) (hrd : 0 < p.rd) (_hlt : p.ln * p.rd < p.rn * p.ld)
    (hnnL : 0 ≤ p.a0 * (p.ld : ℤ) + p.a1 * (p.ln : ℤ))
    (hnnR : 0 ≤ p.a0 * (p.rd : ℤ) + p.a1 * (p.rn : ℤ)) :
    (∑ k ∈ Finset.range 12,
      let tlo : ℝ := max ((2 : ℝ) / 7) ((k : ℝ) + (p.ln : ℝ) / (p.ld : ℝ))
      let thi : ℝ := (k : ℝ) + (p.rn : ℝ) / (p.rd : ℝ)
      if tlo < thi then
        ∫ x in (1 / thi)..(1 / tlo),
          (1 + x / 6) * ((p.a0 : ℝ) + (p.a1 : ℝ) * (1 / x - (k : ℝ)))
      else 0) ≤
    (periodic12Ceil p.a0 p.a1 p.ln p.ld p.rn p.rd : ℝ) / (certDen : ℝ) := by
  have hldR : (0 : ℝ) < (p.ld : ℝ) := by exact_mod_cast hld
  have hrdR : (0 : ℝ) < (p.rd : ℝ) := by exact_mod_cast hrd
  have hDR : (0 : ℝ) < (certDen : ℝ) := by unfold certDen; norm_num
  let stepTerm (k : ℕ) : ℕ :=
    let clip : Bool := k == 0 && 7 * p.ln < 2 * p.ld
    let uln : ℕ := if clip then 2 else p.ln
    let uld : ℕ := if clip then 7 else p.ld
    if uln * p.rd < p.rn * uld then
      let xn : ℕ := k * uld + uln
      let xd : ℕ := uld
      let dx : ℤ := (p.rn : ℤ) * (uld : ℤ) - (uln : ℤ) * (p.rd : ℤ)
      let sum2 : ℤ := 2 * p.a0 * (uld : ℤ) * (p.rd : ℤ) +
        p.a1 * ((uln : ℤ) * (p.rd : ℤ) + (p.rn : ℤ) * (uld : ℤ))
      let numI : ℤ := dx * sum2
      let denI : ℕ := 2 * (uld * p.rd) * (uld * p.rd)
      let wNum : ℕ := 6 * xd * xd * xn + xd * xd * xd
      let wDen : ℕ := 6 * xn * xn * xn
      if numI ≤ 0 then 0 else ceilDiv (numI.toNat * wNum * certDen) (denI * wDen)
    else 0
  have hfold_eq : periodic12Ceil p.a0 p.a1 p.ln p.ld p.rn p.rd =
      ∑ k ∈ Finset.range 12, stepTerm k := by
    have hgo : ∀ m acc,
        periodic12Ceil.go p.a0 p.a1 p.ln p.ld p.rn p.rd m acc =
          acc + ∑ k ∈ Finset.range m, stepTerm k := by
      intro m
      induction m with
      | zero => intro acc; simp [periodic12Ceil.go]
      | succ m ih =>
        intro acc
        rw [periodic12Ceil.go, ih, Finset.sum_range_succ]
        dsimp [stepTerm]
        split_ifs <;> ring
    simpa [periodic12Ceil] using hgo 12 0
  rw [hfold_eq, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro k hk
  dsimp only
  let clip : Bool := k == 0 && 7 * p.ln < 2 * p.ld
  let uln : ℕ := if clip then 2 else p.ln
  let uld : ℕ := if clip then 7 else p.ld
  have huld_pos : 0 < uld := by dsimp [uld]; split_ifs <;> omega
  have huldR : (0 : ℝ) < (uld : ℝ) := by exact_mod_cast huld_pos
  have htlo_eq : max ((2 : ℝ) / 7) ((k : ℝ) + (p.ln : ℝ) / (p.ld : ℝ)) =
      (k : ℝ) + (uln : ℝ) / (uld : ℝ) := by
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.cast_zero, zero_add]
      by_cases hlt27 : 7 * p.ln < 2 * p.ld
      · have hclip : clip = true := by simp [clip, hlt27]
        simp only [uln, uld, hclip, ite_true]
        have hle : (p.ln : ℝ) / (p.ld : ℝ) ≤ (2 : ℝ) / 7 := by
          rw [div_le_div_iff₀ hldR (by norm_num : (0 : ℝ) < 7)]
          have : p.ln * 7 ≤ 2 * p.ld := by omega
          exact_mod_cast this
        exact max_eq_left hle
      · have hclip : clip = false := by simp [clip, hlt27]
        simp only [uln, uld, hclip, Bool.false_eq_true, ite_false]
        have hge : (2 : ℝ) / 7 ≤ (p.ln : ℝ) / (p.ld : ℝ) := by
          rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 7) hldR]
          have : 2 * p.ld ≤ p.ln * 7 := by omega
          exact_mod_cast this
        exact max_eq_right hge
    · have hclip : clip = false := by simp [clip, hk0]
      simp only [uln, uld, hclip, Bool.false_eq_true, ite_false]
      have hge : (2 : ℝ) / 7 ≤ (k : ℝ) + (p.ln : ℝ) / (p.ld : ℝ) := by
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hk0)
        have hnn : 0 ≤ (p.ln : ℝ) / (p.ld : ℝ) := by positivity
        linarith
      exact max_eq_right hge
  rw [htlo_eq]
  have hcond_iff : (k : ℝ) + (uln : ℝ) / (uld : ℝ) < (k : ℝ) + (p.rn : ℝ) / (p.rd : ℝ) ↔
      uln * p.rd < p.rn * uld := by
    rw [add_lt_add_iff_left, div_lt_div_iff₀ huldR hrdR]
    exact_mod_cast Iff.rfl
  by_cases hltR : (k : ℝ) + (uln : ℝ) / (uld : ℝ) < (k : ℝ) + (p.rn : ℝ) / (p.rd : ℝ)
  · have hltN : uln * p.rd < p.rn * uld := hcond_iff.mp hltR
    simp only [hltR, ite_true]
    have hstep_eq : stepTerm k = periodic12Step p.a0 p.a1 k uln uld p.rn p.rd := by
      dsimp only [stepTerm]
      change (if uln * p.rd < p.rn * uld then periodic12Step p.a0 p.a1 k uln uld p.rn p.rd else 0) = _
      simp only [hltN, ite_true]
    rw [hstep_eq]
    let tlo : ℝ := (k : ℝ) + (uln : ℝ) / (uld : ℝ)
    let thi : ℝ := (k : ℝ) + (p.rn : ℝ) / (p.rd : ℝ)
    have htlo_ge27 : (2 : ℝ) / 7 ≤ tlo := by
      dsimp only [tlo]; rw [← htlo_eq]; exact le_max_left _ _
    have htlo_pos : 0 < tlo := by linarith
    have hthi_pos : 0 < thi := htlo_pos.trans hltR
    have hsub := integral_inv_sub
      (fun x => (1 + x / 6) * ((p.a0 : ℝ) + (p.a1 : ℝ) * (1 / x - (k : ℝ))))
      htlo_pos hltR.le (by
        intro x hx
        have hx0 : x ≠ 0 := (lt_of_lt_of_le (by positivity) hx.1).ne'
        have h6 : (6 : ℝ) ≠ 0 := by norm_num
        fun_prop (disch := assumption))
    change (∫ u in (1 / thi)..(1 / tlo),
      (1 + u / 6) * ((p.a0 : ℝ) + (p.a1 : ℝ) * (1 / u - (k : ℝ)))) ≤ _
    rw [hsub]
    have haff_nn : ∀ t ∈ Set.Icc tlo thi, 0 ≤ (p.a0 : ℝ) + (p.a1 : ℝ) * (t - (k : ℝ)) := by
      intro t ht
      have hlo_u : (p.ln : ℝ) / (p.ld : ℝ) ≤ t - (k : ℝ) := by
        have h1 : (k : ℝ) + (p.ln : ℝ) / (p.ld : ℝ) ≤ tlo := by
          dsimp only [tlo]; rw [← htlo_eq]; exact le_max_right _ _
        linarith [ht.1]
      have hhi_u : t - (k : ℝ) ≤ (p.rn : ℝ) / (p.rd : ℝ) := by linarith [ht.2]
      have hL : 0 ≤ (p.a0 : ℝ) + (p.a1 : ℝ) * ((p.ln : ℝ) / (p.ld : ℝ)) := by
        have : (0 : ℝ) ≤ (p.a0 : ℝ) * (p.ld : ℝ) + (p.a1 : ℝ) * (p.ln : ℝ) := by exact_mod_cast hnnL
        have := div_nonneg this hldR.le
        field_simp [hldR.ne'] at this ⊢; linarith
      have hR : 0 ≤ (p.a0 : ℝ) + (p.a1 : ℝ) * ((p.rn : ℝ) / (p.rd : ℝ)) := by
        have : (0 : ℝ) ≤ (p.a0 : ℝ) * (p.rd : ℝ) + (p.a1 : ℝ) * (p.rn : ℝ) := by exact_mod_cast hnnR
        have := div_nonneg this hrdR.le
        field_simp [hrdR.ne'] at this ⊢; linarith
      by_cases hs : (0 : ℝ) ≤ (p.a1 : ℝ)
      · have := mul_le_mul_of_nonneg_left hlo_u hs; linarith
      · have hneg : (0 : ℝ) ≤ -(p.a1 : ℝ) := by linarith
        have := mul_le_mul_of_nonneg_left hhi_u hneg; linarith
    have hint_le : (∫ t in tlo..thi,
        (1 + 1 / t / 6) * ((p.a0 : ℝ) + (p.a1 : ℝ) * (1 / (1 / t) - (k : ℝ))) * (1 / t ^ 2)) ≤
        ((1 / tlo ^ 2 + 1 / (6 * tlo ^ 3)) *
          ∫ t in tlo..thi, ((p.a0 : ℝ) + (p.a1 : ℝ) * (t - (k : ℝ)))) := by
      rw [← intervalIntegral.integral_const_mul]
      have hrew_int : (∫ t in tlo..thi,
          (1 + 1 / t / 6) * ((p.a0 : ℝ) + (p.a1 : ℝ) * (1 / (1 / t) - (k : ℝ))) * (1 / t ^ 2)) =
          ∫ t in tlo..thi, (1 + 1 / t / 6) * ((p.a0 : ℝ) + (p.a1 : ℝ) * (t - (k : ℝ))) * (1 / t ^ 2) := by
        congr 1; ext t; rw [one_div_one_div]
      rw [hrew_int]
      apply intervalIntegral.integral_mono_on hltR.le
      · apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hltR.le]
        intro t ht
        have ht0 : t ≠ 0 := (htlo_pos.trans_le ht.1).ne'
        have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
        have h6 : (6 : ℝ) ≠ 0 := by norm_num
        fun_prop (disch := assumption)
      · exact Continuous.intervalIntegrable (by fun_prop) _ _
      · intro t ht
        have htpos : 0 < t := htlo_pos.trans_le ht.1
        have hwt_le : (1 + 1 / t / 6) * (1 / t ^ 2) ≤ 1 / tlo ^ 2 + 1 / (6 * tlo ^ 3) := by
          have heq_t : (1 + 1 / t / 6) * (1 / t ^ 2) = 1 / t ^ 2 + 1 / (6 * t ^ 3) := by
            field_simp [htpos.ne']
          rw [heq_t]
          have h2 : 1 / t ^ 2 ≤ 1 / tlo ^ 2 :=
            one_div_le_one_div_of_le (pow_pos htlo_pos 2) (pow_le_pow_left₀ htlo_pos.le ht.1 2)
          have h3 : 1 / (6 * t ^ 3) ≤ 1 / (6 * tlo ^ 3) :=
            one_div_le_one_div_of_le (by positivity)
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htlo_pos.le ht.1 3) (by norm_num))
          linarith
        have hnn := haff_nn t ht
        have hmul := mul_le_mul_of_nonneg_right hwt_le hnn
        linarith
    have hint_aff : (∫ t in tlo..thi, ((p.a0 : ℝ) + (p.a1 : ℝ) * (t - (k : ℝ)))) =
        ((p.rn : ℝ) / (p.rd : ℝ) - (uln : ℝ) / (uld : ℝ)) *
          ((p.a0 : ℝ) + (p.a1 : ℝ) * (((uln : ℝ) / (uld : ℝ) + (p.rn : ℝ) / (p.rd : ℝ)) / 2)) := by
      have h1 : (∫ t in tlo..thi, ((p.a0 : ℝ) + (p.a1 : ℝ) * (t - (k : ℝ)))) =
          (∫ _t in tlo..thi, ((p.a0 : ℝ) - (p.a1 : ℝ) * (k : ℝ))) +
          (p.a1 : ℝ) * (∫ t in tlo..thi, t) := by
        rw [← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_add intervalIntegrable_const
            (Continuous.intervalIntegrable (by fun_prop) _ _)]
        congr 1; ext t; ring
      rw [h1, intervalIntegral.integral_const, smul_eq_mul, integral_id]
      dsimp [tlo, thi]; ring
    refine hint_le.trans ?_
    rw [hint_aff]
    have hxn_pos : 0 < k * uld + uln := by
      have htlo_frac : tlo = ((k * uld + uln : ℕ) : ℝ) / (uld : ℝ) := by
        dsimp [tlo]; push_cast; field_simp [huldR.ne']
      have : (0 : ℝ) < ((k * uld + uln : ℕ) : ℝ) / (uld : ℝ) := htlo_frac ▸ htlo_pos
      have : (0 : ℝ) < ((k * uld + uln : ℕ) : ℝ) := (div_pos_iff_of_pos_right huldR).mp this
      exact_mod_cast this
    exact periodic12Ceil_ceil_step p.a0 p.a1 k uln uld p.rn p.rd huld_pos hrd hxn_pos
  · simp only [hltR, ite_false]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! ## Telescoping tail bound for `k ∈ [12, K_max)` -/

theorem tail_inv_sq_sum_le (K : ℕ) :
    (∑ k ∈ Finset.Ico 12 K, (1 : ℝ) / ((k : ℝ) ^ 2)) ≤ 1 / 11 := by
  have hterm : ∀ k ∈ Finset.Ico 12 K,
      (1 : ℝ) / ((k : ℝ) ^ 2) ≤ 1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) := by
    intro k hk
    have hk12 : 12 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkR : (0 : ℝ) < (k : ℝ) := by
      have : 0 < k := by omega
      exact_mod_cast this
    have hk1R : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
      have : 0 < k - 1 := by omega
      exact_mod_cast this
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    rw [hcast]
    have hk1pos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    rw [div_sub_div _ _ hk1pos.ne' hkR.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  clear hterm
  by_cases hK : 12 ≤ K
  · have htel : (∑ k ∈ Finset.Ico 12 K, (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ))) =
        1 / (11 : ℝ) - 1 / ((K - 1 : ℕ) : ℝ) := by
      induction K, hK using Nat.le_induction with
      | base => simp
      | succ m hm ih =>
        rw [Finset.sum_Ico_succ_top hm, ih]
        have h1 : m + 1 - 1 = m := by omega
        rw [h1]; ring
    rw [htel]
    have hnn : 0 ≤ 1 / ((K - 1 : ℕ) : ℝ) := by positivity
    linarith
  · have hemp : Finset.Ico 12 K = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hemp, Finset.sum_empty]
    norm_num

theorem tail_inv_cube_sum_le (K : ℕ) :
    (∑ k ∈ Finset.Ico 12 K, (1 : ℝ) / (6 * (k : ℝ) ^ 3)) ≤ 1 / (12 * 11 ^ 2) := by
  have hterm : ∀ k ∈ Finset.Ico 12 K,
      (1 : ℝ) / (6 * (k : ℝ) ^ 3) ≤
        1 / (12 * ((k - 1 : ℕ) : ℝ) ^ 2) - 1 / (12 * (k : ℝ) ^ 2) := by
    intro k hk
    have hk12 : 12 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkR : (12 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk12
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    rw [hcast]
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hk1pos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    rw [div_sub_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  clear hterm
  by_cases hK : 12 ≤ K
  · have htel : (∑ k ∈ Finset.Ico 12 K,
        (1 / (12 * ((k - 1 : ℕ) : ℝ) ^ 2) - 1 / (12 * (k : ℝ) ^ 2))) =
        1 / (12 * (11 : ℝ) ^ 2) - 1 / (12 * ((K - 1 : ℕ) : ℝ) ^ 2) := by
      induction K, hK using Nat.le_induction with
      | base => simp
      | succ m hm ih =>
        rw [Finset.sum_Ico_succ_top hm, ih]
        have h1 : m + 1 - 1 = m := by omega
        rw [h1]; ring
    rw [htel]
    have hnn : 0 ≤ 1 / (12 * ((K - 1 : ℕ) : ℝ) ^ 2) := by positivity
    linarith
  · have hemp : Finset.Ico 12 K = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hemp, Finset.sum_empty]
    norm_num

/-! ## Helpers for `isPerm12`, `indexOfNat`, `checkSortedLines`, and `checkPeriodicShard` -/

theorem isPerm12_hasAll_mem (perm : List ℕ) (k : ℕ)
    (h : isPerm12.hasAll perm k = true) : ∀ j < k, j ∈ perm := by
  induction k with
  | zero => intro j hj; omega
  | succ k' ih =>
    simp only [isPerm12.hasAll, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · exact ih h.2 j hlt
    · exact h.1

theorem indexOfNat_go_spec (xs : List ℕ) (target idx : ℕ) (hmem : target ∈ xs) :
    idx ≤ indexOfNat.go target xs idx ∧
    indexOfNat.go target xs idx < idx + xs.length ∧
    xs[indexOfNat.go target xs idx - idx]? = some target := by
  induction xs generalizing idx with
  | nil => cases hmem
  | cons a t ih =>
    simp only [indexOfNat.go]
    by_cases ha : a = target
    · subst ha
      simp
    · have hbeq : (a == target) = false := beq_false_of_ne ha
      rw [hbeq]; simp only [Bool.false_eq_true, ite_false]
      have ht : target ∈ t := by
        rcases List.mem_cons.mp hmem with rfl | h'
        · exact absurd rfl ha
        · exact h'
      obtain ⟨h1, h2, h3⟩ := ih (idx + 1) ht
      refine ⟨by omega, by simp; omega, ?_⟩
      have hsub : indexOfNat.go target t (idx + 1) - idx =
          (indexOfNat.go target t (idx + 1) - (idx + 1)) + 1 := by omega
      rw [hsub]
      simpa using h3

theorem isPerm12_spec {perm : List ℕ} (h : isPerm12 perm = true) :
    perm.length = 12 ∧ ∀ k < 12, indexOfNat perm k < 12 ∧ perm[indexOfNat perm k]? = some k := by
  unfold isPerm12 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun k hk => ?_⟩
  have hmem : k ∈ perm := isPerm12_hasAll_mem perm 12 h.2 k hk
  obtain ⟨_, hlt, hget⟩ := indexOfNat_go_spec perm k 0 hmem
  unfold indexOfNat
  rw [h.1, zero_add] at hlt
  simpa using ⟨hlt, hget⟩

theorem checkSortedLines_adj {ln ld rn rd : ℕ} {pts : List (ℤ × ℤ)} {x : ℝ}
    (hld : 0 < ld) (hrd : 0 < rd)
    (hlo : (ln : ℝ) / (ld : ℝ) ≤ x) (hhi : x ≤ (rn : ℝ) / (rd : ℝ))
    (hsort : checkSortedLines ln ld rn rd pts = true)
    (k : ℕ) (hk : k + 1 < pts.length) :
    ((pts[k]'(Nat.lt_of_succ_lt hk)).1 : ℝ) + ((pts[k]'(Nat.lt_of_succ_lt hk)).2 : ℝ) * x ≤
      ((pts[k + 1]'hk).1 : ℝ) + ((pts[k + 1]'hk).2 : ℝ) * x := by
  induction pts generalizing k with
  | nil => simp at hk
  | cons a rest ih =>
    cases rest with
    | nil => simp at hk
    | cons b tail =>
      simp only [checkSortedLines, Bool.and_eq_true] at hsort
      cases k with
      | zero => exact affLE_sound hld hrd hlo hhi hsort.1
      | succ k' =>
        have hk' : k' + 1 < (b :: tail).length := by simp at hk ⊢; omega
        exact ih hsort.2 k' hk'

theorem checkSortedLines_mono {ln ld rn rd : ℕ} {pts : List (ℤ × ℤ)} {x : ℝ}
    (hld : 0 < ld) (hrd : 0 < rd)
    (hlo : (ln : ℝ) / (ld : ℝ) ≤ x) (hhi : x ≤ (rn : ℝ) / (rd : ℝ))
    (hsort : checkSortedLines ln ld rn rd pts = true)
    {i j : ℕ} (hij : i ≤ j) (hj : j < pts.length) :
    ((pts[i]'(Nat.lt_of_le_of_lt hij hj)).1 : ℝ) + ((pts[i]'(Nat.lt_of_le_of_lt hij hj)).2 : ℝ) * x ≤
      ((pts[j]'hj).1 : ℝ) + ((pts[j]'hj).2 : ℝ) * x := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    exact (ih (Nat.lt_of_succ_lt hj)).trans
      (checkSortedLines_adj hld hrd hlo hhi hsort m hj)

theorem checkPeriodicRun_spec {curN curD endN endD accF accC fT cT : ℕ} {ps : List PeriodicPiece}
    (h : checkPeriodicRun curN curD endN endD accF accC fT cT ps = true) :
    (∀ piece ∈ ps, checkPeriodicPiece piece = true) ∧
    accF + (ps.map (·.fbarNum)).sum = fT ∧
    accC + (ps.map (·.c0Num)).sum = cT := by
  induction ps generalizing curN curD accF accC with
  | nil =>
    simp only [checkPeriodicRun, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨by simp, by simpa using h.1.2, by simpa using h.2⟩
  | cons piece rest ih =>
    simp only [checkPeriodicRun, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hrest, hF, hC⟩ := ih h.2
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact h.1.2
      · exact hrest q hq'
    · simp only [List.map_cons, List.sum_cons]; omega
    · simp only [List.map_cons, List.sum_cons]; omega

theorem checkPeriodicRun_cover {curN curD endN endD accF accC fT cT : ℕ} {ps : List PeriodicPiece}
    (h : checkPeriodicRun curN curD endN endD accF accC fT cT ps = true)
    {x : ℝ} (hlo : (curN : ℝ) / (curD : ℝ) < x) (hhi : x < (endN : ℝ) / (endD : ℝ))
    (hne : ∀ piece ∈ ps, x ≠ (piece.rn : ℝ) / (piece.rd : ℝ)) :
    ∃ piece ∈ ps, (piece.ln : ℝ) / (piece.ld : ℝ) < x ∧ x < (piece.rn : ℝ) / (piece.rd : ℝ) := by
  induction ps generalizing curN curD accF accC with
  | nil =>
    simp only [checkPeriodicRun, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨rfl, rfl⟩, _⟩, _⟩
    linarith
  | cons piece rest ih =>
    simp only [checkPeriodicRun, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨hln, hld⟩, _⟩, hrest⟩
    have hneq := hne piece (List.mem_cons_self ..)
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · exact ⟨piece, List.mem_cons_self .., by rwa [hln, hld], hlt⟩
    · obtain ⟨q, hq, hqlo, hqhi⟩ := ih hrest hgt (fun r hr => hne r (List.mem_cons_of_mem _ hr))
      exact ⟨q, List.mem_cons_of_mem _ hq, hqlo, hqhi⟩

/-- Maximum denominator across a list of `PeriodicPiece`s (at least `1`). -/
def periodicMaxDen (ps : List PeriodicPiece) : ℕ :=
  ps.foldl (fun m piece => max m (max piece.ld piece.rd)) 1

theorem periodicMaxDen_ge (ps : List PeriodicPiece) :
    ∀ piece ∈ ps, piece.ld ≤ periodicMaxDen ps ∧ piece.rd ≤ periodicMaxDen ps := by
  have hfold : ∀ (init : ℕ) (xs : List PeriodicPiece),
      init ≤ xs.foldl (fun m piece => max m (max piece.ld piece.rd)) init ∧
      ∀ piece ∈ xs,
        piece.ld ≤ xs.foldl (fun m piece => max m (max piece.ld piece.rd)) init ∧
        piece.rd ≤ xs.foldl (fun m piece => max m (max piece.ld piece.rd)) init := by
    intro init xs
    induction xs generalizing init with
    | nil => exact ⟨le_rfl, by simp⟩
    | cons a t ih =>
      simp only [List.foldl_cons]
      obtain ⟨hge, hmem⟩ := ih (max init (max a.ld a.rd))
      refine ⟨(le_max_left _ _).trans hge, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact ⟨((le_max_left _ _).trans (le_max_right _ _)).trans hge,
               ((le_max_right _ _).trans (le_max_right _ _)).trans hge⟩
      · exact hmem q hq'
  exact (hfold 1 ps).2

/-! ## Discrete-to-continuous periodic piece bound -/

/-- Exact evaluation of the strip accumulator `checkPeriodicPiece.sumStrips` at any `τ : ℝ`. -/
private theorem sumStrips_eval (vFact : ℤ)
    (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℕ)
    (rem : List (ℤ × ℤ)) (g : ℕ) (a0 a1 : ℤ) (τ : ℝ) :
    let res := checkPeriodicPiece.sumStrips q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
      vFact p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 g rem a0 a1
    (res.1 : ℝ) + (res.2 : ℝ) * τ =
      (a0 : ℝ) + (a1 : ℝ) * τ +
      ∑ k ∈ Finset.range (rem.length - 1),
        let val : ℤ := (4 - vFact)
          + periodicDelta q0 p0 (g + k) + 2 * periodicDelta q1 p1 (g + k)
          + periodicDelta q2 p2 (g + k) + periodicDelta q3 p3 (g + k)
          + 2 * periodicDelta q4 p4 (g + k) + periodicDelta q5 p5 (g + k)
          + periodicDelta q6 p6 (g + k) + 5 * periodicDelta q7 p7 (g + k)
          + periodicDelta q8 p8 (g + k) + periodicDelta q9 p9 (g + k)
          + 3 * periodicDelta q10 p10 (g + k) - 5 * periodicDelta q11 p11 (g + k)
        let B : ℤ := if val ≤ 0 then 0 else val
        let u := rem[k]?.getD (0, 0)
        let v := rem[k + 1]?.getD (0, 0)
        (B : ℝ) * (((v.1 : ℝ) + (v.2 : ℝ) * τ) - ((u.1 : ℝ) + (u.2 : ℝ) * τ)) := by
  induction rem generalizing g a0 a1 with
  | nil => simp [checkPeriodicPiece.sumStrips]
  | cons u tail ih =>
    cases tail with
    | nil => simp [checkPeriodicPiece.sumStrips]
    | cons v rest =>
      dsimp only
      rw [checkPeriodicPiece.sumStrips]
      rw [ih (g + 1)]
      have hlen : (u :: v :: rest).length - 1 = ((v :: rest).length - 1) + 1 := by simp
      rw [hlen, Finset.sum_range_succ']
      simp only [add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
        show ∀ k, g + 1 + k = g + (k + 1) from fun k => by omega]
      push_cast
      ring

/-- Clean extraction of all verified invariants from `checkPeriodicPiece piece = true`. -/
theorem checkPeriodicPiece_extract (piece : PeriodicPiece) (hchk : checkPeriodicPiece piece = true) :
    let q0 := periodicFloorVal 28 piece.ln piece.ld piece.rn piece.rd
    let q1 := periodicFloorVal 32 piece.ln piece.ld piece.rn piece.rd
    let q2 := periodicFloorVal 34 piece.ln piece.ld piece.rn piece.rd
    let q3 := periodicFloorVal 38 piece.ln piece.ld piece.rn piece.rd
    let q4 := periodicFloorVal 40 piece.ln piece.ld piece.rn piece.rd
    let q5 := periodicFloorVal 42 piece.ln piece.ld piece.rn piece.rd
    let q6 := periodicFloorVal 46 piece.ln piece.ld piece.rn piece.rd
    let q7 := periodicFloorVal 50 piece.ln piece.ld piece.rn piece.rd
    let q8 := periodicFloorVal 54 piece.ln piece.ld piece.rn piece.rd
    let q9 := periodicFloorVal 58 piece.ln piece.ld piece.rn piece.rd
    let q10 := periodicFloorVal 60 piece.ln piece.ld piece.rn piece.rd
    let q11 := periodicFloorVal 140 piece.ln piece.ld piece.rn piece.rd
    let z41 := periodicFloorVal 41 piece.ln piece.ld piece.rn piece.rd
    let z43 := periodicFloorVal 43 piece.ln piece.ld piece.rn piece.rd
    let getQ2 : ℕ → ℕ
      | 0 => q0 | 1 => q1 | 2 => q2 | 3 => q3 | 4 => q4 | 5 => q5
      | 6 => q6 | 7 => q7 | 8 => q8 | 9 => q9 | 10 => q10 | _ => q11
    let vPole : ℤ := (q0 : ℤ) + 2 * (q1 : ℤ) + (q2 : ℤ) + (q3 : ℤ) +
      2 * (q4 : ℤ) + (q5 : ℤ) + (q6 : ℤ) + 5 * (q7 : ℤ)
    let vFact : ℤ := vPole - 2 * (3 * (q4 : ℤ) + (z41 : ℤ) + (z43 : ℤ))
    let pts : List (ℤ × ℤ) :=
      (0, 0) :: piece.perm.map (fun idx => periodicLine2 (radiusValNat idx) (getQ2 idx)) ++ [(1, 0)]
    let stripSum := checkPeriodicPiece.sumStrips q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 vFact
      (indexOfNat piece.perm 0) (indexOfNat piece.perm 1) (indexOfNat piece.perm 2)
      (indexOfNat piece.perm 3) (indexOfNat piece.perm 4) (indexOfNat piece.perm 5)
      (indexOfNat piece.perm 6) (indexOfNat piece.perm 7) (indexOfNat piece.perm 8)
      (indexOfNat piece.perm 9) (indexOfNat piece.perm 10) (indexOfNat piece.perm 11) 0 pts 0 0
    (0 < piece.ld ∧ 0 < piece.rd ∧ piece.ln * piece.rd < piece.rn * piece.ld) ∧
    isPerm12 piece.perm = true ∧
    (periodicFloorOk 28 q0 piece.ln piece.ld piece.rn piece.rd = true ∧
     periodicFloorOk 32 q1 piece.ln piece.ld piece.rn piece.rd = true ∧
     periodicFloorOk 34 q2 piece.ln piece.ld piece.rn piece.rd = true ∧
     periodicFloorOk 38 q3 piece.ln piece.ld piece.rn piece.rd = true ∧
     periodicFloorOk 40 q4 piece.ln piece.ld piece.rn piece.rd = true ∧
     periodicFloorOk 42 q5 piece.ln piece.ld piece.rn piece.rd = true ∧
     periodicFloorOk 46 q6 piece.ln piece.ld piece.rn piece.rd = true ∧
     periodicFloorOk 50 q7 piece.ln piece.ld piece.rn piece.rd = true ∧
     periodicFloorOk 54 q8 piece.ln piece.ld piece.rn piece.rd = true ∧
     periodicFloorOk 58 q9 piece.ln piece.ld piece.rn piece.rd = true ∧
     periodicFloorOk 60 q10 piece.ln piece.ld piece.rn piece.rd = true ∧
     periodicFloorOk 140 q11 piece.ln piece.ld piece.rn piece.rd = true ∧
     periodicFloorOk 41 z41 piece.ln piece.ld piece.rn piece.rd = true ∧
     periodicFloorOk 43 z43 piece.ln piece.ld piece.rn piece.rd = true) ∧
    checkSortedLines piece.ln piece.ld piece.rn piece.rd pts = true ∧
    (stripSum.1 = piece.a0 ∧ stripSum.2 = piece.a1) ∧
    (0 ≤ piece.a0 * (piece.ld : ℤ) + piece.a1 * (piece.ln : ℤ) ∧
     0 ≤ piece.a0 * (piece.rd : ℤ) + piece.a1 * (piece.rn : ℤ) ∧
     affIntCeil piece.a0 piece.a1 piece.ln piece.ld piece.rn piece.rd certDen ≤ piece.fbarNum ∧
     periodic12Ceil piece.a0 piece.a1 piece.ln piece.ld piece.rn piece.rd ≤ piece.c0Num) := by
  unfold checkPeriodicPiece at hchk
  split_ifs at hchk with h1 h2
  dsimp +zetaHave only at hchk
  split_ifs at hchk with h3 h4 h5
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.not_eq_false,
    Bool.and_eq_true, decide_eq_true_eq, decide_eq_false_iff_not, not_or, not_lt, not_le, bne_iff_ne, not_ne_iff] at h1 h2 h3 h4 h5 hchk
  refine ⟨⟨Nat.pos_of_ne_zero h1.1.1, Nat.pos_of_ne_zero h1.1.2, h1.2⟩, h2, ?_, h4, ?_, ?_⟩
  · exact ⟨h3.1.1.1.1.1.1.1.1.1.1.1.1.1, h3.1.1.1.1.1.1.1.1.1.1.1.1.2,
      h3.1.1.1.1.1.1.1.1.1.1.1.2, h3.1.1.1.1.1.1.1.1.1.1.2, h3.1.1.1.1.1.1.1.1.1.2,
      h3.1.1.1.1.1.1.1.1.2, h3.1.1.1.1.1.1.1.2, h3.1.1.1.1.1.1.2, h3.1.1.1.1.1.2,
      h3.1.1.1.1.2, h3.1.1.1.2, h3.1.1.2, h3.1.2, h3.2⟩
  · exact ⟨h5.1, h5.2⟩
  · exact ⟨hchk.1.1.1, hchk.1.1.2, hchk.1.2, hchk.2⟩

/-- For any prime `p` (`0 < p`) and any checked `PeriodicPiece` whose strict interior contains
`τ = (n % p) / p`, `∑ c : Fin (p/2 + 1), sixCoarsePeriodicCost n p c ≤ (p/2) * (a0 + a1 * τ) + 486`. -/
theorem periodicPiece_discrete_sum_le (n p : ℕ) (hp : 0 < p)
    (piece : PeriodicPiece) (hchk : checkPeriodicPiece piece = true)
    (hlo : (piece.ln : ℝ) / (piece.ld : ℝ) < ((n % p : ℕ) : ℝ) / (p : ℝ))
    (hhi : ((n % p : ℕ) : ℝ) / (p : ℝ) < (piece.rn : ℝ) / (piece.rd : ℝ)) :
    (∑ c : Fin (p / 2 + 1), (sixCoarsePeriodicCost n p c : ℝ)) ≤
      ((p : ℝ) / 2) * ((piece.a0 : ℝ) + (piece.a1 : ℝ) * (((n % p : ℕ) : ℝ) / (p : ℝ))) + 486 := by
  have hext := checkPeriodicPiece_extract piece hchk
  dsimp only at hext
  obtain ⟨⟨hld_pos, hrd_pos, _⟩, hperm, hfloors, hsort, hstrip, _⟩ := hext
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  let rn : ℕ := n % p
  let τ : ℝ := (rn : ℝ) / (p : ℝ)
  let q0 := periodicFloorVal 28 piece.ln piece.ld piece.rn piece.rd
  let q1 := periodicFloorVal 32 piece.ln piece.ld piece.rn piece.rd
  let q2 := periodicFloorVal 34 piece.ln piece.ld piece.rn piece.rd
  let q3 := periodicFloorVal 38 piece.ln piece.ld piece.rn piece.rd
  let q4 := periodicFloorVal 40 piece.ln piece.ld piece.rn piece.rd
  let q5 := periodicFloorVal 42 piece.ln piece.ld piece.rn piece.rd
  let q6 := periodicFloorVal 46 piece.ln piece.ld piece.rn piece.rd
  let q7 := periodicFloorVal 50 piece.ln piece.ld piece.rn piece.rd
  let q8 := periodicFloorVal 54 piece.ln piece.ld piece.rn piece.rd
  let q9 := periodicFloorVal 58 piece.ln piece.ld piece.rn piece.rd
  let q10 := periodicFloorVal 60 piece.ln piece.ld piece.rn piece.rd
  let q11 := periodicFloorVal 140 piece.ln piece.ld piece.rn piece.rd
  let z41 := periodicFloorVal 41 piece.ln piece.ld piece.rn piece.rd
  let z43 := periodicFloorVal 43 piece.ln piece.ld piece.rn piece.rd
  have hfl_strict : ∀ {m q : ℕ}, 0 < m → periodicFloorOk m q piece.ln piece.ld piece.rn piece.rd = true →
      q * p ≤ m * rn ∧ m * rn < (q + 1) * p ∧ (m * rn) / p = q := by
    intro m q hm hq
    unfold periodicFloorOk at hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    have hldR : (0 : ℝ) < (piece.ld : ℝ) := by exact_mod_cast hld_pos
    have hrdR : (0 : ℝ) < (piece.rd : ℝ) := by exact_mod_cast hrd_pos
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have h1 : (q : ℝ) < (m : ℝ) * τ := by
      have hql : (q : ℝ) ≤ (m : ℝ) * ((piece.ln : ℝ) / (piece.ld : ℝ)) := by
        have : (q : ℝ) * (piece.ld : ℝ) ≤ (m : ℝ) * (piece.ln : ℝ) := by exact_mod_cast hq.1
        rw [← mul_div_assoc, le_div_iff₀ hldR]; exact this
      exact hql.trans_lt (mul_lt_mul_of_pos_left hlo hmR)
    have h2 : (m : ℝ) * τ < ((q + 1 : ℕ) : ℝ) := by
      have hqr : (m : ℝ) * ((piece.rn : ℝ) / (piece.rd : ℝ)) ≤ ((q + 1 : ℕ) : ℝ) := by
        have : (m : ℝ) * (piece.rn : ℝ) ≤ ((q + 1 : ℕ) : ℝ) * (piece.rd : ℝ) := by exact_mod_cast hq.2
        rw [← mul_div_assoc, div_le_iff₀ hrdR]; exact this
      exact (mul_lt_mul_of_pos_left hhi hmR).trans_le hqr
    have h1' : (q : ℝ) * (p : ℝ) < (m : ℝ) * (rn : ℝ) := by
      have := mul_lt_mul_of_pos_right h1 hpR
      rwa [mul_div_assoc', div_mul_cancel₀ _ hpR.ne'] at this
    have h2' : (m : ℝ) * (rn : ℝ) < ((q + 1 : ℕ) : ℝ) * (p : ℝ) := by
      have := mul_lt_mul_of_pos_right h2 hpR
      rwa [mul_div_assoc', div_mul_cancel₀ _ hpR.ne'] at this
    have hloN : q * p ≤ m * rn := le_of_lt (by exact_mod_cast h1')
    have hhiN : m * rn < (q + 1) * p := by exact_mod_cast h2'
    have hdiv : (m * rn) / p = q := by
      have hge : q ≤ (m * rn) / p := (Nat.le_div_iff_mul_le hp).mpr hloN
      have hlt : (m * rn) / p < q + 1 := (Nat.div_lt_iff_lt_mul hp).mpr hhiN
      omega
    exact ⟨hloN, hhiN, hdiv⟩
  rcases hfloors with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hz41, hz43⟩
  have h0 := hfl_strict (by omega) hq0
  have h1 := hfl_strict (by omega) hq1
  have h2 := hfl_strict (by omega) hq2
  have h3 := hfl_strict (by omega) hq3
  have h4 := hfl_strict (by omega) hq4
  have h5 := hfl_strict (by omega) hq5
  have h6 := hfl_strict (by omega) hq6
  have h7 := hfl_strict (by omega) hq7
  have h8 := hfl_strict (by omega) hq8
  have h9 := hfl_strict (by omega) hq9
  have h10 := hfl_strict (by omega) hq10
  have h11 := hfl_strict (by omega) hq11
  have h41 := hfl_strict (by omega) hz41
  have h43 := hfl_strict (by omega) hz43
  let getQ2 : ℕ → ℕ
    | 0 => q0 | 1 => q1 | 2 => q2 | 3 => q3 | 4 => q4 | 5 => q5
    | 6 => q6 | 7 => q7 | 8 => q8 | 9 => q9 | 10 => q10 | _ => q11
  let vPole : ℤ := (q0 : ℤ) + 2 * (q1 : ℤ) + (q2 : ℤ) + (q3 : ℤ) +
    2 * (q4 : ℤ) + (q5 : ℤ) + (q6 : ℤ) + 5 * (q7 : ℤ)
  let vFact : ℤ := vPole - 2 * (3 * (q4 : ℤ) + (z41 : ℤ) + (z43 : ℤ))
  let pts : List (ℤ × ℤ) :=
    (0, 0) :: piece.perm.map (fun idx => periodicLine2 (radiusValNat idx) (getQ2 idx)) ++ [(1, 0)]
  obtain ⟨hplen, hpidx⟩ := isPerm12_spec hperm
  have hptslen : pts.length = 14 := by simp [pts, hplen]
  let p0 := indexOfNat piece.perm 0
  let p1 := indexOfNat piece.perm 1
  let p2 := indexOfNat piece.perm 2
  let p3 := indexOfNat piece.perm 3
  let p4 := indexOfNat piece.perm 4
  let p5 := indexOfNat piece.perm 5
  let p6 := indexOfNat piece.perm 6
  let p7 := indexOfNat piece.perm 7
  let p8 := indexOfNat piece.perm 8
  let p9 := indexOfNat piece.perm 9
  let p10 := indexOfNat piece.perm 10
  let p11 := indexOfNat piece.perm 11
  let ptAt (i : ℕ) : ℤ × ℤ := pts[i]?.getD (0, 0)
  let evalZ (u : ℤ × ℤ) : ℤ := u.1 * (p : ℤ) + u.2 * (rn : ℤ)
  let evalR (u : ℤ × ℤ) : ℝ := (u.1 : ℝ) + (u.2 : ℝ) * τ
  have hevalZR : ∀ u : ℤ × ℤ, (evalZ u : ℝ) = evalR u * (p : ℝ) := by
    intro u; dsimp [evalZ, evalR, τ]; push_cast; field_simp [hpR.ne']
  have hpt0 : ptAt 0 = (0, 0) := by simp [ptAt, pts]
  have hpt13 : ptAt 13 = (1, 0) := by
    have hlen12 : (piece.perm.map (fun idx => periodicLine2 (radiusValNat idx) (getQ2 idx))).length = 12 := by
      simp [hplen]
    dsimp [ptAt, pts]
    rw [List.getElem?_append_right (by omega), hlen12]
    simp
  have hpt_rad : ∀ k < 12, ptAt (indexOfNat piece.perm k + 1) =
      periodicLine2 (radiusValNat k) (getQ2 k) := by
    intro k hk
    obtain ⟨hlt, hget⟩ := hpidx k hk
    dsimp [ptAt, pts]
    rw [List.getElem?_append_left (by simp [hplen]; omega),
      List.getElem?_map, hget]
    rfl
  have hpt_monoR : ∀ {i j : ℕ}, i ≤ j → j < 14 → evalR (ptAt i) ≤ evalR (ptAt j) := by
    intro i j hij hj
    have hj' : j < pts.length := by omega
    have hi' : i < pts.length := Nat.lt_of_le_of_lt hij hj'
    have h1 : ptAt i = pts[i]'hi' := by dsimp [ptAt]; rw [List.getElem?_eq_getElem hi']; rfl
    have h2 : ptAt j = pts[j]'hj' := by dsimp [ptAt]; rw [List.getElem?_eq_getElem hj']; rfl
    rw [h1, h2]
    exact checkSortedLines_mono hld_pos hrd_pos hlo.le hhi.le hsort hij hj'
  have hpt_monoZ : ∀ {i j : ℕ}, i ≤ j → j < 14 → evalZ (ptAt i) ≤ evalZ (ptAt j) := by
    intro i j hij hj
    have hR := hpt_monoR hij hj
    have hmul : (evalZ (ptAt i) : ℝ) ≤ (evalZ (ptAt j) : ℝ) := by
      rw [hevalZR, hevalZR]; exact mul_le_mul_of_nonneg_right hR hpR.le
    exact_mod_cast hmul
  -- Exact `sixFactVal n p` expression
  have hfact_eq : sixFactVal n p = vFact + 174 * ((n / p : ℕ) : ℤ) := by
    rw [sixFactVal_eq_mod n p hp]
    dsimp [rn] at h0 h1 h2 h3 h4 h5 h6 h7 h41 h43
    rw [h0.2.2, h1.2.2, h2.2.2, h3.2.2, h4.2.2, h5.2.2, h6.2.2, h7.2.2, h41.2.2, h43.2.2]
  -- Define boundary set `Bdy` and 13 open strips `Strip g`
  let Bdy : Finset (Fin (p / 2 + 1)) :=
    Finset.univ.filter (fun c => ∃ i : Fin 14, 2 * (c.val : ℤ) = evalZ (ptAt i.val))
  let Strip (g : ℕ) : Finset (Fin (p / 2 + 1)) :=
    Finset.univ.filter (fun c => evalZ (ptAt g) < 2 * (c.val : ℤ) ∧ 2 * (c.val : ℤ) < evalZ (ptAt (g + 1)))
  -- Strip value function `Bfun g`
  let valFun (g : ℕ) : ℤ := (4 - vFact)
    + periodicDelta q0 p0 g + 2 * periodicDelta q1 p1 g
    + periodicDelta q2 p2 g + periodicDelta q3 p3 g
    + 2 * periodicDelta q4 p4 g + periodicDelta q5 p5 g
    + periodicDelta q6 p6 g + 5 * periodicDelta q7 p7 g
    + periodicDelta q8 p8 g + periodicDelta q9 p9 g
    + 3 * periodicDelta q10 p10 g - 5 * periodicDelta q11 p11 g
  let Bfun (g : ℕ) : ℤ := if valFun g ≤ 0 then 0 else valFun g
  -- On every `c ∈ Strip g` (`g < 13`), `sixCoarsePeriodicCost n p c = Bfun g`!
  have hstrip_val : ∀ g < 13, ∀ c ∈ Strip g,
      (sixCoarsePeriodicCost n p c : ℤ) = Bfun g := by
    intro g hg c hc
    have hmem := (Finset.mem_filter.mp hc).2
    have hc0 : 0 < c.val := by
      have hge0 : (0 : ℤ) ≤ evalZ (ptAt g) := by
        have := hpt_monoZ (Nat.zero_le g) (by omega)
        have h0z : evalZ (ptAt 0) = 0 := by rw [hpt0]; simp [evalZ]
        linarith
      omega
    have hchalf : 2 * c.val < p := by
      have hlep : evalZ (ptAt (g + 1)) ≤ (p : ℤ) := by
        have := hpt_monoZ (show g + 1 ≤ 13 by omega) (by omega)
        have h13z : evalZ (ptAt 13) = (p : ℤ) := by rw [hpt13]; simp [evalZ]
        linarith
      omega
    have hdel : ∀ k < 12,
        symBlockMultCount p (radiusValNat k * rn) (c.val : ℤ) =
          periodicDelta (getQ2 k) (indexOfNat piece.perm k) g := by
      intro k hk
      obtain ⟨hpos_lt, _⟩ := hpidx k hk
      have hline_eq := hpt_rad k hk
      have hq2_bnds : getQ2 k * p ≤ 2 * radiusValNat k * rn ∧
          2 * radiusValNat k * rn ≤ (getQ2 k + 1) * p := by
        interval_cases k
        · exact ⟨h0.1, h0.2.1.le⟩
        · exact ⟨h1.1, h1.2.1.le⟩
        · exact ⟨h2.1, h2.2.1.le⟩
        · exact ⟨h3.1, h3.2.1.le⟩
        · exact ⟨h4.1, h4.2.1.le⟩
        · exact ⟨h5.1, h5.2.1.le⟩
        · exact ⟨h6.1, h6.2.1.le⟩
        · exact ⟨h7.1, h7.2.1.le⟩
        · exact ⟨h8.1, h8.2.1.le⟩
        · exact ⟨h9.1, h9.2.1.le⟩
        · exact ⟨h10.1, h10.2.1.le⟩
        · exact ⟨h11.1, h11.2.1.le⟩
      apply symBlockMultCount_eq_periodicDelta p (radiusValNat k) rn (getQ2 k)
        (indexOfNat piece.perm k) g hp c.val hc0 hchalf hq2_bnds.1 hq2_bnds.2
      dsimp only
      rw [← hline_eq]
      constructor
      · intro hgp
        exact lt_of_lt_of_le hmem.2 (hpt_monoZ (by omega) (by omega))
      · intro hngp
        exact lt_of_le_of_lt (hpt_monoZ (by omega) (by omega)) hmem.1
    have hd0 := hdel 0 (by omega)
    have hd1 := hdel 1 (by omega)
    have hd2 := hdel 2 (by omega)
    have hd3 := hdel 3 (by omega)
    have hd4 := hdel 4 (by omega)
    have hd5 := hdel 5 (by omega)
    have hd6 := hdel 6 (by omega)
    have hd7 := hdel 7 (by omega)
    have hd8 := hdel 8 (by omega)
    have hd9 := hdel 9 (by omega)
    have hd10 := hdel 10 (by omega)
    have hd11 := hdel 11 (by omega)
    dsimp [radiusValNat, getQ2] at hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10 hd11
    unfold sixCoarsePeriodicCost
    have hinner : (4 + (sixPoleClassCount n p (c.val : ℤ) : ℤ) -
        (sixZeroClassCount n p (c.val : ℤ) : ℤ) - sixFactVal n p) = valFun g := by
      rw [sixPoleClassCount_eq_symBlocks n p hp, sixZeroClassCount_eq_symBlocks n p hp, hfact_eq]
      rw [symBlockMultCount_mod p 14 n hp, symBlockMultCount_mod p 16 n hp,
        symBlockMultCount_mod p 17 n hp, symBlockMultCount_mod p 19 n hp,
        symBlockMultCount_mod p 20 n hp, symBlockMultCount_mod p 21 n hp,
        symBlockMultCount_mod p 23 n hp, symBlockMultCount_mod p 25 n hp,
        symBlockMultCount_mod p 27 n hp, symBlockMultCount_mod p 29 n hp,
        symBlockMultCount_mod p 30 n hp, symBlockMultCount_mod p 70 n hp]
      rw [show symBlockMultCount p (14 * (n % p)) (c.val : ℤ) = periodicDelta q0 p0 g from hd0,
        show symBlockMultCount p (16 * (n % p)) (c.val : ℤ) = periodicDelta q1 p1 g from hd1,
        show symBlockMultCount p (17 * (n % p)) (c.val : ℤ) = periodicDelta q2 p2 g from hd2,
        show symBlockMultCount p (19 * (n % p)) (c.val : ℤ) = periodicDelta q3 p3 g from hd3,
        show symBlockMultCount p (20 * (n % p)) (c.val : ℤ) = periodicDelta q4 p4 g from hd4,
        show symBlockMultCount p (21 * (n % p)) (c.val : ℤ) = periodicDelta q5 p5 g from hd5,
        show symBlockMultCount p (23 * (n % p)) (c.val : ℤ) = periodicDelta q6 p6 g from hd6,
        show symBlockMultCount p (25 * (n % p)) (c.val : ℤ) = periodicDelta q7 p7 g from hd7,
        show symBlockMultCount p (27 * (n % p)) (c.val : ℤ) = periodicDelta q8 p8 g from hd8,
        show symBlockMultCount p (29 * (n % p)) (c.val : ℤ) = periodicDelta q9 p9 g from hd9,
        show symBlockMultCount p (30 * (n % p)) (c.val : ℤ) = periodicDelta q10 p10 g from hd10,
        show symBlockMultCount p (70 * (n % p)) (c.val : ℤ) = periodicDelta q11 p11 g from hd11]
      dsimp [valFun]
      ring
    rw [hinner]
    dsimp [Bfun]
    split_ifs with hle <;> omega
  -- Every `c : Fin (p / 2 + 1)` is in `Bdy` or some `Strip g` (`g < 13`)
  have hcover_c : ∀ c : Fin (p / 2 + 1), c ∈ Bdy ∨ ∃ g ∈ Finset.range 13, c ∈ Strip g := by
    intro c
    by_cases hcb : c ∈ Bdy
    · exact Or.inl hcb
    · right
      have hne : ∀ i : Fin 14, 2 * (c.val : ℤ) ≠ evalZ (ptAt i.val) := by
        intro i heq; exact hcb (Finset.mem_filter.mpr ⟨Finset.mem_univ c, ⟨i, heq⟩⟩)
      have h0lt : evalZ (ptAt 0) < 2 * (c.val : ℤ) := by
        have h0z : evalZ (ptAt 0) = 0 := by rw [hpt0]; simp [evalZ]
        have hne0 : 2 * (c.val : ℤ) ≠ evalZ (ptAt 0) := hne ⟨0, by omega⟩
        omega
      have hlt13 : 2 * (c.val : ℤ) < evalZ (ptAt 13) := by
        have h13z : evalZ (ptAt 13) = (p : ℤ) := by rw [hpt13]; simp [evalZ]
        have hne13 : 2 * (c.val : ℤ) ≠ evalZ (ptAt 13) := hne ⟨13, by omega⟩
        have hc_le : 2 * c.val ≤ p := by omega
        omega
      -- Pick largest `g < 14` with `evalZ (ptAt g) < 2 * c.val`
      let S : Finset ℕ := (Finset.range 14).filter (fun i => evalZ (ptAt i) < 2 * (c.val : ℤ))
      have hSne : S.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h0lt⟩⟩
      let g := S.max' hSne
      have hg_mem := Finset.mem_filter.mp (Finset.max'_mem S hSne)
      have hg_lt14 : g < 14 := Finset.mem_range.mp hg_mem.1
      have hg_lt13 : g < 13 := by
        by_contra hge
        have hg13 : S.max' hSne = 13 := by dsimp only [g] at hge hg_lt14; omega
        have hbad13 := hg_mem.2
        rw [hg13] at hbad13
        omega
      have hg_next : 2 * (c.val : ℤ) < evalZ (ptAt (g + 1)) := by
        have hnot : g + 1 ∉ S := fun hm => by
          have := Finset.le_max' S (g + 1) hm; omega
        have hge : 2 * (c.val : ℤ) ≤ evalZ (ptAt (g + 1)) := by
          by_contra hlt; push Not at hlt
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hlt⟩)
        have hne' : 2 * (c.val : ℤ) ≠ evalZ (ptAt (g + 1)) := hne ⟨g + 1, by omega⟩
        omega
      exact ⟨g, Finset.mem_range.mpr hg_lt13,
        Finset.mem_filter.mpr ⟨Finset.mem_univ c, ⟨hg_mem.2, hg_next⟩⟩⟩
  -- Bound `Bdy.card ≤ 14`
  have hBdy_card : Bdy.card ≤ 14 := by
    classical
    let pick (c : Fin (p / 2 + 1)) : Fin 14 :=
      if h : ∃ i : Fin 14, 2 * (c.val : ℤ) = evalZ (ptAt i.val) then Classical.choose h else ⟨0, by omega⟩
    have hcard_le : Bdy.card ≤ (Finset.univ : Finset (Fin 14)).card := by
      apply Finset.card_le_card_of_injOn pick
      · intro _ _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
      · intro c₁ hc₁ c₂ hc₂ heq
        have h1 : ∃ i : Fin 14, 2 * (c₁.val : ℤ) = evalZ (ptAt i.val) := (Finset.mem_filter.mp hc₁).2
        have h2 : ∃ i : Fin 14, 2 * (c₂.val : ℤ) = evalZ (ptAt i.val) := (Finset.mem_filter.mp hc₂).2
        dsimp only [pick] at heq
        simp only [h1, h2, dite_true] at heq
        have hs1 := Classical.choose_spec h1
        have hs2 := Classical.choose_spec h2
        rw [heq] at hs1
        exact Fin.ext (by omega)
    simpa using hcard_le
  have hBdy_sum : (∑ c ∈ Bdy, (sixCoarsePeriodicCost n p c : ℝ)) ≤ 252 := by
    calc
      ∑ c ∈ Bdy, (sixCoarsePeriodicCost n p c : ℝ)
          ≤ ∑ _c ∈ Bdy, (18 : ℝ) := Finset.sum_le_sum (fun c _ => by
              exact_mod_cast sixCoarsePeriodicCost_le_18 n p hp c)
      _ = (Bdy.card : ℝ) * 18 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 14 * 18 := by
            have : (Bdy.card : ℝ) ≤ 14 := by exact_mod_cast hBdy_card
            linarith
      _ = 252 := by norm_num
  -- Bound each `Strip g` sum
  have hStrip_sum : ∀ g ∈ Finset.range 13,
      (∑ c ∈ Strip g, (sixCoarsePeriodicCost n p c : ℝ)) ≤
        ((p : ℝ) / 2) * ((Bfun g : ℝ) * (evalR (ptAt (g + 1)) - evalR (ptAt g))) + 18 := by
    intro g hg
    have hg13 : g < 13 := Finset.mem_range.mp hg
    have hBnn : (0 : ℝ) ≤ (Bfun g : ℝ) := by
      have : (0 : ℤ) ≤ Bfun g := by dsimp [Bfun]; split_ifs <;> omega
      exact_mod_cast this
    have hdiff_nn : 0 ≤ evalR (ptAt (g + 1)) - evalR (ptAt g) :=
      sub_nonneg.mpr (hpt_monoR (by omega) (by omega))
    by_cases hemp : Strip g = ∅
    · rw [hemp, Finset.sum_empty]
      have : 0 ≤ ((p : ℝ) / 2) * ((Bfun g : ℝ) * (evalR (ptAt (g + 1)) - evalR (ptAt g))) := by
        positivity
      linarith
    · obtain ⟨c₀, hc₀⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      have hB18 : (Bfun g : ℝ) ≤ 18 := by
        have h1 : (sixCoarsePeriodicCost n p c₀ : ℤ) = Bfun g := hstrip_val g hg13 c₀ hc₀
        have h2 : sixCoarsePeriodicCost n p c₀ ≤ 18 := sixCoarsePeriodicCost_le_18 n p hp c₀
        have : Bfun g ≤ 18 := by omega
        exact_mod_cast this
      have hcard_le : ((Strip g).card : ℝ) ≤
          ((p : ℝ) / 2) * (evalR (ptAt (g + 1)) - evalR (ptAt g)) + 1 := by
        have himg : ((Strip g).image (fun c : Fin (p / 2 + 1) => c.val)).card = (Strip g).card :=
          Finset.card_image_of_injective _ Fin.val_injective
        rw [← himg]
        have hnat := nat_open_interval_card_le
          (((p : ℝ) / 2) * evalR (ptAt g)) (((p : ℝ) / 2) * evalR (ptAt (g + 1)))
          (mul_le_mul_of_nonneg_left (hpt_monoR (by omega) (by omega)) (by positivity))
          ((Strip g).image (fun c : Fin (p / 2 + 1) => c.val)) (by
            intro m hm
            obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hm
            have hmem := (Finset.mem_filter.mp hc).2
            have h1 : (evalZ (ptAt g) : ℝ) < 2 * (c.val : ℝ) := by exact_mod_cast hmem.1
            have h2 : 2 * (c.val : ℝ) < (evalZ (ptAt (g + 1)) : ℝ) := by exact_mod_cast hmem.2
            rw [hevalZR] at h1 h2
            constructor <;> linarith)
        linarith
      calc
        ∑ c ∈ Strip g, (sixCoarsePeriodicCost n p c : ℝ)
            = ∑ _c ∈ Strip g, (Bfun g : ℝ) := by
              apply Finset.sum_congr rfl; intro c hc
              exact_mod_cast hstrip_val g hg13 c hc
        _ = ((Strip g).card : ℝ) * (Bfun g : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (((p : ℝ) / 2) * (evalR (ptAt (g + 1)) - evalR (ptAt g)) + 1) * (Bfun g : ℝ) :=
              mul_le_mul_of_nonneg_right hcard_le hBnn
        _ ≤ ((p : ℝ) / 2) * ((Bfun g : ℝ) * (evalR (ptAt (g + 1)) - evalR (ptAt g))) + 18 := by
              nlinarith
  -- Sum over `c : Fin (p / 2 + 1)` via `Bdy ∪ ⋃_{g < 13} Strip g`
  have htotal : (∑ c : Fin (p / 2 + 1), (sixCoarsePeriodicCost n p c : ℝ)) ≤
      (∑ c ∈ Bdy, (sixCoarsePeriodicCost n p c : ℝ)) +
      ∑ g ∈ Finset.range 13, ∑ c ∈ Strip g, (sixCoarsePeriodicCost n p c : ℝ) := by
    calc
      ∑ c : Fin (p / 2 + 1), (sixCoarsePeriodicCost n p c : ℝ)
          ≤ ∑ c : Fin (p / 2 + 1),
              ((if c ∈ Bdy then (sixCoarsePeriodicCost n p c : ℝ) else 0) +
               ∑ g ∈ Finset.range 13, if c ∈ Strip g then (sixCoarsePeriodicCost n p c : ℝ) else 0) := by
            apply Finset.sum_le_sum; intro c _
            rcases hcover_c c with hcb | ⟨g₀, hg₀, hcg⟩
            · have hnn : 0 ≤ ∑ g ∈ Finset.range 13,
                  if c ∈ Strip g then (sixCoarsePeriodicCost n p c : ℝ) else 0 :=
                Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
              simp only [hcb, ite_true]
              exact le_add_of_nonneg_right hnn
            · have h1 : (sixCoarsePeriodicCost n p c : ℝ) ≤
                  ∑ g ∈ Finset.range 13, if c ∈ Strip g then (sixCoarsePeriodicCost n p c : ℝ) else 0 := by
                have := Finset.single_le_sum
                  (f := fun g => if c ∈ Strip g then (sixCoarsePeriodicCost n p c : ℝ) else 0)
                  (fun g _ => by split_ifs <;> positivity) hg₀
                simp only [hcg, ite_true] at this
                exact this
              have hnn : 0 ≤ if c ∈ Bdy then (sixCoarsePeriodicCost n p c : ℝ) else 0 := by
                split_ifs <;> positivity
              exact le_add_of_nonneg_of_le hnn h1
      _ = (∑ c : Fin (p / 2 + 1), if c ∈ Bdy then (sixCoarsePeriodicCost n p c : ℝ) else 0) +
          ∑ c : Fin (p / 2 + 1), ∑ g ∈ Finset.range 13,
            if c ∈ Strip g then (sixCoarsePeriodicCost n p c : ℝ) else 0 := Finset.sum_add_distrib
      _ = (∑ c ∈ Bdy, (sixCoarsePeriodicCost n p c : ℝ)) +
          ∑ g ∈ Finset.range 13, ∑ c ∈ Strip g, (sixCoarsePeriodicCost n p c : ℝ) := by
            congr 1
            · rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
            · rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro g _
              rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  -- Match the strip sum against `piece.a0 + piece.a1 * τ` via `sumStrips_eval`
  have hsum_strips_eq :
      (∑ g ∈ Finset.range 13, (Bfun g : ℝ) * (evalR (ptAt (g + 1)) - evalR (ptAt g))) =
        (piece.a0 : ℝ) + (piece.a1 : ℝ) * τ := by
    have hse := sumStrips_eval vFact q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
      p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 pts 0 0 0 τ
    dsimp only at hse
    rw [hstrip.1, hstrip.2, hptslen] at hse
    simp only [Int.cast_zero, zero_mul, zero_add, show 14 - 1 = 13 from rfl] at hse
    exact hse.symm
  have hstrips_le :
      (∑ g ∈ Finset.range 13, ∑ c ∈ Strip g, (sixCoarsePeriodicCost n p c : ℝ)) ≤
        ((p : ℝ) / 2) * ((piece.a0 : ℝ) + (piece.a1 : ℝ) * τ) + 234 := by
    calc
      ∑ g ∈ Finset.range 13, ∑ c ∈ Strip g, (sixCoarsePeriodicCost n p c : ℝ)
          ≤ ∑ g ∈ Finset.range 13,
              (((p : ℝ) / 2) * ((Bfun g : ℝ) * (evalR (ptAt (g + 1)) - evalR (ptAt g))) + 18) :=
            Finset.sum_le_sum hStrip_sum
      _ = ((p : ℝ) / 2) * (∑ g ∈ Finset.range 13,
              (Bfun g : ℝ) * (evalR (ptAt (g + 1)) - evalR (ptAt g))) + 234 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range]
            norm_num
      _ = ((p : ℝ) / 2) * ((piece.a0 : ℝ) + (piece.a1 : ℝ) * τ) + 234 := by
            rw [hsum_strips_eq]
  linarith only [htotal, hBdy_sum, hstrips_le]

/-! ## Combining the 6 certified periodic shards -/

def allPeriodicPieces : List PeriodicPiece :=
  (((((OddZetaSix.PeriodicData.Shard0.shard0Pieces ++
       OddZetaSix.PeriodicData.Shard1.shard1Pieces) ++
       OddZetaSix.PeriodicData.Shard2.shard2Pieces) ++
       OddZetaSix.PeriodicData.Shard3.shard3Pieces) ++
       OddZetaSix.PeriodicData.Shard4.shard4Pieces) ++
       OddZetaSix.PeriodicData.Shard5.shard5Pieces)

theorem allPeriodicPieces_valid :
    checkPeriodicShard 0 1 1 1 611246243 2688712227 allPeriodicPieces = true := by
  unfold allPeriodicPieces
  have h01 := checkPeriodicShard_append_eq (f3 := 202521158) (c3 := 726820695) rfl rfl
    OddZetaSix.PeriodicData.Shard0.shard0_valid OddZetaSix.PeriodicData.Shard1.shard1_valid
  have h02 := checkPeriodicShard_append_eq (f3 := 307731599) (c3 := 1718419500) rfl rfl
    h01 OddZetaSix.PeriodicData.Shard2.shard2_valid
  have h03 := checkPeriodicShard_append_eq (f3 := 407767934) (c3 := 2184806188) rfl rfl
    h02 OddZetaSix.PeriodicData.Shard3.shard3_valid
  have h04 := checkPeriodicShard_append_eq (f3 := 508072006) (c3 := 2477411120) rfl rfl
    h03 OddZetaSix.PeriodicData.Shard4.shard4_valid
  exact checkPeriodicShard_append_eq (f3 := 611246243) (c3 := 2688712227) rfl rfl
    h04 OddZetaSix.PeriodicData.Shard5.shard5_valid

/-! ## Main periodic-band rate theorem (`C₀ ≤ 552 / 1000`) -/

/-- Helper relating `(xs.map g).sum` to a `Finset.range xs.length` sum without `ofFn`. -/
theorem list_map_sum_eq_range {α : Type*} (xs : List α) (d : α) (g : α → ℕ) :
    (xs.map g).sum = ∑ j ∈ Finset.range xs.length, g (xs[j]?.getD d) := by
  induction xs with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ', ih]
    simp [add_comm]

/-- Exceptional primes for the periodic band: all cutoff primes below `N₀`, and divisors of `n`
above `n / 10000` for `n ≥ N₀`. -/
private def periodicExceptional (N₀ n : ℕ) : Finset ℕ :=
  if n < N₀ then sixCutoffPrimes n
  else (sixCutoffPrimes n).filter (fun p => p ∣ n ∧ ((1 : ℝ) / 10000) * (n : ℝ) < (p : ℝ))

/-- Generic periodic-band rate theorem for any certified `List PeriodicPiece` covering `[0, 1]`. -/
theorem sixPeriodicBand_rate_of_shard (ps : List PeriodicPiece) (fTotal cTotal Kmax : ℕ)
    (hKmax : Kmax = 10000)
    (hval : checkPeriodicShard 0 1 1 1 fTotal cTotal ps = true)
    (hcert : ((15 : ℝ) * (((cTotal : ℝ) / (certDen : ℝ)) +
        (1 / 11 + 1 / (12 * 11 ^ 2)) * ((fTotal : ℝ) / (certDen : ℝ)))) / 750 ≤
        (552 : ℝ) / 1000) :
    ∀ δ > 0, ∀ᶠ n : ℕ in atTop,
      sixBandPrimeCost n ((1 : ℝ) / 10000) ((7 : ℝ) / 2) / sixNorm n ≤ (552 : ℝ) / 1000 + δ := by
  unfold checkPeriodicShard at hval
  obtain ⟨hall_chk, hFsum, hCsum⟩ := checkPeriodicRun_spec hval
  simp only [zero_add] at hFsum hCsum
  have hpiece_props : ∀ piece ∈ ps,
      0 < piece.ld ∧ 0 < piece.rd ∧ piece.ln * piece.rd < piece.rn * piece.ld ∧
      0 ≤ piece.a0 * (piece.ld : ℤ) + piece.a1 * (piece.ln : ℤ) ∧
      0 ≤ piece.a0 * (piece.rd : ℤ) + piece.a1 * (piece.rn : ℤ) ∧
      affIntCeil piece.a0 piece.a1 piece.ln piece.ld piece.rn piece.rd certDen ≤ piece.fbarNum ∧
      periodic12Ceil piece.a0 piece.a1 piece.ln piece.ld piece.rn piece.rd ≤ piece.c0Num := by
    intro piece hp
    have hext := checkPeriodicPiece_extract piece (hall_chk piece hp)
    dsimp only at hext
    obtain ⟨⟨h1, h2, h3⟩, _, _, _, _, ⟨h4, h5, h6, h7⟩⟩ := hext
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  let L := ps.length
  let getPiece (j : ℕ) : PeriodicPiece := ps[j]?.getD ⟨0, 1, 1, 1, [], 0, 0, 0, 0⟩
  let tlo (idx : ℕ × ℕ) : ℝ :=
    let p := getPiece idx.2
    max ((2 : ℝ) / 7) ((idx.1 : ℝ) + (p.ln : ℝ) / (p.ld : ℝ))
  let thi (idx : ℕ × ℕ) : ℝ :=
    let p := getPiece idx.2
    (idx.1 : ℝ) + (p.rn : ℝ) / (p.rd : ℝ)
  let s : Finset (ℕ × ℕ) :=
    (Finset.range Kmax ×ˢ Finset.range L).filter (fun idx => tlo idx < thi idx)
  let lo (idx : ℕ × ℕ) : ℝ := 1 / thi idx
  let hi (idx : ℕ × ℕ) : ℝ := 1 / tlo idx
  let f (idx : ℕ × ℕ) (x : ℝ) : ℝ :=
    let p := getPiece idx.2
    15 * (1 + x / 6) * ((p.a0 : ℝ) + (p.a1 : ℝ) * (1 / x - (idx.1 : ℝ)))
  let maxD : ℕ := periodicMaxDen ps
  let N₀ : ℕ := max 20000000000 (10000 * (maxD + 1))
  let E : ℕ → Finset ℕ := periodicExceptional N₀
  have hEsub : ∀ n, E n ⊆ sixCutoffPrimes n := by
    intro n; dsimp only [E]; unfold periodicExceptional; split_ifs
    · exact Finset.Subset.rfl
    · exact Finset.filter_subset _ _
  have hEcard : ∀ᶠ n : ℕ in atTop, (E n).card ≤ Kmax := by
    filter_upwards [eventually_ge_atTop N₀] with n hn
    have hnotlt : ¬ n < N₀ := by omega
    dsimp only [E]; unfold periodicExceptional; simp only [hnotlt, ite_false]
    have hn_pos : 0 < n := by dsimp [N₀] at hn; omega
    have hinj : Set.InjOn (fun p : ℕ => n / p)
        ↑((sixCutoffPrimes n).filter (fun p => p ∣ n ∧ ((1 : ℝ) / 10000) * (n : ℝ) < (p : ℝ))) := by
      intro p₁ hp₁ p₂ hp₂ hdiv
      dsimp only at hdiv
      have hd1 : p₁ ∣ n := (Finset.mem_filter.mp hp₁).2.1
      have hd2 : p₂ ∣ n := (Finset.mem_filter.mp hp₂).2.1
      have h1 : p₁ * (n / p₁) = n := Nat.mul_div_cancel' hd1
      have h2 : p₂ * (n / p₂) = n := Nat.mul_div_cancel' hd2
      have hqpos : 0 < n / p₁ := by
        by_contra h0
        have hq0 : n / p₁ = 0 := Nat.eq_zero_of_not_pos h0
        rw [hq0, mul_zero] at h1; omega
      rw [hdiv] at h1
      exact Nat.eq_of_mul_eq_mul_right (hdiv ▸ hqpos) (h1.trans h2.symm)
    have himg : ((sixCutoffPrimes n).filter (fun p => p ∣ n ∧ ((1 : ℝ) / 10000) * (n : ℝ) < (p : ℝ))).image
        (fun p => n / p) ⊆ Finset.range Kmax := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      have hgt : ((1 : ℝ) / 10000) * (n : ℝ) < (p : ℝ) := (Finset.mem_filter.mp hp).2.2
      have hppos : 0 < p := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2.pos
      have hlt : n < Kmax * p := by
        have : (n : ℝ) < 10000 * (p : ℝ) := by linarith
        have : n < 10000 * p := by exact_mod_cast this
        rw [hKmax]; exact this
      exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hppos).mpr hlt)
    calc
      ((sixCutoffPrimes n).filter (fun p => p ∣ n ∧ ((1 : ℝ) / 10000) * (n : ℝ) < (p : ℝ))).card
          = (((sixCutoffPrimes n).filter _).image (fun p => n / p)).card :=
            (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range Kmax).card := Finset.card_le_card himg
      _ = Kmax := Finset.card_range Kmax
  have haff_nn_piece : ∀ piece ∈ ps, ∀ u : ℝ,
      (piece.ln : ℝ) / (piece.ld : ℝ) ≤ u → u ≤ (piece.rn : ℝ) / (piece.rd : ℝ) →
      0 ≤ (piece.a0 : ℝ) + (piece.a1 : ℝ) * u := by
    intro piece hp u h1 h2
    obtain ⟨hld, hrd, _, hnnL, hnnR, _, _⟩ := hpiece_props piece hp
    have hldR : (0 : ℝ) < (piece.ld : ℝ) := by exact_mod_cast hld
    have hrdR : (0 : ℝ) < (piece.rd : ℝ) := by exact_mod_cast hrd
    have hL : 0 ≤ (piece.a0 : ℝ) + (piece.a1 : ℝ) * ((piece.ln : ℝ) / (piece.ld : ℝ)) := by
      have : (0 : ℝ) ≤ (piece.a0 : ℝ) * (piece.ld : ℝ) + (piece.a1 : ℝ) * (piece.ln : ℝ) := by
        exact_mod_cast hnnL
      have := div_nonneg this hldR.le
      field_simp [hldR.ne'] at this ⊢; linarith
    have hR : 0 ≤ (piece.a0 : ℝ) + (piece.a1 : ℝ) * ((piece.rn : ℝ) / (piece.rd : ℝ)) := by
      have : (0 : ℝ) ≤ (piece.a0 : ℝ) * (piece.rd : ℝ) + (piece.a1 : ℝ) * (piece.rn : ℝ) := by
        exact_mod_cast hnnR
      have := div_nonneg this hrdR.le
      field_simp [hrdR.ne'] at this ⊢; linarith
    by_cases hs : (0 : ℝ) ≤ (piece.a1 : ℝ) <;> nlinarith
  have hpiece_mem : ∀ j < L, getPiece j ∈ ps := by
    intro j hj
    dsimp [getPiece]
    rw [List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  have hpw := sixBandPrimeCost_rate_of_piecewise_majorant s ((1 : ℝ) / 10000) ((7 : ℝ) / 2)
    (by norm_num) (by norm_num) lo hi f
    (by
      intro idx hidx
      have hact : tlo idx < thi idx := (Finset.mem_filter.mp hidx).2
      have htlo_pos : 0 < tlo idx := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 7) (le_max_left _ _)
      have hthi_pos : 0 < thi idx := htlo_pos.trans hact
      dsimp [lo]; positivity)
    (by
      intro idx hidx
      have hact : tlo idx < thi idx := (Finset.mem_filter.mp hidx).2
      have htlo_pos : 0 < tlo idx := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 7) (le_max_left _ _)
      dsimp [lo, hi]
      exact one_div_le_one_div_of_le htlo_pos hact.le)
    (by
      intro idx _
      have htlo_ge : (2 : ℝ) / 7 ≤ tlo idx := le_max_left _ _
      dsimp [hi]
      have : 1 / tlo idx ≤ (7 : ℝ) / 2 := by
        have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2 / 7) htlo_ge
        linarith
      linarith)
    (by
      intro idx hidx
      have hact : tlo idx < thi idx := (Finset.mem_filter.mp hidx).2
      have htlo_pos : 0 < tlo idx := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 7) (le_max_left _ _)
      have hlo_pos : 0 < lo idx := by dsimp [lo]; have := htlo_pos.trans hact; positivity
      intro x hx
      have hx0 : x ≠ 0 := (hlo_pos.trans_le hx.1).ne'
      dsimp [f]; fun_prop (disch := assumption))
    (by
      intro idx hidx x hx
      have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hidx).1
      have hjL : idx.2 < L := Finset.mem_range.mp hmem.2
      have hact : tlo idx < thi idx := (Finset.mem_filter.mp hidx).2
      have htlo_pos : 0 < tlo idx := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 7) (le_max_left _ _)
      have hthi_pos : 0 < thi idx := htlo_pos.trans hact
      have hx_pos : 0 < x := lt_of_lt_of_le (by dsimp [lo]; positivity) hx.1
      have hinv_lo : tlo idx ≤ 1 / x := by
        have h1 : x ≤ 1 / tlo idx := hx.2
        have := one_div_le_one_div_of_le hx_pos h1
        rwa [one_div_one_div] at this
      have hinv_hi : 1 / x ≤ thi idx := by
        have h1 : 1 / thi idx ≤ x := hx.1
        have := one_div_le_one_div_of_le (by positivity) h1
        rwa [one_div_one_div] at this
      have hu_lo : ((getPiece idx.2).ln : ℝ) / ((getPiece idx.2).ld : ℝ) ≤ 1 / x - (idx.1 : ℝ) := by
        have : (idx.1 : ℝ) + ((getPiece idx.2).ln : ℝ) / ((getPiece idx.2).ld : ℝ) ≤ tlo idx :=
          le_max_right _ _
        linarith
      have hu_hi : 1 / x - (idx.1 : ℝ) ≤ ((getPiece idx.2).rn : ℝ) / ((getPiece idx.2).rd : ℝ) := by
        dsimp [thi] at hinv_hi; linarith
      have haff := haff_nn_piece (getPiece idx.2) (hpiece_mem idx.2 hjL) (1 / x - (idx.1 : ℝ)) hu_lo hu_hi
      dsimp [f]; positivity)
    (486 * 300005 : ℝ) (by norm_num) E Kmax hEsub hEcard
    (by
      intro n hn p hpS hpE
      have hp_mem := Finset.mem_filter.mp hpS
      have hp_pr : p.Prime := (Nat.mem_primesLE.mp hp_mem.1).2
      have hp_le_35 : (p : ℝ) ≤ ((7 : ℝ) / 2) * (n : ℝ) :=
        (Nat.le_floor_iff (by positivity)).mp (Nat.mem_primesLE.mp hp_mem.1).1
      have hp_gt_eps : ((1 : ℝ) / 10000) * (n : ℝ) < (p : ℝ) := hp_mem.2
      have hp_cut : p ∈ sixCutoffPrimes n := by
        rw [sixCutoffPrimes, Nat.mem_primesLE]
        have hp_le_55 : (p : ℝ) ≤ 55 * (n : ℝ) := by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        refine ⟨?_, hp_pr⟩
        exact_mod_cast hp_le_55
      have hnN0 : N₀ ≤ n := by
        by_contra hlt; push Not at hlt
        apply hpE
        dsimp only [E]; unfold periodicExceptional
        simp only [hlt, ite_true]
        exact hp_cut
      have hndvd : ¬ (p ∣ n) := by
        intro hd
        apply hpE
        dsimp only [E]; unfold periodicExceptional
        have hnotlt : ¬ n < N₀ := by omega
        simp only [hnotlt, ite_false, Finset.mem_filter]
        exact ⟨hp_cut, hd, hp_gt_eps⟩
      have hp_gt_maxD : maxD < p := by
        have h1 : 10000 * (maxD + 1) ≤ n := (le_max_right _ _).trans hnN0
        have h2 : (maxD + 1 : ℝ) < (p : ℝ) := by
          have : ((10000 * (maxD + 1) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
          push_cast at this; linarith
        have : maxD + 1 ≤ p := le_of_lt (by exact_mod_cast h2)
        omega
      have hsq : 140 * n + 2 < p ^ 2 := by
        have h1 : 20000000000 ≤ n := (le_max_left _ _).trans hnN0
        have hnR : (20000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
        have hpR : (n : ℝ) / 10000 < (p : ℝ) := by linarith
        have hsq1 : ((n : ℝ) / 10000) ^ 2 < (p : ℝ) ^ 2 := by
          have hnn : (0 : ℝ) ≤ (n : ℝ) / 10000 := by linarith
          exact sq_lt_sq' (by linarith) hpR
        have hsq2 : 140 * (n : ℝ) + 2 < ((n : ℝ) / 10000) ^ 2 := by
          have hdiff : ((n : ℝ) / 10000) ^ 2 - (140 * (n : ℝ) + 2) =
              ((n : ℝ) - 20000000000) * ((n : ℝ) + 6000000000) / 100000000 +
              (1200000000000 - 2) := by ring
          have hterm1 : 0 ≤ ((n : ℝ) - 20000000000) * ((n : ℝ) + 6000000000) / 100000000 := by
            have : (0 : ℝ) ≤ (n : ℝ) - 20000000000 := by linarith
            have : (0 : ℝ) ≤ (n : ℝ) + 6000000000 := by linarith
            positivity
          linarith
        have hsqR : 140 * (n : ℝ) + 2 < (p : ℝ) ^ 2 := hsq2.trans hsq1
        exact_mod_cast hsqR
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pr.pos
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      let k := n / p
      let rn := n % p
      let τ : ℝ := (rn : ℝ) / (p : ℝ)
      have hk_lt : k < Kmax := by
        have hlt : n < Kmax * p := by
          have : (n : ℝ) < 10000 * (p : ℝ) := by linarith
          have : n < 10000 * p := by exact_mod_cast this
          rw [hKmax]; exact this
        exact (Nat.div_lt_iff_lt_mul hp_pr.pos).mpr hlt
      have hrn_pos : 0 < rn := by
        have : n % p ≠ 0 := fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0)
        omega
      have hrn_lt : rn < p := Nat.mod_lt n hp_pr.pos
      have hτ_pos : ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) < τ := by
        dsimp [τ]; simp only [Nat.cast_zero, Nat.cast_one, zero_div]; positivity
      have hτ_lt1 : τ < ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
        dsimp [τ]; simp only [Nat.cast_one, div_one]; rw [div_lt_one hpR]; exact_mod_cast hrn_lt
      have hτ_ne : ∀ piece ∈ ps, τ ≠ (piece.rn : ℝ) / (piece.rd : ℝ) := by
        intro piece hpm heq
        obtain ⟨_, hrd, _, _, _, _, _⟩ := hpiece_props piece hpm
        have hrdR : (0 : ℝ) < (piece.rd : ℝ) := by exact_mod_cast hrd
        have hmulR : (rn : ℝ) * (piece.rd : ℝ) = (piece.rn : ℝ) * (p : ℝ) := by
          dsimp [τ] at heq
          have := (div_eq_div_iff hpR.ne' hrdR.ne').mp heq
          linarith
        have hmulN : rn * piece.rd = piece.rn * p := by exact_mod_cast hmulR
        have hdvd : p ∣ rn * piece.rd := ⟨piece.rn, by linarith⟩
        rcases hp_pr.dvd_mul.mp hdvd with h1 | h2
        · exact absurd (Nat.le_of_dvd hrn_pos h1) (not_le.mpr hrn_lt)
        · have hle_maxD := (periodicMaxDen_ge ps piece hpm).2
          have hle_rd := Nat.le_of_dvd hrd h2
          omega
      obtain ⟨piece, hpm, hplo, hphi⟩ := checkPeriodicRun_cover hval hτ_pos hτ_lt1 hτ_ne
      obtain ⟨j, hjL, hj_eq⟩ := List.mem_iff_getElem.mp hpm
      have hget_eq : getPiece j = piece := by
        dsimp [getPiece]; rw [List.getElem?_eq_getElem hjL]; exact hj_eq
      have hdiv_eq : (n : ℝ) / (p : ℝ) = (k : ℝ) + τ := by
        have hdm : k * p + rn = n := by dsimp [k, rn]; rw [mul_comm]; exact Nat.div_add_mod n p
        have hdmR : (k : ℝ) * (p : ℝ) + (rn : ℝ) = (n : ℝ) := by exact_mod_cast hdm
        dsimp [τ]; field_simp [hpR.ne']; linarith
      have hnp_ge : (2 : ℝ) / 7 ≤ (n : ℝ) / (p : ℝ) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 7) hpR]; linarith
      have htlo_le : tlo (k, j) ≤ (n : ℝ) / (p : ℝ) := by
        dsimp [tlo]; rw [hget_eq]
        exact max_le hnp_ge (by rw [hdiv_eq]; linarith)
      have hthi_gt : (n : ℝ) / (p : ℝ) < thi (k, j) := by
        dsimp [thi]; rw [hget_eq, hdiv_eq]; linarith
      have hact : tlo (k, j) < thi (k, j) := lt_of_le_of_lt htlo_le hthi_gt
      have htlo_pos : 0 < tlo (k, j) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 7) (le_max_left _ _)
      have hthi_pos : 0 < thi (k, j) := htlo_pos.trans hact
      refine ⟨(k, j), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hk_lt, Finset.mem_range.mpr hjL⟩, hact⟩, ?_, ?_, ?_⟩
      · dsimp [lo]
        rw [one_div_mul_eq_div, div_lt_iff₀ hthi_pos]
        have := (div_lt_iff₀ hpR).mp hthi_gt; linarith
      · dsimp [hi]
        rw [one_div_mul_eq_div, le_div_iff₀ htlo_pos]
        have := (le_div_iff₀ hpR).mp htlo_le; linarith
      · have : Fact p.Prime := ⟨hp_pr⟩
        have hcoarse := sixPrimitiveScalar_periodic_coarse_bound n p hn hsq
        have hexp_le : sixPrimeExpReal n p ≤
            ((2 * rank n / p + 5 : ℕ) : ℝ) * ∑ c : Fin (p / 2 + 1), (sixCoarsePeriodicCost n p c : ℝ) := by
          unfold sixPrimeExpReal
          have h1 : ((-(padicValRat p (sixPrimitiveScalar n)) : ℤ) : ℝ) ≤
              ((2 * rank n / p + 5 : ℕ) : ℝ) * ∑ c : Fin (p / 2 + 1), (sixCoarsePeriodicCost n p c : ℝ) := by
            have hcast : ((-(padicValRat p (sixPrimitiveScalar n)) : ℤ) : ℝ) ≤
                ((((2 * rank n / p + 5 : ℕ) : ℤ) *
                  ∑ c : Fin (p / 2 + 1), (sixCoarsePeriodicCost n p c : ℤ) : ℤ) : ℝ) := by
              exact_mod_cast hcoarse
            rw [Int.cast_mul, Int.cast_natCast, Int.cast_sum] at hcast
            simpa only [Int.cast_natCast] using hcast
          rw [Int.cast_neg] at h1
          have h0_le : ((0 : ℤ) : ℝ) ≤
              ((2 * rank n / p + 5 : ℕ) : ℝ) * ∑ c : Fin (p / 2 + 1), (sixCoarsePeriodicCost n p c : ℝ) := by
            rw [Int.cast_zero]
            exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
          exact max_le h0_le h1
        have hdisc := periodicPiece_discrete_sum_le n p hp_pr.pos piece (hall_chk piece hpm) hplo hphi
        have hmul_le : ((2 * rank n / p + 5 : ℕ) : ℝ) ≤ 30 * ((n : ℝ) / (p : ℝ)) + 5 := by
          have hr : 2 * rank n = 30 * n := by unfold rank; ring
          rw [hr, Nat.cast_add, Nat.cast_ofNat]
          have hdiv_le : ((30 * n / p : ℕ) : ℝ) ≤ 30 * ((n : ℝ) / (p : ℝ)) := by
            rw [← mul_div_assoc, le_div_iff₀ hpR]
            exact_mod_cast Nat.div_mul_le_self (30 * n) p
          linarith
        have hmul_cap : ((2 * rank n / p + 5 : ℕ) : ℝ) ≤ 300005 := by
          have : (n : ℝ) / (p : ℝ) < 10000 := by
            rw [div_lt_iff₀ hpR]; linarith
          linarith
        have haff_nn := haff_nn_piece piece hpm τ hplo.le hphi.le
        have hτ_eq : 1 / ((p : ℝ) / (n : ℝ)) - (k : ℝ) = τ := by
          rw [one_div_div, hdiv_eq]; ring
        have hmain : ((2 * rank n / p + 5 : ℕ) : ℝ) * (((p : ℝ) / 2) *
            ((piece.a0 : ℝ) + (piece.a1 : ℝ) * τ)) ≤ (n : ℝ) * f (k, j) ((p : ℝ) / (n : ℝ)) := by
          dsimp [f]; rw [hget_eq, hτ_eq]
          have hcoef : ((2 * rank n / p + 5 : ℕ) : ℝ) * ((p : ℝ) / 2) ≤
              (n : ℝ) * (15 * (1 + ((p : ℝ) / (n : ℝ)) / 6)) := by
            have hstep : (30 * ((n : ℝ) / (p : ℝ)) + 5) * ((p : ℝ) / 2) =
                (n : ℝ) * (15 * (1 + ((p : ℝ) / (n : ℝ)) / 6)) := by
              field_simp [hpR.ne', hnR.ne']; ring
            rw [← hstep]
            exact mul_le_mul_of_nonneg_right hmul_le (by positivity)
          have hassoc : ((2 * rank n / p + 5 : ℕ) : ℝ) * (((p : ℝ) / 2) *
              ((piece.a0 : ℝ) + (piece.a1 : ℝ) * τ)) =
              (((2 * rank n / p + 5 : ℕ) : ℝ) * ((p : ℝ) / 2)) *
              ((piece.a0 : ℝ) + (piece.a1 : ℝ) * τ) := by ring
          rw [hassoc]
          have hassoc2 : (n : ℝ) * (15 * (1 + ((p : ℝ) / (n : ℝ)) / 6) *
              ((piece.a0 : ℝ) + (piece.a1 : ℝ) * τ)) =
              ((n : ℝ) * (15 * (1 + ((p : ℝ) / (n : ℝ)) / 6))) *
              ((piece.a0 : ℝ) + (piece.a1 : ℝ) * τ) := by ring
          rw [hassoc2]
          exact mul_le_mul_of_nonneg_right hcoef haff_nn
        have hstep1 : ((2 * rank n / p + 5 : ℕ) : ℝ) *
            ∑ c : Fin (p / 2 + 1), (sixCoarsePeriodicCost n p c : ℝ) ≤
            ((2 * rank n / p + 5 : ℕ) : ℝ) *
              (((p : ℝ) / 2) * ((piece.a0 : ℝ) + (piece.a1 : ℝ) * τ) + 486) :=
          mul_le_mul_of_nonneg_left hdisc (by positivity)
        have hstep2 : ((2 * rank n / p + 5 : ℕ) : ℝ) * 486 ≤ 486 * 300005 := by linarith
        linarith)
  have hint_bound : (∑ idx ∈ s, ∫ x in lo idx..hi idx, f idx x) / 750 ≤ (552 : ℝ) / 1000 := by
    let gTerm (k j : ℕ) : ℝ :=
      if tlo (k, j) < thi (k, j) then
        ∫ x in lo (k, j)..hi (k, j),
          (1 + x / 6) * (((getPiece j).a0 : ℝ) + ((getPiece j).a1 : ℝ) * (1 / x - (k : ℝ)))
      else 0
    have hrewrite : (∑ idx ∈ s, ∫ x in lo idx..hi idx, f idx x) =
        15 * ((∑ j ∈ Finset.range L, ∑ k ∈ Finset.range 12, gTerm k j) +
              (∑ j ∈ Finset.range L, ∑ k ∈ Finset.Ico 12 Kmax, gTerm k j)) := by
      have h1 : (∑ idx ∈ s, ∫ x in lo idx..hi idx, f idx x) =
          ∑ idx ∈ Finset.range Kmax ×ˢ Finset.range L, 15 * gTerm idx.1 idx.2 := by
        dsimp [s]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro idx _
        dsimp [gTerm, f]
        split_ifs
        · rw [← intervalIntegral.integral_const_mul]
          congr 1; ext x; ring
        · ring
      rw [h1, ← Finset.mul_sum, Finset.sum_product_right]
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _
      dsimp only
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
      exact (Finset.sum_Ico_consecutive (f := fun k => gTerm k j)
        (show 0 ≤ 12 by omega) (show 12 ≤ Kmax by omega)).symm
    have hhead : (∑ j ∈ Finset.range L, ∑ k ∈ Finset.range 12, gTerm k j) ≤
        (cTotal : ℝ) / (certDen : ℝ) := by
      have hsum_map : (cTotal : ℝ) = ∑ j ∈ Finset.range L, ((getPiece j).c0Num : ℝ) := by
        rw [← hCsum, ← Nat.cast_sum]
        exact_mod_cast list_map_sum_eq_range ps ⟨0, 1, 1, 1, [], 0, 0, 0, 0⟩ (·.c0Num)
      rw [hsum_map, Finset.sum_div]
      apply Finset.sum_le_sum; intro j hj
      have hjL : j < L := Finset.mem_range.mp hj
      have hpm := hpiece_mem j hjL
      obtain ⟨hld, hrd, hlt, hnnL, hnnR, _, hc0⟩ := hpiece_props (getPiece j) hpm
      have hc := periodic12Ceil_sound (getPiece j) hld hrd hlt hnnL hnnR
      have hc0R : (periodic12Ceil (getPiece j).a0 (getPiece j).a1 (getPiece j).ln
          (getPiece j).ld (getPiece j).rn (getPiece j).rd : ℝ) / (certDen : ℝ) ≤
          ((getPiece j).c0Num : ℝ) / (certDen : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hc0) (by unfold certDen; positivity)
      exact hc.trans hc0R
    have htail : (∑ j ∈ Finset.range L, ∑ k ∈ Finset.Ico 12 Kmax, gTerm k j) ≤
        (1 / 11 + 1 / (12 * 11 ^ 2)) * ((fTotal : ℝ) / (certDen : ℝ)) := by
      have hsum_map : (fTotal : ℝ) = ∑ j ∈ Finset.range L, ((getPiece j).fbarNum : ℝ) := by
        rw [← hFsum, ← Nat.cast_sum]
        exact_mod_cast list_map_sum_eq_range ps ⟨0, 1, 1, 1, [], 0, 0, 0, 0⟩ (·.fbarNum)
      rw [hsum_map, Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_le_sum; intro j hj
      have hjL : j < L := Finset.mem_range.mp hj
      have hpm := hpiece_mem j hjL
      obtain ⟨hld, hrd, hlt, hnnL, hnnR, hfbar, _⟩ := hpiece_props (getPiece j) hpm
      have hldR : (0 : ℝ) < ((getPiece j).ld : ℝ) := by exact_mod_cast hld
      have hrdR : (0 : ℝ) < ((getPiece j).rd : ℝ) := by exact_mod_cast hrd
      have hlrR : ((getPiece j).ln : ℝ) / ((getPiece j).ld : ℝ) <
          ((getPiece j).rn : ℝ) / ((getPiece j).rd : ℝ) := by
        rw [div_lt_div_iff₀ hldR hrdR]; exact_mod_cast hlt
      have hterm_k : ∀ k ∈ Finset.Ico 12 Kmax,
          gTerm k j ≤ ((1 : ℝ) / ((k : ℝ) ^ 2) + 1 / (6 * (k : ℝ) ^ 3)) *
            (((getPiece j).fbarNum : ℝ) / (certDen : ℝ)) := by
        intro k hk
        have hk12 : 12 ≤ k := (Finset.mem_Ico.mp hk).1
        have hkR : (12 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk12
        have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
        have htlo_eq : tlo (k, j) = (k : ℝ) + ((getPiece j).ln : ℝ) / ((getPiece j).ld : ℝ) := by
          dsimp [tlo]
          apply max_eq_right
          have : 0 ≤ ((getPiece j).ln : ℝ) / ((getPiece j).ld : ℝ) := by positivity
          linarith
        have hact : tlo (k, j) < thi (k, j) := by
          rw [htlo_eq]; dsimp [thi]; linarith
        have htlo_ge_k : (k : ℝ) ≤ tlo (k, j) := by
          rw [htlo_eq]; have : 0 ≤ ((getPiece j).ln : ℝ) / ((getPiece j).ld : ℝ) := by positivity
          linarith
        have htlo_pos : 0 < tlo (k, j) := lt_of_lt_of_le hkpos htlo_ge_k
        dsimp [gTerm]; simp only [hact, ite_true]
        dsimp [lo, hi]
        rw [integral_inv_sub _ htlo_pos hact.le (by
          intro x hx
          have hx0 : x ≠ 0 := (lt_of_lt_of_le (by have := htlo_pos.trans hact; positivity) hx.1).ne'
          have h6 : (6 : ℝ) ≠ 0 := by norm_num
          fun_prop (disch := assumption))]
        have hstep : (∫ t in tlo (k, j)..thi (k, j),
            (1 + 1 / t / 6) *
              (((getPiece j).a0 : ℝ) + ((getPiece j).a1 : ℝ) * (1 / (1 / t) - (k : ℝ))) * (1 / t ^ 2)) ≤
            ((1 : ℝ) / ((k : ℝ) ^ 2) + 1 / (6 * (k : ℝ) ^ 3)) *
              ∫ t in tlo (k, j)..thi (k, j),
                (((getPiece j).a0 : ℝ) + ((getPiece j).a1 : ℝ) * (t - (k : ℝ))) := by
          rw [← intervalIntegral.integral_const_mul]
          have hrew_int : (∫ t in tlo (k, j)..thi (k, j),
              (1 + 1 / t / 6) *
                (((getPiece j).a0 : ℝ) + ((getPiece j).a1 : ℝ) * (1 / (1 / t) - (k : ℝ))) * (1 / t ^ 2)) =
              ∫ t in tlo (k, j)..thi (k, j),
                (1 + 1 / t / 6) *
                  (((getPiece j).a0 : ℝ) + ((getPiece j).a1 : ℝ) * (t - (k : ℝ))) * (1 / t ^ 2) := by
            congr 1; ext t; rw [one_div_one_div]
          rw [hrew_int]
          apply intervalIntegral.integral_mono_on hact.le
          · apply ContinuousOn.intervalIntegrable
            rw [Set.uIcc_of_le hact.le]
            intro t ht
            have ht0 : t ≠ 0 := (htlo_pos.trans_le ht.1).ne'
            have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
            have h6 : (6 : ℝ) ≠ 0 := by norm_num
            fun_prop (disch := assumption)
          · exact Continuous.intervalIntegrable (by fun_prop) _ _
          · intro t ht
            have htk : (k : ℝ) ≤ t := htlo_ge_k.trans ht.1
            have htpos : 0 < t := hkpos.trans_le htk
            have hwt : (1 + 1 / t / 6) * (1 / t ^ 2) ≤ 1 / (k : ℝ) ^ 2 + 1 / (6 * (k : ℝ) ^ 3) := by
              have heq_t : (1 + 1 / t / 6) * (1 / t ^ 2) = 1 / t ^ 2 + 1 / (6 * t ^ 3) := by
                field_simp [htpos.ne']
              rw [heq_t]
              have h2 : 1 / t ^ 2 ≤ 1 / (k : ℝ) ^ 2 :=
                one_div_le_one_div_of_le (pow_pos hkpos 2) (pow_le_pow_left₀ hkpos.le htk 2)
              have h3 : 1 / (6 * t ^ 3) ≤ 1 / (6 * (k : ℝ) ^ 3) :=
                one_div_le_one_div_of_le (by positivity)
                  (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hkpos.le htk 3) (by norm_num))
              linarith
            have hu1 : ((getPiece j).ln : ℝ) / ((getPiece j).ld : ℝ) ≤ t - (k : ℝ) := by
              rw [htlo_eq] at ht; linarith [ht.1]
            have hu2 : t - (k : ℝ) ≤ ((getPiece j).rn : ℝ) / ((getPiece j).rd : ℝ) := by
              dsimp [thi] at ht; linarith [ht.2]
            have hnn := haff_nn_piece (getPiece j) hpm (t - (k : ℝ)) hu1 hu2
            have hmul := mul_le_mul_of_nonneg_right hwt hnn
            linarith
        have hshift : (∫ t in tlo (k, j)..thi (k, j),
            (((getPiece j).a0 : ℝ) + ((getPiece j).a1 : ℝ) * (t - (k : ℝ)))) =
            ∫ u in (((getPiece j).ln : ℝ) / ((getPiece j).ld : ℝ))..
                (((getPiece j).rn : ℝ) / ((getPiece j).rd : ℝ)),
              (((getPiece j).a0 : ℝ) + ((getPiece j).a1 : ℝ) * u) := by
          rw [htlo_eq]; dsimp [thi]
          have hs := intervalIntegral.integral_comp_sub_right
            (a := (k : ℝ) + ((getPiece j).ln : ℝ) / ((getPiece j).ld : ℝ))
            (b := (k : ℝ) + ((getPiece j).rn : ℝ) / ((getPiece j).rd : ℝ))
            (fun u => ((getPiece j).a0 : ℝ) + ((getPiece j).a1 : ℝ) * u) (k : ℝ)
          simpa only [add_sub_cancel_left] using hs
        have haff_le : (∫ u in (((getPiece j).ln : ℝ) / ((getPiece j).ld : ℝ))..
                (((getPiece j).rn : ℝ) / ((getPiece j).rd : ℝ)),
              (((getPiece j).a0 : ℝ) + ((getPiece j).a1 : ℝ) * u)) ≤
            ((getPiece j).fbarNum : ℝ) / (certDen : ℝ) :=
          (affIntCeil_sound hld hrd hlt (by unfold certDen; norm_num) hnnL hnnR).trans
            (div_le_div_of_nonneg_right (by exact_mod_cast hfbar) (by unfold certDen; positivity))
        exact hstep.trans (by rw [hshift]; exact mul_le_mul_of_nonneg_left haff_le (by positivity))
      calc
        ∑ k ∈ Finset.Ico 12 Kmax, gTerm k j
            ≤ ∑ k ∈ Finset.Ico 12 Kmax,
                ((1 : ℝ) / ((k : ℝ) ^ 2) + 1 / (6 * (k : ℝ) ^ 3)) *
                  (((getPiece j).fbarNum : ℝ) / (certDen : ℝ)) := Finset.sum_le_sum hterm_k
        _ = (∑ k ∈ Finset.Ico 12 Kmax, ((1 : ℝ) / ((k : ℝ) ^ 2) + 1 / (6 * (k : ℝ) ^ 3))) *
              (((getPiece j).fbarNum : ℝ) / (certDen : ℝ)) := (Finset.sum_mul ..).symm
        _ ≤ (1 / 11 + 1 / (12 * 11 ^ 2)) * (((getPiece j).fbarNum : ℝ) / (certDen : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (by unfold certDen; positivity)
            rw [Finset.sum_add_distrib]
            exact add_le_add (tail_inv_sq_sum_le Kmax) (tail_inv_cube_sum_le Kmax)
    rw [hrewrite]
    linarith
  intro δ hδ
  filter_upwards [hpw δ hδ] with n hn
  exact hn.trans (by linarith)

/-- **Stage 2B Periodic Band Bound**: on `(1/10000) * n < p ≤ (7/2) * n`,
`sixBandPrimeCost n (1/10000) (7/2) / sixNorm n ≤ 552 / 1000 + δ` eventually. -/
theorem sixPeriodicBand_rate_le :
    ∀ δ > 0, ∀ᶠ n : ℕ in atTop,
      sixBandPrimeCost n ((1 : ℝ) / 10000) ((7 : ℝ) / 2) / sixNorm n ≤ (552 : ℝ) / 1000 + δ :=
  sixPeriodicBand_rate_of_shard allPeriodicPieces 611246243 2688712227 10000 rfl
    allPeriodicPieces_valid (by unfold certDen; norm_num)

end OddZetaSix
