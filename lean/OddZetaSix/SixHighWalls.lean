import OddZetaSix.SixFoldedCertCore
import OddZetaSix.SixLocalSlots
import OddZetaSix.SixPNTBridge
import OddZetaSix.SixPeriodicRate
import OddZetaSix.HighData.Shard0
import OddZetaSix.HighData.Shard1
import OddZetaSix.HighData.Shard2
import OddZetaSix.HighData.Shard3
import OddZetaSix.HighData.Shard4
import OddZetaSix.HighData.Shard5
import OddZetaSix.HighData.Shard6
import OddZetaSix.HighData.Shard7
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Middle/High-Prime Rate Bound (`3.5 n < p ≤ 55 n`, `C₁ ≤ 7206/1000`)

Certifies the exact 12-line folded joint capacity bound on `(7/2) * n < p ≤ 55 * n`:
1. Soundness of `highFloorOk`, `sumRangeIcc` (exact zero-error row penalty bound),
   `capIntCeil` (exact 4-case integral of `min 15 ((u0 + u1 * x) / 2)`),
   `refinedOrderCostO1`, `addBranchSlotsPacked` (bit-packed `256^v` histogram),
   `packedToSuffixCounts`, and `jointCapFromN`.
2. Exact discrete-to-continuous high-tile bound `highTile_discrete_bound`:
   for every prime `p` with `p^2 > 140n + 2` in the strict interior `(t.ln/t.ld, t.rn/t.rd)`
   of a checked `HighTile t`,
   `sixPrimeExpReal n p ≤ n * highTileMajorant t (p / n) + 102060`.
3. Assembles the 8 certified high shards (`HighData.Shard0`..`Shard7`, 506 flat tiles
   covering `[7/2, 55]`) and proves
   `sixHighBand_rate_le : ∀ δ > 0, ∀ᶠ n in atTop, sixBandPrimeCost n (7/2) 55 / sixNorm n ≤ 7206 / 1000 + δ`.

Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

noncomputable section
set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix

open Finset Filter MeasureTheory
open OddZetaSix.CertCore
open scoped BigOperators

/-! ## Section 1: Floor, row-penalty, and capped-integral soundness -/

theorem highFloorOk_strict {num q ln ld rn rd n p : ℕ}
    (hld : 0 < ld) (hrd : 0 < rd) (hn : 0 < n) (hp : 0 < p) (_hnum : 0 < num)
    (hlo : (ln : ℝ) / (ld : ℝ) < (p : ℝ) / (n : ℝ))
    (hhi : (p : ℝ) / (n : ℝ) < (rn : ℝ) / (rd : ℝ))
    (h : highFloorOk num q ln ld rn rd = true) :
    q * p ≤ num * n ∧ num * n < (q + 1) * p ∧ (num * n) / p = q := by
  unfold highFloorOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hldR : (0 : ℝ) < (ld : ℝ) := by exact_mod_cast hld
  have hrdR : (0 : ℝ) < (rd : ℝ) := by exact_mod_cast hrd
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hq1 : (q : ℝ) * ((p : ℝ) / (n : ℝ)) ≤ (num : ℝ) := by
    have h1 : (q : ℝ) * ((rn : ℝ) / (rd : ℝ)) ≤ (num : ℝ) := by
      have : (q : ℝ) * (rn : ℝ) ≤ (num : ℝ) * (rd : ℝ) := by exact_mod_cast h.1
      rw [← mul_div_assoc, div_le_iff₀ hrdR]; exact this
    exact (mul_le_mul_of_nonneg_left hhi.le (Nat.cast_nonneg q)).trans h1
  have hq2 : (num : ℝ) < ((q + 1 : ℕ) : ℝ) * ((p : ℝ) / (n : ℝ)) := by
    have h2 : (num : ℝ) ≤ ((q + 1 : ℕ) : ℝ) * ((ln : ℝ) / (ld : ℝ)) := by
      have : (num : ℝ) * (ld : ℝ) ≤ ((q + 1 : ℕ) : ℝ) * (ln : ℝ) := by exact_mod_cast h.2
      rw [← mul_div_assoc, le_div_iff₀ hldR]; exact this
    have hq1pos : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
    exact h2.trans_lt (mul_lt_mul_of_pos_left hlo hq1pos)
  have h1' : (q : ℝ) * (p : ℝ) ≤ (num : ℝ) * (n : ℝ) := by
    have := mul_le_mul_of_nonneg_right hq1 hnR.le
    rwa [mul_div_assoc', div_mul_cancel₀ _ hnR.ne'] at this
  have h2' : (num : ℝ) * (n : ℝ) < ((q + 1 : ℕ) : ℝ) * (p : ℝ) := by
    have := mul_lt_mul_of_pos_right hq2 hnR
    rwa [mul_div_assoc', div_mul_cancel₀ _ hnR.ne'] at this
  have hloN : q * p ≤ num * n := by exact_mod_cast h1'
  have hhiN : num * n < (q + 1) * p := by exact_mod_cast h2'
  have hdiv : (num * n) / p = q := by
    have hge : q ≤ (num * n) / p := (Nat.le_div_iff_mul_le hp).mpr hloN
    have hlt : (num * n) / p < q + 1 := (Nat.div_lt_iff_lt_mul hp).mpr hhiN
    omega
  exact ⟨hloN, hhiN, hdiv⟩

theorem sumRangeIcc_eq (q K : ℕ) (hqK : q ≤ K) :
    sumRangeIcc q K = ∑ k ∈ Finset.Icc (q + 1) K, k := by
  have hev : ∀ m : ℕ, 2 ∣ m * (m + 1) := by
    intro m
    rcases Nat.even_or_odd m with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · exact ⟨r * (r + r + 1), by ring⟩
    · exact ⟨(2 * r + 1) * (r + 1), by ring⟩
  have hdouble : 2 * (∑ k ∈ Finset.Icc (q + 1) K, k) + q * (q + 1) = K * (K + 1) := by
    induction K, hqK using Nat.le_induction with
    | base =>
      simp
    | succ m hm ih =>
      have hsub : Finset.Icc (q + 1) (m + 1) = insert (m + 1) (Finset.Icc (q + 1) m) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : m + 1 ∉ Finset.Icc (q + 1) m := by simp
      rw [hsub, Finset.sum_insert hnot]
      linarith
  obtain ⟨a, ha⟩ := hev K
  obtain ⟨b, hb⟩ := hev q
  unfold sumRangeIcc
  rw [ha, hb, Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)]
  omega

/-- Exact zero-error row-penalty bound for `rank n = 15 * n`. -/
theorem two_mul_sixRowPenalty_le (n p q k30 : ℕ) (hn : 0 < n) (hp : 0 < p)
    (hqk : q ≤ k30) (hk30 : 30 * n / p = k30) :
    2 * (sixRowPenalty (rank n) p q : ℝ) ≤
      (n : ℝ) * ((30 * ((k30 - q : ℕ) : ℝ)) - ((sumRangeIcc q k30 : ℕ) : ℝ) * ((p : ℝ) / (n : ℝ))) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr : rank n = 15 * n := rfl
  have hsub_sum : ∀ m : ℕ, m ≤ k30 →
      m - q = ∑ k ∈ Finset.Icc (q + 1) k30, if k ≤ m then 1 else 0 := by
    intro m hm
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have heq : (Finset.Icc (q + 1) k30).filter (fun k => k ≤ m) = Finset.Icc (q + 1) m := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [heq, Nat.card_Icc]; omega
  have hpen_eq : sixRowPenalty (rank n) p q =
      ∑ k ∈ Finset.Icc (q + 1) k30,
        ((Finset.range (15 * n)).filter (fun i => k ≤ 2 * i / p)).card := by
    unfold sixRowPenalty
    rw [hr, Fin.sum_univ_eq_sum_range (fun i => 2 * i / p - q)]
    have h1 : (∑ i ∈ Finset.range (15 * n), (2 * i / p - q)) =
        ∑ i ∈ Finset.range (15 * n), ∑ k ∈ Finset.Icc (q + 1) k30,
          if k ≤ 2 * i / p then 1 else 0 := by
      apply Finset.sum_congr rfl; intro i hi
      have hilt : i < 15 * n := Finset.mem_range.mp hi
      have hle : 2 * i / p ≤ k30 := by
        rw [← hk30]; exact Nat.div_le_div_right (by omega)
      exact hsub_sum _ hle
    rw [h1, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  have hterm_le : ∀ k ∈ Finset.Icc (q + 1) k30,
      2 * (((Finset.range (15 * n)).filter (fun i => k ≤ 2 * i / p)).card : ℝ) ≤
        30 * (n : ℝ) - (k : ℝ) * (p : ℝ) := by
    intro k hk
    have hk_le : k ≤ k30 := (Finset.mem_Icc.mp hk).2
    have hkp : k * p ≤ 30 * n := by
      calc k * p ≤ k30 * p := Nat.mul_le_mul_right p hk_le
        _ = (30 * n / p) * p := by rw [hk30]
        _ ≤ 30 * n := Nat.div_mul_le_self (30 * n) p
    let a := (k * p + 1) / 2
    have hsub : (Finset.range (15 * n)).filter (fun i => k ≤ 2 * i / p) ⊆
        Finset.Ico a (15 * n) := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      have hmul : k * p ≤ 2 * i := (Nat.le_div_iff_mul_le hp).mp hi.2
      exact Finset.mem_Ico.mpr ⟨by dsimp [a]; omega, hi.1⟩
    have hcard : ((Finset.range (15 * n)).filter (fun i => k ≤ 2 * i / p)).card ≤ 15 * n - a := by
      exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Ico])
    have h2a : k * p ≤ 2 * a := by dsimp [a]; omega
    have h2c : 2 * ((Finset.range (15 * n)).filter (fun i => k ≤ 2 * i / p)).card + k * p ≤ 30 * n := by
      omega
    have h2cR : 2 * (((Finset.range (15 * n)).filter (fun i => k ≤ 2 * i / p)).card : ℝ) +
        (k : ℝ) * (p : ℝ) ≤ 30 * (n : ℝ) := by exact_mod_cast h2c
    linarith
  have hsum : 2 * (sixRowPenalty (rank n) p q : ℝ) ≤
      ∑ k ∈ Finset.Icc (q + 1) k30, (30 * (n : ℝ) - (k : ℝ) * (p : ℝ)) := by
    rw [hpen_eq, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum hterm_le
  have hcardIcc : (Finset.Icc (q + 1) k30).card = k30 - q := by rw [Nat.card_Icc]; omega
  have hrhs : (∑ k ∈ Finset.Icc (q + 1) k30, (30 * (n : ℝ) - (k : ℝ) * (p : ℝ))) =
      (n : ℝ) * ((30 * ((k30 - q : ℕ) : ℝ)) - ((sumRangeIcc q k30 : ℕ) : ℝ) * ((p : ℝ) / (n : ℝ))) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcardIcc,
      ← Finset.sum_mul, ← Nat.cast_sum, ← sumRangeIcc_eq q k30 hqk]
    field_simp [hnR.ne']
  linarith

/-- Soundness of `capIntCeil`: exact 4-case integral bound on `min 15 ((u0 + u1 * x) / 2)`. -/
theorem capIntCeil_sound (u0 u1 : ℤ) {ln ld rn rd D : ℕ}
    (hld : 0 < ld) (hrd : 0 < rd) (hlt : ln * rd < rn * ld) (hD : 0 < D) :
    (∫ x in ((ln : ℝ) / (ld : ℝ))..((rn : ℝ) / (rd : ℝ)),
      min (15 : ℝ) (((u0 : ℝ) + (u1 : ℝ) * x) / 2)) ≤
      (capIntCeil u0 u1 ln ld rn rd D : ℝ) / (D : ℝ) := by
  have hldR : (0 : ℝ) < (ld : ℝ) := by exact_mod_cast hld
  have hrdR : (0 : ℝ) < (rd : ℝ) := by exact_mod_cast hrd
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  let l : ℝ := (ln : ℝ) / (ld : ℝ)
  let r : ℝ := (rn : ℝ) / (rd : ℝ)
  have hlr : l < r := by
    dsimp [l, r]; rw [div_lt_div_iff₀ hldR hrdR]; exact_mod_cast hlt
  let va : ℤ := u0 * (ld : ℤ) + u1 * (ln : ℤ)
  let vb : ℤ := u0 * (rd : ℤ) + u1 * (rn : ℤ)
  let capL : ℤ := 30 * (ld : ℤ)
  let capR : ℤ := 30 * (rd : ℤ)
  let dx : ℤ := (rn : ℤ) * (ld : ℤ) - (ln : ℤ) * (rd : ℤ)
  have hdx_pos : 0 < dx := by dsimp [dx]; omega
  have hgl : ((u0 : ℝ) + (u1 : ℝ) * l) / 2 = (va : ℝ) / (2 * (ld : ℝ)) := by
    dsimp [l, va]; push_cast; field_simp [hldR.ne']
  have hgr : ((u0 : ℝ) + (u1 : ℝ) * r) / 2 = (vb : ℝ) / (2 * (rd : ℝ)) := by
    dsimp [r, vb]; push_cast; field_simp [hrdR.ne']
  have hceil_step : ∀ (num : ℤ) (den : ℕ), 0 < den →
      (num : ℝ) / (den : ℝ) ≤
        ((if num ≤ 0 then 0 else ceilDiv (num.toNat * D) den : ℕ) : ℝ) / (D : ℝ) := by
    intro num den hden
    split_ifs with h0
    · have : (num : ℝ) ≤ 0 := by exact_mod_cast h0
      have hle0 : (num : ℝ) / (den : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg this (Nat.cast_nonneg _)
      simpa using hle0
    · have hnn : 0 ≤ num := by omega
      have hto : ((num.toNat : ℕ) : ℝ) = (num : ℝ) := by
        have : (num.toNat : ℤ) = num := Int.toNat_of_nonneg hnn
        exact_mod_cast this
      rw [← hto, le_div_iff₀ hDR]
      have hc := div_le_ceilDiv_real (num.toNat * D) den hden
      calc ((num.toNat : ℕ) : ℝ) / (den : ℝ) * (D : ℝ)
          = ((num.toNat * D : ℕ) : ℝ) / (den : ℝ) := by push_cast; ring
        _ ≤ (ceilDiv (num.toNat * D) den : ℝ) := hc
  have hint_aff : ∀ a b : ℝ,
      (∫ x in a..b, ((u0 : ℝ) + (u1 : ℝ) * x) / 2) =
        (b - a) * (((u0 : ℝ) + (u1 : ℝ) * a) / 2 + ((u0 : ℝ) + (u1 : ℝ) * b) / 2) / 2 := by
    intro a b
    have h1 : (∫ x in a..b, ((u0 : ℝ) + (u1 : ℝ) * x) / 2) =
        (∫ _x in a..b, ((u0 : ℝ) / 2)) + ((u1 : ℝ) / 2) * (∫ x in a..b, x) := by
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add intervalIntegrable_const
          (Continuous.intervalIntegrable (by fun_prop) _ _)]
      congr 1; ext x; ring
    rw [h1, intervalIntegral.integral_const, smul_eq_mul, integral_id]; ring
  unfold capIntCeil
  dsimp +zetaHave only
  change (∫ x in l..r, min (15 : ℝ) (((u0 : ℝ) + (u1 : ℝ) * x) / 2)) ≤
    ((if (va ≤ capL && vb ≤ capR) then
        if dx * (va * (rd : ℤ) + vb * (ld : ℤ)) ≤ 0 then 0
        else ceilDiv ((dx * (va * (rd : ℤ) + vb * (ld : ℤ))).toNat * D) (4 * (ld * rd) * (ld * rd))
      else if (capL ≤ va && capR ≤ vb) then
        if 15 * dx ≤ 0 then 0
        else ceilDiv ((15 * dx).toNat * D) (ld * rd)
      else if (va < capL && capR < vb) then
        let s : ℕ := u1.toNat
        if 60 * (ld : ℤ) * (s : ℤ) * dx - (rd : ℤ) * (capL - va) * (capL - va) ≤ 0 then 0
        else ceilDiv ((60 * (ld : ℤ) * (s : ℤ) * dx - (rd : ℤ) * (capL - va) * (capL - va)).toNat * D)
          (4 * ld * ld * rd * s)
      else
        let s : ℕ := (-u1).toNat
        if 60 * (rd : ℤ) * (s : ℤ) * dx - (ld : ℤ) * (capR - vb) * (capR - vb) ≤ 0 then 0
        else ceilDiv ((60 * (rd : ℤ) * (s : ℤ) * dx - (ld : ℤ) * (capR - vb) * (capR - vb)).toNat * D)
          (4 * ld * rd * rd * s) : ℕ) : ℝ) / (D : ℝ)
  by_cases hc1 : va ≤ capL ∧ vb ≤ capR
  · have hb1 : (va ≤ capL && vb ≤ capR) = true := by simp [hc1]
    simp only [hb1, ite_true]
    have hmin_eq : ∀ x ∈ Set.uIcc l r,
        min (15 : ℝ) (((u0 : ℝ) + (u1 : ℝ) * x) / 2) = ((u0 : ℝ) + (u1 : ℝ) * x) / 2 := by
      intro x hx
      rw [Set.uIcc_of_le hlr.le] at hx
      apply min_eq_right
      have hL : ((u0 : ℝ) + (u1 : ℝ) * l) / 2 ≤ 15 := by
        rw [hgl, div_le_iff₀ (by positivity)]
        have : (va : ℝ) ≤ (capL : ℝ) := by exact_mod_cast hc1.1
        dsimp [capL] at this; push_cast at this; linarith
      have hR : ((u0 : ℝ) + (u1 : ℝ) * r) / 2 ≤ 15 := by
        rw [hgr, div_le_iff₀ (by positivity)]
        have : (vb : ℝ) ≤ (capR : ℝ) := by exact_mod_cast hc1.2
        dsimp [capR] at this; push_cast at this; linarith
      by_cases hs : (0 : ℝ) ≤ (u1 : ℝ) <;> nlinarith [hx.1, hx.2]
    rw [intervalIntegral.integral_congr hmin_eq, hint_aff l r]
    have heq : (r - l) * (((u0 : ℝ) + (u1 : ℝ) * l) / 2 + ((u0 : ℝ) + (u1 : ℝ) * r) / 2) / 2 =
        (((dx * (va * (rd : ℤ) + vb * (ld : ℤ))) : ℤ) : ℝ) / ((4 * (ld * rd) * (ld * rd) : ℕ) : ℝ) := by
      rw [hgl, hgr]; dsimp [l, r, dx]; push_cast; field_simp [hldR.ne', hrdR.ne']; ring
    rw [heq]
    exact hceil_step _ _ (by positivity)
  · have hb1 : (va ≤ capL && vb ≤ capR) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; tauto
    simp only [hb1, Bool.false_eq_true, ite_false]
    by_cases hc2 : capL ≤ va ∧ capR ≤ vb
    · have hb2 : (capL ≤ va && capR ≤ vb) = true := by simp [hc2]
      simp only [hb2, ite_true]
      have hmin_eq : ∀ x ∈ Set.uIcc l r,
          min (15 : ℝ) (((u0 : ℝ) + (u1 : ℝ) * x) / 2) = 15 := by
        intro x hx
        rw [Set.uIcc_of_le hlr.le] at hx
        apply min_eq_left
        have hL : 15 ≤ ((u0 : ℝ) + (u1 : ℝ) * l) / 2 := by
          rw [hgl, le_div_iff₀ (by positivity)]
          have : (capL : ℝ) ≤ (va : ℝ) := by exact_mod_cast hc2.1
          dsimp [capL] at this; push_cast at this; linarith
        have hR : 15 ≤ ((u0 : ℝ) + (u1 : ℝ) * r) / 2 := by
          rw [hgr, le_div_iff₀ (by positivity)]
          have : (capR : ℝ) ≤ (vb : ℝ) := by exact_mod_cast hc2.2
          dsimp [capR] at this; push_cast at this; linarith
        by_cases hs : (0 : ℝ) ≤ (u1 : ℝ) <;> nlinarith [hx.1, hx.2]
      rw [intervalIntegral.integral_congr hmin_eq, intervalIntegral.integral_const, smul_eq_mul]
      have heq : (r - l) * 15 = (((15 * dx : ℤ) : ℝ) / ((ld * rd : ℕ) : ℝ)) := by
        dsimp [l, r, dx]; push_cast; field_simp [hldR.ne', hrdR.ne']
      rw [heq]
      exact hceil_step _ _ (by positivity)
    · have hb2 : (capL ≤ va && capR ≤ vb) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; tauto
      simp only [hb2, Bool.false_eq_true, ite_false]
      by_cases hc3 : va < capL ∧ capR < vb
      · have hb3 : (va < capL && capR < vb) = true := by simp [hc3]
        simp only [hb3, ite_true]
        have hu1_pos : 0 < u1 := by
          have hL : (u0 : ℝ) + (u1 : ℝ) * l < 30 := by
            have hv : (va : ℝ) < (capL : ℝ) := by exact_mod_cast hc3.1
            dsimp [capL] at hv; push_cast at hv
            have : (va : ℝ) / (2 * (ld : ℝ)) < 15 := (div_lt_iff₀ (by positivity)).mpr (by linarith)
            linarith [hgl]
          have hR : 30 < (u0 : ℝ) + (u1 : ℝ) * r := by
            have hv : (capR : ℝ) < (vb : ℝ) := by exact_mod_cast hc3.2
            dsimp [capR] at hv; push_cast at hv
            have : 15 < (vb : ℝ) / (2 * (rd : ℝ)) := (lt_div_iff₀ (by positivity)).mpr (by linarith)
            linarith [hgr]
          have : (0 : ℝ) < (u1 : ℝ) := by nlinarith
          exact_mod_cast this
        let s : ℕ := u1.toNat
        have hs_eq : (s : ℤ) = u1 := Int.toNat_of_nonneg hu1_pos.le
        have hs_pos : 0 < s := by omega
        have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos
        have hu1R : (u1 : ℝ) = (s : ℝ) := by exact_mod_cast hs_eq.symm
        let x0 : ℝ := (30 - (u0 : ℝ)) / (s : ℝ)
        have hgl_lt : ((u0 : ℝ) + (u1 : ℝ) * l) / 2 < 15 := by
          rw [hgl, div_lt_iff₀ (by positivity)]
          have : (va : ℝ) < (capL : ℝ) := by exact_mod_cast hc3.1
          dsimp [capL] at this; push_cast at this; linarith
        have hgr_gt : 15 < ((u0 : ℝ) + (u1 : ℝ) * r) / 2 := by
          rw [hgr, lt_div_iff₀ (by positivity)]
          have : (capR : ℝ) < (vb : ℝ) := by exact_mod_cast hc3.2
          dsimp [capR] at this; push_cast at this; linarith
        have hlx0 : l < x0 := by
          dsimp [x0]; rw [lt_div_iff₀ hsR]; rw [hu1R] at hgl_lt; linarith
        have hx0r : x0 < r := by
          dsimp [x0]; rw [div_lt_iff₀ hsR]; rw [hu1R] at hgr_gt; linarith
        rw [← intervalIntegral.integral_add_adjacent_intervals (b := x0)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _)]
        have hleft : (∫ x in l..x0, min (15 : ℝ) (((u0 : ℝ) + (u1 : ℝ) * x) / 2)) =
            ∫ x in l..x0, ((u0 : ℝ) + (u1 : ℝ) * x) / 2 := by
          apply intervalIntegral.integral_congr; intro x hx
          rw [Set.uIcc_of_le hlx0.le] at hx
          apply min_eq_right
          have := (le_div_iff₀ hsR).mp hx.2
          rw [hu1R]; linarith
        have hright : (∫ x in x0..r, min (15 : ℝ) (((u0 : ℝ) + (u1 : ℝ) * x) / 2)) =
            ∫ _x in x0..r, (15 : ℝ) := by
          apply intervalIntegral.integral_congr; intro x hx
          rw [Set.uIcc_of_le hx0r.le] at hx
          apply min_eq_left
          have := (div_le_iff₀ hsR).mp hx.1
          rw [hu1R]; linarith
        rw [hleft, hright, hint_aff l x0, intervalIntegral.integral_const, smul_eq_mul]
        have heq : (x0 - l) * (((u0 : ℝ) + (u1 : ℝ) * l) / 2 + ((u0 : ℝ) + (u1 : ℝ) * x0) / 2) / 2 +
            (r - x0) * 15 =
            (((60 * (ld : ℤ) * (s : ℤ) * dx - (rd : ℤ) * (capL - va) * (capL - va) : ℤ) : ℝ) /
              ((4 * ld * ld * rd * s : ℕ) : ℝ)) := by
          dsimp [x0, l, r, dx, capL, va]; push_cast; rw [hu1R]
          field_simp [hldR.ne', hrdR.ne', hsR.ne']; ring
        rw [heq]
        exact hceil_step _ _ (by positivity)
      · have hb3 : (va < capL && capR < vb) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; tauto
        simp only [hb3, Bool.false_eq_true, ite_false]
        have hc4 : capL < va ∧ vb < capR := by omega
        have hu1_neg : u1 < 0 := by
          have hL : 30 < (u0 : ℝ) + (u1 : ℝ) * l := by
            have hv : (capL : ℝ) < (va : ℝ) := by exact_mod_cast hc4.1
            dsimp [capL] at hv; push_cast at hv
            have : 15 < (va : ℝ) / (2 * (ld : ℝ)) := (lt_div_iff₀ (by positivity)).mpr (by linarith)
            linarith [hgl]
          have hR : (u0 : ℝ) + (u1 : ℝ) * r < 30 := by
            have hv : (vb : ℝ) < (capR : ℝ) := by exact_mod_cast hc4.2
            dsimp [capR] at hv; push_cast at hv
            have : (vb : ℝ) / (2 * (rd : ℝ)) < 15 := (div_lt_iff₀ (by positivity)).mpr (by linarith)
            linarith [hgr]
          have : (u1 : ℝ) < 0 := by nlinarith
          exact_mod_cast this
        let s : ℕ := (-u1).toNat
        have hs_eq : (s : ℤ) = -u1 := Int.toNat_of_nonneg (by omega)
        have hs_pos : 0 < s := by omega
        have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos
        have hu1R : (u1 : ℝ) = -(s : ℝ) := by
          have : (u1 : ℤ) = -(s : ℤ) := by omega
          exact_mod_cast this
        let x0 : ℝ := ((u0 : ℝ) - 30) / (s : ℝ)
        have hgl_gt : 15 < ((u0 : ℝ) + (u1 : ℝ) * l) / 2 := by
          rw [hgl, lt_div_iff₀ (by positivity)]
          have : (capL : ℝ) < (va : ℝ) := by exact_mod_cast hc4.1
          dsimp [capL] at this; push_cast at this; linarith
        have hgr_lt : ((u0 : ℝ) + (u1 : ℝ) * r) / 2 < 15 := by
          rw [hgr, div_lt_iff₀ (by positivity)]
          have : (vb : ℝ) < (capR : ℝ) := by exact_mod_cast hc4.2
          dsimp [capR] at this; push_cast at this; linarith
        have hlx0 : l < x0 := by
          dsimp [x0]; rw [lt_div_iff₀ hsR]; rw [hu1R] at hgl_gt; linarith
        have hx0r : x0 < r := by
          dsimp [x0]; rw [div_lt_iff₀ hsR]; rw [hu1R] at hgr_lt; linarith
        rw [← intervalIntegral.integral_add_adjacent_intervals (b := x0)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _)]
        have hleft : (∫ x in l..x0, min (15 : ℝ) (((u0 : ℝ) + (u1 : ℝ) * x) / 2)) =
            ∫ _x in l..x0, (15 : ℝ) := by
          apply intervalIntegral.integral_congr; intro x hx
          rw [Set.uIcc_of_le hlx0.le] at hx
          apply min_eq_left
          have := (le_div_iff₀ hsR).mp hx.2
          rw [hu1R]; linarith
        have hright : (∫ x in x0..r, min (15 : ℝ) (((u0 : ℝ) + (u1 : ℝ) * x) / 2)) =
            ∫ x in x0..r, ((u0 : ℝ) + (u1 : ℝ) * x) / 2 := by
          apply intervalIntegral.integral_congr; intro x hx
          rw [Set.uIcc_of_le hx0r.le] at hx
          apply min_eq_right
          have := (div_le_iff₀ hsR).mp hx.1
          rw [hu1R]; linarith
        rw [hleft, hright, intervalIntegral.integral_const, smul_eq_mul, hint_aff x0 r]
        have heq : (x0 - l) * 15 +
            (r - x0) * (((u0 : ℝ) + (u1 : ℝ) * x0) / 2 + ((u0 : ℝ) + (u1 : ℝ) * r) / 2) / 2 =
            (((60 * (rd : ℤ) * (s : ℤ) * dx - (ld : ℤ) * (capR - vb) * (capR - vb) : ℤ) : ℝ) /
              ((4 * ld * rd * rd * s : ℕ) : ℝ)) := by
          dsimp [x0, l, r, dx, capR, vb]; push_cast; rw [hu1R]
          field_simp [hldR.ne', hrdR.ne', hsR.ne']; ring
        rw [heq]
        exact hceil_step _ _ (by positivity)

/-! ## Section 2: `refinedOrderCostO1`, bit-packed histogram, and `jointCapFromN` soundness -/

theorem sixHarmonicIndicator_eq_parity (n p k l : ℕ) :
    sixHarmonicIndicator n p k l =
      if Even l then sixHarmonicIndicator n p k 0 else sixHarmonicIndicator n p k 1 := by
  unfold sixHarmonicIndicator
  simp only [show Even (0 : ℕ) by decide, ite_true, show ¬ Even (1 : ℕ) by decide, ite_false]

theorem sixHarmonicIndicator_le_one (n p k l : ℕ) : sixHarmonicIndicator n p k l ≤ 1 := by
  unfold sixHarmonicIndicator; split_ifs <;> omega

/-- Soundness of the `O(1)` 4-candidate formula `refinedOrderCostO1`. -/
theorem sixRefinedOrderCost_le_O1 (n p k r : ℕ) (hr : r < sixPoleOrder n k) :
    sixRefinedOrderCost n p k r ≤
      refinedOrderCostO1 (sixPoleOrder n k) (sixSiteBaseVal n p k)
        (decide (sixDenomAliasCount n p k = 0)) (sixNumAliasCount n p k)
        (sixHarmonicIndicator n p k 0) (sixHarmonicIndicator n p k 1) r := by
  let m := sixPoleOrder n k
  let baseVal := sixSiteBaseVal n p k
  let daZero := decide (sixDenomAliasCount n p k = 0)
  let nz := sixNumAliasCount n p k
  let iE := sixHarmonicIndicator n p k 0
  let iO := sixHarmonicIndicator n p k 1
  have hiE : iE = 0 ∨ iE = 1 := by have := sixHarmonicIndicator_le_one n p k 0; omega
  have hiO : iO = 0 ∨ iO = 1 := by have := sixHarmonicIndicator_le_one n p k 1; omega
  let evalL (l ind : ℕ) : ℕ :=
    let d := m - 1 - l - r
    let d' := if daZero then min d nz else d
    let v : ℤ := (r : ℤ) - baseVal + (d' : ℤ) + ((l + 5 : ℕ) : ℤ) * (ind : ℤ)
    if v ≤ 0 then 0 else v.toNat
  have hmono : ∀ (l₁ l₂ ind : ℕ), l₁ ≤ l₂ → l₂ ≤ m - 1 - r → (ind = 0 ∨ ind = 1) →
      (ind = 0 → evalL l₂ ind ≤ evalL l₁ ind) ∧ (ind = 1 → evalL l₁ ind ≤ evalL l₂ ind) := by
    intro l₁ l₂ ind h12 h2max hind
    constructor
    · intro h0; subst h0
      dsimp [evalL]; split_ifs <;> omega
    · intro h1; subst h1
      dsimp [evalL]; split_ifs <;> omega
  unfold sixRefinedOrderCost
  apply Finset.sup_le
  intro l hl
  have hl_mem := Finset.mem_filter.mp hl
  have hl_max : l ≤ m - 1 - r := by
    have := Finset.mem_range.mp hl_mem.1; omega
  have hterm_eq :
      ((r : ℤ) - baseVal + (sixEffectiveOrderLoss n p k (m - 1 - l - r) : ℤ) +
        ((l + 5 : ℕ) : ℤ) * (sixHarmonicIndicator n p k l : ℤ)).toNat =
      evalL l (if Even l then iE else iO) := by
    rw [sixHarmonicIndicator_eq_parity n p k l]
    unfold sixEffectiveOrderLoss
    dsimp [evalL, daZero, nz, iE, iO, baseVal, m]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega
  change ((r : ℤ) - baseVal + (sixEffectiveOrderLoss n p k (m - 1 - l - r) : ℤ) +
    ((l + 5 : ℕ) : ℤ) * (sixHarmonicIndicator n p k l : ℤ)).toNat ≤ _
  rw [hterm_eq]
  unfold refinedOrderCostO1
  dsimp +zetaHave only
  let Lmax := m - 1 - r
  let maxEven := if Lmax % 2 == 0 then Lmax else Lmax - 1
  let b0 := evalL 0 iE
  let b1 := if maxEven > 0 then max b0 (evalL maxEven iE) else b0
  have hb0_le_b1 : b0 ≤ b1 := by dsimp [b1]; split_ifs <;> omega
  have hbmaxE_le_b1 : evalL maxEven iE ≤ b1 := by
    dsimp [b1]; split_ifs with h
    · exact le_max_right _ _
    · have : maxEven = 0 := by omega
      rw [this]
  have hb1_le_res : b1 ≤
      if Lmax ≥ 1 then
        let b2 := max b1 (evalL 1 iO)
        let maxOdd := if Lmax % 2 == 1 then Lmax else Lmax - 1
        if maxOdd > 1 then max b2 (evalL maxOdd iO) else b2
      else b1 := by
    dsimp only; split_ifs <;> omega
  by_cases hev : Even l
  · simp only [hev, ite_true]
    have hl_le_me : l ≤ maxEven := by
      rcases hev with ⟨t, rfl⟩
      dsimp [maxEven, Lmax]; simp only [beq_iff_eq]; split_ifs <;> omega
    have hme_le : maxEven ≤ m - 1 - r := by dsimp [maxEven, Lmax]; split_ifs <;> omega
    rcases hiE with h0 | h1
    · exact ((hmono 0 l iE (Nat.zero_le l) hl_max (Or.inl h0)).1 h0).trans (hb0_le_b1.trans hb1_le_res)
    · exact ((hmono l maxEven iE hl_le_me hme_le (Or.inr h1)).2 h1).trans (hbmaxE_le_b1.trans hb1_le_res)
  · simp only [hev, ite_false]
    have hl_odd : l % 2 = 1 := by
      rcases Nat.even_or_odd l with h | ⟨t, rfl⟩
      · exact absurd h hev
      · omega
    have hL1 : Lmax ≥ 1 := by dsimp [Lmax]; omega
    change evalL l iO ≤
      if Lmax ≥ 1 then
        let b2 := max b1 (evalL 1 iO)
        let maxOdd := if Lmax % 2 == 1 then Lmax else Lmax - 1
        if maxOdd > 1 then max b2 (evalL maxOdd iO) else b2
      else b1
    simp only [hL1, ite_true]
    let maxOdd := if Lmax % 2 == 1 then Lmax else Lmax - 1
    have hl_ge1 : 1 ≤ l := by omega
    have hl_le_mo : l ≤ maxOdd := by dsimp [maxOdd, Lmax]; simp only [beq_iff_eq]; split_ifs <;> omega
    have hmo_le : maxOdd ≤ m - 1 - r := by dsimp [maxOdd, Lmax]; split_ifs <;> omega
    have hb2_le : max b1 (evalL 1 iO) ≤
        if maxOdd > 1 then max (max b1 (evalL 1 iO)) (evalL maxOdd iO) else max b1 (evalL 1 iO) := by
      split_ifs <;> omega
    rcases hiO with h0 | h1
    · exact ((hmono 1 l iO hl_ge1 hl_max (Or.inl h0)).1 h0).trans ((le_max_right _ _).trans hb2_le)
    · have hmo_step : evalL maxOdd iO ≤
          if maxOdd > 1 then max (max b1 (evalL 1 iO)) (evalL maxOdd iO) else max b1 (evalL 1 iO) := by
        split_ifs with h
        · exact le_max_right _ _
        · have : maxOdd = 1 := by omega
          rw [this]; exact le_max_right _ _
      exact ((hmono l maxOdd iO hl_le_mo hmo_le (Or.inr h1)).2 h1).trans hmo_step

/-- When `sixDenomAliasCount > 0` and `iOdd ≤ iEven`, every slot cost is bounded by the single constant
`min (max 0 (m - 1 - baseVal + 5 * iEven)) 18`. -/
theorem sixRefinedSlotCost_le_const_of_daPos (n p k a : ℕ) (hp : 0 < p)
    (hda : sixDenomAliasCount n p k ≠ 0)
    (hio : sixHarmonicIndicator n p k 1 ≤ sixHarmonicIndicator n p k 0) :
    sixRefinedSlotCost n p k a ≤
      (let v : ℤ := (sixPoleOrder n k : ℤ) - 1 - sixSiteBaseVal n p k +
          5 * (sixHarmonicIndicator n p k 0 : ℤ)
       if v ≤ 0 then 0 else min v.toNat 18) := by
  have h18 := sixRefinedSlotCost_le_18 n p k a hp
  unfold sixRefinedSlotCost
  have hval : ((Finset.range (sixPoleOrder n k)).filter (fun r => a ≤ r)).sup
      (fun r => sixRefinedOrderCost n p k r) ≤
      (let v : ℤ := (sixPoleOrder n k : ℤ) - 1 - sixSiteBaseVal n p k +
          5 * (sixHarmonicIndicator n p k 0 : ℤ)
       if v ≤ 0 then 0 else v.toNat) := by
    apply Finset.sup_le; intro r hr
    unfold sixRefinedOrderCost
    apply Finset.sup_le; intro l hl
    have hl_mem := Finset.mem_filter.mp hl
    have hl_lt : l < sixPoleOrder n k := Finset.mem_range.mp hl_mem.1
    have hr_le : r ≤ sixPoleOrder n k - 1 - l := hl_mem.2
    have hloss : sixEffectiveOrderLoss n p k (sixPoleOrder n k - 1 - l - r) =
        sixPoleOrder n k - 1 - l - r := by
      unfold sixEffectiveOrderLoss; simp [hda]
    change ((r : ℤ) - sixSiteBaseVal n p k +
      (sixEffectiveOrderLoss n p k (sixPoleOrder n k - 1 - l - r) : ℤ) +
      ((l + 5 : ℕ) : ℤ) * (sixHarmonicIndicator n p k l : ℤ)).toNat ≤ _
    rw [hloss, sixHarmonicIndicator_eq_parity n p k l]
    have hi0 := sixHarmonicIndicator_le_one n p k 0
    have hi1 := sixHarmonicIndicator_le_one n p k 1
    rcases (by omega : sixHarmonicIndicator n p k 0 = 0 ∨ sixHarmonicIndicator n p k 0 = 1) with h0e | h0e <;>
      rcases (by omega : sixHarmonicIndicator n p k 1 = 0 ∨ sixHarmonicIndicator n p k 1 = 1) with h1e | h1e <;>
      simp only [h0e, h1e, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one] <;>
      split_ifs <;> omega
  dsimp only at hval ⊢
  split_ifs at hval ⊢ with hv
  · exact hval
  · exact le_min hval h18

/-- Bit-packed base-256 histogram invariant on bins `v ∈ 1..18`. -/
def HistRepr (cnt : ℕ → ℕ) (packed : ℕ) : Prop :=
  packed = ∑ v ∈ Finset.Icc 1 18, cnt v * pow256 v

theorem pow256_eq_pow (v : ℕ) (hv : v ≤ 18) : pow256 v = 256 ^ v := by
  interval_cases v <;> decide

theorem histRepr_zero : HistRepr (fun _ => 0) 0 := by
  unfold HistRepr; simp

theorem histRepr_add_bin {cnt : ℕ → ℕ} {packed : ℕ} (h : HistRepr cnt packed)
    (b k : ℕ) (hb1 : 1 ≤ b) (hb18 : b ≤ 18) :
    HistRepr (fun v => cnt v + if v = b then k else 0) (packed + k * pow256 b) := by
  unfold HistRepr at *
  rw [h]
  have hmem : b ∈ Finset.Icc 1 18 := Finset.mem_Icc.mpr ⟨hb1, hb18⟩
  have hsum : (∑ v ∈ Finset.Icc 1 18, (cnt v + if v = b then k else 0) * pow256 v) =
      (∑ v ∈ Finset.Icc 1 18, cnt v * pow256 v) +
      (∑ v ∈ Finset.Icc 1 18, (if v = b then k * pow256 v else 0)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro v _
    split_ifs <;> ring
  rw [hsum, Finset.sum_ite_eq' (Finset.Icc 1 18) b (fun v => k * pow256 v)]
  simp only [hmem, ite_true]

theorem histRepr_extract {cnt : ℕ → ℕ} {packed : ℕ} (h : HistRepr cnt packed)
    (hsmall : ∀ v ∈ Finset.Icc 1 18, cnt v < 256)
    (v : ℕ) (hv1 : 1 ≤ v) (hv18 : v ≤ 18) :
    (packed / pow256 v) % 256 = cnt v := by
  have hpow : ∀ w ∈ Finset.Icc 1 18, pow256 w = 256 ^ w := fun w hw =>
    pow256_eq_pow w (Finset.mem_Icc.mp hw).2
  have hpacked : packed =
      (∑ w ∈ Finset.Ico 1 v, cnt w * 256 ^ w) +
      cnt v * 256 ^ v +
      (∑ w ∈ Finset.Ioc v 18, cnt w * 256 ^ w) := by
    rw [h]
    have hsplit1 : Finset.Icc 1 18 = Finset.Ico 1 v ∪ insert v (Finset.Ioc v 18) := by
      ext w; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico, Finset.mem_insert,
        Finset.mem_Ioc]; omega
    have hdisj : Disjoint (Finset.Ico 1 v) (insert v (Finset.Ioc v 18)) := by
      rw [Finset.disjoint_left]; intro w hw1 hw2
      simp only [Finset.mem_Ico] at hw1
      simp only [Finset.mem_insert, Finset.mem_Ioc] at hw2; omega
    have hnot : v ∉ Finset.Ioc v 18 := by simp
    have hrew : (∑ w ∈ Finset.Icc 1 18, cnt w * pow256 w) =
        ∑ w ∈ Finset.Icc 1 18, cnt w * 256 ^ w :=
      Finset.sum_congr rfl (fun w hw => by rw [hpow w hw])
    rw [hrew, hsplit1, Finset.sum_union hdisj, Finset.sum_insert hnot]; ring
  have hlow_lt : ∑ w ∈ Finset.Ico 1 v, cnt w * 256 ^ w < 256 ^ v := by
    have hgeom : ∀ m ≤ 18, ∑ w ∈ Finset.Ico 1 m, cnt w * 256 ^ w < 256 ^ m := by
      intro m hm
      induction m with
      | zero => simp
      | succ m' ih =>
        by_cases hm0 : m' = 0
        · subst hm0; simp
        · have hIco : Finset.Ico 1 (m' + 1) = insert m' (Finset.Ico 1 m') := by
            ext w; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
          have hnot : m' ∉ Finset.Ico 1 m' := by simp
          rw [hIco, Finset.sum_insert hnot]
          have hih := ih (by omega)
          have hcnt : cnt m' ≤ 255 := Nat.lt_succ_iff.mp (hsmall m' (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
          calc cnt m' * 256 ^ m' + ∑ w ∈ Finset.Ico 1 m', cnt w * 256 ^ w
              < cnt m' * 256 ^ m' + 256 ^ m' := Nat.add_lt_add_left hih _
            _ ≤ 255 * 256 ^ m' + 256 ^ m' := Nat.add_le_add_right (Nat.mul_le_mul_right _ hcnt) _
            _ = 256 ^ (m' + 1) := by rw [pow_succ]; ring
    exact hgeom v hv18
  have hhigh_dvd : 256 * 256 ^ v ∣ ∑ w ∈ Finset.Ioc v 18, cnt w * 256 ^ w := by
    apply Finset.dvd_sum; intro w hw
    have hwgt : v < w := (Finset.mem_Ioc.mp hw).1
    have hpow_dvd : 256 ^ (v + 1) ∣ 256 ^ w := Nat.pow_dvd_pow 256 (by omega)
    rw [pow_succ, mul_comm] at hpow_dvd
    exact dvd_mul_of_dvd_right hpow_dvd _
  obtain ⟨q, hq⟩ := hhigh_dvd
  rw [pow256_eq_pow v hv18, hpacked, hq]
  have hpos : 0 < 256 ^ v := by positivity
  have hrew : (∑ w ∈ Finset.Ico 1 v, cnt w * 256 ^ w) + cnt v * 256 ^ v + 256 * 256 ^ v * q =
      (∑ w ∈ Finset.Ico 1 v, cnt w * 256 ^ w) + (cnt v + 256 * q) * 256 ^ v := by ring
  rw [hrew, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlow_lt, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hsmall v (Finset.mem_Icc.mpr ⟨hv1, hv18⟩))]

/-- Soundness of `packedToSuffixCounts`: entry `v ∈ 1..18` equals `∑ w ∈ Icc v 18, cnt w`. -/
theorem packedToSuffixCounts_spec {cnt : ℕ → ℕ} {packed : ℕ} (h : HistRepr cnt packed)
    (hsmall : ∀ v ∈ Finset.Icc 1 18, cnt v < 256) :
    ∀ v ∈ Finset.Icc 1 18,
      (packedToSuffixCounts packed).getD v 0 = ∑ w ∈ Finset.Icc v 18, cnt w := by
  have hgo : ∀ (k : ℕ) (hk : k ≤ 18) (running : ℕ) (acc : List ℕ),
      (∀ w ∈ Finset.Icc (k + 1) 18,
        acc.getD (w - (k + 1)) 0 = ∑ u ∈ Finset.Icc w 18, cnt u) →
      running = ∑ u ∈ Finset.Icc (k + 1) 18, cnt u →
      ∀ v ∈ Finset.Icc 1 18,
        (packedToSuffixCounts.go packed k running acc).getD v 0 = ∑ u ∈ Finset.Icc v 18, cnt u := by
    intro k
    induction k with
    | zero =>
      intro _ running acc hacc _ v hv
      simp only [packedToSuffixCounts.go]
      have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
      cases v with
      | zero => omega
      | succ v' =>
        simp only [List.getD_cons_succ]
        have := hacc (v' + 1) (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hv).2⟩)
        simpa using this
    | succ k' ih =>
      intro hk running acc hacc hrun v hv
      simp only [packedToSuffixCounts.go]
      have hcnt_eq : (packed / pow256 (k' + 1)) % 256 = cnt (k' + 1) :=
        histRepr_extract h hsmall (k' + 1) (by omega) hk
      rw [hcnt_eq]
      apply ih (by omega)
      · intro w hw
        have hw1 : k' + 1 ≤ w := (Finset.mem_Icc.mp hw).1
        have hw18 : w ≤ 18 := (Finset.mem_Icc.mp hw).2
        by_cases hweq : w = k' + 1
        · subst hweq
          simp only [Nat.sub_self, List.getD_cons_zero]
          have hIcc : Finset.Icc (k' + 1) 18 = insert (k' + 1) (Finset.Icc (k' + 2) 18) := by
            ext u; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hrun, hIcc, Finset.sum_insert (by simp), add_comm]
        · have hsub : w - (k' + 1) = (w - (k' + 2)) + 1 := by omega
          rw [hsub, List.getD_cons_succ]
          exact hacc w (Finset.mem_Icc.mpr ⟨by omega, hw18⟩)
      · have hIcc : Finset.Icc (k' + 1) 18 = insert (k' + 1) (Finset.Icc (k' + 2) 18) := by
          ext u; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hrun, hIcc, Finset.sum_insert (by simp), add_comm]
      · exact hv
  exact hgo 18 le_rfl 0 [] (by intro w hw; simp only [Finset.mem_Icc] at hw; omega)
    (by simp)

/-- Soundness of `addBranchSlotsPacked` for one half-pole `k` of order `m`:
adds counts `Δcnt` with `∑_{v=1}^{18} Δcnt v ≤ m` dominating `sixRefinedSlotCost n p k a` for all `a < m`. -/
theorem addBranchSlotsPacked_sound (n p k : ℕ) (hp : 0 < p)
    (hio : sixHarmonicIndicator n p k 1 ≤ sixHarmonicIndicator n p k 0)
    (cnt0 : ℕ → ℕ) (packed0 : ℕ) (hrepr0 : HistRepr cnt0 packed0) :
    ∃ Δcnt : ℕ → ℕ,
      HistRepr (fun v => cnt0 v + Δcnt v)
        (addBranchSlotsPacked (sixPoleOrder n k) (sixSiteBaseVal n p k)
          (decide (sixDenomAliasCount n p k = 0)) (sixNumAliasCount n p k)
          (sixHarmonicIndicator n p k 0) (sixHarmonicIndicator n p k 1) packed0) ∧
      (∑ v ∈ Finset.Icc 1 18, Δcnt v) ≤ sixPoleOrder n k ∧
      ∀ v ∈ Finset.Icc 1 18,
        ((Finset.range (sixPoleOrder n k)).filter (fun a => v ≤ sixRefinedSlotCost n p k a)).card ≤
          ∑ w ∈ Finset.Icc v 18, Δcnt w := by
  let m := sixPoleOrder n k
  let baseVal := sixSiteBaseVal n p k
  let daZero := decide (sixDenomAliasCount n p k = 0)
  let nz := sixNumAliasCount n p k
  let iE := sixHarmonicIndicator n p k 0
  let iO := sixHarmonicIndicator n p k 1
  unfold addBranchSlotsPacked
  by_cases hda : sixDenomAliasCount n p k = 0
  · simp only [hda, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    -- Backward suffix-max loop `go rem curMax acc`
    let stepB (a : ℕ) : ℕ :=
      ((Finset.Ico a m).sup (fun r => refinedOrderCostO1 m baseVal true nz iE iO r))
    have hgo : ∀ (rem : ℕ) (hrem : rem ≤ m) (c0 : ℕ → ℕ) (p0 : ℕ),
        HistRepr c0 p0 →
        ∃ d : ℕ → ℕ,
          HistRepr (fun v => c0 v + d v)
            (addBranchSlotsPacked.go m baseVal nz iE iO rem (stepB rem) p0) ∧
          (∑ v ∈ Finset.Icc 1 18, d v) ≤ rem ∧
          ∀ v ∈ Finset.Icc 1 18,
            ((Finset.range rem).filter (fun a => v ≤ stepB a)).card ≤
              ∑ w ∈ Finset.Icc v 18, d w := by
      intro rem
      induction rem with
      | zero =>
        intro _ c0 p0 hr0
        refine ⟨fun _ => 0, by simpa [addBranchSlotsPacked.go] using hr0, by simp, by simp⟩
      | succ r ih =>
        intro hrm c0 p0 hr0
        simp only [addBranchSlotsPacked.go]
        have hstep_eq : max (stepB (r + 1)) (refinedOrderCostO1 m baseVal true nz iE iO r) = stepB r := by
          dsimp [stepB]
          have hIco : Finset.Ico r m = insert r (Finset.Ico (r + 1) m) := by
            ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
          rw [hIco, Finset.sup_insert, max_comm]
        rw [hstep_eq]
        let b := stepB r
        change ∃ d : ℕ → ℕ,
          HistRepr (fun v => c0 v + d v)
            (addBranchSlotsPacked.go m baseVal nz iE iO r b (if (b == 0) = true then p0 else p0 + pow256 (min b 18))) ∧
          (∑ v ∈ Finset.Icc 1 18, d v) ≤ r + 1 ∧
          ∀ v ∈ Finset.Icc 1 18,
            ((Finset.range (r + 1)).filter (fun a => v ≤ stepB a)).card ≤
              ∑ w ∈ Finset.Icc v 18, d w
        by_cases hb0 : b = 0
        · simp only [hb0, beq_self_eq_true, ite_true]
          obtain ⟨d, hr1, hsum1, hdom1⟩ := ih (by omega) c0 p0 hr0
          refine ⟨d, by rwa [show (0 : ℕ) = stepB r from hb0.symm], by omega, fun v hv => ?_⟩
          have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
          have hfilt : (Finset.range (r + 1)).filter (fun a => v ≤ stepB a) =
              (Finset.range r).filter (fun a => v ≤ stepB a) := by
            ext a; simp only [Finset.mem_filter, Finset.mem_range]
            constructor
            · rintro ⟨ha, hle⟩
              refine ⟨?_, hle⟩
              by_contra hge
              have har : a = r := by omega
              subst har; change v ≤ b at hle; omega
            · rintro ⟨ha, hle⟩; exact ⟨by omega, hle⟩
          rw [hfilt]; exact hdom1 v hv
        · have hbne : (b == 0) = false := beq_false_of_ne hb0
          simp only [hbne, Bool.false_eq_true, ite_false]
          let b' := min b 18
          have hb'1 : 1 ≤ b' := by dsimp [b']; omega
          have hb'18 : b' ≤ 18 := min_le_right _ _
          have hr_step := histRepr_add_bin hr0 b' 1 hb'1 hb'18
          simp only [one_mul] at hr_step
          obtain ⟨d, hr1, hsum1, hdom1⟩ := ih (by omega) _ _ hr_step
          refine ⟨fun v => (if v = b' then 1 else 0) + d v, ?_, ?_, ?_⟩
          · convert hr1 using 1; ext v; ring
          · rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.Icc 1 18) b' (fun _ => 1)]
            simp only [Finset.mem_Icc.mpr ⟨hb'1, hb'18⟩, ite_true]
            omega
          · intro v hv
            have hv18 : v ≤ 18 := (Finset.mem_Icc.mp hv).2
            rw [Finset.sum_add_distrib]
            have hrange : (Finset.range (r + 1)).filter (fun a => v ≤ stepB a) =
                (if v ≤ b then {r} else ∅) ∪ (Finset.range r).filter (fun a => v ≤ stepB a) := by
              ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
              by_cases har : a = r
              · subst har; split_ifs with hvb <;> simp [b, hvb]
              · split_ifs <;> simp [har] <;> omega
            rw [hrange]
            have hcard_le : ((if v ≤ b then ({r} : Finset ℕ) else ∅) ∪
                (Finset.range r).filter (fun a => v ≤ stepB a)).card ≤
                (if v ≤ b then 1 else 0) + ((Finset.range r).filter (fun a => v ≤ stepB a)).card := by
              refine (Finset.card_union_le _ _).trans ?_
              split_ifs <;> simp
            have hite_eq : (∑ w ∈ Finset.Icc v 18, if w = b' then 1 else 0) = if v ≤ b then 1 else 0 := by
              rw [Finset.sum_ite_eq' (Finset.Icc v 18) b' (fun _ => 1)]
              have hiff : b' ∈ Finset.Icc v 18 ↔ v ≤ b := by
                simp only [Finset.mem_Icc, b']; omega
              by_cases hvb : v ≤ b <;> simp [hiff, hvb]
            rw [hite_eq]
            exact hcard_le.trans (Nat.add_le_add_left (hdom1 v hv) _)
    have hstep_m : stepB m = 0 := by
      dsimp [stepB]
      simp
    have hrepr_m := hgo m le_rfl cnt0 packed0 hrepr0
    rw [hstep_m] at hrepr_m
    obtain ⟨d, hr1, hsum1, hdom1⟩ := hrepr_m
    refine ⟨d, hr1, hsum1, fun v hv => ?_⟩
    refine (Finset.card_le_card ?_).trans (hdom1 v hv)
    intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨ha.1, ha.2.trans ?_⟩
    unfold sixRefinedSlotCost
    apply Finset.sup_le; intro r hr
    have hr_mem := Finset.mem_filter.mp hr
    have hr_lt : r < m := Finset.mem_range.mp hr_mem.1
    have h1 := sixRefinedOrderCost_le_O1 n p k r hr_lt
    simp only [hda, decide_true] at h1
    exact h1.trans (Finset.le_sup (f := fun r => refinedOrderCostO1 m baseVal true nz iE iO r)
      (Finset.mem_Ico.mpr ⟨hr_mem.2, hr_lt⟩))
  · simp only [hda, decide_false, Bool.not_false, ite_true]
    let v0 : ℤ := (m : ℤ) - 1 - baseVal + 5 * (iE : ℤ)
    let b : ℕ := if v0 ≤ 0 then 0 else min v0.toNat 18
    change ∃ Δcnt : ℕ → ℕ,
      HistRepr (fun v => cnt0 v + Δcnt v)
        (if (b == 0) = true then packed0 else packed0 + m * pow256 b) ∧
      (∑ v ∈ Finset.Icc 1 18, Δcnt v) ≤ m ∧
      ∀ v ∈ Finset.Icc 1 18,
        ((Finset.range m).filter (fun a => v ≤ sixRefinedSlotCost n p k a)).card ≤
          ∑ w ∈ Finset.Icc v 18, Δcnt w
    by_cases hb0 : b = 0
    · simp only [hb0, beq_self_eq_true, ite_true]
      refine ⟨fun _ => 0, by simpa using hrepr0, by simp, fun v hv => ?_⟩
      have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
      have hemp : (Finset.range m).filter (fun a => v ≤ sixRefinedSlotCost n p k a) = ∅ := by
        ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
        rintro ⟨_, hle⟩
        have hcap := sixRefinedSlotCost_le_const_of_daPos n p k a hp hda hio
        change sixRefinedSlotCost n p k a ≤ b at hcap
        omega
      rw [hemp]; simp
    · have hbne : (b == 0) = false := beq_false_of_ne hb0
      simp only [hbne, Bool.false_eq_true, ite_false]
      have hb1 : 1 ≤ b := by omega
      have hb18 : b ≤ 18 := by dsimp [b]; split_ifs <;> omega
      refine ⟨fun v => if v = b then m else 0,
        histRepr_add_bin hrepr0 b m hb1 hb18, ?_, fun v hv => ?_⟩
      · rw [Finset.sum_ite_eq' (Finset.Icc 1 18) b (fun _ => m)]
        simp only [Finset.mem_Icc.mpr ⟨hb1, hb18⟩, ite_true, le_rfl]
      · rw [Finset.sum_ite_eq' (Finset.Icc v 18) b (fun _ => m)]
        by_cases hvb : v ≤ b
        · simp only [Finset.mem_Icc.mpr ⟨hvb, hb18⟩, ite_true]
          exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
        · have hemp : (Finset.range m).filter (fun a => v ≤ sixRefinedSlotCost n p k a) = ∅ := by
            ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
            rintro ⟨_, hle⟩
            have hcap := sixRefinedSlotCost_le_const_of_daPos n p k a hp hda hio
            change sixRefinedSlotCost n p k a ≤ b at hcap
            omega
          rw [hemp]; simp

private theorem hw_descWeights_length {α : Type*} (S : Finset α) (B : α → ℕ) :
    (descWeights S B).length = S.card := by
  unfold descWeights
  rw [List.length_mergeSort, List.length_map, Finset.length_toList]

private theorem hw_descWeights_perm {α : Type*} (S : Finset α) (B : α → ℕ) :
    (descWeights S B).Perm (S.toList.map B) :=
  List.mergeSort_perm _ _

private theorem hw_descWeights_antitone {α : Type*} (S : Finset α) (B : α → ℕ) :
    ∀ i j : ℕ, (hi : i < (descWeights S B).length) → (hj : j < (descWeights S B).length) →
      i ≤ j → (descWeights S B)[j] ≤ (descWeights S B)[i] := by
  have hpw : (descWeights S B).Pairwise (fun a b => decide (b ≤ a) = true) :=
    List.pairwise_mergeSort (le := fun a b => decide (b ≤ a))
      (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega)
      (fun a b => by simp; omega) _
  intro i j hi hj hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have := List.pairwise_iff_getElem.mp hpw i j hi hj hlt
    simpa using this

/-- Descending-weight threshold lemma: `v ≤ nthDescWeight S B r → r < #{u ∈ S : v ≤ B u}`. -/
theorem lt_card_filter_of_le_nthDescWeight {α : Type*} (S : Finset α) (B : α → ℕ)
    {r v : ℕ} (hr : r < S.card) (hv : v ≤ nthDescWeight S B r) :
    r < (S.filter (fun u => v ≤ B u)).card := by
  have hrlen : r < (descWeights S B).length := by rwa [hw_descWeights_length]
  have hget : v ≤ (descWeights S B)[r] := by
    unfold nthDescWeight at hv
    rwa [List.getD_eq_getElem _ _ hrlen] at hv
  have hcnt_ge : r + 1 ≤ (descWeights S B).countP (fun x => decide (v ≤ x)) := by
    have hgen : ∀ (l : List ℕ) (p : ℕ → Bool),
        l.countP p = ((Finset.range l.length).filter (fun j => p (l.getD j 0))).card := by
      intro l p
      induction l with
      | nil => simp
      | cons x xs ih =>
        rw [List.countP_cons, List.length_cons, ih]
        have hsplit : (Finset.range (xs.length + 1)).filter (fun j => p ((x :: xs).getD j 0)) =
            (if p x then {0} else ∅) ∪
              ((Finset.range xs.length).filter (fun j => p (xs.getD j 0))).image (· + 1) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
          cases j with
          | zero => by_cases hpx : p x <;> simp [hpx]
          | succ j =>
            simp only [List.getD_cons_succ, Nat.succ_lt_succ_iff, Nat.succ_inj, exists_eq_right]
            split_ifs <;> simp
        rw [hsplit, Finset.card_union_of_disjoint]
        · rw [Finset.card_image_of_injective _ (fun _ _ h => by omega)]
          split_ifs <;> simp [add_comm]
        · rw [Finset.disjoint_left]; intro j hj1 hj2
          simp only [Finset.mem_image] at hj2
          obtain ⟨k, _, rfl⟩ := hj2
          split_ifs at hj1 <;> simp at hj1
    rw [hgen]
    have hsub : Finset.range (r + 1) ⊆ (Finset.range (descWeights S B).length).filter
        (fun j => decide (v ≤ (descWeights S B).getD j 0)) := by
      intro j hj
      have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hjlen : j < (descWeights S B).length := hjr.trans_lt hrlen
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨hjlen, ?_⟩
      rw [List.getD_eq_getElem _ _ hjlen]
      simp [hget.trans (hw_descWeights_antitone S B j r hjlen hrlen hjr)]
    simpa using Finset.card_le_card hsub
  have heq : (descWeights S B).countP (fun x => decide (v ≤ x)) =
      (S.filter (fun u => v ≤ B u)).card := by
    have h1 := ((hw_descWeights_perm S B).countP_eq (fun x => decide (v ≤ x)))
    rw [h1, List.countP_map]
    have h2 : (S.toList.countP (fun u => decide (v ≤ B u))) =
        (S.filter (fun u => v ≤ B u)).card := by
      have hnodup : S.toList.Nodup := Finset.nodup_toList S
      rw [← Finset.length_toList (S.filter (fun u => v ≤ B u)), List.countP_eq_length_filter]
      have hperm : (S.filter (fun u => v ≤ B u)).toList.Perm
          (S.toList.filter (fun u => decide (v ≤ B u))) := by
        rw [List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (hnodup.filter _)]
        intro u
        simp [Finset.mem_toList, Finset.mem_filter]
      exact hperm.symm.length_eq
    simpa [Function.comp_def] using h2
  omega

/-- Soundness of `jointCapFromN`: bounds the number of qualifying descending ranks in a class `S`. -/
theorem jointCapFromN_sound {α : Type*} (S : Finset α) (B : α → ℕ)
    (hB18 : ∀ u ∈ S, B u ≤ 18) (Nlist : List ℕ)
    (hN : ∀ v ∈ Finset.Icc 1 18, (S.filter (fun u => v ≤ B u)).card ≤ Nlist.getD v 0)
    (q j : ℕ) (hj1 : 1 ≤ j) (hj18 : j ≤ 18) :
    ((Finset.range S.card).filter
      (fun r => (j : ℤ) ≤ (nthDescWeight S B r : ℤ) - 2 * ((r - q : ℕ) : ℤ))).card ≤
      jointCapFromN Nlist q j := by
  have hgo_mono : ∀ (steps k best : ℕ), best ≤ jointCapFromN.go Nlist q j steps k best := by
    intro steps
    induction steps with
    | zero => intro _ _; exact le_rfl
    | succ s ih =>
      intro k best
      simp only [jointCapFromN.go]
      split_ifs with hgt hlt
      · exact le_rfl
      · exact (le_max_left _ _).trans (ih _ _)
      · exact ih _ _
  have hgo_hit : ∀ (steps k best t : ℕ), t < steps → j + 2 * (k + t) ≤ 18 →
      q + (k + t) < Nlist.getD (j + 2 * (k + t)) 0 →
      q + (k + t) + 1 ≤ jointCapFromN.go Nlist q j steps k best := by
    intro steps
    induction steps with
    | zero => intro _ _ _ ht; omega
    | succ s ih =>
      intro k best t ht h18 hlt
      simp only [jointCapFromN.go]
      have hvv_le : ¬ (j + 2 * k > 18) := by omega
      simp only [hvv_le, ite_false]
      cases t with
      | zero =>
        simp only [add_zero] at hlt ⊢
        simp only [hlt, ite_true]
        exact (le_max_right _ _).trans (hgo_mono s (k + 1) _)
      | succ t' =>
        have heq : k + (t' + 1) = (k + 1) + t' := by omega
        rw [heq] at h18 hlt ⊢
        exact ih (k + 1) _ t' (by omega) h18 hlt
  have hsub : (Finset.range S.card).filter
      (fun r => (j : ℤ) ≤ (nthDescWeight S B r : ℤ) - 2 * ((r - q : ℕ) : ℤ)) ⊆
      Finset.range (jointCapFromN Nlist q j) := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    rw [Finset.mem_range]
    unfold jointCapFromN
    by_cases hrq : r < q
    · have hsub0 : r - q = 0 := by omega
      have hge : j ≤ nthDescWeight S B r := by omega
      have hltN : r < Nlist.getD j 0 :=
        (lt_card_filter_of_le_nthDescWeight S B hr.1 hge).trans_le
          (hN j (Finset.mem_Icc.mpr ⟨hj1, hj18⟩))
      exact (lt_min hrq hltN).trans_le (hgo_mono 10 0 _)
    · let k := r - q
      have hr_eq : r = q + k := by omega
      have h18w : nthDescWeight S B r ≤ 18 := nthDescWeight_le_bound S B 18 hB18 r
      have hge : j + 2 * k ≤ nthDescWeight S B r := by omega
      have hvv18 : j + 2 * k ≤ 18 := hge.trans h18w
      have hk10 : k < 10 := by omega
      have hltN : q + k < Nlist.getD (j + 2 * k) 0 := by
        rw [← hr_eq]
        exact (lt_card_filter_of_le_nthDescWeight S B hr.1 hge).trans_le
          (hN (j + 2 * k) (Finset.mem_Icc.mpr ⟨by omega, hvv18⟩))
      have hhit := hgo_hit 10 0 (min q (Nlist.getD j 0)) k hk10 (by simpa using hvv18) (by simpa using hltN)
      simp only [zero_add] at hhit
      omega
  exact (Finset.card_le_card hsub).trans (by rw [Finset.card_range])

/-! ## Section 3: High-band folded residue geometry (`x = p/n ∈ (7/2, 55)`) -/

/-- Exact `highDelta` evaluation for any radius `rad`, prime `p`, and `0 < c < p/2`. -/
theorem symBlockMultCount_eq_highDelta (n p rad q2 pos g : ℕ) (hp : 0 < p) (c : ℕ)
    (hc0 : 0 < c) (hchalf : 2 * c < p)
    (hq2_lo : q2 * p ≤ 2 * rad * n) (hq2_hi : 2 * rad * n < (q2 + 1) * p)
    (hside : let line := highLine2 rad q2;
      (g ≤ pos → 2 * (c : ℤ) < line.1 * (n : ℤ) + line.2 * (p : ℤ)) ∧
      (¬ g ≤ pos → line.1 * (n : ℤ) + line.2 * (p : ℤ) < 2 * (c : ℤ))) :
    symBlockMultCount p (rad * n) (c : ℤ) =
      ((let qr := q2 / 2; if q2 % 2 == 0 then 2 * qr + (if g ≤ pos then 1 else 0)
        else 2 * qr + (if g ≤ pos then 1 else 2) : ℕ) : ℤ) := by
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  let q : ℕ := q2 / 2
  have hq2_split : q2 = 2 * q + q2 % 2 := (Nat.div_add_mod q2 2).symm
  have hq2_loZ : (q2 : ℤ) * (p : ℤ) ≤ 2 * (rad : ℤ) * (n : ℤ) := by exact_mod_cast hq2_lo
  have hq2_hiZ : 2 * (rad : ℤ) * (n : ℤ) < ((q2 : ℤ) + 1) * (p : ℤ) := by exact_mod_cast hq2_hi
  have hediv : ∀ (x z : ℤ), z * (p : ℤ) ≤ x → x < (z + 1) * (p : ℤ) → x / (p : ℤ) = z := by
    intro x z hlo hhi
    have h1 : z ≤ x / (p : ℤ) := (Int.le_ediv_iff_mul_le hpZ).mpr hlo
    have h2 : x / (p : ℤ) < z + 1 := (Int.ediv_lt_iff_lt_mul hpZ).mpr hhi
    omega
  unfold symBlockMultCount
  by_cases hev : q2 % 2 = 0
  · simp only [hev, beq_self_eq_true, ite_true]
    have hq2_eq : (q2 : ℤ) = 2 * (q : ℤ) := by omega
    have hline : highLine2 rad q2 = (2 * (rad : ℤ), -2 * (q : ℤ)) := by
      unfold highLine2; simp [hev, q]
    have hq_lo : (q : ℤ) * (p : ℤ) ≤ (rad : ℤ) * (n : ℤ) := by nlinarith
    have hq_hi : 2 * ((rad : ℤ) * (n : ℤ)) < (2 * (q : ℤ) + 1) * (p : ℤ) := by nlinarith
    have h1 : ((c : ℤ) + ((rad * n : ℕ) : ℤ)) / (p : ℤ) = (q : ℤ) :=
      hediv _ _ (by push_cast; nlinarith) (by push_cast; nlinarith)
    split_ifs with hgp
    · have hlt := hside.1 hgp
      rw [hline] at hlt; dsimp only at hlt
      have h2 : ((c : ℤ) - ((rad * n : ℕ) : ℤ) - 1) / (p : ℤ) = -(q : ℤ) - 1 :=
        hediv _ _ (by push_cast; nlinarith) (by push_cast; nlinarith)
      rw [h1, h2]; dsimp only [q]; omega
    · have hgt := hside.2 hgp
      rw [hline] at hgt; dsimp only at hgt
      have h2 : ((c : ℤ) - ((rad * n : ℕ) : ℤ) - 1) / (p : ℤ) = -(q : ℤ) :=
        hediv _ _ (by push_cast; nlinarith) (by push_cast; nlinarith)
      rw [h1, h2]; dsimp only [q]; omega
  · have hodd : q2 % 2 = 1 := by omega
    simp only [hodd, show (1 == 0) = false from rfl, Bool.false_eq_true, ite_false]
    have hq2_eq : (q2 : ℤ) = 2 * (q : ℤ) + 1 := by omega
    have hline : highLine2 rad q2 = (-2 * (rad : ℤ), 2 * ((q + 1 : ℕ) : ℤ)) := by
      unfold highLine2; simp [hodd, q]
    have hq_lo : (2 * (q : ℤ) + 1) * (p : ℤ) ≤ 2 * ((rad : ℤ) * (n : ℤ)) := by nlinarith
    have hq_hi : (rad : ℤ) * (n : ℤ) < ((q : ℤ) + 1) * (p : ℤ) := by nlinarith
    have h2 : ((c : ℤ) - ((rad * n : ℕ) : ℤ) - 1) / (p : ℤ) = -(q : ℤ) - 1 :=
      hediv _ _ (by push_cast; nlinarith) (by push_cast; nlinarith)
    split_ifs with hgp
    · have hlt := hside.1 hgp
      rw [hline] at hlt; dsimp only at hlt; push_cast at hlt
      have h1 : ((c : ℤ) + ((rad * n : ℕ) : ℤ)) / (p : ℤ) = (q : ℤ) :=
        hediv _ _ (by push_cast; nlinarith) (by push_cast; nlinarith)
      rw [h1, h2]; dsimp only [q]; omega
    · have hgt := hside.2 hgp
      rw [hline] at hgt; dsimp only at hgt; push_cast at hgt
      have h1 : ((c : ℤ) + ((rad * n : ℕ) : ℤ)) / (p : ℤ) = (q : ℤ) + 1 :=
        hediv _ _ (by push_cast; nlinarith) (by push_cast; nlinarith)
      rw [h1, h2]; dsimp only [q]; omega

/-- Exact half-pole order formula for `t : Fin (25 * n + 1)`. -/
theorem sixPoleOrder_halfPole_eq (n : ℕ) (t : Fin (25 * n + 1)) :
    sixPoleOrder n (sixHalfPole n t) =
      (if t.val ≤ 14 * n then 1 else 0) + (if t.val ≤ 16 * n then 2 else 0) +
      (if t.val ≤ 17 * n then 1 else 0) + (if t.val ≤ 19 * n then 1 else 0) +
      (if t.val ≤ 20 * n then 2 else 0) + (if t.val ≤ 21 * n then 1 else 0) +
      (if t.val ≤ 23 * n then 1 else 0) + (if t.val ≤ 25 * n then 5 else 0) := by
  have hord : sixPoleOrder n (sixHalfPole n t) =
      ∑ b : Fin 14, if t.val ≤ (25 - sixOffset b) * n then 1 else 0 := by
    unfold sixPoleOrder sixPoleList
    rw [list_count_flatMap, ← Fin.sum_univ_def]
    apply Finset.sum_congr rfl; intro b _
    have hob : sixOffset b ≤ 11 := by fin_cases b <;> decide
    have hmem : sixHalfPole n t ∈ (List.range (sixBlockLen n b + 1)).map (fun j => sixBlockStart n b + j) ↔
        t.val ≤ (25 - sixOffset b) * n := by
      simp only [List.mem_map, List.mem_range, sixHalfPole, sixCenter, sixBlockStart, sixBlockLen]
      constructor
      · rintro ⟨j, hj, heq⟩
        have h1 : (45 + sixOffset b) * n + (50 - 2 * sixOffset b) * n = (95 - sixOffset b) * n := by
          calc _ = ((45 + sixOffset b) + (50 - 2 * sixOffset b)) * n := by ring
               _ = (95 - sixOffset b) * n := by congr 1; omega
        have h2 : 70 * n + (25 - sixOffset b) * n = (95 - sixOffset b) * n := by
          calc _ = (70 + (25 - sixOffset b)) * n := by ring
               _ = (95 - sixOffset b) * n := by congr 1; omega
        omega
      · intro hle
        refine ⟨(25 - sixOffset b) * n + t.val, ?_, ?_⟩
        · have h1 : (50 - 2 * sixOffset b) * n = 2 * ((25 - sixOffset b) * n) := by
            calc _ = (2 * (25 - sixOffset b)) * n := by congr 1; omega
                 _ = _ := by ring
          omega
        · have h1 : (45 + sixOffset b) * n + (25 - sixOffset b) * n = 70 * n := by
            calc _ = ((45 + sixOffset b) + (25 - sixOffset b)) * n := by ring
                 _ = 70 * n := by congr 1; omega
          omega
    change ((List.range (sixBlockLen n b + 1)).map (fun j => sixBlockStart n b + j)).count (sixHalfPole n t) = _
    split_ifs with h
    · exact List.count_eq_one_of_mem
        ((List.nodup_map_iff (fun _ _ h => Nat.add_left_cancel h)).mpr List.nodup_range)
        (hmem.mpr h)
    · exact List.count_eq_zero_of_not_mem (fun hk' => h (hmem.mp hk'))
  rw [hord, Fin.sum_univ_def]
  simp only [List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, sixOffset, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  have h2 : ∀ (P : Prop) [Decidable P],
      (if P then (1 : ℕ) else 0) + (if P then 1 else 0) = if P then 2 else 0 := by
    intro P _; split_ifs <;> rfl
  have h5 : ∀ (P : Prop) [Decidable P],
      (if P then (1 : ℕ) else 0) + ((if P then 1 else 0) + ((if P then 1 else 0) +
        ((if P then 1 else 0) + (if P then 1 else 0)))) = if P then 5 else 0 := by
    intro P _; split_ifs <;> rfl
  rw [← h2 (t.val ≤ 16 * n), ← h2 (t.val ≤ 20 * n), ← h5 (t.val ≤ 25 * n)]
  ring

/-- Unconditional upper bound on active slots in any folded residue class `c` when `(7/2) * n < p`. -/
theorem active_slots_card_le_210 (n p : ℕ) (hp : 0 < p) (h35 : 7 * n ≤ 2 * p)
    (c : Fin (p / 2 + 1)) :
    ((Finset.univ.filter (fun u : Fin (sixSlotCount n) =>
        foldMod p hp (sixSlotCenter n u) = c)).filter
      (fun u => 1 ≤ sixSlotCost n p u)).card ≤ 210 := by
  have h1 : ((Finset.univ.filter (fun u : Fin (sixSlotCount n) =>
        foldMod p hp (sixSlotCenter n u) = c)).filter
      (fun u => 1 ≤ sixSlotCost n p u)).card ≤
      14 * ((Finset.univ : Finset (Fin (25 * n + 1))).filter
        (fun t => foldMod p hp (-(t.val : ℤ)) = c)).card := by
    let T := (Finset.univ : Finset (Fin (25 * n + 1))).filter
      (fun t => foldMod p hp (-(t.val : ℤ)) = c)
    have hsub : (Finset.univ.filter (fun u : Fin (sixSlotCount n) =>
          foldMod p hp (sixSlotCenter n u) = c)).filter (fun u => 1 ≤ sixSlotCost n p u) ⊆
        (T ×ˢ (Finset.univ : Finset (Fin 14))).image (sixSlotEquiv n) := by
      intro u hu
      have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
      rw [Finset.mem_image]
      refine ⟨(sixSlotEquiv n).symm u, Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩,
        (sixSlotEquiv n).apply_symm_apply u⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_image_of_injective _ (sixSlotEquiv n).injective, Finset.card_product]
    simp [mul_comm, T]
  have h2 : ((Finset.univ : Finset (Fin (25 * n + 1))).filter
      (fun t => foldMod p hp (-(t.val : ℤ)) = c)).card ≤ 15 := by
    have hsub : (Finset.univ : Finset (Fin (25 * n + 1))).filter
        (fun t => foldMod p hp (-(t.val : ℤ)) = c) ⊆
        ((Finset.univ : Finset (Fin (25 * n + 1))).filter (fun t => (p : ℤ) ∣ (t.val : ℤ) - (c.val : ℤ))) ∪
        ((Finset.univ : Finset (Fin (25 * n + 1))).filter (fun t => (p : ℤ) ∣ (t.val : ℤ) + (c.val : ℤ))) := by
      intro t ht
      have hfold := (Finset.mem_filter.mp ht).2
      have hcong := foldMod_congruence p hp (-(t.val : ℤ))
      rw [hfold] at hcong
      unfold foldSign at hcong
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      split_ifs at hcong
      · right
        refine ⟨Finset.mem_univ _, ?_⟩
        obtain ⟨k, hk⟩ := hcong
        exact ⟨-k, by linarith⟩
      · left
        refine ⟨Finset.mem_univ _, ?_⟩
        obtain ⟨k, hk⟩ := hcong
        exact ⟨k, by linarith⟩
    have hcount_le : ∀ b : ℤ,
        ((Finset.univ : Finset (Fin (25 * n + 1))).filter
          (fun t => (p : ℤ) ∣ b + (t.val : ℤ))).card ≤ 25 * n / p + 1 := by
      intro b
      have hbi : ((Finset.univ : Finset (Fin (25 * n + 1))).filter
          (fun t => (p : ℤ) ∣ b + (t.val : ℤ))).card =
          ((Finset.range (25 * n + 1)).filter (fun j : ℕ => (p : ℤ) ∣ b + (j : ℤ))).card := by
        apply Finset.card_bij (fun t _ => t.val)
        · intro t ht; rw [Finset.mem_filter] at ht ⊢; exact ⟨Finset.mem_range.mpr t.isLt, ht.2⟩
        · intro _ _ _ _ h; exact Fin.ext h
        · intro j hj; rw [Finset.mem_filter, Finset.mem_range] at hj
          exact ⟨⟨j, hj.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.2⟩, rfl⟩
      rw [hbi]
      have hdiv := range_multiples_card_eq_ediv p hp b (25 * n)
      have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
      have hstep : (b + ((25 * n : ℕ) : ℤ)) / (p : ℤ) - (b - 1) / (p : ℤ) ≤ ((25 * n / p : ℕ) : ℤ) + 1 := by
        have h1 := Int.ediv_mul_le (b + ((25 * n : ℕ) : ℤ)) hpZ.ne'
        have h2 := Int.lt_ediv_add_one_mul_self (b - 1) hpZ
        have h3 : (((25 * n : ℕ) : ℤ)) < (((25 * n / p : ℕ) : ℤ) + 1) * (p : ℤ) := by
          have : 25 * n < (25 * n / p + 1) * p := (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)
          exact_mod_cast this
        nlinarith
      omega
    have hdiv7 : 25 * n / p ≤ 7 := by
      have : 25 * n < 8 * p := by omega
      have := (Nat.div_lt_iff_lt_mul hp).mpr this
      omega
    have hA : ((Finset.univ : Finset (Fin (25 * n + 1))).filter
        (fun t => (p : ℤ) ∣ (t.val : ℤ) - (c.val : ℤ))).card ≤ 8 := by
      have h := hcount_le (-(c.val : ℤ))
      have heq : (Finset.univ : Finset (Fin (25 * n + 1))).filter (fun t => (p : ℤ) ∣ (t.val : ℤ) - (c.val : ℤ)) =
          (Finset.univ : Finset (Fin (25 * n + 1))).filter (fun t => (p : ℤ) ∣ -(c.val : ℤ) + (t.val : ℤ)) := by
        ext t; simp only [Finset.mem_filter, and_congr_right_iff]
        intro _; constructor <;> intro hd <;> (convert hd using 1; ring)
      rw [heq]; omega
    have hB : ((Finset.univ : Finset (Fin (25 * n + 1))).filter
        (fun t => (p : ℤ) ∣ (t.val : ℤ) + (c.val : ℤ))).card ≤ 8 := by
      have h := hcount_le (c.val : ℤ)
      have heq : (Finset.univ : Finset (Fin (25 * n + 1))).filter (fun t => (p : ℤ) ∣ (t.val : ℤ) + (c.val : ℤ)) =
          (Finset.univ : Finset (Fin (25 * n + 1))).filter (fun t => (p : ℤ) ∣ (c.val : ℤ) + (t.val : ℤ)) := by
        ext t; simp only [Finset.mem_filter, and_congr_right_iff]
        intro _; constructor <;> intro hd <;> (convert hd using 1; ring)
      rw [heq]; omega
    -- Actually `hA + hB ≤ 16`, tighten `hA` or `hB`? Wait: `t = 0` or `c ≤ p/2` gives ≤ 15!
    -- Even better: `50 * n / p + 1 ≤ 15` via `sixBlockLen`!
    -- Wait: check `c = 0`: `hA = hB ≤ 8`, intersection has `t = 0` so union ≤ 8!
    -- For `0 < c < p/2`: `#{t ∈ [-25n, 25n] : p ∣ t + c} ≤ 50n / p + 1 ≤ 15`!
    have hsym : ((Finset.univ : Finset (Fin (25 * n + 1))).filter
        (fun t => foldMod p hp (-(t.val : ℤ)) = c)).card ≤
        ((Finset.range (50 * n + 1)).filter (fun j : ℕ => (p : ℤ) ∣ (c.val : ℤ) - ((25 * n : ℕ) : ℤ) + (j : ℤ))).card := by
      by_cases hc0 : c.val = 0
      · -- For `c = 0`, `foldMod (-t) = 0 ↔ p ∣ t`, map `t ↦ 25*n + t`
        apply Finset.card_le_card_of_injOn (fun t : Fin (25 * n + 1) => 25 * n + t.val)
        · intro t ht
          have hfold := (Finset.mem_filter.mp ht).2
          have hcong := foldMod_congruence p hp (-(t.val : ℤ))
          rw [hfold, hc0] at hcong
          have hdvd : (p : ℤ) ∣ (t.val : ℤ) := by
            unfold foldSign at hcong; split_ifs at hcong
            · obtain ⟨k, hk⟩ := hcong; simp only [Nat.cast_zero, sub_zero, one_mul] at hk; exact ⟨-k, by linarith⟩
            · obtain ⟨k, hk⟩ := hcong; simp only [Nat.cast_zero, sub_zero] at hk; exact ⟨k, by linarith⟩
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
          dsimp only
          refine ⟨by have := t.isLt; omega, ?_⟩
          rw [hc0]; convert hdvd using 1; push_cast; ring
        · intro t₁ _ t₂ _ h; dsimp only at h; exact Fin.ext (by omega)
      · -- For `0 < c`: `p ∣ t + c` maps to `25n + t`, `p ∣ t - c` maps to `25n - t` (disjoint since `0 < c ≤ p/2` and `t = 0` impossible!)
        let f : Fin (25 * n + 1) → ℕ := fun t =>
          if (p : ℤ) ∣ (t.val : ℤ) + (c.val : ℤ) then 25 * n + t.val else 25 * n - t.val
        apply Finset.card_le_card_of_injOn f
        · intro t ht
          have hfold := (Finset.mem_filter.mp ht).2
          have hcong := foldMod_congruence p hp (-(t.val : ℤ))
          rw [hfold] at hcong
          have hor : (p : ℤ) ∣ (t.val : ℤ) + (c.val : ℤ) ∨ (p : ℤ) ∣ (t.val : ℤ) - (c.val : ℤ) := by
            unfold foldSign at hcong; split_ifs at hcong
            · left; obtain ⟨k, hk⟩ := hcong; exact ⟨-k, by linarith⟩
            · right; obtain ⟨k, hk⟩ := hcong; exact ⟨k, by linarith⟩
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
          dsimp [f]
          split_ifs with hp1
          · refine ⟨by have := t.isLt; omega, ?_⟩
            convert hp1 using 1; push_cast; ring
          · have hp2 : (p : ℤ) ∣ (t.val : ℤ) - (c.val : ℤ) := hor.resolve_left hp1
            refine ⟨by have := t.isLt; omega, ?_⟩
            have hle : t.val ≤ 25 * n := by have := t.isLt; omega
            have hcast : ((25 * n - t.val : ℕ) : ℤ) = ((25 * n : ℕ) : ℤ) - (t.val : ℤ) :=
              Int.ofNat_sub hle
            rw [hcast]
            obtain ⟨k, hk⟩ := hp2
            exact ⟨-k, by push_cast at hk ⊢; linarith only [hk]⟩
        · intro t₁ ht₁ t₂ ht₂ heq
          have ht0 : ∀ t ∈ (Finset.univ : Finset (Fin (25 * n + 1))).filter
              (fun t => foldMod p hp (-(t.val : ℤ)) = c), 0 < t.val := by
            intro t ht
            by_contra h0
            have htval : t.val = 0 := by omega
            have hfold := (Finset.mem_filter.mp ht).2
            rw [htval] at hfold
            have h0fold : foldMod p hp (0 : ℤ) = ⟨0, by omega⟩ := by
              unfold foldMod; simp
            have : c = ⟨0, by omega⟩ := by simpa [h0fold] using hfold.symm
            exact hc0 (congrArg Fin.val this)
          have h1pos := ht0 t₁ ht₁
          have h2pos := ht0 t₂ ht₂
          dsimp [f] at heq
          split_ifs at heq <;> exact Fin.ext (by omega)
    have h50 : ((Finset.range (50 * n + 1)).filter
        (fun j : ℕ => (p : ℤ) ∣ (c.val : ℤ) - ((25 * n : ℕ) : ℤ) + (j : ℤ))).card ≤ 50 * n / p + 1 := by
      have hdiv := range_multiples_card_eq_ediv p hp ((c.val : ℤ) - ((25 * n : ℕ) : ℤ)) (50 * n)
      have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
      have hstep : (((c.val : ℤ) - ((25 * n : ℕ) : ℤ)) + ((50 * n : ℕ) : ℤ)) / (p : ℤ) -
          (((c.val : ℤ) - ((25 * n : ℕ) : ℤ)) - 1) / (p : ℤ) ≤ ((50 * n / p : ℕ) : ℤ) + 1 := by
        have h1 := Int.ediv_mul_le (((c.val : ℤ) - ((25 * n : ℕ) : ℤ)) + ((50 * n : ℕ) : ℤ)) hpZ.ne'
        have h2 := Int.lt_ediv_add_one_mul_self (((c.val : ℤ) - ((25 * n : ℕ) : ℤ)) - 1) hpZ
        have h3 : ((50 * n : ℕ) : ℤ) < (((50 * n / p : ℕ) : ℤ) + 1) * (p : ℤ) := by
          have : 50 * n < (50 * n / p + 1) * p := (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)
          exact_mod_cast this
        nlinarith
      omega
    have h50le : 50 * n / p ≤ 14 := by
      have : 50 * n < 15 * p := by omega
      exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hp).mpr this)
    exact hsym.trans (h50.trans (by omega))
  omega

/-! ## Section 4: Extracting tile majorant and `highTile_discrete_bound` -/

/-- Check run helpers for `checkHighShard`. -/
theorem checkHighRun_spec {curN curD endN endD accU uT : ℕ} {ts : List HighTile}
    (h : checkHighRun curN curD endN endD accU uT ts = true) :
    (∀ t ∈ ts, checkHighTile t = true) ∧
    accU + (ts.map (·.uNum)).sum = uT := by
  induction ts generalizing curN curD accU with
  | nil =>
    simp only [checkHighRun, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨by simp, by simpa using h.2⟩
  | cons t rest ih =>
    simp only [checkHighRun, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hrest, hU⟩ := ih h.2
    refine ⟨?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact h.1.2
      · exact hrest q hq'
    · simp only [List.map_cons, List.sum_cons]; omega

theorem checkHighRun_cover {curN curD endN endD accU uT : ℕ} {ts : List HighTile}
    (h : checkHighRun curN curD endN endD accU uT ts = true)
    {x : ℝ} (hlo : (curN : ℝ) / (curD : ℝ) < x) (hhi : x < (endN : ℝ) / (endD : ℝ))
    (hne : ∀ t ∈ ts, x ≠ (t.rn : ℝ) / (t.rd : ℝ)) :
    ∃ t ∈ ts, (t.ln : ℝ) / (t.ld : ℝ) < x ∧ x < (t.rn : ℝ) / (t.rd : ℝ) := by
  induction ts generalizing curN curD accU with
  | nil =>
    simp only [checkHighRun, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨rfl, rfl⟩, _⟩
    linarith
  | cons t rest ih =>
    simp only [checkHighRun, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨hln, hld⟩, _⟩, hrest⟩
    have hneq := hne t (List.mem_cons_self ..)
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · exact ⟨t, List.mem_cons_self .., by rwa [hln, hld], hlt⟩
    · obtain ⟨q, hq, hqlo, hqhi⟩ := ih hrest hgt (fun r hr => hne r (List.mem_cons_of_mem _ hr))
      exact ⟨q, List.mem_cons_of_mem _ hq, hqlo, hqhi⟩

/-- Maximum denominator across a list of `HighTile`s (at least `1`). -/
def highMaxDen (ts : List HighTile) : ℕ :=
  ts.foldl (fun m t => max m (max t.ld t.rd)) 1

theorem highMaxDen_ge (ts : List HighTile) :
    ∀ t ∈ ts, t.ld ≤ highMaxDen ts ∧ t.rd ≤ highMaxDen ts := by
  have hfold : ∀ (init : ℕ) (xs : List HighTile),
      init ≤ xs.foldl (fun m t => max m (max t.ld t.rd)) init ∧
      ∀ t ∈ xs,
        t.ld ≤ xs.foldl (fun m t => max m (max t.ld t.rd)) init ∧
        t.rd ≤ xs.foldl (fun m t => max m (max t.ld t.rd)) init := by
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
  exact (hfold 1 ts).2

/-- Pure deterministic computation of the strip summaries `(w0, w1, info)` for a `HighTile`
(exact mirror of `checkHighTile.buildStrips`). -/
def highTileStrips (t : HighTile) : List (ℤ × ℤ × Sum (ℕ × ℕ) (List ℕ)) :=
  let q0 := highFloorVal 28 t.ln t.ld t.rn t.rd
  let q1 := highFloorVal 32 t.ln t.ld t.rn t.rd
  let q2 := highFloorVal 34 t.ln t.ld t.rn t.rd
  let q3 := highFloorVal 38 t.ln t.ld t.rn t.rd
  let q4 := highFloorVal 40 t.ln t.ld t.rn t.rd
  let q5 := highFloorVal 42 t.ln t.ld t.rn t.rd
  let q6 := highFloorVal 46 t.ln t.ld t.rn t.rd
  let q7 := highFloorVal 50 t.ln t.ld t.rn t.rd
  let q8 := highFloorVal 54 t.ln t.ld t.rn t.rd
  let q9 := highFloorVal 58 t.ln t.ld t.rn t.rd
  let q10 := highFloorVal 60 t.ln t.ld t.rn t.rd
  let q11 := highFloorVal 140 t.ln t.ld t.rn t.rd
  let z41 := highFloorVal 41 t.ln t.ld t.rn t.rd
  let z43 := highFloorVal 43 t.ln t.ld t.rn t.rd
  let getQ2 : ℕ → ℕ
    | 0 => q0 | 1 => q1 | 2 => q2 | 3 => q3 | 4 => q4 | 5 => q5
    | 6 => q6 | 7 => q7 | 8 => q8 | 9 => q9 | 10 => q10 | _ => q11
  let vPole : ℤ :=
    (q0 : ℤ) + 2 * (q1 : ℤ) + (q2 : ℤ) + (q3 : ℤ) +
    2 * (q4 : ℤ) + (q5 : ℤ) + (q6 : ℤ) + 5 * (q7 : ℤ)
  let vFact : ℤ := vPole - 2 * (3 * (q4 : ℤ) + (z41 : ℤ) + (z43 : ℤ))
  let pts : List (ℤ × ℤ) :=
    (0, 0) :: t.perm.map (fun idx => highLine2 (radiusValNat idx) (getQ2 idx)) ++ [(0, 1)]
  let p0 := indexOfNat t.perm 0
  let p1 := indexOfNat t.perm 1
  let p2 := indexOfNat t.perm 2
  let p3 := indexOfNat t.perm 3
  let p4 := indexOfNat t.perm 4
  let p5 := indexOfNat t.perm 5
  let p6 := indexOfNat t.perm 6
  let p7 := indexOfNat t.perm 7
  let p8 := indexOfNat t.perm 8
  let p9 := indexOfNat t.perm 9
  let p10 := indexOfNat t.perm 10
  let p11 := indexOfNat t.perm 11
  let k25 : ℕ := q7 / 2
  let q30 : ℕ := q10 / 2
  let s30 : ℕ := q10 % 2
  let deltaOf (qv pv g : ℕ) : ℕ :=
    let qr := qv / 2
    if qv % 2 == 0 then 2 * qr + (if g ≤ pv then 1 else 0)
    else 2 * qr + (if g ≤ pv then 1 else 2)
  let mkPlus (m g : ℕ) : ℕ :=
    let f (qv pv mult : ℕ) : ℕ :=
      let qr := qv / 2
      if m < qr || (m == qr && (qv % 2 == 1 || g ≤ pv)) then mult else 0
    f q0 p0 1 + f q1 p1 2 + f q2 p2 1 + f q3 p3 1 +
    f q4 p4 2 + f q5 p5 1 + f q6 p6 1 + f q7 p7 5
  let mkMinus (m g : ℕ) : ℕ :=
    let f (qv pv mult : ℕ) : ℕ :=
      let qr := qv / 2
      if m ≤ qr || (m == qr + 1 && qv % 2 == 1 && pv < g) then mult else 0
    f q0 p0 1 + f q1 p1 2 + f q2 p2 1 + f q3 p3 1 +
    f q4 p4 2 + f q5 p5 1 + f q6 p6 1 + f q7 p7 5
  checkHighTile.buildStrips q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 vFact
    p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 k25 q30 s30 deltaOf mkPlus mkMinus 0 pts

/-- Exact affine pair `(u0, u1)` for layer `j ∈ 1..18` of a `HighTile`. -/
def highTileLayerAff (t : HighTile) (j : ℕ) : ℤ × ℤ :=
  checkHighTile.sumCaps.accumJ t (j - 1) (highTileStrips t) 0 0

/-- Continuous nonnegative majorant `f_t(x)` for a `HighTile t` on `[t.ln/t.ld, t.rn/t.rd]`. -/
def highTileMajorant (t : HighTile) (x : ℝ) : ℝ :=
  let k30 := highFloorVal 30 t.ln t.ld t.rn t.rd
  ((30 * ((k30 - t.q : ℕ) : ℝ)) - ((sumRangeIcc t.q k30 : ℕ) : ℝ) * x) +
  ∑ j ∈ Finset.Icc 1 18,
    let ab := highTileLayerAff t j
    min (15 : ℝ) (((ab.1 : ℝ) + (ab.2 : ℝ) * x) / 2)

/-- Helper: `sumCaps` equals the sum of `capIntCeil` over `j ∈ Icc 1 18`. -/
private theorem sumCaps_eq_sum (t : HighTile) (strips : List (ℤ × ℤ × Sum (ℕ × ℕ) (List ℕ)))
    (m acc : ℕ) :
    checkHighTile.sumCaps t strips m acc =
      acc + ∑ j ∈ Finset.Icc 1 m,
        let ab := checkHighTile.sumCaps.accumJ t (j - 1) strips 0 0
        capIntCeil ab.1 ab.2 t.ln t.ld t.rn t.rd certDen := by
  induction m generalizing acc with
  | zero => simp [checkHighTile.sumCaps]
  | succ m' ih =>
    rw [checkHighTile.sumCaps, ih]
    have hIcc : Finset.Icc 1 (m' + 1) = insert (m' + 1) (Finset.Icc 1 m') := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    simp only [Nat.add_sub_cancel]; omega

/-- Helper: linear evaluation of `accumJ` on any strip list. -/
private theorem accumJ_eval (t : HighTile) (j' : ℕ)
    (strips : List (ℤ × ℤ × Sum (ℕ × ℕ) (List ℕ))) (u0 u1 : ℤ) (x : ℝ) :
    let res := checkHighTile.sumCaps.accumJ t j' strips u0 u1
    (res.1 : ℝ) + (res.2 : ℝ) * x =
      (u0 : ℝ) + (u1 : ℝ) * x +
      (strips.map (fun s =>
        let mult : ℕ := match s.2.2 with
          | Sum.inl (Np, B) => if j' + 1 ≤ B then min Np (t.q + 1 + (B - (j' + 1)) / 2) else 0
          | Sum.inr Nlist => jointCapFromN Nlist t.q (j' + 1)
        (mult : ℝ) * ((s.1 : ℝ) + (s.2.1 : ℝ) * x))).sum := by
  induction strips generalizing u0 u1 with
  | nil => simp [checkHighTile.sumCaps.accumJ]
  | cons s rest ih =>
    rcases s with ⟨w0, w1, info⟩
    rcases info with ⟨Np, B⟩ | Nlist
    · dsimp only
      let m : ℕ := if j' + 1 ≤ B then min Np (t.q + 1 + (B - (j' + 1)) / 2) else 0
      have hm_eq :
          (if j' + 1 ≤ B then min (Np : ℤ) ((t.q : ℤ) + 1 + ((B : ℤ) - ((j' : ℤ) + 1)) / 2) else 0) = (m : ℤ) := by
        dsimp only [m]
        split_ifs with hle
        · simp only [Nat.cast_min, Nat.cast_add, Nat.cast_one]
          congr 2
          have hsub : ((B - (j' + 1) : ℕ) : ℤ) = (B : ℤ) - ((j' : ℤ) + 1) := by
            rw [Int.ofNat_sub hle]; push_cast; ring
          rw [← hsub, Int.natCast_ediv]; rfl
        · rfl
      rw [checkHighTile.sumCaps.accumJ.eq_def]
      dsimp +zetaHave only
      simp only [hm_eq]
      by_cases hm0 : m = 0
      · simp only [hm0, Nat.cast_zero, beq_self_eq_true, ite_true, List.map_cons, List.sum_cons]
        have hm0' : (if j' + 1 ≤ B then min Np (t.q + 1 + (B - (j' + 1)) / 2) else 0) = 0 := hm0
        rw [hm0', Nat.cast_zero, zero_mul, zero_add]
        exact ih u0 u1
      · have hne : ((m : ℤ) == 0) = false := beq_false_of_ne (by exact_mod_cast hm0)
        simp only [hne, Bool.false_eq_true, ite_false]
        rw [ih (u0 + (m : ℤ) * w0) (u1 + (m : ℤ) * w1)]
        simp only [List.map_cons, List.sum_cons]
        change ((u0 + (m : ℤ) * w0 : ℤ) : ℝ) + ((u1 + (m : ℤ) * w1 : ℤ) : ℝ) * x + _ =
          (u0 : ℝ) + (u1 : ℝ) * x + ((m : ℝ) * ((w0 : ℝ) + (w1 : ℝ) * x) + _)
        push_cast; ring
    · dsimp only
      let m : ℕ := jointCapFromN Nlist t.q (j' + 1)
      rw [checkHighTile.sumCaps.accumJ.eq_def]
      dsimp +zetaHave only
      by_cases hm0 : m = 0
      · have hm0' : jointCapFromN Nlist t.q (j' + 1) = 0 := hm0
        simp only [hm0', Nat.cast_zero, beq_self_eq_true, ite_true, List.map_cons, List.sum_cons, zero_mul, zero_add]
        exact ih u0 u1
      · have hne : ((jointCapFromN Nlist t.q (j' + 1) : ℤ) == 0) = false :=
          beq_false_of_ne (by exact_mod_cast hm0)
        simp only [hne, Bool.false_eq_true, ite_false]
        rw [ih (u0 + (jointCapFromN Nlist t.q (j' + 1) : ℤ) * w0)
               (u1 + (jointCapFromN Nlist t.q (j' + 1) : ℤ) * w1)]
        simp only [List.map_cons, List.sum_cons]
        push_cast; ring

/-- Helper: relate `buildStrips` map sum to `Finset.range (rem.length - 1)` sum. -/
private theorem buildStrips_map_sum
    (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : ℕ) (vFact : ℤ)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 k25 q30 s30 : ℕ)
    (deltaOf : ℕ → ℕ → ℕ → ℕ) (mkPlus mkMinus : ℕ → ℕ → ℕ)
    (t : HighTile) (j' : ℕ) (x : ℝ)
    (rem : List (ℤ × ℤ)) (g : ℕ) :
    let strips := checkHighTile.buildStrips q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 vFact
      p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 k25 q30 s30 deltaOf mkPlus mkMinus g rem
    (strips.map (fun s =>
      let mult : ℕ := match s.2.2 with
        | Sum.inl (Np, B) => if j' + 1 ≤ B then min Np (t.q + 1 + (B - (j' + 1)) / 2) else 0
        | Sum.inr Nlist => jointCapFromN Nlist t.q (j' + 1)
      (mult : ℝ) * ((s.1 : ℝ) + (s.2.1 : ℝ) * x))).sum =
    ∑ k ∈ Finset.range (rem.length - 1),
      let u := rem[k]?.getD (0, 0)
      let v := rem[k + 1]?.getD (0, 0)
      let w0 : ℤ := v.1 - u.1
      let w1 : ℤ := v.2 - u.2
      let gg := g + k
      let Np : ℕ :=
        deltaOf q0 p0 gg + 2 * deltaOf q1 p1 gg + deltaOf q2 p2 gg + deltaOf q3 p3 gg +
        2 * deltaOf q4 p4 gg + deltaOf q5 p5 gg + deltaOf q6 p6 gg + 5 * deltaOf q7 p7 gg
      let Nz : ℕ :=
        5 * deltaOf q11 p11 gg - (deltaOf q8 p8 gg + deltaOf q9 p9 gg + 3 * deltaOf q10 p10 gg)
      let lt30 : Bool := gg ≤ p10
      let f30Plus : ℕ := q30 + (if s30 == 1 && !lt30 then 1 else 0)
      let f30Minus : ℕ := q30 - (if s30 == 0 && !lt30 then 1 else 0)
      let info : Sum (ℕ × ℕ) (List ℕ) :=
        if 15 ≤ Np && 1 ≤ f30Plus then
          let bInt : ℤ := 4 + (Np : ℤ) - (Nz : ℤ) - vFact
          let B : ℕ := if bInt ≤ 0 then 0 else bInt.toNat
          Sum.inl (Np, B)
        else
          let packed :=
            checkHighTile.buildStrips.addMinus vFact mkMinus gg Np Nz f30Plus f30Minus (k25 + 1)
              (checkHighTile.buildStrips.addPlus vFact mkPlus gg Np Nz f30Plus f30Minus (k25 + 1) 0)
          Sum.inr (packedToSuffixCounts packed)
      let mult : ℕ := match info with
        | Sum.inl (Np, B) => if j' + 1 ≤ B then min Np (t.q + 1 + (B - (j' + 1)) / 2) else 0
        | Sum.inr Nlist => jointCapFromN Nlist t.q (j' + 1)
      (mult : ℝ) * ((w0 : ℝ) + (w1 : ℝ) * x) := by
  induction rem generalizing g with
  | nil => rw [checkHighTile.buildStrips.eq_def]; simp
  | cons u tail ih =>
    cases tail with
    | nil => rw [checkHighTile.buildStrips.eq_def]; simp
    | cons v rest =>
      dsimp only
      rw [checkHighTile.buildStrips.eq_def]
      dsimp +zetaHave only
      have hlen : (u :: v :: rest).length - 1 = ((v :: rest).length - 1) + 1 := by simp
      rw [hlen, Finset.sum_range_succ']
      by_cases hw0 : v.1 - u.1 = 0 ∧ v.2 - u.2 = 0
      · have hb : (v.1 - u.1 == 0 && v.2 - u.2 == 0) = true := by simp [hw0]
        simp only [hb, ite_true]
        rw [ih (g + 1)]
        simp only [add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
          show ∀ k, g + 1 + k = g + (k + 1) from fun k => by omega]
        have hzero : ((v.1 - u.1 : ℤ) : ℝ) + ((v.2 - u.2 : ℤ) : ℝ) * x = 0 := by
          rw [hw0.1, hw0.2]; simp
        rw [hzero, mul_zero, add_zero]
      · have hb : (v.1 - u.1 == 0 && v.2 - u.2 == 0) = false := by
          simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; tauto
        simp only [hb, Bool.false_eq_true, ite_false]
        let Np0 : ℕ :=
          deltaOf q0 p0 g + 2 * deltaOf q1 p1 g + deltaOf q2 p2 g + deltaOf q3 p3 g +
          2 * deltaOf q4 p4 g + deltaOf q5 p5 g + deltaOf q6 p6 g + 5 * deltaOf q7 p7 g
        let f30P0 : ℕ := q30 + (if s30 == 1 && !(decide (g ≤ p10)) then 1 else 0)
        by_cases hfast : (decide (15 ≤ Np0) && decide (1 ≤ f30P0)) = true
        · dsimp only [Np0, f30P0] at hfast
          simp only [add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
            hfast, ite_true, List.map_cons, List.sum_cons]
          rw [ih (g + 1), add_comm]
          congr 1
          apply Finset.sum_congr rfl; intro k _
          simp only [List.getElem?_cons_succ, show g + 1 + k = g + (k + 1) by omega]
        · have hfastF : (decide (15 ≤ Np0) && decide (1 ≤ f30P0)) = false := Bool.eq_false_iff.mpr hfast
          dsimp only [Np0, f30P0] at hfastF
          simp only [add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
            hfastF, Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons]
          rw [ih (g + 1), add_comm]
          congr 1
          apply Finset.sum_congr rfl; intro k _
          simp only [List.getElem?_cons_succ, show g + 1 + k = g + (k + 1) by omega]

/-- Clean extraction of all verified invariants from `checkHighTile t = true`. -/
theorem checkHighTile_extract (t : HighTile) (hchk : checkHighTile t = true) :
    let k30 := highFloorVal 30 t.ln t.ld t.rn t.rd
    let q0 := highFloorVal 28 t.ln t.ld t.rn t.rd
    let q1 := highFloorVal 32 t.ln t.ld t.rn t.rd
    let q2 := highFloorVal 34 t.ln t.ld t.rn t.rd
    let q3 := highFloorVal 38 t.ln t.ld t.rn t.rd
    let q4 := highFloorVal 40 t.ln t.ld t.rn t.rd
    let q5 := highFloorVal 42 t.ln t.ld t.rn t.rd
    let q6 := highFloorVal 46 t.ln t.ld t.rn t.rd
    let q7 := highFloorVal 50 t.ln t.ld t.rn t.rd
    let q8 := highFloorVal 54 t.ln t.ld t.rn t.rd
    let q9 := highFloorVal 58 t.ln t.ld t.rn t.rd
    let q10 := highFloorVal 60 t.ln t.ld t.rn t.rd
    let q11 := highFloorVal 140 t.ln t.ld t.rn t.rd
    let z41 := highFloorVal 41 t.ln t.ld t.rn t.rd
    let z43 := highFloorVal 43 t.ln t.ld t.rn t.rd
    let getQ2 : ℕ → ℕ
      | 0 => q0 | 1 => q1 | 2 => q2 | 3 => q3 | 4 => q4 | 5 => q5
      | 6 => q6 | 7 => q7 | 8 => q8 | 9 => q9 | 10 => q10 | _ => q11
    let pts : List (ℤ × ℤ) :=
      (0, 0) :: t.perm.map (fun idx => highLine2 (radiusValNat idx) (getQ2 idx)) ++ [(0, 1)]
    let p0 : ℤ := 30 * ((k30 - t.q : ℕ) : ℤ)
    let p1 : ℤ := -((sumRangeIcc t.q k30 : ℕ) : ℤ)
    (0 < t.ld ∧ 0 < t.rd ∧ t.ln * t.rd < t.rn * t.ld) ∧
    (7 * t.ld ≤ 2 * t.ln ∧ t.rn ≤ 55 * t.rd) ∧
    isPerm12 t.perm = true ∧
    (t.q ≤ k30 ∧
     highFloorOk 30 k30 t.ln t.ld t.rn t.rd = true ∧
     highFloorOk 28 q0 t.ln t.ld t.rn t.rd = true ∧
     highFloorOk 32 q1 t.ln t.ld t.rn t.rd = true ∧
     highFloorOk 34 q2 t.ln t.ld t.rn t.rd = true ∧
     highFloorOk 38 q3 t.ln t.ld t.rn t.rd = true ∧
     highFloorOk 40 q4 t.ln t.ld t.rn t.rd = true ∧
     highFloorOk 42 q5 t.ln t.ld t.rn t.rd = true ∧
     highFloorOk 46 q6 t.ln t.ld t.rn t.rd = true ∧
     highFloorOk 50 q7 t.ln t.ld t.rn t.rd = true ∧
     highFloorOk 54 q8 t.ln t.ld t.rn t.rd = true ∧
     highFloorOk 58 q9 t.ln t.ld t.rn t.rd = true ∧
     highFloorOk 60 q10 t.ln t.ld t.rn t.rd = true ∧
     highFloorOk 140 q11 t.ln t.ld t.rn t.rd = true ∧
     highFloorOk 41 z41 t.ln t.ld t.rn t.rd = true ∧
     highFloorOk 43 z43 t.ln t.ld t.rn t.rd = true) ∧
    checkSortedLines t.ln t.ld t.rn t.rd pts = true ∧
    affIntCeil p0 p1 t.ln t.ld t.rn t.rd certDen +
      checkHighTile.sumCaps t (highTileStrips t) 18 0 ≤ t.uNum := by
  unfold checkHighTile at hchk
  split_ifs at hchk with h1 h2 h3
  dsimp +zetaHave only at hchk
  split_ifs at hchk with h4 h5
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.not_eq_false,
    Bool.and_eq_true, decide_eq_true_eq, decide_eq_false_iff_not, not_or, not_lt, not_le] at h1 h2 h3 h4 h5
  simp only [decide_eq_true_eq] at hchk
  refine ⟨⟨Nat.pos_of_ne_zero h1.1.1, Nat.pos_of_ne_zero h1.1.2, h1.2⟩,
    ⟨h2.1, h2.2⟩, h3, ?_, h5, hchk⟩
  exact ⟨h4.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1, h4.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
        h4.1.1.1.1.1.1.1.1.1.1.1.1.1.2, h4.1.1.1.1.1.1.1.1.1.1.1.1.2,
        h4.1.1.1.1.1.1.1.1.1.1.1.2, h4.1.1.1.1.1.1.1.1.1.1.2,
        h4.1.1.1.1.1.1.1.1.1.2, h4.1.1.1.1.1.1.1.1.2, h4.1.1.1.1.1.1.1.2,
        h4.1.1.1.1.1.1.2, h4.1.1.1.1.1.2, h4.1.1.1.1.2, h4.1.1.1.2,
        h4.1.1.2, h4.1.2, h4.2⟩

/-- Nonnegativity and integral upper bound of `highTileMajorant t` on `[t.ln/t.ld, t.rn/t.rd]`. -/
theorem highTileMajorant_nonneg_and_integral (t : HighTile) (hchk : checkHighTile t = true) :
    0 < t.ld ∧ 0 < t.rd ∧ t.ln * t.rd < t.rn * t.ld ∧
    7 * t.ld ≤ 2 * t.ln ∧ t.rn ≤ 55 * t.rd ∧
    (∀ x ∈ Set.Icc ((t.ln : ℝ) / (t.ld : ℝ)) ((t.rn : ℝ) / (t.rd : ℝ)), 0 ≤ highTileMajorant t x) ∧
    (∫ x in ((t.ln : ℝ) / (t.ld : ℝ))..((t.rn : ℝ) / (t.rd : ℝ)), highTileMajorant t x) ≤
      (t.uNum : ℝ) / (certDen : ℝ) := by
  have hext := checkHighTile_extract t hchk
  dsimp only at hext
  obtain ⟨⟨hld, hrd, hlt⟩, hrange, hperm, hfloors, hsort, hchk'⟩ := hext
  have hldR : (0 : ℝ) < (t.ld : ℝ) := by exact_mod_cast hld
  have hrdR : (0 : ℝ) < (t.rd : ℝ) := by exact_mod_cast hrd
  have hDR : (0 : ℝ) < (certDen : ℝ) := by unfold certDen; norm_num
  rcases hfloors with ⟨hqk, hk30, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  let k30 := highFloorVal 30 t.ln t.ld t.rn t.rd
  have hk30_rn : k30 * t.rn ≤ 30 * t.rd := by
    unfold highFloorOk at hk30; simp only [Bool.and_eq_true, decide_eq_true_eq] at hk30; exact hk30.1
  have hpen_nn : ∀ x ∈ Set.Icc ((t.ln : ℝ) / (t.ld : ℝ)) ((t.rn : ℝ) / (t.rd : ℝ)),
      0 ≤ (30 * ((k30 - t.q : ℕ) : ℝ)) - ((sumRangeIcc t.q k30 : ℕ) : ℝ) * x := by
    intro x hx
    have hx_le : x ≤ (t.rn : ℝ) / (t.rd : ℝ) := hx.2
    have hkx : (k30 : ℝ) * x ≤ 30 := by
      have h1 : (k30 : ℝ) * ((t.rn : ℝ) / (t.rd : ℝ)) ≤ 30 := by
        rw [← mul_div_assoc, div_le_iff₀ hrdR]; exact_mod_cast hk30_rn
      exact (mul_le_mul_of_nonneg_left hx_le (Nat.cast_nonneg k30)).trans h1
    have hxnn : 0 ≤ x := (div_nonneg (Nat.cast_nonneg _) hldR.le).trans hx.1
    rw [sumRangeIcc_eq t.q k30 hqk, Nat.cast_sum, Finset.sum_mul]
    have hcard : (Finset.Icc (t.q + 1) k30).card = k30 - t.q := by rw [Nat.card_Icc]; omega
    have h30 : (30 * ((k30 - t.q : ℕ) : ℝ)) = ∑ _k ∈ Finset.Icc (t.q + 1) k30, (30 : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
    rw [h30, ← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg; intro k hk
    have hkle : (k : ℝ) ≤ (k30 : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    nlinarith
  have hlayer_nn : ∀ j ∈ Finset.Icc 1 18,
      ∀ x ∈ Set.Icc ((t.ln : ℝ) / (t.ld : ℝ)) ((t.rn : ℝ) / (t.rd : ℝ)),
        0 ≤ min (15 : ℝ) ((((highTileLayerAff t j).1 : ℝ) + ((highTileLayerAff t j).2 : ℝ) * x) / 2) := by
    intro j hj x hx
    apply le_min (by norm_num)
    apply div_nonneg _ (by norm_num)
    unfold highTileLayerAff highTileStrips
    rw [accumJ_eval]
    simp only [Int.cast_zero, zero_mul, zero_add]
    rw [buildStrips_map_sum]
    apply Finset.sum_nonneg; intro k hk
    let getQ2 : ℕ → ℕ
      | 0 => highFloorVal 28 t.ln t.ld t.rn t.rd
      | 1 => highFloorVal 32 t.ln t.ld t.rn t.rd
      | 2 => highFloorVal 34 t.ln t.ld t.rn t.rd
      | 3 => highFloorVal 38 t.ln t.ld t.rn t.rd
      | 4 => highFloorVal 40 t.ln t.ld t.rn t.rd
      | 5 => highFloorVal 42 t.ln t.ld t.rn t.rd
      | 6 => highFloorVal 46 t.ln t.ld t.rn t.rd
      | 7 => highFloorVal 50 t.ln t.ld t.rn t.rd
      | 8 => highFloorVal 54 t.ln t.ld t.rn t.rd
      | 9 => highFloorVal 58 t.ln t.ld t.rn t.rd
      | 10 => highFloorVal 60 t.ln t.ld t.rn t.rd
      | _ => highFloorVal 140 t.ln t.ld t.rn t.rd
    let pts := (0, 0) :: t.perm.map (fun idx => highLine2 (radiusValNat idx) (getQ2 idx)) ++ [(0, 1)]
    have hklen : k + 1 < pts.length := by
      have hplen := (isPerm12_spec hperm).1
      have hlt_k := Finset.mem_range.mp hk
      simp [pts, hplen] at hlt_k ⊢; omega
    have hmono := checkSortedLines_mono hld hrd hx.1 hx.2 hsort (Nat.le_succ k) hklen
    have hu : pts[k]?.getD (0, 0) = pts[k]'(Nat.lt_of_succ_lt hklen) := by
      rw [List.getElem?_eq_getElem (Nat.lt_of_succ_lt hklen)]; rfl
    have hv : pts[k + 1]?.getD (0, 0) = pts[k + 1]'hklen := by
      rw [List.getElem?_eq_getElem hklen]; rfl
    dsimp only
    change 0 ≤ (_ : ℝ) * (((pts[k + 1]?.getD (0, 0)).1 - (pts[k]?.getD (0, 0)).1 : ℤ) +
      (((pts[k + 1]?.getD (0, 0)).2 - (pts[k]?.getD (0, 0)).2 : ℤ) : ℝ) * x)
    rw [hu, hv]; push_cast
    have hdiff : 0 ≤ (((pts[k + 1]'hklen).1 : ℝ) + ((pts[k + 1]'hklen).2 : ℝ) * x) -
        (((pts[k]'(Nat.lt_of_succ_lt hklen)).1 : ℝ) + ((pts[k]'(Nat.lt_of_succ_lt hklen)).2 : ℝ) * x) :=
      sub_nonneg.mpr hmono
    have hrew : ((((pts[k + 1]'hklen).1 : ℝ) - ((pts[k]'(Nat.lt_of_succ_lt hklen)).1 : ℝ)) +
        (((pts[k + 1]'hklen).2 : ℝ) - ((pts[k]'(Nat.lt_of_succ_lt hklen)).2 : ℝ)) * x) =
        (((pts[k + 1]'hklen).1 : ℝ) + ((pts[k + 1]'hklen).2 : ℝ) * x) -
        (((pts[k]'(Nat.lt_of_succ_lt hklen)).1 : ℝ) + ((pts[k]'(Nat.lt_of_succ_lt hklen)).2 : ℝ) * x) := by ring
    rw [hrew]
    exact mul_nonneg (Nat.cast_nonneg _) hdiff
  refine ⟨hld, hrd, hlt, hrange.1, hrange.2, ?_, ?_⟩
  · intro x hx
    unfold highTileMajorant
    exact add_nonneg (hpen_nn x hx) (Finset.sum_nonneg (fun j hj => hlayer_nn j hj x hx))
  · -- Integral bound: `perCeil + capCeil ≤ t.uNum`
    let p0 : ℤ := 30 * ((k30 - t.q : ℕ) : ℤ)
    let p1 : ℤ := -((sumRangeIcc t.q k30 : ℕ) : ℤ)
    have hnnL : 0 ≤ p0 * (t.ld : ℤ) + p1 * (t.ln : ℤ) := by
      have h := hpen_nn ((t.ln : ℝ) / (t.ld : ℝ)) ⟨le_rfl, (div_lt_div_iff₀ hldR hrdR).mpr (by exact_mod_cast hlt) |>.le⟩
      have hmul : 0 ≤ (p0 : ℝ) * (t.ld : ℝ) + (p1 : ℝ) * (t.ln : ℝ) := by
        have := mul_nonneg h hldR.le
        dsimp [p0, p1]; push_cast; field_simp [hldR.ne'] at this ⊢; linarith
      exact_mod_cast hmul
    have hnnR : 0 ≤ p0 * (t.rd : ℤ) + p1 * (t.rn : ℤ) := by
      have h := hpen_nn ((t.rn : ℝ) / (t.rd : ℝ)) ⟨(div_lt_div_iff₀ hldR hrdR).mpr (by exact_mod_cast hlt) |>.le, le_rfl⟩
      have hmul : 0 ≤ (p0 : ℝ) * (t.rd : ℝ) + (p1 : ℝ) * (t.rn : ℝ) := by
        have := mul_nonneg h hrdR.le
        dsimp [p0, p1]; push_cast; field_simp [hrdR.ne'] at this ⊢; linarith
      exact_mod_cast hmul
    unfold highTileMajorant
    rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by
        apply continuous_finsetSum; intro j _; fun_prop) _ _)]
    rw [intervalIntegral.integral_finsetSum (fun j _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
    have hper : (∫ x in ((t.ln : ℝ) / (t.ld : ℝ))..((t.rn : ℝ) / (t.rd : ℝ)),
        (30 * ((k30 - t.q : ℕ) : ℝ)) - ((sumRangeIcc t.q k30 : ℕ) : ℝ) * x) ≤
        (affIntCeil p0 p1 t.ln t.ld t.rn t.rd certDen : ℝ) / (certDen : ℝ) := by
      have hrew : (fun x : ℝ => (30 * ((k30 - t.q : ℕ) : ℝ)) - ((sumRangeIcc t.q k30 : ℕ) : ℝ) * x) =
          (fun x : ℝ => (p0 : ℝ) + (p1 : ℝ) * x) := by
        ext x; dsimp [p0, p1]; push_cast; ring
      rw [hrew]
      exact affIntCeil_sound hld hrd hlt (by unfold certDen; norm_num) hnnL hnnR
    have hcaps : (∑ j ∈ Finset.Icc 1 18,
        ∫ x in ((t.ln : ℝ) / (t.ld : ℝ))..((t.rn : ℝ) / (t.rd : ℝ)),
          min (15 : ℝ) ((((highTileLayerAff t j).1 : ℝ) + ((highTileLayerAff t j).2 : ℝ) * x) / 2)) ≤
        (checkHighTile.sumCaps t (highTileStrips t) 18 0 : ℝ) / (certDen : ℝ) := by
      rw [sumCaps_eq_sum, zero_add, Nat.cast_sum, Finset.sum_div]
      apply Finset.sum_le_sum; intro j _
      exact capIntCeil_sound _ _ hld hrd hlt (by unfold certDen; norm_num)
    have htot : ((affIntCeil p0 p1 t.ln t.ld t.rn t.rd certDen : ℝ) +
        (checkHighTile.sumCaps t (highTileStrips t) 18 0 : ℝ)) / (certDen : ℝ) ≤
        (t.uNum : ℝ) / (certDen : ℝ) := by
      apply div_le_div_of_nonneg_right _ hDR.le
      have : affIntCeil p0 p1 t.ln t.ld t.rn t.rd certDen +
          checkHighTile.sumCaps t (highTileStrips t) 18 0 ≤ t.uNum := hchk'
      exact_mod_cast this
    rw [add_div] at htot
    linarith

/-- Helper: total pole-order multiplicity of half-poles in class `c` (`0 < c`) is bounded by `sixPoleClassCount`. -/
private theorem sum_halfPoleOrder_le_poleClassCount (n p : ℕ) (hp : 0 < p)
    (c : Fin (p / 2 + 1)) (hc0 : 0 < c.val) :
    (∑ x ∈ (Finset.univ : Finset (Fin (25 * n + 1))).filter
        (fun x => foldMod p hp (-(x.val : ℤ)) = c),
      sixPoleOrder n (sixHalfPole n x)) ≤ sixPoleClassCount n p (c.val : ℤ) := by
  let Tc := (Finset.univ : Finset (Fin (25 * n + 1))).filter
    (fun x => foldMod p hp (-(x.val : ℤ)) = c)
  have hord_sum : ∀ x : Fin (25 * n + 1), sixPoleOrder n (sixHalfPole n x) =
      ∑ b : Fin 14, if x.val ≤ (25 - sixOffset b) * n then 1 else 0 := by
    intro x
    rw [sixPoleOrder_halfPole_eq, Fin.sum_univ_def]
    simp only [List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, sixOffset, Matrix.cons_val_zero, Matrix.cons_val_succ]
    norm_num
    have h2 : ∀ (P : Prop) [Decidable P],
        (if P then (1 : ℕ) else 0) + (if P then 1 else 0) = if P then 2 else 0 := by
      intro P _; split_ifs <;> rfl
    have h5 : ∀ (P : Prop) [Decidable P],
        (if P then (1 : ℕ) else 0) + ((if P then 1 else 0) + ((if P then 1 else 0) +
          ((if P then 1 else 0) + (if P then 1 else 0)))) = if P then 5 else 0 := by
      intro P _; split_ifs <;> rfl
    rw [← h2 (x.val ≤ 16 * n), ← h2 (x.val ≤ 20 * n), ← h5 (x.val ≤ 25 * n)]
    ring
  change (∑ x ∈ Tc, sixPoleOrder n (sixHalfPole n x)) ≤ sixPoleClassCount n p (c.val : ℤ)
  simp_rw [hord_sum]
  rw [Finset.sum_comm]
  unfold sixPoleClassCount
  apply Finset.sum_le_sum; intro b _
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  have hob : sixOffset b ≤ 11 := by fin_cases b <;> decide
  let R := (25 - sixOffset b) * n
  have hL : sixBlockLen n b = 2 * R := by
    unfold sixBlockLen; dsimp [R]
    calc (50 - 2 * sixOffset b) * n = (2 * (25 - sixOffset b)) * n := by congr 1; omega
      _ = _ := by ring
  have hst : (sixBlockStart n b : ℤ) - (sixCenter n : ℤ) = -(R : ℤ) := by
    unfold sixBlockStart sixCenter; dsimp [R]
    have hsum : (45 + sixOffset b) * n + (25 - sixOffset b) * n = 70 * n := by
      calc _ = ((45 + sixOffset b) + (25 - sixOffset b)) * n := by ring
           _ = 70 * n := by congr 1; omega
    have hsumZ : (((45 + sixOffset b) * n : ℕ) : ℤ) + (((25 - sixOffset b) * n : ℕ) : ℤ) =
        ((70 * n : ℕ) : ℤ) := by exact_mod_cast hsum
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hsumZ ⊢
    linarith only [hsumZ]
  let f : Fin (25 * n + 1) → ℕ := fun x =>
    if (p : ℤ) ∣ (x.val : ℤ) + (c.val : ℤ) then R + x.val else R - x.val
  apply Finset.card_le_card_of_injOn f
  · intro x hx
    have hxT := (Finset.mem_filter.mp hx).1
    have hxR : x.val ≤ R := (Finset.mem_filter.mp hx).2
    have hfold := (Finset.mem_filter.mp hxT).2
    have hcong := foldMod_congruence p hp (-(x.val : ℤ))
    rw [hfold] at hcong
    have hor : (p : ℤ) ∣ (x.val : ℤ) + (c.val : ℤ) ∨ (p : ℤ) ∣ (x.val : ℤ) - (c.val : ℤ) := by
      unfold foldSign at hcong; split_ifs at hcong
      · left; obtain ⟨k, hk⟩ := hcong; exact ⟨-k, by linarith⟩
      · right; obtain ⟨k, hk⟩ := hcong; exact ⟨k, by linarith⟩
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    dsimp [f]; split_ifs with hp1
    · refine ⟨by omega, ?_⟩
      have heq : (sixBlockStart n b : ℤ) + ((R + x.val : ℕ) : ℤ) - (sixCenter n : ℤ) + (c.val : ℤ) =
          (x.val : ℤ) + (c.val : ℤ) := by push_cast; linarith
      rw [heq]; exact hp1
    · have hp2 : (p : ℤ) ∣ (x.val : ℤ) - (c.val : ℤ) := hor.resolve_left hp1
      refine ⟨by omega, ?_⟩
      have hcast : ((R - x.val : ℕ) : ℤ) = (R : ℤ) - (x.val : ℤ) := Int.ofNat_sub hxR
      have heq : (sixBlockStart n b : ℤ) + ((R - x.val : ℕ) : ℤ) - (sixCenter n : ℤ) + (c.val : ℤ) =
          -((x.val : ℤ) - (c.val : ℤ)) := by rw [hcast]; linarith
      rw [heq]; exact dvd_neg.mpr hp2
  · intro x₁ hx₁ x₂ hx₂ heq
    have hxpos : ∀ x ∈ Tc.filter (fun x => x.val ≤ R), 0 < x.val := by
      intro x hx
      by_contra h0
      have hxv : x.val = 0 := by omega
      have hfold := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      rw [hxv] at hfold
      have h0f : foldMod p hp (0 : ℤ) = ⟨0, by omega⟩ := by unfold foldMod; simp
      have : c = ⟨0, by omega⟩ := by simpa [h0f] using hfold.symm
      have : c.val = 0 := congrArg Fin.val this
      omega
    have h1p := hxpos x₁ hx₁; have h2p := hxpos x₂ hx₂
    have h1R : x₁.val ≤ R := (Finset.mem_filter.mp hx₁).2
    have h2R : x₂.val ≤ R := (Finset.mem_filter.mp hx₂).2
    dsimp [f] at heq; split_ifs at heq <;> exact Fin.ext (by omega)

/-- Helper: when `7 * n ≤ 2 * p`, `sixPoleClassCount n p c ≤ 210`. -/
private theorem poleClassCount_le_210 (n p : ℕ) (hp : 0 < p) (h35 : 7 * n ≤ 2 * p) (c : ℤ) :
    sixPoleClassCount n p c ≤ 210 := by
  unfold sixPoleClassCount
  have h14 : (∑ _b : Fin 14, (15 : ℕ)) = 210 := by simp
  rw [← h14]
  apply Finset.sum_le_sum; intro b _
  have hob : sixOffset b ≤ 11 := by fin_cases b <;> decide
  have hlen50 : sixBlockLen n b ≤ 50 * n := by
    unfold sixBlockLen
    exact Nat.mul_le_mul_right n (by omega)
  have hdiv := range_multiples_card_eq_ediv p hp
    ((sixBlockStart n b : ℤ) - (sixCenter n : ℤ) + c) (sixBlockLen n b)
  have hrew : (Finset.range (sixBlockLen n b + 1)).filter
      (fun j : ℕ => (p : ℤ) ∣ ((sixBlockStart n b : ℤ) + (j : ℤ) - (sixCenter n : ℤ)) + c) =
      (Finset.range (sixBlockLen n b + 1)).filter
        (fun j : ℕ => (p : ℤ) ∣ ((sixBlockStart n b : ℤ) - (sixCenter n : ℤ) + c) + (j : ℤ)) := by
    ext u; simp only [Finset.mem_filter, and_congr_right_iff]
    intro _; constructor <;> intro hd <;> (convert hd using 1; ring)
  rw [hrew]
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have hstep : (((sixBlockStart n b : ℤ) - (sixCenter n : ℤ) + c) + ((sixBlockLen n b : ℕ) : ℤ)) / (p : ℤ) -
      (((sixBlockStart n b : ℤ) - (sixCenter n : ℤ) + c) - 1) / (p : ℤ) ≤ 15 := by
    have ha1 := Int.ediv_mul_le (((sixBlockStart n b : ℤ) - (sixCenter n : ℤ) + c) + ((sixBlockLen n b : ℕ) : ℤ)) hpZ.ne'
    have ha2 := Int.lt_ediv_add_one_mul_self (((sixBlockStart n b : ℤ) - (sixCenter n : ℤ) + c) - 1) hpZ
    have ha3 : ((sixBlockLen n b : ℕ) : ℤ) < 15 * (p : ℤ) := by
      have : sixBlockLen n b < 15 * p := by omega
      exact_mod_cast this
    nlinarith only [ha1, ha2, ha3, hpZ]
  omega

private lemma one_le_of_le_sub_two {j w r q : ℕ} (hj1 : 1 ≤ j)
    (h : (j : ℤ) ≤ (w : ℤ) - 2 * ((r - q : ℕ) : ℤ)) : 1 ≤ w := by
  omega

private lemma lt_add_one_add_div_two_of_le {j w B r q : ℕ} (hjB : j ≤ B) (hwB : w ≤ B)
    (h : (j : ℤ) ≤ (w : ℤ) - 2 * ((r - q : ℕ) : ℤ)) : r < q + 1 + (B - j) / 2 := by
  omega

private lemma not_le_sub_two_of_lt {j w B r q : ℕ} (hjB : ¬ j ≤ B) (hwB : w ≤ B)
    (h : (j : ℤ) ≤ (w : ℤ) - 2 * ((r - q : ℕ) : ℤ)) : False := by
  omega

private lemma radiusValNat_le_25 (k : ℕ) (hk : k < 8) : radiusValNat k ≤ 25 := by
  interval_cases k <;> decide

private lemma nat_sub_mul_div (a m p : ℕ) (hp : 0 < p) (hle : m * p ≤ a) :
    (a - m * p) / p = a / p - m := by
  have hq := Nat.div_add_mod (a - m * p) p
  have hm := Nat.mod_lt (a - m * p) hp
  have hsub : a - m * p + m * p = a := Nat.sub_add_cancel hle
  have h3 : a = (a - m * p) % p + ((a - m * p) / p + m) * p := by
    calc a = (a - m * p) + m * p := hsub.symm
      _ = (p * ((a - m * p) / p) + (a - m * p) % p) + m * p := by rw [hq]
      _ = (a - m * p) % p + ((a - m * p) / p + m) * p := by ring
  have h4 : a / p = (a - m * p) / p + m := by
    conv_lhs => rw [h3]
    rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hm, zero_add]
  rw [h4, Nat.add_sub_cancel]

set_option maxHeartbeats 1200000 in
/-- **Discrete-to-continuous high-tile bound**: for every prime `p` (`p^2 > 140n + 2`) in the
strict interior `(t.ln/t.ld, t.rn/t.rd)` of a checked `HighTile t`,
`sixPrimeExpReal n p ≤ n * highTileMajorant t (p / n) + 102060`. -/
theorem highTile_discrete_bound (n p : ℕ) [Fact p.Prime] (hn : 0 < n)
    (hsq : 140 * n + 2 < p ^ 2) (t : HighTile) (hchk : checkHighTile t = true)
    (hlo : (t.ln : ℝ) / (t.ld : ℝ) < (p : ℝ) / (n : ℝ))
    (hhi : (p : ℝ) / (n : ℝ) < (t.rn : ℝ) / (t.rd : ℝ)) :
    sixPrimeExpReal n p ≤ (n : ℝ) * highTileMajorant t ((p : ℝ) / (n : ℝ)) + 102060 := by
  have hp_pr : p.Prime := Fact.out
  have hp : 0 < p := hp_pr.pos
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hext := checkHighTile_extract t hchk
  dsimp only at hext
  obtain ⟨⟨hld, hrd, _⟩, hrange, hperm, hfloors, hsort, _⟩ := hext
  have h35 : 7 * n ≤ 2 * p := by
    have hldR : (0 : ℝ) < (t.ld : ℝ) := by exact_mod_cast hld
    have h1 : (7 : ℝ) / 2 ≤ (t.ln : ℝ) / (t.ld : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hldR]
      have : 7 * t.ld ≤ t.ln * 2 := by omega
      exact_mod_cast this
    have h2 : (7 : ℝ) * (n : ℝ) ≤ 2 * (p : ℝ) := by
      have := h1.trans hlo.le
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hnR] at this; linarith
    exact_mod_cast h2
  have h55 : p ≤ 55 * n := by
    have hrdR : (0 : ℝ) < (t.rd : ℝ) := by exact_mod_cast hrd
    have h1 : (t.rn : ℝ) / (t.rd : ℝ) ≤ 55 := by
      rw [div_le_iff₀ hrdR]; exact_mod_cast hrange.2
    have h2 : (p : ℝ) ≤ 55 * (n : ℝ) := by
      have := hhi.le.trans h1
      rwa [div_le_iff₀ hnR] at this
    exact_mod_cast h2
  let k30 := highFloorVal 30 t.ln t.ld t.rn t.rd
  let q0 := highFloorVal 28 t.ln t.ld t.rn t.rd
  let q1 := highFloorVal 32 t.ln t.ld t.rn t.rd
  let q2 := highFloorVal 34 t.ln t.ld t.rn t.rd
  let q3 := highFloorVal 38 t.ln t.ld t.rn t.rd
  let q4 := highFloorVal 40 t.ln t.ld t.rn t.rd
  let q5 := highFloorVal 42 t.ln t.ld t.rn t.rd
  let q6 := highFloorVal 46 t.ln t.ld t.rn t.rd
  let q7 := highFloorVal 50 t.ln t.ld t.rn t.rd
  let q8 := highFloorVal 54 t.ln t.ld t.rn t.rd
  let q9 := highFloorVal 58 t.ln t.ld t.rn t.rd
  let q10 := highFloorVal 60 t.ln t.ld t.rn t.rd
  let q11 := highFloorVal 140 t.ln t.ld t.rn t.rd
  let z41 := highFloorVal 41 t.ln t.ld t.rn t.rd
  let z43 := highFloorVal 43 t.ln t.ld t.rn t.rd
  rcases hfloors with ⟨hqk, hk30, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hz41, hz43⟩
  have hfl30 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hk30
  have h0 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hq0
  have h1 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hq1
  have h2 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hq2
  have h3 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hq3
  have h4 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hq4
  have h5 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hq5
  have h6 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hq6
  have h7 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hq7
  have h8 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hq8
  have h9 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hq9
  have h10 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hq10
  have h11 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hq11
  have h41 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hz41
  have h43 := highFloorOk_strict hld hrd hn hp (by omega) hlo hhi hz43
  let getQ2 : ℕ → ℕ
    | 0 => q0 | 1 => q1 | 2 => q2 | 3 => q3 | 4 => q4 | 5 => q5
    | 6 => q6 | 7 => q7 | 8 => q8 | 9 => q9 | 10 => q10 | _ => q11
  let vPole : ℤ := (q0 : ℤ) + 2 * (q1 : ℤ) + (q2 : ℤ) + (q3 : ℤ) +
    2 * (q4 : ℤ) + (q5 : ℤ) + (q6 : ℤ) + 5 * (q7 : ℤ)
  let vFact : ℤ := vPole - 2 * (3 * (q4 : ℤ) + (z41 : ℤ) + (z43 : ℤ))
  have hfact_eq : sixFactVal n p = vFact := by
    have hdiv : ∀ (m : ℤ) (q : ℕ), 0 ≤ m → m.toNat * n / p = q → m * (n : ℤ) / (p : ℤ) = (q : ℤ) := by
      intro m q hm hq
      have h1 : ((m.toNat * n / p : ℕ) : ℤ) = (q : ℤ) := by exact_mod_cast hq
      have h2 : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
      simpa [Int.natCast_ediv, Nat.cast_mul, h2] using h1
    unfold sixFactVal sixBlockLen
    rw [Fin.sum_univ_def, Fin.sum_univ_def]
    simp only [List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, sixOffset, sixZero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    norm_num
    rw [hdiv 28 q0 (by omega) h0.2.2, hdiv 32 q1 (by omega) h1.2.2, hdiv 34 q2 (by omega) h2.2.2,
      hdiv 38 q3 (by omega) h3.2.2, hdiv 40 q4 (by omega) h4.2.2, hdiv 42 q5 (by omega) h5.2.2,
      hdiv 46 q6 (by omega) h6.2.2, hdiv 50 q7 (by omega) h7.2.2,
      hdiv 41 z41 (by omega) h41.2.2, hdiv 43 z43 (by omega) h43.2.2]
    dsimp [vFact, vPole]; ring
  let pts : List (ℤ × ℤ) :=
    (0, 0) :: t.perm.map (fun idx => highLine2 (radiusValNat idx) (getQ2 idx)) ++ [(0, 1)]
  obtain ⟨hplen, hpidx⟩ := isPerm12_spec hperm
  have hptslen : pts.length = 14 := by simp [pts, hplen]
  let p0 := indexOfNat t.perm 0
  let p1 := indexOfNat t.perm 1
  let p2 := indexOfNat t.perm 2
  let p3 := indexOfNat t.perm 3
  let p4 := indexOfNat t.perm 4
  let p5 := indexOfNat t.perm 5
  let p6 := indexOfNat t.perm 6
  let p7 := indexOfNat t.perm 7
  let p8 := indexOfNat t.perm 8
  let p9 := indexOfNat t.perm 9
  let p10 := indexOfNat t.perm 10
  let p11 := indexOfNat t.perm 11
  let k25 : ℕ := q7 / 2
  let q30 : ℕ := q10 / 2
  let s30 : ℕ := q10 % 2
  let ptAt (i : ℕ) : ℤ × ℤ := pts[i]?.getD (0, 0)
  let evalZ (u : ℤ × ℤ) : ℤ := u.1 * (n : ℤ) + u.2 * (p : ℤ)
  let evalR (u : ℤ × ℤ) : ℝ := (u.1 : ℝ) + (u.2 : ℝ) * ((p : ℝ) / (n : ℝ))
  have hevalZR : ∀ u : ℤ × ℤ, (evalZ u : ℝ) = evalR u * (n : ℝ) := by
    intro u; dsimp [evalZ, evalR]; push_cast; field_simp [hnR.ne']
  have hpt0 : ptAt 0 = (0, 0) := by simp [ptAt, pts]
  have hpt13 : ptAt 13 = (0, 1) := by
    have hlen12 : (t.perm.map (fun idx => highLine2 (radiusValNat idx) (getQ2 idx))).length = 12 := by
      simp [hplen]
    dsimp [ptAt, pts]
    rw [List.getElem?_append_right (by omega), hlen12]; simp
  have hpt_rad : ∀ k < 12, ptAt (indexOfNat t.perm k + 1) =
      highLine2 (radiusValNat k) (getQ2 k) := by
    intro k hk
    obtain ⟨hlt', hget⟩ := hpidx k hk
    dsimp [ptAt, pts]
    rw [List.getElem?_append_left (by simp [hplen]; omega), List.getElem?_map, hget]; rfl
  have hpt_monoR : ∀ {i j : ℕ}, i ≤ j → j < 14 → evalR (ptAt i) ≤ evalR (ptAt j) := by
    intro i j hij hj
    have hj' : j < pts.length := by omega
    have hi' : i < pts.length := Nat.lt_of_le_of_lt hij hj'
    have h1 : ptAt i = pts[i]'hi' := by dsimp [ptAt]; rw [List.getElem?_eq_getElem hi']; rfl
    have h2 : ptAt j = pts[j]'hj' := by dsimp [ptAt]; rw [List.getElem?_eq_getElem hj']; rfl
    rw [h1, h2]
    exact checkSortedLines_mono hld hrd hlo.le hhi.le hsort hij hj'
  have hpt_monoZ : ∀ {i j : ℕ}, i ≤ j → j < 14 → evalZ (ptAt i) ≤ evalZ (ptAt j) := by
    intro i j hij hj
    have hmul : (evalZ (ptAt i) : ℝ) ≤ (evalZ (ptAt j) : ℝ) := by
      rw [hevalZR, hevalZR]; exact mul_le_mul_of_nonneg_right (hpt_monoR hij hj) hnR.le
    exact_mod_cast hmul
  -- Start from Stage 2A master theorem `sixPrimitiveScalar_folded_joint_bound`
  have hmaster := sixPrimitiveScalar_folded_joint_bound n p hn hsq t.q
  dsimp only at hmaster
  let clsSet : Fin (p / 2 + 1) → Finset (Fin (sixSlotCount n)) :=
    fun c => Finset.univ.filter (fun u => foldMod p hp (sixSlotCenter n u) = c)
  let slotPairs : Finset (Fin (p / 2 + 1) × Fin (sixSlotCount n)) :=
    Finset.univ.filter (fun cr => cr.2.val < (clsSet cr.1).card)
  let inc : Fin (p / 2 + 1) × Fin (sixSlotCount n) → ℤ := fun cr =>
    (nthDescWeight (clsSet cr.1) (sixSlotCost n p) cr.2.val : ℤ) - 2 * ((cr.2.val - t.q : ℕ) : ℤ)
  have hexp_le : sixPrimeExpReal n p ≤
      2 * (sixRowPenalty (rank n) p t.q : ℝ) +
      ∑ j ∈ Finset.Icc 1 18,
        min ((rank n : ℝ)) (((slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℝ)) := by
    unfold sixPrimeExpReal
    have h1 : (-padicValRat p (sixPrimitiveScalar n) : ℝ) ≤
        2 * (sixRowPenalty (rank n) p t.q : ℝ) +
        ∑ j ∈ Finset.Icc 1 18,
          min ((rank n : ℝ)) (((slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℝ)) := by
      have hcast : ((-padicValRat p (sixPrimitiveScalar n) : ℤ) : ℝ) ≤
          ((2 * (sixRowPenalty (rank n) p t.q : ℤ) +
            ∑ j ∈ Finset.Icc 1 18,
              (min (rank n) (slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℤ) : ℤ) : ℝ) :=
        Int.cast_le (R := ℝ) |>.mpr hmaster
      rw [Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_sum] at hcast
      refine hcast.trans_eq ?_
      congr 1
      apply Finset.sum_congr rfl; intro j _
      rw [Int.cast_min, Int.cast_natCast, Int.cast_natCast]
    exact max_le (by
      rw [Int.cast_zero]
      exact add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg _))
        (Finset.sum_nonneg (fun _ _ => le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)))) h1
  -- Define `Bdy` and 13 open strips `Strip g`
  let Bdy : Finset (Fin (p / 2 + 1)) :=
    Finset.univ.filter (fun c => ∃ i : Fin 14, 2 * (c.val : ℤ) = evalZ (ptAt i.val))
  let Strip (g : ℕ) : Finset (Fin (p / 2 + 1)) :=
    Finset.univ.filter (fun c => evalZ (ptAt g) < 2 * (c.val : ℤ) ∧ 2 * (c.val : ℤ) < evalZ (ptAt (g + 1)))
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
      let S : Finset ℕ := (Finset.range 14).filter (fun i => evalZ (ptAt i) < 2 * (c.val : ℤ))
      have hSne : S.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h0lt⟩⟩
      let g := S.max' hSne
      have hg_mem := Finset.mem_filter.mp (Finset.max'_mem S hSne)
      have hg_lt14 : g < 14 := Finset.mem_range.mp hg_mem.1
      have hg_lt13 : g < 13 := by
        by_contra hge
        have hg13 : g = 13 := by omega
        have hbad13 : evalZ (ptAt g) < 2 * (c.val : ℤ) := hg_mem.2
        rw [hg13] at hbad13; omega
      have hg_next : 2 * (c.val : ℤ) < evalZ (ptAt (g + 1)) := by
        have hnot : g + 1 ∉ S := fun hm => by
          have := Finset.le_max' S (g + 1) hm; omega
        have hge : 2 * (c.val : ℤ) ≤ evalZ (ptAt (g + 1)) := by
          by_contra hlt'; push Not at hlt'
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hlt'⟩)
        have hne' : 2 * (c.val : ℤ) ≠ evalZ (ptAt (g + 1)) := hne ⟨g + 1, by omega⟩
        omega
      exact ⟨g, Finset.mem_range.mpr hg_lt13,
        Finset.mem_filter.mpr ⟨Finset.mem_univ c, ⟨hg_mem.2, hg_next⟩⟩⟩
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
  -- Per-class layer count `capClass j c`
  let capClass (j : ℕ) (c : Fin (p / 2 + 1)) : ℕ :=
    ((Finset.range (clsSet c).card).filter
      (fun r => (j : ℤ) ≤ (nthDescWeight (clsSet c) (sixSlotCost n p) r : ℤ) -
        2 * ((r - t.q : ℕ) : ℤ))).card
  -- Fiber decomposition of `slotPairs.filter (j ≤ inc)` over `c : Fin (p / 2 + 1)`
  have hfiber : ∀ j : ℕ,
      (slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card =
        ∑ c : Fin (p / 2 + 1), capClass j c := by
    intro j
    rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to
      (g := Prod.fst) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl; intro c _
    rw [← Finset.card_eq_sum_ones]
    apply Finset.card_bij (fun cr _ => cr.2.val)
    · intro cr hcr
      have hm1 := Finset.mem_filter.mp hcr
      have hm2 := Finset.mem_filter.mp hm1.1
      have hm3 := Finset.mem_filter.mp hm2.1
      rw [Finset.mem_filter, Finset.mem_range]
      dsimp only [inc] at hm2
      rw [hm1.2] at hm3 hm2
      exact ⟨hm3.2, hm2.2⟩
    · intro cr₁ h₁ cr₂ h₂ hval
      have hc1 := (Finset.mem_filter.mp h₁).2
      have hc2 := (Finset.mem_filter.mp h₂).2
      exact Prod.ext (hc1.trans hc2.symm) (Fin.ext hval)
    · intro r hr
      rw [Finset.mem_filter, Finset.mem_range] at hr
      have hr_lt : r < sixSlotCount n := hr.1.trans_le ((Finset.card_le_univ _).trans (by simp))
      refine ⟨(c, ⟨r, hr_lt⟩), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨⟨Finset.mem_univ _, hr.1⟩, hr.2⟩, rfl⟩
  -- Unconditional upper bound `capClass j c ≤ 210` for all `j ≥ 1` and all `c`
  have hcap_le_210 : ∀ j ≥ 1, ∀ c : Fin (p / 2 + 1), capClass j c ≤ 210 := by
    intro j hj c
    have hsub : (Finset.range (clsSet c).card).filter
        (fun r => (j : ℤ) ≤ (nthDescWeight (clsSet c) (sixSlotCost n p) r : ℤ) -
          2 * ((r - t.q : ℕ) : ℤ)) ⊆
        Finset.range ((clsSet c).filter (fun u => 1 ≤ sixSlotCost n p u)).card := by
      intro r hr
      rw [Finset.mem_filter, Finset.mem_range] at hr
      rw [Finset.mem_range]
      exact lt_card_filter_of_le_nthDescWeight (clsSet c) (sixSlotCost n p) hr.1 (by omega)
    exact ((Finset.card_le_card hsub).trans (by rw [Finset.card_range])).trans
      (active_slots_card_le_210 n p hp h35 c)
  -- Strip multiplier helper matching `buildStrips`
  let deltaOf (qv pv gg : ℕ) : ℕ :=
    let qr := qv / 2
    if qv % 2 == 0 then 2 * qr + (if gg ≤ pv then 1 else 0)
    else 2 * qr + (if gg ≤ pv then 1 else 2)
  let mkPlus (m gg : ℕ) : ℕ :=
    let f (qv pv mult : ℕ) : ℕ :=
      let qr := qv / 2
      if m < qr || (m == qr && (qv % 2 == 1 || gg ≤ pv)) then mult else 0
    f q0 p0 1 + f q1 p1 2 + f q2 p2 1 + f q3 p3 1 +
    f q4 p4 2 + f q5 p5 1 + f q6 p6 1 + f q7 p7 5
  let mkMinus (m gg : ℕ) : ℕ :=
    let f (qv pv mult : ℕ) : ℕ :=
      let qr := qv / 2
      if m ≤ qr || (m == qr + 1 && qv % 2 == 1 && pv < gg) then mult else 0
    f q0 p0 1 + f q1 p1 2 + f q2 p2 1 + f q3 p3 1 +
    f q4 p4 2 + f q5 p5 1 + f q6 p6 1 + f q7 p7 5
  let stripInfo (gg : ℕ) : Sum (ℕ × ℕ) (List ℕ) :=
    let Np : ℕ :=
      deltaOf q0 p0 gg + 2 * deltaOf q1 p1 gg + deltaOf q2 p2 gg + deltaOf q3 p3 gg +
      2 * deltaOf q4 p4 gg + deltaOf q5 p5 gg + deltaOf q6 p6 gg + 5 * deltaOf q7 p7 gg
    let Nz : ℕ :=
      5 * deltaOf q11 p11 gg - (deltaOf q8 p8 gg + deltaOf q9 p9 gg + 3 * deltaOf q10 p10 gg)
    let lt30 : Bool := gg ≤ p10
    let f30Plus : ℕ := q30 + (if s30 == 1 && !lt30 then 1 else 0)
    let f30Minus : ℕ := q30 - (if s30 == 0 && !lt30 then 1 else 0)
    if 15 ≤ Np && 1 ≤ f30Plus then
      let bInt : ℤ := 4 + (Np : ℤ) - (Nz : ℤ) - vFact
      let B : ℕ := if bInt ≤ 0 then 0 else bInt.toNat
      Sum.inl (Np, B)
    else
      let packed :=
        checkHighTile.buildStrips.addMinus vFact mkMinus gg Np Nz f30Plus f30Minus (k25 + 1)
          (checkHighTile.buildStrips.addPlus vFact mkPlus gg Np Nz f30Plus f30Minus (k25 + 1) 0)
      Sum.inr (packedToSuffixCounts packed)
  let stripMult (j gg : ℕ) : ℕ :=
    match stripInfo gg with
    | Sum.inl (Np, B) => if j ≤ B then min Np (t.q + 1 + (B - j) / 2) else 0
    | Sum.inr Nlist => jointCapFromN Nlist t.q j
  -- CORE STRIP BOUND: for `g < 13`, `c ∈ Strip g`, and `j ∈ Icc 1 18`, `capClass j c ≤ stripMult j g`!
  have hstrip_cap : ∀ g < 13, ∀ c ∈ Strip g, ∀ j ∈ Finset.Icc 1 18,
      capClass j c ≤ stripMult j g := by
    intro g hg c hc j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj18 : j ≤ 18 := (Finset.mem_Icc.mp hj).2
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
        symBlockMultCount p (radiusValNat k * n) (c.val : ℤ) =
          (deltaOf (getQ2 k) (indexOfNat t.perm k) g : ℤ) := by
      intro k hk
      obtain ⟨hpos_lt, _⟩ := hpidx k hk
      have hline_eq := hpt_rad k hk
      have hq2_bnds : getQ2 k * p ≤ 2 * radiusValNat k * n ∧
          2 * radiusValNat k * n < (getQ2 k + 1) * p := by
        interval_cases k
        · exact ⟨h0.1, h0.2.1⟩
        · exact ⟨h1.1, h1.2.1⟩
        · exact ⟨h2.1, h2.2.1⟩
        · exact ⟨h3.1, h3.2.1⟩
        · exact ⟨h4.1, h4.2.1⟩
        · exact ⟨h5.1, h5.2.1⟩
        · exact ⟨h6.1, h6.2.1⟩
        · exact ⟨h7.1, h7.2.1⟩
        · exact ⟨h8.1, h8.2.1⟩
        · exact ⟨h9.1, h9.2.1⟩
        · exact ⟨h10.1, h10.2.1⟩
        · exact ⟨h11.1, h11.2.1⟩
      apply symBlockMultCount_eq_highDelta n p (radiusValNat k) (getQ2 k)
        (indexOfNat t.perm k) g hp c.val hc0 hchalf hq2_bnds.1 hq2_bnds.2
      dsimp only; rw [← hline_eq]
      exact ⟨fun hgp => lt_of_lt_of_le hmem.2 (hpt_monoZ (by omega) (by omega)),
             fun hngp => lt_of_le_of_lt (hpt_monoZ (by omega) (by omega)) hmem.1⟩
    have hd0 := hdel 0 (by omega); have hd1 := hdel 1 (by omega)
    have hd2 := hdel 2 (by omega); have hd3 := hdel 3 (by omega)
    have hd4 := hdel 4 (by omega); have hd5 := hdel 5 (by omega)
    have hd6 := hdel 6 (by omega); have hd7 := hdel 7 (by omega)
    have hd8 := hdel 8 (by omega); have hd9 := hdel 9 (by omega)
    have hd10 := hdel 10 (by omega); have hd11 := hdel 11 (by omega)
    simp only [radiusValNat, getQ2] at hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10 hd11
    let Np : ℕ :=
      deltaOf q0 p0 g + 2 * deltaOf q1 p1 g + deltaOf q2 p2 g + deltaOf q3 p3 g +
      2 * deltaOf q4 p4 g + deltaOf q5 p5 g + deltaOf q6 p6 g + 5 * deltaOf q7 p7 g
    let Nz : ℕ :=
      5 * deltaOf q11 p11 g - (deltaOf q8 p8 g + deltaOf q9 p9 g + 3 * deltaOf q10 p10 g)
    have hNp_eq : sixPoleClassCount n p (c.val : ℤ) = Np := by
      have hZ : (sixPoleClassCount n p (c.val : ℤ) : ℤ) = (Np : ℤ) := by
        rw [sixPoleClassCount_eq_symBlocks n p hp, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7]
        dsimp [Np, p0, p1, p2, p3, p4, p5, p6, p7]
      exact_mod_cast hZ
    have hNz_eq : sixZeroClassCount n p (c.val : ℤ) = Nz := by
      have hZ : (sixZeroClassCount n p (c.val : ℤ) : ℤ) =
          5 * (deltaOf q11 p11 g : ℤ) -
          ((deltaOf q8 p8 g : ℤ) + (deltaOf q9 p9 g : ℤ) + 3 * (deltaOf q10 p10 g : ℤ)) := by
        rw [sixZeroClassCount_eq_symBlocks n p hp, hd8, hd9, hd10, hd11]
      have hnn : (deltaOf q8 p8 g : ℤ) + (deltaOf q9 p9 g : ℤ) + 3 * (deltaOf q10 p10 g : ℤ) ≤
          5 * (deltaOf q11 p11 g : ℤ) := by omega
      dsimp [Nz]; omega
    -- Exact `f30Plus = (30n + c) / p` and `f30Minus = (30n - c) / p`
    let lt30 : Bool := g ≤ p10
    let f30Plus : ℕ := q30 + (if s30 == 1 && !lt30 then 1 else 0)
    let f30Minus : ℕ := q30 - (if s30 == 0 && !lt30 then 1 else 0)
    have h30_ge_c : c.val ≤ 30 * n := by omega
    have hq10_pos : 1 ≤ q10 := by
      have hp60 : p ≤ 60 * n := by omega
      have h10_hi : 60 * n < (q10 + 1) * p := h10.2.1
      by_contra h0; have hq0' : q10 = 0 := by omega
      rw [hq0', zero_add, one_mul] at h10_hi; omega
    have hf30 : (30 * n + c.val) / p = f30Plus ∧ (30 * n - c.val) / p = f30Minus := by
      have hline10 := hpt_rad 10 (by omega)
      simp only [radiusValNat, getQ2] at hline10
      have hpos10 := (hpidx 10 (by omega)).1
      have hq10_split : q10 = 2 * q30 + s30 := (Nat.div_add_mod q10 2).symm
      have hs30_lt : s30 < 2 := Nat.mod_lt q10 (by omega)
      have hlo10 : q10 * p ≤ 60 * n := h10.1
      have hhi10 : 60 * n < (q10 + 1) * p := h10.2.1
      have hnat_div : ∀ a b : ℕ, b * p ≤ a → a < (b + 1) * p → a / p = b := by
        intro a b ha1 ha2
        have h1 := (Nat.le_div_iff_mul_le hp).mpr ha1
        have h2 := (Nat.div_lt_iff_lt_mul hp).mpr ha2
        omega
      by_cases hs0 : s30 = 0
      · have hq30_pos : 1 ≤ q30 := by omega
        have hl : highLine2 30 q10 = (60, -2 * (q30 : ℤ)) := by
          unfold highLine2; simp [show q10 % 2 = 0 from hs0, q30]
        constructor
        · have hf : f30Plus = q30 := by simp [f30Plus, hs0]
          rw [hf]
          apply hnat_div _ _ (by nlinarith only [hq10_split, hs0, hlo10])
            (by nlinarith only [hq10_split, hs0, hhi10, hchalf])
        · by_cases hgp : g ≤ p10
          · have hf : f30Minus = q30 := by simp [f30Minus, hs0, lt30, hgp]
            rw [hf]
            have hltc : 2 * (c.val : ℤ) < evalZ (ptAt (p10 + 1)) :=
              lt_of_lt_of_le hmem.2 (hpt_monoZ (by omega) (by omega))
            rw [show p10 = indexOfNat t.perm 10 from rfl, hline10, hl] at hltc
            dsimp [evalZ] at hltc
            have hltcN : c.val + q30 * p < 30 * n := by
              have hZ : (c.val : ℤ) + (q30 : ℤ) * (p : ℤ) < 30 * (n : ℤ) := by linarith only [hltc]
              exact_mod_cast hZ
            apply hnat_div _ _ (by omega)
              (by have : 30 * n < (q30 + 1) * p := by nlinarith only [hq10_split, hs0, hhi10, hp]
                  omega)
          · have hf : f30Minus = q30 - 1 := by simp [f30Minus, hs0, lt30, hgp]
            rw [hf]
            have hgtc : evalZ (ptAt (p10 + 1)) < 2 * (c.val : ℤ) :=
              lt_of_le_of_lt (hpt_monoZ (by omega) (by omega)) hmem.1
            rw [show p10 = indexOfNat t.perm 10 from rfl, hline10, hl] at hgtc
            dsimp [evalZ] at hgtc
            have hgtcN : 30 * n < c.val + q30 * p := by
              have hZ : 30 * (n : ℤ) < (c.val : ℤ) + (q30 : ℤ) * (p : ℤ) := by linarith only [hgtc]
              exact_mod_cast hZ
            have h1 : (q30 - 1) * p + p = q30 * p := by
              have : (q30 - 1) + 1 = q30 := by omega
              calc (q30 - 1) * p + p = ((q30 - 1) + 1) * p := by ring
                _ = q30 * p := by rw [this]
            have hlo_sub : (q30 - 1) * p + c.val ≤ 30 * n := by
              nlinarith only [hq10_split, hs0, hlo10, hchalf, h1]
            have hhi_sub : (q30 - 1 + 1) * p = q30 * p := by rw [Nat.sub_add_cancel hq30_pos]
            apply hnat_div _ _ (by omega) (by rw [hhi_sub]; omega)
      · have hs1 : s30 = 1 := by omega
        have hl : highLine2 30 q10 = (-60, 2 * ((q30 + 1 : ℕ) : ℤ)) := by
          unfold highLine2; simp [show q10 % 2 = 1 from hs1, q30]
        constructor
        · by_cases hgp : g ≤ p10
          · have hf : f30Plus = q30 := by simp [f30Plus, hs1, lt30, hgp]
            rw [hf]
            have hltc : 2 * (c.val : ℤ) < evalZ (ptAt (p10 + 1)) :=
              lt_of_lt_of_le hmem.2 (hpt_monoZ (by omega) (by omega))
            rw [show p10 = indexOfNat t.perm 10 from rfl, hline10, hl] at hltc
            dsimp [evalZ] at hltc
            have hltcN : 30 * n + c.val < (q30 + 1) * p := by
              have hZ : 30 * (n : ℤ) + (c.val : ℤ) < ((q30 : ℤ) + 1) * (p : ℤ) := by linarith only [hltc]
              exact_mod_cast hZ
            apply hnat_div _ _ (by nlinarith only [hq10_split, hs1, hlo10]) hltcN
          · have hf : f30Plus = q30 + 1 := by simp [f30Plus, hs1, lt30, hgp]
            rw [hf]
            have hgtc : evalZ (ptAt (p10 + 1)) < 2 * (c.val : ℤ) :=
              lt_of_le_of_lt (hpt_monoZ (by omega) (by omega)) hmem.1
            rw [show p10 = indexOfNat t.perm 10 from rfl, hline10, hl] at hgtc
            dsimp [evalZ] at hgtc
            have hgtcN : (q30 + 1) * p < 30 * n + c.val := by
              have hZ : ((q30 : ℤ) + 1) * (p : ℤ) < 30 * (n : ℤ) + (c.val : ℤ) := by linarith only [hgtc]
              exact_mod_cast hZ
            apply hnat_div _ _ (by omega) (by nlinarith only [hq10_split, hs1, hhi10, hchalf])
        · have hf : f30Minus = q30 := by simp [f30Minus, hs1]
          rw [hf]
          have hlo_m : q30 * p + c.val ≤ 30 * n := by nlinarith only [hq10_split, hs1, hlo10, hchalf]
          have hhi_m : 30 * n < (q30 + 1) * p := by nlinarith only [hq10_split, hs1, hhi10]
          apply hnat_div _ _ (by omega) (by omega)
    -- Active slot count in `clsSet c` equals `∑_{t in class c} sixPoleOrder` and `≤ Np`
    have hactive_le_Np : ((clsSet c).filter (fun u => 1 ≤ sixSlotCost n p u)).card ≤ Np := by
      rw [← hNp_eq]
      -- Map each active slot `(t, a)` with `a < sixPoleOrder n (sixHalfPole n t)` into the disjoint union over blocks
      -- Wait: even simpler! Count per `t` with `foldMod (-t) = c`:
      let Tc := (Finset.univ : Finset (Fin (25 * n + 1))).filter
        (fun x => foldMod p hp (-(x.val : ℤ)) = c)
      have h1 : ((clsSet c).filter (fun u => 1 ≤ sixSlotCost n p u)).card ≤
          ∑ x ∈ Tc, sixPoleOrder n (sixHalfPole n x) := by
        let Ssig := Tc.sigma (fun x => Finset.range (sixPoleOrder n (sixHalfPole n x)))
        have hcard_sig : Ssig.card = ∑ x ∈ Tc, sixPoleOrder n (sixHalfPole n x) := by
          simp [Ssig, Finset.card_sigma]
        rw [← hcard_sig]
        apply Finset.card_le_card_of_injOn (fun u =>
          ⟨((sixSlotEquiv n).symm u).1, ((sixSlotEquiv n).symm u).2.val⟩)
        · intro u hu
          have hmem_cls := (Finset.mem_filter.mp hu).1
          have hcost1 := (Finset.mem_filter.mp hu).2
          have hfold := (Finset.mem_filter.mp hmem_cls).2
          have ha_lt : ((sixSlotEquiv n).symm u).2.val <
              sixPoleOrder n (sixHalfPole n ((sixSlotEquiv n).symm u).1) := by
            by_contra hge
            have h0 : sixSlotCost n p u = 0 := by
              unfold sixSlotCost sixRefinedSlotCost
              have hemp : (Finset.range (sixPoleOrder n (sixHalfPole n ((sixSlotEquiv n).symm u).1))).filter
                  (fun r => ((sixSlotEquiv n).symm u).2.val ≤ r) = ∅ := by
                ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
                omega
              change ((Finset.range _).filter _).sup _ = 0
              rw [hemp, Finset.sup_empty]; rfl
            omega
          exact Finset.mem_coe.mpr (Finset.mem_sigma.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfold⟩, Finset.mem_range.mpr ha_lt⟩)
        · intro u₁ _ u₂ _ heq
          have h1 : ((sixSlotEquiv n).symm u₁).1 = ((sixSlotEquiv n).symm u₂).1 := congrArg Sigma.fst heq
          have h2 : ((sixSlotEquiv n).symm u₁).2.val = ((sixSlotEquiv n).symm u₂).2.val := by
            simpa using congrArg Sigma.snd heq
          exact (sixSlotEquiv n).symm.injective (Prod.ext h1 (Fin.ext h2))
      exact h1.trans (sum_halfPoleOrder_le_poleClassCount n p hp c hc0)
    -- Split on fast path (`15 ≤ Np && 1 ≤ f30Plus`) vs general packed-histogram path
    change capClass j c ≤
      match (if (decide (15 ≤ Np) && decide (1 ≤ f30Plus)) = true then
          Sum.inl (Np, if 4 + (Np : ℤ) - (Nz : ℤ) - vFact ≤ 0 then 0 else (4 + (Np : ℤ) - (Nz : ℤ) - vFact).toNat)
        else
          Sum.inr (packedToSuffixCounts
            (checkHighTile.buildStrips.addMinus vFact mkMinus g Np Nz f30Plus f30Minus (k25 + 1)
              (checkHighTile.buildStrips.addPlus vFact mkPlus g Np Nz f30Plus f30Minus (k25 + 1) 0)))) with
      | Sum.inl (Np', B') => if j ≤ B' then min Np' (t.q + 1 + (B' - j) / 2) else 0
      | Sum.inr Nlist => jointCapFromN Nlist t.q j
    by_cases hfast : 15 ≤ Np ∧ 1 ≤ f30Plus
    · have hbf : (decide (15 ≤ Np) && decide (1 ≤ f30Plus)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hfast
      simp only [hbf, ite_true]
      let bInt : ℤ := 4 + (Np : ℤ) - (Nz : ℤ) - vFact
      let B : ℕ := if bInt ≤ 0 then 0 else bInt.toNat
      have hB_eq : sixCoarsePeriodicCost n p c = B := by
        unfold sixCoarsePeriodicCost
        rw [hNp_eq, hNz_eq, hfact_eq]
        dsimp [B, bInt]; split_ifs <;> omega
      have hcost_le_B : ∀ u ∈ clsSet c, sixSlotCost n p u ≤ B := by
        intro u hu
        rw [← hB_eq]
        have hfold := (Finset.mem_filter.mp hu).2
        unfold sixSlotCost
        have hcenter : (sixCenter n : ℤ) - (sixHalfPole n ((sixSlotEquiv n).symm u).1 : ℤ) =
            sixSlotCenter n u := by
          unfold sixHalfPole sixSlotCenter; push_cast; ring
        have hle := sixRefinedSlotCost_le_coarse n p (sixHalfPole n ((sixSlotEquiv n).symm u).1)
          ((sixSlotEquiv n).symm u).2.val hp
        rwa [hcenter, hfold] at hle
      by_cases hjB : j ≤ B
      · have hjB' : j ≤ (if 4 + (Np : ℤ) - (Nz : ℤ) - vFact ≤ 0 then 0
            else (4 + (Np : ℤ) - (Nz : ℤ) - vFact).toNat) := hjB
        simp only [hjB', ite_true]
        have hsub : (Finset.range (clsSet c).card).filter
            (fun r => (j : ℤ) ≤ (nthDescWeight (clsSet c) (sixSlotCost n p) r : ℤ) -
              2 * ((r - t.q : ℕ) : ℤ)) ⊆
            Finset.range (min Np (t.q + 1 + (B - j) / 2)) := by
          intro r hr
          rw [Finset.mem_filter, Finset.mem_range] at hr
          rw [Finset.mem_range]
          have h1 : r < Np :=
            (lt_card_filter_of_le_nthDescWeight (clsSet c) (sixSlotCost n p) hr.1
              (one_le_of_le_sub_two hj1 hr.2)).trans_le hactive_le_Np
          have h2 : nthDescWeight (clsSet c) (sixSlotCost n p) r ≤ B :=
            nthDescWeight_le_bound (clsSet c) (sixSlotCost n p) B hcost_le_B r
          have h3 : r < t.q + 1 + (B - j) / 2 := lt_add_one_add_div_two_of_le hjB h2 hr.2
          exact lt_min h1 h3
        exact (Finset.card_le_card hsub).trans (by rw [Finset.card_range])
      · have hjB' : ¬ j ≤ (if 4 + (Np : ℤ) - (Nz : ℤ) - vFact ≤ 0 then 0
            else (4 + (Np : ℤ) - (Nz : ℤ) - vFact).toNat) := hjB
        simp only [hjB', ite_false]
        have hemp : (Finset.range (clsSet c).card).filter
            (fun r => (j : ℤ) ≤ (nthDescWeight (clsSet c) (sixSlotCost n p) r : ℤ) -
              2 * ((r - t.q : ℕ) : ℤ)) = ∅ := by
          ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
          rintro ⟨_, hle⟩
          have h2 := nthDescWeight_le_bound (clsSet c) (sixSlotCost n p) B hcost_le_B r
          exact not_le_sub_two_of_lt hjB h2 hle
        change ((Finset.range _).filter _).card ≤ 0
        rw [hemp]; simp
    · -- General bit-packed histogram path (`¬ (15 ≤ Np ∧ 1 ≤ f30Plus)`)
      have hbf : (decide (15 ≤ Np) && decide (1 ≤ f30Plus)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; exact not_and_or.mp hfast
      simp only [hbf, Bool.false_eq_true, ite_false]
      -- First prove `Np < 256` (in fact `Np ≤ 210`!)
      have hNp_lt256 : Np < 256 := by
        have hle210 : Np ≤ 210 := by
          rw [← hNp_eq]
          exact poleClassCount_le_210 n p hp h35 (c.val : ℤ)
        omega
      -- Helper: radius comparison for `m * p + c ≤ rad * n` and `m * p - c ≤ rad * n`
      have hplus_rad : ∀ (k : ℕ) (hk : k < 8) (m : ℕ),
          m * p + c.val ≤ radiusValNat k * n ↔
            (m < getQ2 k / 2 ∨ (m = getQ2 k / 2 ∧ (getQ2 k % 2 = 1 ∨ g ≤ indexOfNat t.perm k))) := by
        intro k hk m
        have hk12 : k < 12 := by omega
        have hpos_lt := (hpidx k hk12).1
        have hline_eq := hpt_rad k hk12
        have hq2_bnds : getQ2 k * p ≤ 2 * radiusValNat k * n ∧
            2 * radiusValNat k * n < (getQ2 k + 1) * p := by
          match k, hk with
          | 0, _ => exact ⟨h0.1, h0.2.1⟩
          | 1, _ => exact ⟨h1.1, h1.2.1⟩
          | 2, _ => exact ⟨h2.1, h2.2.1⟩
          | 3, _ => exact ⟨h3.1, h3.2.1⟩
          | 4, _ => exact ⟨h4.1, h4.2.1⟩
          | 5, _ => exact ⟨h5.1, h5.2.1⟩
          | 6, _ => exact ⟨h6.1, h6.2.1⟩
          | 7, _ => exact ⟨h7.1, h7.2.1⟩
        let qr := getQ2 k / 2
        have hsplit : getQ2 k = 2 * qr + getQ2 k % 2 := (Nat.div_add_mod (getQ2 k) 2).symm
        by_cases hev : getQ2 k % 2 = 0
        · have hl : highLine2 (radiusValNat k) (getQ2 k) = (2 * (radiusValNat k : ℤ), -2 * (qr : ℤ)) := by
            unfold highLine2; simp [hev, qr]
          by_cases hgp : g ≤ indexOfNat t.perm k
          · have hltc : 2 * (c.val : ℤ) < evalZ (ptAt (indexOfNat t.perm k + 1)) :=
              lt_of_lt_of_le hmem.2 (hpt_monoZ (by omega) (by omega))
            rw [hline_eq, hl] at hltc; dsimp [evalZ] at hltc
            have hltN : c.val + qr * p < radiusValNat k * n := by
              have hZ : (c.val : ℤ) + (qr : ℤ) * (p : ℤ) < (radiusValNat k : ℤ) * (n : ℤ) := by linarith only [hltc]
              exact_mod_cast hZ
            have hq2_hi' : radiusValNat k * n < (qr + 1) * p := by
              nlinarith only [hq2_bnds.2, hsplit, hev]
            constructor
            · intro hle
              by_cases hmq : m < qr
              · exact Or.inl hmq
              · right; refine ⟨?_, Or.inr hgp⟩
                have : m ≤ qr := by nlinarith only [hle, hq2_hi', hp]
                omega
            · rintro (hmq | ⟨rfl, _⟩)
              · have hmp : m * p ≤ qr * p := Nat.mul_le_mul_right p (Nat.le_of_lt hmq)
                omega
              · dsimp only [qr] at hltN; omega
          · have hgtc : evalZ (ptAt (indexOfNat t.perm k + 1)) < 2 * (c.val : ℤ) :=
              lt_of_le_of_lt (hpt_monoZ (by omega) (by omega)) hmem.1
            rw [hline_eq, hl] at hgtc; dsimp [evalZ] at hgtc
            have hgtN : radiusValNat k * n < qr * p + c.val := by
              have hZ : (radiusValNat k : ℤ) * (n : ℤ) < (qr : ℤ) * (p : ℤ) + (c.val : ℤ) := by linarith only [hgtc]
              exact_mod_cast hZ
            have hq2_lo' : qr * p ≤ radiusValNat k * n := by
              nlinarith only [hq2_bnds.1, hsplit, hev]
            constructor
            · intro hle; left
              by_contra hge
              have hmp : qr * p ≤ m * p := Nat.mul_le_mul_right p (Nat.le_of_not_lt hge)
              omega
            · rintro (hmq | ⟨_, hbad'⟩)
              · have hmp : m * p + p ≤ qr * p := by
                  simpa [Nat.succ_mul] using Nat.mul_le_mul_right p hmq
                omega
              · rcases hbad' with h1 | h2
                · omega
                · exact absurd h2 hgp
        · have hodd : getQ2 k % 2 = 1 := by omega
          have hlo' : (2 * qr + 1) * p ≤ 2 * radiusValNat k * n := by
            nlinarith only [hq2_bnds.1, hsplit, hodd]
          have hhi' : radiusValNat k * n < (qr + 1) * p := by
            nlinarith only [hq2_bnds.2, hsplit, hodd]
          constructor
          · intro hle
            by_cases hmq : m < qr
            · exact Or.inl hmq
            · right; refine ⟨?_, Or.inl hodd⟩
              have : m ≤ qr := by nlinarith only [hle, hhi', hp]
              omega
          · rintro (hmq | ⟨rfl, _⟩)
            · have hmp : m * p ≤ qr * p := Nat.mul_le_mul_right p (Nat.le_of_lt hmq)
              have hlo2 : 2 * (qr * p) + p ≤ 2 * (radiusValNat k * n) := by nlinarith only [hlo']
              omega
            · dsimp only [qr] at hlo'
              have hlo2 : 2 * (getQ2 k / 2 * p) + p ≤ 2 * (radiusValNat k * n) := by nlinarith only [hlo']
              omega
      have hminus_rad : ∀ (k : ℕ) (hk : k < 8) (m : ℕ), 1 ≤ m →
          (m * p - c.val ≤ radiusValNat k * n ↔
            (m ≤ getQ2 k / 2 ∨ (m = getQ2 k / 2 + 1 ∧ getQ2 k % 2 = 1 ∧ indexOfNat t.perm k < g))) := by
        intro k hk m hm1
        have hk12 : k < 12 := by omega
        have hpos_lt := (hpidx k hk12).1
        have hline_eq := hpt_rad k hk12
        have hq2_bnds : getQ2 k * p ≤ 2 * radiusValNat k * n ∧
            2 * radiusValNat k * n < (getQ2 k + 1) * p := by
          match k, hk with
          | 0, _ => exact ⟨h0.1, h0.2.1⟩
          | 1, _ => exact ⟨h1.1, h1.2.1⟩
          | 2, _ => exact ⟨h2.1, h2.2.1⟩
          | 3, _ => exact ⟨h3.1, h3.2.1⟩
          | 4, _ => exact ⟨h4.1, h4.2.1⟩
          | 5, _ => exact ⟨h5.1, h5.2.1⟩
          | 6, _ => exact ⟨h6.1, h6.2.1⟩
          | 7, _ => exact ⟨h7.1, h7.2.1⟩
        let qr := getQ2 k / 2
        have hsplit : getQ2 k = 2 * qr + getQ2 k % 2 := (Nat.div_add_mod (getQ2 k) 2).symm
        have hcmp : c.val ≤ m * p := by
          have hpm : p ≤ m * p := Nat.le_mul_of_pos_left p hm1
          omega
        by_cases hev : getQ2 k % 2 = 0
        · have hlo' : qr * p ≤ radiusValNat k * n := by nlinarith only [hq2_bnds.1, hsplit, hev]
          have hhi' : 2 * radiusValNat k * n < (2 * qr + 1) * p := by nlinarith only [hq2_bnds.2, hsplit, hev]
          constructor
          · intro hle; left
            by_contra hgt
            have h1 : (qr + 1) * p ≤ m * p := Nat.mul_le_mul_right p (by omega)
            have h2 : 2 * (qr * p) + 2 * p ≤ 2 * (m * p) := by nlinarith only [h1]
            have h3 : 2 * (radiusValNat k * n) < 2 * (qr * p) + p := by nlinarith only [hhi']
            omega
          · rintro (hmq | ⟨_, hodd, _⟩)
            · have : m * p ≤ qr * p := Nat.mul_le_mul_right p hmq
              omega
            · omega
        · have hodd : getQ2 k % 2 = 1 := by omega
          have hl : highLine2 (radiusValNat k) (getQ2 k) =
              (-2 * (radiusValNat k : ℤ), 2 * ((qr + 1 : ℕ) : ℤ)) := by
            unfold highLine2; simp [hodd, qr]
          have hlo' : (2 * qr + 1) * p ≤ 2 * radiusValNat k * n := by nlinarith only [hq2_bnds.1, hsplit, hodd]
          have hhi' : radiusValNat k * n < (qr + 1) * p := by nlinarith only [hq2_bnds.2, hsplit, hodd]
          by_cases hgp : g ≤ indexOfNat t.perm k
          · have hltc : 2 * (c.val : ℤ) < evalZ (ptAt (indexOfNat t.perm k + 1)) :=
              lt_of_lt_of_le hmem.2 (hpt_monoZ (by omega) (by omega))
            rw [hline_eq, hl] at hltc; dsimp [evalZ] at hltc
            have hgtN : radiusValNat k * n + c.val < (qr + 1) * p := by
              have hZ : (radiusValNat k : ℤ) * (n : ℤ) + (c.val : ℤ) < ((qr : ℤ) + 1) * (p : ℤ) := by linarith only [hltc]
              exact_mod_cast hZ
            constructor
            · intro hle; left
              by_contra hgt
              have : (qr + 1) * p ≤ m * p := Nat.mul_le_mul_right p (by omega)
              omega
            · rintro (hmq | ⟨_, _, hpg⟩)
              · have hmp : m * p ≤ qr * p := Nat.mul_le_mul_right p hmq
                have hqr : qr * p ≤ radiusValNat k * n := by nlinarith only [hlo']
                omega
              · omega
          · have hgtc : evalZ (ptAt (indexOfNat t.perm k + 1)) < 2 * (c.val : ℤ) :=
              lt_of_le_of_lt (hpt_monoZ (by omega) (by omega)) hmem.1
            rw [hline_eq, hl] at hgtc; dsimp [evalZ] at hgtc
            have hltN : (qr + 1) * p < radiusValNat k * n + c.val := by
              have hZ : ((qr : ℤ) + 1) * (p : ℤ) < (radiusValNat k : ℤ) * (n : ℤ) + (c.val : ℤ) := by linarith only [hgtc]
              exact_mod_cast hZ
            constructor
            · intro hle
              by_cases hmq : m ≤ qr
              · exact Or.inl hmq
              · right; refine ⟨?_, hodd, by omega⟩
                have : m ≤ qr + 1 := by
                  by_contra hgt2
                  have h1 : (qr + 2) * p ≤ m * p := Nat.mul_le_mul_right p (by omega)
                  have h2 : (qr + 1) * p + p ≤ m * p := by nlinarith only [h1]
                  omega
                omega
            · rintro (hmq | ⟨rfl, _, _⟩)
              · have hmp : m * p ≤ qr * p := Nat.mul_le_mul_right p hmq
                have hqr : qr * p ≤ radiusValNat k * n := by nlinarith only [hlo']
                omega
              · dsimp only [qr] at hltN; omega
      -- Exact branch order matching for `+` (`m * p + c`) and `-` (`m * p - c`)
      have hmkPlus_pos_le25 : ∀ m, mkPlus m g ≠ 0 → m * p + c.val ≤ 25 * n := by
        intro m hne
        by_contra hgt
        -- If radius 25 fails, every radius ≤ 25 also fails!
        have hfail : ∀ k < 8, ¬ (m < getQ2 k / 2 ∨ m = getQ2 k / 2 ∧ (getQ2 k % 2 = 1 ∨ g ≤ indexOfNat t.perm k)) := by
          intro k hk hk_ok
          have hle := (hplus_rad k hk m).mpr hk_ok
          have hrad25 : radiusValNat k ≤ 25 := radiusValNat_le_25 k hk
          have : radiusValNat k * n ≤ 25 * n := Nat.mul_le_mul_right n hrad25
          omega
        have hf0 := hfail 0 (by omega); have hf1 := hfail 1 (by omega)
        have hf2 := hfail 2 (by omega); have hf3 := hfail 3 (by omega)
        have hf4 := hfail 4 (by omega); have hf5 := hfail 5 (by omega)
        have hf6 := hfail 6 (by omega); have hf7 := hfail 7 (by omega)
        simp only [getQ2] at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7
        apply hne; dsimp [mkPlus, p0, p1, p2, p3, p4, p5, p6, p7]
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
          hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, ite_false, add_zero]
      have hmkMinus_pos_le25 : ∀ m, 1 ≤ m → mkMinus m g ≠ 0 → m * p - c.val ≤ 25 * n := by
        intro m hm1 hne
        by_contra hgt
        have hfail : ∀ k < 8, ¬ (m ≤ getQ2 k / 2 ∨ (m = getQ2 k / 2 + 1 ∧ getQ2 k % 2 = 1) ∧ indexOfNat t.perm k < g) := by
          intro k hk hk_ok
          have hle := (hminus_rad k hk m hm1).mpr (hk_ok.imp id fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩)
          have hrad25 : radiusValNat k ≤ 25 := radiusValNat_le_25 k hk
          have : radiusValNat k * n ≤ 25 * n := Nat.mul_le_mul_right n hrad25
          omega
        have hf0 := hfail 0 (by omega); have hf1 := hfail 1 (by omega)
        have hf2 := hfail 2 (by omega); have hf3 := hfail 3 (by omega)
        have hf4 := hfail 4 (by omega); have hf5 := hfail 5 (by omega)
        have hf6 := hfail 6 (by omega); have hf7 := hfail 7 (by omega)
        simp only [getQ2] at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7
        apply hne; dsimp [mkMinus, p0, p1, p2, p3, p4, p5, p6, p7]
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
          hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, ite_false, add_zero]
      have hmkPlus_eq_ord : ∀ (m : ℕ) (hle : m * p + c.val ≤ 25 * n),
          sixPoleOrder n (sixHalfPole n ⟨m * p + c.val, by omega⟩) = mkPlus m g := by
        intro m hle
        rw [sixPoleOrder_halfPole_eq]
        have heq_k : ∀ k < 8,
            (if m * p + c.val ≤ radiusValNat k * n then (1 : ℕ) else 0) =
              (if m < getQ2 k / 2 || (m == getQ2 k / 2 && (getQ2 k % 2 == 1 || g ≤ indexOfNat t.perm k)) then 1 else 0) := by
          intro k hk
          have hiff := hplus_rad k hk m
          by_cases h1 : m * p + c.val ≤ radiusValNat k * n
          · have h2 := hiff.mp h1
            simp only [h1, ite_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, h2]
          · have h2 : ¬ (m < getQ2 k / 2 ∨ m = getQ2 k / 2 ∧ (getQ2 k % 2 = 1 ∨ g ≤ indexOfNat t.perm k)) :=
              fun h => h1 (hiff.mpr h)
            simp only [h1, ite_false, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, h2]
        have hscale : ∀ (P Q : Prop) [Decidable P] [Decidable Q] (w : ℕ),
            ((if P then (1 : ℕ) else 0) = if Q then 1 else 0) →
            (if P then w else 0) = if Q then w else 0 := by
          intro P Q _ _ w h; by_cases hP : P <;> by_cases hQ : Q <;> simp_all
        dsimp only [mkPlus]
        have e0 := heq_k 0 (by omega); have e1 := heq_k 1 (by omega)
        have e2 := heq_k 2 (by omega); have e3 := heq_k 3 (by omega)
        have e4 := heq_k 4 (by omega); have e5 := heq_k 5 (by omega)
        have e6 := heq_k 6 (by omega); have e7 := heq_k 7 (by omega)
        simp only [radiusValNat, getQ2] at e0 e1 e2 e3 e4 e5 e6 e7
        dsimp only [p0, p1, p2, p3, p4, p5, p6, p7]
        rw [e0, hscale _ _ 2 e1, e2, e3, hscale _ _ 2 e4, e5, e6, hscale _ _ 5 e7]
      have hmkMinus_eq_ord : ∀ (m : ℕ) (hm1 : 1 ≤ m) (hle : m * p - c.val ≤ 25 * n),
          sixPoleOrder n (sixHalfPole n ⟨m * p - c.val, by omega⟩) = mkMinus m g := by
        intro m hm1 hle
        rw [sixPoleOrder_halfPole_eq]
        have heq_k : ∀ k < 8,
            (if m * p - c.val ≤ radiusValNat k * n then (1 : ℕ) else 0) =
              (if m ≤ getQ2 k / 2 || (m == getQ2 k / 2 + 1 && getQ2 k % 2 == 1 && indexOfNat t.perm k < g) then 1 else 0) := by
          intro k hk
          have hiff := hminus_rad k hk m hm1
          by_cases h1 : m * p - c.val ≤ radiusValNat k * n
          · have h2 := hiff.mp h1
            simp only [h1, ite_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
            have h2' : m ≤ getQ2 k / 2 ∨ (m = getQ2 k / 2 + 1 ∧ getQ2 k % 2 = 1) ∧ indexOfNat t.perm k < g :=
              h2.imp id fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩
            simp only [h2', ite_true]
          · have h2 : ¬ (m ≤ getQ2 k / 2 ∨ (m = getQ2 k / 2 + 1 ∧ getQ2 k % 2 = 1) ∧ indexOfNat t.perm k < g) :=
              fun h => h1 (hiff.mpr (h.imp id fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩))
            simp only [h1, ite_false, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, h2]
        have hscale : ∀ (P Q : Prop) [Decidable P] [Decidable Q] (w : ℕ),
            ((if P then (1 : ℕ) else 0) = if Q then 1 else 0) →
            (if P then w else 0) = if Q then w else 0 := by
          intro P Q _ _ w h; by_cases hP : P <;> by_cases hQ : Q <;> simp_all
        dsimp only [mkMinus]
        have e0 := heq_k 0 (by omega); have e1 := heq_k 1 (by omega)
        have e2 := heq_k 2 (by omega); have e3 := heq_k 3 (by omega)
        have e4 := heq_k 4 (by omega); have e5 := heq_k 5 (by omega)
        have e6 := heq_k 6 (by omega); have e7 := heq_k 7 (by omega)
        simp only [radiusValNat, getQ2] at e0 e1 e2 e3 e4 e5 e6 e7
        dsimp only [p0, p1, p2, p3, p4, p5, p6, p7]
        rw [e0, hscale _ _ 2 e1, e2, e3, hscale _ _ 2 e4, e5, e6, hscale _ _ 5 e7]
      -- Prove `addPlus` and `addMinus` accumulate valid `HistRepr` dominating all slots in `clsSet c`!
      -- Define helper: for any `x : Fin (25*n+1)` with `foldMod (-x) = c`, its `sixPoleClassCount`, `sixZeroClassCount`, `sixSiteBaseVal` match `(Np, Nz, vFact)`
      have hsite_counts : ∀ x : Fin (25 * n + 1), foldMod p hp (-(x.val : ℤ)) = c →
          sixDenomAliasCount n p (sixHalfPole n x) = Np - sixPoleOrder n (sixHalfPole n x) ∧
          sixNumAliasCount n p (sixHalfPole n x) = Nz ∧
          sixSiteBaseVal n p (sixHalfPole n x) =
            vFact + (Nz : ℤ) - ((Np - sixPoleOrder n (sixHalfPole n x) : ℕ) : ℤ) := by
        intro x hx
        have hcenter : (sixCenter n : ℤ) - (sixHalfPole n x : ℤ) = -(x.val : ℤ) := by
          unfold sixHalfPole; push_cast; ring
        have hp_c : sixPoleClassCount n p ((sixCenter n : ℤ) - (sixHalfPole n x : ℤ)) = Np := by
          rw [hcenter, sixPoleClassCount_foldMod n p hp, hx, hNp_eq]
        have hz_c : sixZeroClassCount n p ((sixCenter n : ℤ) - (sixHalfPole n x : ℤ)) = Nz := by
          rw [hcenter, sixZeroClassCount_foldMod n p hp, hx, hNz_eq]
        refine ⟨by unfold sixDenomAliasCount; rw [hp_c],
                by unfold sixNumAliasCount; rw [hz_c],
                by unfold sixSiteBaseVal sixDenomAliasCount sixNumAliasCount; rw [hp_c, hz_c, hfact_eq]⟩
      -- Induction for `addPlus`: covers `{x ∈ Tc : ∃ m < rem, x.val = m * p + c.val}`
      have haddPlus : ∀ (rem : ℕ) (c0 : ℕ → ℕ) (p0 : ℕ), HistRepr c0 p0 →
          ∃ d : ℕ → ℕ,
            HistRepr (fun v => c0 v + d v)
              (checkHighTile.buildStrips.addPlus vFact mkPlus g Np Nz f30Plus f30Minus rem p0) ∧
            (∑ v ∈ Finset.Icc 1 18, d v) ≤
              ∑ m ∈ Finset.range rem, mkPlus m g ∧
            ∀ v ∈ Finset.Icc 1 18,
              (∑ m ∈ Finset.range rem,
                if hle : m * p + c.val ≤ 25 * n then
                  ((Finset.range (sixPoleOrder n (sixHalfPole n ⟨m * p + c.val, by omega⟩))).filter
                    (fun a => v ≤ sixRefinedSlotCost n p (sixHalfPole n ⟨m * p + c.val, by omega⟩) a)).card
                else 0) ≤
              ∑ w ∈ Finset.Icc v 18, d w := by
        intro rem
        induction rem with
        | zero =>
          intro c0 p0 hr0
          exact ⟨fun _ => 0, by rw [checkHighTile.buildStrips.addPlus.eq_def]; simpa using hr0, by simp, by simp⟩
        | succ m ih =>
          intro c0 p0 hr0
          rw [checkHighTile.buildStrips.addPlus.eq_def]
          dsimp +zetaHave only
          by_cases hmk0 : mkPlus m g = 0
          · simp only [hmk0, beq_self_eq_true, ite_true]
            obtain ⟨d, hr1, hsum1, hdom1⟩ := ih c0 p0 hr0
            refine ⟨d, hr1, by rw [Finset.sum_range_succ, hmk0, add_zero]; exact hsum1, fun v hv => ?_⟩
            rw [Finset.sum_range_succ]
            have hm_term : (if hle : m * p + c.val ≤ 25 * n then
                ((Finset.range (sixPoleOrder n (sixHalfPole n ⟨m * p + c.val, by omega⟩))).filter
                  (fun a => v ≤ sixRefinedSlotCost n p (sixHalfPole n ⟨m * p + c.val, by omega⟩) a)).card
                else 0) = 0 := by
              split_ifs with hle
              · rw [hmkPlus_eq_ord m hle, hmk0]; simp
              · rfl
            rw [hm_term, add_zero]; exact hdom1 v hv
          · have hne : (mkPlus m g == 0) = false := beq_false_of_ne hmk0
            simp only [hne, Bool.false_eq_true, ite_false]
            have hle25 : m * p + c.val ≤ 25 * n := hmkPlus_pos_le25 m hmk0
            let x : Fin (25 * n + 1) := ⟨m * p + c.val, by omega⟩
            let k := sixHalfPole n x
            have hord : sixPoleOrder n k = mkPlus m g := hmkPlus_eq_ord m hle25
            have hfold_x : foldMod p hp (-(x.val : ℤ)) = c := by
              unfold foldMod
              dsimp +zetaHave only
              have hmod : (-(x.val : ℤ)) % (p : ℤ) = (p : ℤ) - (c.val : ℤ) := by
                have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
                have hrew : -(x.val : ℤ) = ((p : ℤ) - (c.val : ℤ)) + (-(m : ℤ) - 1) * (p : ℤ) := by
                  dsimp [x]; ring
                rw [hrew, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
              simp only [hmod]
              have hto : ((p : ℤ) - (c.val : ℤ)).toNat = p - c.val := by omega
              simp only [hto]
              have hgt : ¬ (p - c.val ≤ p / 2) := by omega
              simp only [hgt, dite_false]
              apply Fin.ext; dsimp only; omega
            obtain ⟨hda_eq, hnz_eq, hbv_eq⟩ := hsite_counts x hfold_x
            -- Exact harmonic indicators for `k = 70n + 1 + m*p + c`
            have hk_right : (k - 40 * n - 1) / p = m + f30Plus := by
              have h1 : k - 40 * n - 1 = (30 * n + c.val) + m * p := by
                dsimp [k, sixHalfPole, sixCenter, x]; omega
              rw [h1, Nat.add_mul_div_right _ _ hp, hf30.1]; omega
            have hk_left : (sixReflectedPole n k - 40 * n - 1) / p = f30Minus - m := by
              have h1 : sixReflectedPole n k - 40 * n - 1 + m * p = 30 * n - c.val := by
                dsimp [k, sixReflectedPole, sixHalfPole, sixCenter, x]; omega
              have hle_mp : m * p ≤ 30 * n - c.val := by omega
              have h2 : sixReflectedPole n k - 40 * n - 1 = (30 * n - c.val) - m * p := by omega
              rw [h2, nat_sub_mul_div _ m p hp hle_mp, hf30.2]
            have hiE_eq : sixHarmonicIndicator n p k 0 = if 1 ≤ m + f30Plus then 1 else 0 := by
              unfold sixHarmonicIndicator; simp [hk_right]
            have hiO_eq : sixHarmonicIndicator n p k 1 = if f30Minus - m < m + f30Plus then 1 else 0 := by
              unfold sixHarmonicIndicator; simp [show ¬ Even (1 : ℕ) by decide, hk_right, hk_left]
            have hio : sixHarmonicIndicator n p k 1 ≤ sixHarmonicIndicator n p k 0 := by
              rw [hiE_eq, hiO_eq]; split_ifs <;> omega
            have hstep := addBranchSlotsPacked_sound n p k hp hio c0 p0 hr0
            rw [hord, hda_eq, hnz_eq, hbv_eq, hiE_eq, hiO_eq, hord] at hstep
            obtain ⟨d1, hr_mid, hd1_sum, hd1_dom⟩ := hstep
            obtain ⟨d2, hr_end, hd2_sum, hd2_dom⟩ := ih _ _ hr_mid
            refine ⟨fun v => d1 v + d2 v, ?_, ?_, fun v hv => ?_⟩
            · convert hr_end using 1
              · ext v; ring
              · rw [show (Np - mkPlus m g == 0) = decide (Np - mkPlus m g = 0) from
                  Bool.eq_iff_iff.mpr (by simp)]
            · rw [Finset.sum_add_distrib, Finset.sum_range_succ]; omega
            · rw [Finset.sum_add_distrib, Finset.sum_range_succ]
              simp only [hle25, dite_true]
              have hdom1 := hd1_dom v hv
              rw [← hord] at hdom1
              exact Nat.add_le_add (hd2_dom v hv) hdom1 |>.trans (by omega)
      -- Induction for `addMinus`: covers `{x ∈ Tc : ∃ m0 < rem, x.val = (m0 + 1) * p - c.val}`
      have haddMinus : ∀ (rem : ℕ) (c0 : ℕ → ℕ) (p0 : ℕ), HistRepr c0 p0 →
          ∃ d : ℕ → ℕ,
            HistRepr (fun v => c0 v + d v)
              (checkHighTile.buildStrips.addMinus vFact mkMinus g Np Nz f30Plus f30Minus rem p0) ∧
            (∑ v ∈ Finset.Icc 1 18, d v) ≤
              ∑ m0 ∈ Finset.range rem, mkMinus (m0 + 1) g ∧
            ∀ v ∈ Finset.Icc 1 18,
              (∑ m0 ∈ Finset.range rem,
                if hle : (m0 + 1) * p - c.val ≤ 25 * n then
                  ((Finset.range (sixPoleOrder n (sixHalfPole n ⟨(m0 + 1) * p - c.val, by omega⟩))).filter
                    (fun a => v ≤ sixRefinedSlotCost n p (sixHalfPole n ⟨(m0 + 1) * p - c.val, by omega⟩) a)).card
                else 0) ≤
              ∑ w ∈ Finset.Icc v 18, d w := by
        intro rem
        induction rem with
        | zero =>
          intro c0 p0 hr0
          exact ⟨fun _ => 0, by rw [checkHighTile.buildStrips.addMinus.eq_def]; simpa using hr0, by simp, by simp⟩
        | succ m0 ih =>
          intro c0 p0 hr0
          rw [checkHighTile.buildStrips.addMinus.eq_def]
          dsimp +zetaHave only
          let m := m0 + 1
          by_cases hmk0 : mkMinus m g = 0
          · simp only [show m0 + 1 = m from rfl, hmk0, beq_self_eq_true, ite_true]
            obtain ⟨d, hr1, hsum1, hdom1⟩ := ih c0 p0 hr0
            refine ⟨d, hr1, by rw [Finset.sum_range_succ, hmk0, add_zero]; exact hsum1, fun v hv => ?_⟩
            rw [Finset.sum_range_succ]
            have hm_term : (if hle : m * p - c.val ≤ 25 * n then
                ((Finset.range (sixPoleOrder n (sixHalfPole n ⟨m * p - c.val, by omega⟩))).filter
                  (fun a => v ≤ sixRefinedSlotCost n p (sixHalfPole n ⟨m * p - c.val, by omega⟩) a)).card
                else 0) = 0 := by
              split_ifs with hle
              · rw [hmkMinus_eq_ord m (by omega) hle, hmk0]; simp
              · rfl
            rw [hm_term, add_zero]; exact hdom1 v hv
          · have hne : (mkMinus m g == 0) = false := beq_false_of_ne hmk0
            simp only [show m0 + 1 = m from rfl, hne, Bool.false_eq_true, ite_false]
            have hle25 : m * p - c.val ≤ 25 * n := hmkMinus_pos_le25 m (by omega) hmk0
            have hcm : c.val ≤ m * p := by
              have hm1 : 1 ≤ m := by omega
              nlinarith only [hm1, hchalf]
            let x : Fin (25 * n + 1) := ⟨m * p - c.val, by omega⟩
            let k := sixHalfPole n x
            have hord : sixPoleOrder n k = mkMinus m g := hmkMinus_eq_ord m (by omega) hle25
            have hfold_x : foldMod p hp (-(x.val : ℤ)) = c := by
              unfold foldMod
              dsimp +zetaHave only
              have hmod : (-(x.val : ℤ)) % (p : ℤ) = (c.val : ℤ) := by
                have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
                have hxZ : (x.val : ℤ) = (m : ℤ) * (p : ℤ) - (c.val : ℤ) := by
                  dsimp [x]; rw [Nat.cast_sub hcm]; push_cast; ring
                have hrew : -(x.val : ℤ) = (c.val : ℤ) + (-(m : ℤ)) * (p : ℤ) := by rw [hxZ]; ring
                rw [hrew, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
              simp only [hmod]
              have hto : ((c.val : ℤ)).toNat = c.val := by omega
              simp only [hto]
              have hle_half : c.val ≤ p / 2 := by omega
              simp only [hle_half, dite_true]
            obtain ⟨hda_eq, hnz_eq, hbv_eq⟩ := hsite_counts x hfold_x
            have hk_right : (k - 40 * n - 1) / p = m + f30Minus := by
              have h1 : k - 40 * n - 1 = (30 * n - c.val) + m * p := by
                dsimp [k, sixHalfPole, sixCenter, x]; omega
              rw [h1, Nat.add_mul_div_right _ _ hp, hf30.2]; omega
            have hk_left : (sixReflectedPole n k - 40 * n - 1) / p = f30Plus - m := by
              have hle_mp : m * p ≤ 30 * n + c.val := by omega
              have h2 : sixReflectedPole n k - 40 * n - 1 = (30 * n + c.val) - m * p := by
                dsimp [k, sixReflectedPole, sixHalfPole, sixCenter, x]; omega
              rw [h2, nat_sub_mul_div _ m p hp hle_mp, hf30.1]
            have hiE_eq : sixHarmonicIndicator n p k 0 = if 1 ≤ m + f30Minus then 1 else 0 := by
              unfold sixHarmonicIndicator; simp [hk_right]
            have hiO_eq : sixHarmonicIndicator n p k 1 = if f30Plus - m < m + f30Minus then 1 else 0 := by
              unfold sixHarmonicIndicator; simp [show ¬ Even (1 : ℕ) by decide, hk_right, hk_left]
            have hio : sixHarmonicIndicator n p k 1 ≤ sixHarmonicIndicator n p k 0 := by
              rw [hiE_eq, hiO_eq]; split_ifs <;> omega
            have hstep := addBranchSlotsPacked_sound n p k hp hio c0 p0 hr0
            rw [hord, hda_eq, hnz_eq, hbv_eq, hiE_eq, hiO_eq, hord] at hstep
            obtain ⟨d1, hr_mid, hd1_sum, hd1_dom⟩ := hstep
            obtain ⟨d2, hr_end, hd2_sum, hd2_dom⟩ := ih _ _ hr_mid
            refine ⟨fun v => d1 v + d2 v, ?_, ?_, fun v hv => ?_⟩
            · convert hr_end using 1
              · ext v; ring
              · rw [show (Np - mkMinus m g == 0) = decide (Np - mkMinus m g = 0) from
                  Bool.eq_iff_iff.mpr (by simp)]
            · dsimp only [m] at hd1_sum
              rw [Finset.sum_add_distrib, Finset.sum_range_succ]; omega
            · rw [Finset.sum_add_distrib, Finset.sum_range_succ]
              simp only [show m0 + 1 = m from rfl, hle25, dite_true]
              have hdom1 := hd1_dom v hv
              rw [← hord] at hdom1
              exact Nat.add_le_add (hd2_dom v hv) hdom1 |>.trans (by omega)
      -- Combine `addPlus (k25 + 1)` and `addMinus (k25 + 1)`
      obtain ⟨dP, hrP, hsumP, hdomP⟩ := haddPlus (k25 + 1) (fun _ => 0) 0 histRepr_zero
      obtain ⟨dM, hrM, hsumM, hdomM⟩ := haddMinus (k25 + 1) _ _ hrP
      have hk25_eq : 25 * n / p = k25 := by
        have hq7_split : q7 = 2 * k25 + q7 % 2 := (Nat.div_add_mod q7 2).symm
        have hq7_mod : q7 % 2 ≤ 1 := by omega
        have h1 : q7 * p ≤ 50 * n := h7.1
        have h2 : 50 * n < (q7 + 1) * p := h7.2.1
        rw [hq7_split] at h1 h2
        have ha : k25 * p ≤ 25 * n := by
          have h0' : 2 * k25 * p ≤ 50 * n :=
            (Nat.mul_le_mul_right p (Nat.le_add_right (2 * k25) (q7 % 2))).trans h1
          have h0'' : 2 * (k25 * p) ≤ 50 * n := by simpa [mul_assoc] using h0'
          omega
        have hb : 25 * n < (k25 + 1) * p := by
          have h0' : 50 * n < 2 * (k25 + 1) * p :=
            lt_of_lt_of_le h2 (Nat.mul_le_mul_right p (by omega))
          have h0'' : 50 * n < 2 * ((k25 + 1) * p) := by simpa [mul_assoc] using h0'
          omega
        have hge := (Nat.le_div_iff_mul_le hp).mpr ha
        have hlt' := (Nat.div_lt_iff_lt_mul hp).mpr hb
        omega
      -- Show total count `≤ Np < 256` so no bin overflows 256
      have htot_le_Np : (∑ m ∈ Finset.range (k25 + 1), mkPlus m g) +
          (∑ m0 ∈ Finset.range (k25 + 1), mkMinus (m0 + 1) g) ≤ Np := by
        -- Even cleaner: sum `deltaOf` directly from `mkPlus` and `mkMinus`!
        -- Actually, for each radius `k < 8`:
        -- `#{m ≤ k25 : m*p + c ≤ rad*n} + #{1 ≤ m ≤ k25+1 : m*p - c ≤ rad*n} = deltaOf (getQ2 k) pos g`!
        have hrad_sum : ∀ (k : ℕ) (hk : k < 8),
            (∑ m ∈ Finset.range (k25 + 1),
              if m < getQ2 k / 2 || (m == getQ2 k / 2 && (getQ2 k % 2 == 1 || g ≤ indexOfNat t.perm k)) then 1 else 0) +
            (∑ m0 ∈ Finset.range (k25 + 1),
              if m0 + 1 ≤ getQ2 k / 2 || (m0 + 1 == getQ2 k / 2 + 1 && getQ2 k % 2 == 1 && indexOfNat t.perm k < g) then 1 else 0) ≤
            deltaOf (getQ2 k) (indexOfNat t.perm k) g := by
          intro k hk
          have hqr_le : getQ2 k / 2 ≤ k25 := by
            have hq_le : getQ2 k ≤ q7 := by
              have hrad25 : radiusValNat k ≤ 25 := radiusValNat_le_25 k hk
              have hq1 : getQ2 k * p ≤ 50 * n := by
                have hb : getQ2 k * p ≤ 2 * radiusValNat k * n := by
                  match k, hk with
                  | 0, _ => exact h0.1
                  | 1, _ => exact h1.1
                  | 2, _ => exact h2.1
                  | 3, _ => exact h3.1
                  | 4, _ => exact h4.1
                  | 5, _ => exact h5.1
                  | 6, _ => exact h6.1
                  | 7, _ => exact h7.1
                have : 2 * radiusValNat k * n ≤ 50 * n := by nlinarith only [hrad25]
                omega
              have hq2 := h7.2.1
              have : getQ2 k < q7 + 1 := by nlinarith only [hq1, hq2, hp]
              omega
            dsimp [k25]; omega
          let qr := getQ2 k / 2
          have hS1 : (∑ m ∈ Finset.range (k25 + 1),
              if m < qr || (m == qr && (getQ2 k % 2 == 1 || g ≤ indexOfNat t.perm k)) then 1 else 0) =
              qr + (if getQ2 k % 2 = 1 ∨ g ≤ indexOfNat t.perm k then 1 else 0) := by
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
            by_cases hc' : getQ2 k % 2 = 1 ∨ g ≤ indexOfNat t.perm k
            · have heq : (Finset.range (k25 + 1)).filter
                  (fun m => m < qr || (m == qr && (getQ2 k % 2 == 1 || g ≤ indexOfNat t.perm k))) =
                  Finset.range (qr + 1) := by
                ext m; simp only [Finset.mem_filter, Finset.mem_range, Bool.or_eq_true,
                  Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
                constructor
                · rintro ⟨_, h1 | ⟨h2, _⟩⟩ <;> omega
                · intro hm
                  refine ⟨by omega, ?_⟩
                  by_cases hlt : m < qr
                  · exact Or.inl hlt
                  · exact Or.inr ⟨by omega, hc'⟩
              rw [heq, Finset.card_range]; simp only [hc', ite_true]
            · have heq : (Finset.range (k25 + 1)).filter
                  (fun m => m < qr || (m == qr && (getQ2 k % 2 == 1 || g ≤ indexOfNat t.perm k))) =
                  Finset.range qr := by
                ext m; simp only [Finset.mem_filter, Finset.mem_range, Bool.or_eq_true,
                  Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
                constructor
                · rintro ⟨_, h1 | ⟨_, h2⟩⟩
                  · exact h1
                  · exact absurd h2 hc'
                · intro hm; exact ⟨by omega, Or.inl hm⟩
              rw [heq, Finset.card_range]; simp only [hc', ite_false]; omega
          have hS2 : (∑ m0 ∈ Finset.range (k25 + 1),
              if m0 + 1 ≤ qr || (m0 + 1 == qr + 1 && getQ2 k % 2 == 1 && indexOfNat t.perm k < g) then 1 else 0) =
              qr + (if getQ2 k % 2 = 1 ∧ indexOfNat t.perm k < g then 1 else 0) := by
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
            by_cases hc' : getQ2 k % 2 = 1 ∧ indexOfNat t.perm k < g
            · have heq : (Finset.range (k25 + 1)).filter
                  (fun m0 => m0 + 1 ≤ qr || (m0 + 1 == qr + 1 && getQ2 k % 2 == 1 && indexOfNat t.perm k < g)) =
                  Finset.range (qr + 1) := by
                ext m0; simp only [Finset.mem_filter, Finset.mem_range, Bool.or_eq_true,
                  Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
                constructor
                · rintro ⟨_, h1 | ⟨⟨h2, _⟩, _⟩⟩ <;> omega
                · intro hm0
                  refine ⟨by omega, ?_⟩
                  by_cases hle : m0 + 1 ≤ qr
                  · exact Or.inl hle
                  · exact Or.inr ⟨⟨by omega, hc'.1⟩, hc'.2⟩
              rw [heq, Finset.card_range]; simp only [hc', and_self, ite_true]
            · have heq : (Finset.range (k25 + 1)).filter
                  (fun m0 => m0 + 1 ≤ qr || (m0 + 1 == qr + 1 && getQ2 k % 2 == 1 && indexOfNat t.perm k < g)) =
                  Finset.range qr := by
                ext m0; simp only [Finset.mem_filter, Finset.mem_range, Bool.or_eq_true,
                  Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
                constructor
                · rintro ⟨_, h1 | ⟨⟨_, h2⟩, h3⟩⟩
                  · omega
                  · exact absurd ⟨h2, h3⟩ hc'
                · intro hm0; exact ⟨by omega, Or.inl (by omega)⟩
              rw [heq, Finset.card_range]; simp only [hc', ite_false]; omega
          rw [hS1, hS2]
          dsimp only [deltaOf, qr]
          have hmod2 : getQ2 k % 2 = 0 ∨ getQ2 k % 2 = 1 := by omega
          rcases hmod2 with h0' | h1'
          · simp only [h0', zero_ne_one, false_or, false_and, ite_false, beq_self_eq_true, ite_true]
            split_ifs <;> omega
          · simp only [h1', true_or, true_and, ite_true, show (1 == 0) = false from rfl, Bool.false_eq_true, ite_false]
            split_ifs <;> omega
        have s0 := hrad_sum 0 (by omega); have s1 := hrad_sum 1 (by omega)
        have s2 := hrad_sum 2 (by omega); have s3 := hrad_sum 3 (by omega)
        have s4 := hrad_sum 4 (by omega); have s5 := hrad_sum 5 (by omega)
        have s6 := hrad_sum 6 (by omega); have s7 := hrad_sum 7 (by omega)
        simp only [getQ2] at s0 s1 s2 s3 s4 s5 s6 s7
        dsimp only [mkPlus, mkMinus, Np]
        simp only [Finset.sum_add_distrib]
        have hmul_ite : ∀ (P : ℕ → Prop) [DecidablePred P] (w : ℕ),
            (∑ i ∈ Finset.range (k25 + 1), if P i then w else 0) =
              w * ∑ i ∈ Finset.range (k25 + 1), if P i then 1 else 0 := by
          intro P _ w; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; split_ifs <;> ring
        have hmul2 := fun (P : ℕ → Prop) [DecidablePred P] => hmul_ite P 2
        have hmul5 := fun (P : ℕ → Prop) [DecidablePred P] => hmul_ite P 5
        simp only [hmul2, hmul5]
        dsimp [p0, p1, p2, p3, p4, p5, p6, p7] at s0 s1 s2 s3 s4 s5 s6 s7 ⊢
        omega
      let cntTot : ℕ → ℕ := fun v => 0 + dP v + dM v
      have hsmall : ∀ v ∈ Finset.Icc 1 18, cntTot v < 256 := by
        intro v hv
        have hle1 : cntTot v ≤ ∑ w ∈ Finset.Icc 1 18, cntTot w :=
          Finset.single_le_sum (f := cntTot) (fun _ _ => Nat.zero_le _) hv
        have hsum_tot : ∑ w ∈ Finset.Icc 1 18, cntTot w ≤ Np := by
          have : ∑ w ∈ Finset.Icc 1 18, cntTot w =
              (∑ w ∈ Finset.Icc 1 18, dP w) + ∑ w ∈ Finset.Icc 1 18, dM w := by
            simp [cntTot, Finset.sum_add_distrib]
          omega
        omega
      have hsuf := packedToSuffixCounts_spec hrM hsmall
      -- Apply `jointCapFromN_sound`!
      apply jointCapFromN_sound (clsSet c) (sixSlotCost n p)
        (fun u _ => sixRefinedSlotCost_le_18 n p _ _ hp) _ ?_ t.q j hj1 hj18
      intro v hv
      rw [hsuf v hv]
      have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
      -- Split `((clsSet c).filter (v ≤ sixSlotCost))` into `+` branches (`m < k25 + 1`) and `-` branches (`m0 < k25 + 1`)
      have hcard_le : ((clsSet c).filter (fun u => v ≤ sixSlotCost n p u)).card ≤
          (∑ m ∈ Finset.range (k25 + 1),
            if hle : m * p + c.val ≤ 25 * n then
              ((Finset.range (sixPoleOrder n (sixHalfPole n ⟨m * p + c.val, by omega⟩))).filter
                (fun a => v ≤ sixRefinedSlotCost n p (sixHalfPole n ⟨m * p + c.val, by omega⟩) a)).card
            else 0) +
          (∑ m0 ∈ Finset.range (k25 + 1),
            if hle : (m0 + 1) * p - c.val ≤ 25 * n then
              ((Finset.range (sixPoleOrder n (sixHalfPole n ⟨(m0 + 1) * p - c.val, by omega⟩))).filter
                (fun a => v ≤ sixRefinedSlotCost n p (sixHalfPole n ⟨(m0 + 1) * p - c.val, by omega⟩) a)).card
            else 0) := by
        let SP := (Finset.range (k25 + 1)).sigma fun m =>
          if hle : m * p + c.val ≤ 25 * n then
            (Finset.range (sixPoleOrder n (sixHalfPole n ⟨m * p + c.val, by omega⟩))).filter
              (fun a => v ≤ sixRefinedSlotCost n p (sixHalfPole n ⟨m * p + c.val, by omega⟩) a)
          else ∅
        let SM := (Finset.range (k25 + 1)).sigma fun m0 =>
          if hle : (m0 + 1) * p - c.val ≤ 25 * n then
            (Finset.range (sixPoleOrder n (sixHalfPole n ⟨(m0 + 1) * p - c.val, by omega⟩))).filter
              (fun a => v ≤ sixRefinedSlotCost n p (sixHalfPole n ⟨(m0 + 1) * p - c.val, by omega⟩) a)
          else ∅
        have hSP_card : SP.card = ∑ m ∈ Finset.range (k25 + 1),
            if hle : m * p + c.val ≤ 25 * n then
              ((Finset.range (sixPoleOrder n (sixHalfPole n ⟨m * p + c.val, by omega⟩))).filter
                (fun a => v ≤ sixRefinedSlotCost n p (sixHalfPole n ⟨m * p + c.val, by omega⟩) a)).card
            else 0 := by
          rw [Finset.card_sigma]; apply Finset.sum_congr rfl; intro m _; split_ifs <;> simp
        have hSM_card : SM.card = ∑ m0 ∈ Finset.range (k25 + 1),
            if hle : (m0 + 1) * p - c.val ≤ 25 * n then
              ((Finset.range (sixPoleOrder n (sixHalfPole n ⟨(m0 + 1) * p - c.val, by omega⟩))).filter
                (fun a => v ≤ sixRefinedSlotCost n p (sixHalfPole n ⟨(m0 + 1) * p - c.val, by omega⟩) a)).card
            else 0 := by
          rw [Finset.card_sigma]; apply Finset.sum_congr rfl; intro m0 _; split_ifs <;> simp
        rw [← hSP_card, ← hSM_card, ← Finset.card_disjSum]
        let mapU : Fin (sixSlotCount n) → Sum (Σ _ : ℕ, ℕ) (Σ _ : ℕ, ℕ) := fun u =>
          let ta := (sixSlotEquiv n).symm u
          if (p : ℤ) ∣ (ta.1.val : ℤ) - (c.val : ℤ) then
            Sum.inl ⟨ta.1.val / p, ta.2.val⟩
          else
            Sum.inr ⟨ta.1.val / p, ta.2.val⟩
        apply Finset.card_le_card_of_injOn mapU
        · intro u hu
          have hcls := (Finset.mem_filter.mp hu).1
          have hvle := (Finset.mem_filter.mp hu).2
          have hfold := (Finset.mem_filter.mp hcls).2
          let ta := (sixSlotEquiv n).symm u
          have ha_lt : ta.2.val < sixPoleOrder n (sixHalfPole n ta.1) := by
            by_contra hge
            have h0 : sixSlotCost n p u = 0 := by
              unfold sixSlotCost sixRefinedSlotCost
              have hemp : (Finset.range (sixPoleOrder n (sixHalfPole n ta.1))).filter
                  (fun r => ta.2.val ≤ r) = ∅ := by
                ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]; omega
              change ((Finset.range _).filter _).sup _ = 0
              rw [hemp, Finset.sup_empty]; rfl
            omega
          have hcong := foldMod_congruence p hp (-(ta.1.val : ℤ))
          change foldMod p hp (-(ta.1.val : ℤ)) = c at hfold
          rw [hfold] at hcong
          have hor : (p : ℤ) ∣ (ta.1.val : ℤ) - (c.val : ℤ) ∨ (p : ℤ) ∣ (ta.1.val : ℤ) + (c.val : ℤ) := by
            unfold foldSign at hcong; split_ifs at hcong
            · right; obtain ⟨k, hk⟩ := hcong; exact ⟨-k, by linarith only [hk]⟩
            · left; obtain ⟨k, hk⟩ := hcong; exact ⟨k, by linarith only [hk]⟩
          rw [Finset.mem_coe, Finset.mem_disjSum]
          dsimp only [mapU]
          split_ifs with hd1
          · left
            refine ⟨⟨ta.1.val / p, ta.2.val⟩, ?_, rfl⟩
            rw [Finset.mem_sigma]
            have hmod : ta.1.val % p = c.val := by
              obtain ⟨k, hk⟩ := hd1
              have h1 : (ta.1.val : ℤ) = (c.val : ℤ) + (p : ℤ) * k := by linarith only [hk]
              have h2 : (ta.1.val : ℤ) % (p : ℤ) = (c.val : ℤ) := by
                rw [h1, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
              exact_mod_cast h2
            have heq_t : (ta.1.val / p) * p + c.val = ta.1.val := by
              have hdm := Nat.div_add_mod ta.1.val p; rw [hmod] at hdm; linarith only [hdm]
            have hm_lt : ta.1.val / p < k25 + 1 := by
              have hle : ta.1.val ≤ 25 * n := by have := ta.1.isLt; omega
              have : ta.1.val / p ≤ 25 * n / p := Nat.div_le_div_right hle
              omega
            refine ⟨Finset.mem_range.mpr hm_lt, ?_⟩
            have hle25 : (ta.1.val / p) * p + c.val ≤ 25 * n := by have := ta.1.isLt; omega
            simp only [hle25, dite_true, Finset.mem_filter, Finset.mem_range]
            have hfin : (⟨(ta.1.val / p) * p + c.val, by omega⟩ : Fin (25 * n + 1)) = ta.1 :=
              Fin.ext heq_t
            rw [hfin]
            exact ⟨ha_lt, hvle⟩
          · right
            have hd2 : (p : ℤ) ∣ (ta.1.val : ℤ) + (c.val : ℤ) := hor.resolve_left hd1
            refine ⟨⟨ta.1.val / p, ta.2.val⟩, ?_, rfl⟩
            rw [Finset.mem_sigma]
            have hmod : ta.1.val % p = p - c.val := by
              obtain ⟨k, hk⟩ := hd2
              have h1 : (ta.1.val : ℤ) = ((p - c.val : ℕ) : ℤ) + (p : ℤ) * (k - 1) := by
                rw [Nat.cast_sub (by omega)]; linarith only [hk]
              have h2 : (ta.1.val : ℤ) % (p : ℤ) = ((p - c.val : ℕ) : ℤ) := by
                rw [h1, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
              exact_mod_cast h2
            have heq_t : (ta.1.val / p + 1) * p - c.val = ta.1.val := by
              have := Nat.div_add_mod ta.1.val p; rw [hmod] at this
              have : (ta.1.val / p + 1) * p = p * (ta.1.val / p) + p := by ring
              omega
            have hm_lt : ta.1.val / p < k25 + 1 := by
              have hle : ta.1.val ≤ 25 * n := by have := ta.1.isLt; omega
              have : ta.1.val / p ≤ 25 * n / p := Nat.div_le_div_right hle
              omega
            refine ⟨Finset.mem_range.mpr hm_lt, ?_⟩
            have hle25 : (ta.1.val / p + 1) * p - c.val ≤ 25 * n := by have := ta.1.isLt; omega
            simp only [hle25, dite_true, Finset.mem_filter, Finset.mem_range]
            have hfin : (⟨(ta.1.val / p + 1) * p - c.val, by omega⟩ : Fin (25 * n + 1)) = ta.1 :=
              Fin.ext heq_t
            rw [hfin]
            exact ⟨ha_lt, hvle⟩
        · intro u₁ hu₁ u₂ hu₂ heq
          have get_mod : ∀ u ∈ (clsSet c).filter (fun u => v ≤ sixSlotCost n p u),
              ((p : ℤ) ∣ (((sixSlotEquiv n).symm u).1.val : ℤ) - (c.val : ℤ) →
                ((sixSlotEquiv n).symm u).1.val % p = c.val) ∧
              (¬ ((p : ℤ) ∣ (((sixSlotEquiv n).symm u).1.val : ℤ) - (c.val : ℤ)) →
                ((sixSlotEquiv n).symm u).1.val % p = p - c.val) := by
            intro u hu
            have hfold := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
            have hcong := foldMod_congruence p hp (-(((sixSlotEquiv n).symm u).1.val : ℤ))
            change foldMod p hp (-(((sixSlotEquiv n).symm u).1.val : ℤ)) = c at hfold
            rw [hfold] at hcong
            have hor : (p : ℤ) ∣ (((sixSlotEquiv n).symm u).1.val : ℤ) - (c.val : ℤ) ∨
                (p : ℤ) ∣ (((sixSlotEquiv n).symm u).1.val : ℤ) + (c.val : ℤ) := by
              unfold foldSign at hcong; split_ifs at hcong
              · right; obtain ⟨k, hk⟩ := hcong; exact ⟨-k, by linarith only [hk]⟩
              · left; obtain ⟨k, hk⟩ := hcong; exact ⟨k, by linarith only [hk]⟩
            constructor
            · intro hd1
              obtain ⟨k, hk⟩ := hd1
              have h1 : (((sixSlotEquiv n).symm u).1.val : ℤ) = (c.val : ℤ) + (p : ℤ) * k := by linarith only [hk]
              have h2 : (((sixSlotEquiv n).symm u).1.val : ℤ) % (p : ℤ) = (c.val : ℤ) := by
                rw [h1, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
              exact_mod_cast h2
            · intro hnd1
              obtain ⟨k, hk⟩ := hor.resolve_left hnd1
              have h1 : (((sixSlotEquiv n).symm u).1.val : ℤ) = ((p - c.val : ℕ) : ℤ) + (p : ℤ) * (k - 1) := by
                rw [Nat.cast_sub (by omega)]; linarith only [hk]
              have h2 : (((sixSlotEquiv n).symm u).1.val : ℤ) % (p : ℤ) = ((p - c.val : ℕ) : ℤ) := by
                rw [h1, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
              exact_mod_cast h2
          have gm1 := get_mod u₁ hu₁
          have gm2 := get_mod u₂ hu₂
          dsimp only [mapU] at heq
          by_cases hd1 : (p : ℤ) ∣ (((sixSlotEquiv n).symm u₁).1.val : ℤ) - (c.val : ℤ)
          · by_cases hd2 : (p : ℤ) ∣ (((sixSlotEquiv n).symm u₂).1.val : ℤ) - (c.val : ℤ)
            · simp only [hd1, hd2, ite_true] at heq
              have hdiv : ((sixSlotEquiv n).symm u₁).1.val / p = ((sixSlotEquiv n).symm u₂).1.val / p :=
                congrArg Sigma.fst (Sum.inl.inj heq)
              have ha : ((sixSlotEquiv n).symm u₁).2.val = ((sixSlotEquiv n).symm u₂).2.val := by
                simpa using congrArg Sigma.snd (Sum.inl.inj heq)
              have h1 := Nat.div_add_mod ((sixSlotEquiv n).symm u₁).1.val p
              have h2 := Nat.div_add_mod ((sixSlotEquiv n).symm u₂).1.val p
              have ht : ((sixSlotEquiv n).symm u₁).1.val = ((sixSlotEquiv n).symm u₂).1.val := by
                rw [gm1.1 hd1] at h1; rw [gm2.1 hd2] at h2; rw [hdiv] at h1; omega
              exact (sixSlotEquiv n).symm.injective (Prod.ext (Fin.ext ht) (Fin.ext ha))
            · simp only [hd1, hd2, ite_true, ite_false] at heq
              exact absurd heq (by simp)
          · by_cases hd2 : (p : ℤ) ∣ (((sixSlotEquiv n).symm u₂).1.val : ℤ) - (c.val : ℤ)
            · simp only [hd1, hd2, ite_true, ite_false] at heq
              exact absurd heq (by simp)
            · simp only [hd1, hd2, ite_false] at heq
              have hdiv : ((sixSlotEquiv n).symm u₁).1.val / p = ((sixSlotEquiv n).symm u₂).1.val / p :=
                congrArg Sigma.fst (Sum.inr.inj heq)
              have ha : ((sixSlotEquiv n).symm u₁).2.val = ((sixSlotEquiv n).symm u₂).2.val := by
                simpa using congrArg Sigma.snd (Sum.inr.inj heq)
              have h1 := Nat.div_add_mod ((sixSlotEquiv n).symm u₁).1.val p
              have h2 := Nat.div_add_mod ((sixSlotEquiv n).symm u₂).1.val p
              have ht : ((sixSlotEquiv n).symm u₁).1.val = ((sixSlotEquiv n).symm u₂).1.val := by
                rw [gm1.2 hd1] at h1; rw [gm2.2 hd2] at h2; rw [hdiv] at h1; omega
              exact (sixSlotEquiv n).symm.injective (Prod.ext (Fin.ext ht) (Fin.ext ha))
      have hdom_tot : (∑ w ∈ Finset.Icc v 18, (0 + dP w + dM w)) =
          (∑ w ∈ Finset.Icc v 18, dP w) + ∑ w ∈ Finset.Icc v 18, dM w := by
        simp [Finset.sum_add_distrib]
      rw [hdom_tot]
      exact hcard_le.trans (Nat.add_le_add (hdomP v hv) (hdomM v hv))
  -- Combine `Bdy` + 13 open strips `Strip g` for each layer `j ∈ Icc 1 18`
  have hlayer_bound : ∀ j ∈ Finset.Icc (1 : ℕ) 18,
      min ((rank n : ℝ)) (((slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℝ)) ≤
        (n : ℝ) * min (15 : ℝ)
          ((((highTileLayerAff t j).1 : ℝ) + ((highTileLayerAff t j).2 : ℝ) * ((p : ℝ) / (n : ℝ))) / 2) +
        5670 := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj18 : j ≤ 18 := (Finset.mem_Icc.mp hj).2
    have htotal_j : ((slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℝ) ≤
        (∑ c ∈ Bdy, (capClass j c : ℝ)) +
        ∑ g ∈ Finset.range 13, ∑ c ∈ Strip g, (capClass j c : ℝ) := by
      rw [hfiber j, Nat.cast_sum]
      calc
        ∑ c : Fin (p / 2 + 1), (capClass j c : ℝ)
            ≤ ∑ c : Fin (p / 2 + 1),
                ((if c ∈ Bdy then (capClass j c : ℝ) else 0) +
                 ∑ g ∈ Finset.range 13, if c ∈ Strip g then (capClass j c : ℝ) else 0) := by
              apply Finset.sum_le_sum; intro c _
              rcases hcover_c c with hcb | ⟨g₀, hg₀, hcg⟩
              · have hnn : 0 ≤ ∑ g ∈ Finset.range 13, if c ∈ Strip g then (capClass j c : ℝ) else 0 :=
                  Finset.sum_nonneg (fun _ _ => by split_ifs; exact Nat.cast_nonneg _; exact le_rfl)
                simp only [hcb, ite_true]
                exact le_add_of_nonneg_right hnn
              · have h1 : (capClass j c : ℝ) ≤
                    ∑ g ∈ Finset.range 13, if c ∈ Strip g then (capClass j c : ℝ) else 0 := by
                  have := Finset.single_le_sum
                    (f := fun g => if c ∈ Strip g then (capClass j c : ℝ) else 0)
                    (fun _ _ => by split_ifs; exact Nat.cast_nonneg _; exact le_rfl) hg₀
                  simp only [hcg, ite_true] at this
                  exact this
                have hnn : 0 ≤ if c ∈ Bdy then (capClass j c : ℝ) else 0 := by
                  split_ifs; exact Nat.cast_nonneg _; exact le_rfl
                exact le_add_of_nonneg_of_le hnn h1
        _ = (∑ c : Fin (p / 2 + 1), if c ∈ Bdy then (capClass j c : ℝ) else 0) +
            ∑ c : Fin (p / 2 + 1), ∑ g ∈ Finset.range 13,
              if c ∈ Strip g then (capClass j c : ℝ) else 0 := Finset.sum_add_distrib
        _ = (∑ c ∈ Bdy, (capClass j c : ℝ)) +
            ∑ g ∈ Finset.range 13, ∑ c ∈ Strip g, (capClass j c : ℝ) := by
              congr 1
              · rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
              · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro g _
                rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hBdy_sum : (∑ c ∈ Bdy, (capClass j c : ℝ)) ≤ 2940 := by
      calc ∑ c ∈ Bdy, (capClass j c : ℝ)
          ≤ ∑ _c ∈ Bdy, (210 : ℝ) := Finset.sum_le_sum (fun c _ => by exact_mod_cast hcap_le_210 j hj1 c)
        _ = (Bdy.card : ℝ) * 210 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 14 * 210 := by
              have hbc : (Bdy.card : ℝ) ≤ 14 := by exact_mod_cast hBdy_card
              linarith only [hbc]
        _ = 2940 := by norm_num
    have hStrip_sum : ∀ g ∈ Finset.range 13,
        (∑ c ∈ Strip g, (capClass j c : ℝ)) ≤
          ((n : ℝ) / 2) * ((stripMult j g : ℝ) * (evalR (ptAt (g + 1)) - evalR (ptAt g))) + 210 := by
      intro g hg
      have hg13 : g < 13 := Finset.mem_range.mp hg
      have hdiff_nn : 0 ≤ evalR (ptAt (g + 1)) - evalR (ptAt g) :=
        sub_nonneg.mpr (hpt_monoR (by omega) (by omega))
      by_cases hemp : Strip g = ∅
      · rw [hemp, Finset.sum_empty]
        have hnn : 0 ≤ ((n : ℝ) / 2) * ((stripMult j g : ℝ) * (evalR (ptAt (g + 1)) - evalR (ptAt g))) :=
          mul_nonneg (div_nonneg hnR.le (by norm_num)) (mul_nonneg (Nat.cast_nonneg _) hdiff_nn)
        linarith only [hnn]
      · have hcard_le : ((Strip g).card : ℝ) ≤
            ((n : ℝ) / 2) * (evalR (ptAt (g + 1)) - evalR (ptAt g)) + 1 := by
          have himg : ((Strip g).image (fun c : Fin (p / 2 + 1) => c.val)).card = (Strip g).card :=
            Finset.card_image_of_injective _ Fin.val_injective
          rw [← himg]
          have hnat := nat_open_interval_card_le
            (((n : ℝ) / 2) * evalR (ptAt g)) (((n : ℝ) / 2) * evalR (ptAt (g + 1)))
            (mul_le_mul_of_nonneg_left (hpt_monoR (by omega) (by omega)) (div_nonneg hnR.le (by norm_num)))
            ((Strip g).image (fun c : Fin (p / 2 + 1) => c.val)) (by
              intro m hm
              obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hm
              have hmem := (Finset.mem_filter.mp hc).2
              have h1 : (evalZ (ptAt g) : ℝ) < 2 * (c.val : ℝ) := by exact_mod_cast hmem.1
              have h2 : 2 * (c.val : ℝ) < (evalZ (ptAt (g + 1)) : ℝ) := by exact_mod_cast hmem.2
              rw [hevalZR] at h1 h2
              constructor <;> linarith only [h1, h2])
          linarith only [hnat]
        have hcap_min : ∀ c ∈ Strip g, (capClass j c : ℝ) ≤ min (stripMult j g : ℝ) 210 := by
          intro c hc
          exact le_min (by exact_mod_cast hstrip_cap g hg13 c hc j hj)
            (by exact_mod_cast hcap_le_210 j hj1 c)
        have hsum_le : (∑ c ∈ Strip g, (capClass j c : ℝ)) ≤
            ((Strip g).card : ℝ) * min (stripMult j g : ℝ) 210 := by
          calc ∑ c ∈ Strip g, (capClass j c : ℝ)
              ≤ ∑ _c ∈ Strip g, min (stripMult j g : ℝ) 210 := Finset.sum_le_sum hcap_min
            _ = ((Strip g).card : ℝ) * min (stripMult j g : ℝ) 210 := by rw [Finset.sum_const, nsmul_eq_mul]
        have hM_nn : 0 ≤ min (stripMult j g : ℝ) 210 := le_min (Nat.cast_nonneg _) (by norm_num)
        have hM_le1 : min (stripMult j g : ℝ) 210 ≤ (stripMult j g : ℝ) := min_le_left _ _
        have hM_le2 : min (stripMult j g : ℝ) 210 ≤ 210 := min_le_right _ _
        have hL_nn : 0 ≤ ((n : ℝ) / 2) * (evalR (ptAt (g + 1)) - evalR (ptAt g)) :=
          mul_nonneg (div_nonneg hnR.le (by norm_num)) hdiff_nn
        calc ∑ c ∈ Strip g, (capClass j c : ℝ)
            ≤ ((Strip g).card : ℝ) * min (stripMult j g : ℝ) 210 := hsum_le
          _ ≤ (((n : ℝ) / 2) * (evalR (ptAt (g + 1)) - evalR (ptAt g)) + 1) *
                min (stripMult j g : ℝ) 210 := mul_le_mul_of_nonneg_right hcard_le hM_nn
          _ = (((n : ℝ) / 2) * (evalR (ptAt (g + 1)) - evalR (ptAt g))) * min (stripMult j g : ℝ) 210 +
                min (stripMult j g : ℝ) 210 := by ring
          _ ≤ (((n : ℝ) / 2) * (evalR (ptAt (g + 1)) - evalR (ptAt g))) * (stripMult j g : ℝ) + 210 :=
                add_le_add (mul_le_mul_of_nonneg_left hM_le1 hL_nn) hM_le2
          _ = ((n : ℝ) / 2) * ((stripMult j g : ℝ) * (evalR (ptAt (g + 1)) - evalR (ptAt g))) + 210 := by ring
    -- Match `∑ g ∈ range 13, stripMult j g * (evalR (ptAt (g+1)) - evalR (ptAt g))` to `highTileLayerAff t j`!
    have haff_eq :
        (∑ g ∈ Finset.range 13, (stripMult j g : ℝ) * (evalR (ptAt (g + 1)) - evalR (ptAt g))) =
          ((highTileLayerAff t j).1 : ℝ) + ((highTileLayerAff t j).2 : ℝ) * ((p : ℝ) / (n : ℝ)) := by
      unfold highTileLayerAff highTileStrips
      rw [accumJ_eval]
      simp only [Int.cast_zero, zero_mul, zero_add]
      rw [buildStrips_map_sum, hptslen]
      simp only [show 14 - 1 = 13 from rfl, show j - 1 + 1 = j by omega, zero_add]
      apply Finset.sum_congr rfl; intro g _
      dsimp only [stripMult, stripInfo, ptAt, evalR, deltaOf, mkPlus, mkMinus]
      congr 1; push_cast; ring
    have hsum_strips : (∑ g ∈ Finset.range 13, ∑ c ∈ Strip g, (capClass j c : ℝ)) ≤
        ((n : ℝ) / 2) * (((highTileLayerAff t j).1 : ℝ) +
          ((highTileLayerAff t j).2 : ℝ) * ((p : ℝ) / (n : ℝ))) + 2730 := by
      calc ∑ g ∈ Finset.range 13, ∑ c ∈ Strip g, (capClass j c : ℝ)
          ≤ ∑ g ∈ Finset.range 13,
              (((n : ℝ) / 2) * ((stripMult j g : ℝ) * (evalR (ptAt (g + 1)) - evalR (ptAt g))) + 210) :=
            Finset.sum_le_sum hStrip_sum
        _ = ((n : ℝ) / 2) * (∑ g ∈ Finset.range 13,
              (stripMult j g : ℝ) * (evalR (ptAt (g + 1)) - evalR (ptAt g))) + 2730 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range]; norm_num
        _ = ((n : ℝ) / 2) * (((highTileLayerAff t j).1 : ℝ) +
              ((highTileLayerAff t j).2 : ℝ) * ((p : ℝ) / (n : ℝ))) + 2730 := by rw [haff_eq]
    have hcard_comb : ((slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℝ) ≤
        ((n : ℝ) / 2) * (((highTileLayerAff t j).1 : ℝ) +
          ((highTileLayerAff t j).2 : ℝ) * ((p : ℝ) / (n : ℝ))) + 5670 := by
      linarith only [htotal_j, hBdy_sum, hsum_strips]
    have hrank_eq : (rank n : ℝ) = (n : ℝ) * 15 := by unfold rank; push_cast; ring
    rw [hrank_eq]
    have hmin_mul : (n : ℝ) * min (15 : ℝ)
        ((((highTileLayerAff t j).1 : ℝ) + ((highTileLayerAff t j).2 : ℝ) * ((p : ℝ) / (n : ℝ))) / 2) =
        min ((n : ℝ) * 15) (((n : ℝ) / 2) * (((highTileLayerAff t j).1 : ℝ) +
          ((highTileLayerAff t j).2 : ℝ) * ((p : ℝ) / (n : ℝ)))) := by
      rw [mul_min_of_nonneg _ _ hnR.le]; congr 1; ring
    rw [hmin_mul]
    exact min_le_min le_rfl hcard_comb |>.trans (by
      rcases le_total ((n : ℝ) * 15) (((n : ℝ) / 2) * (((highTileLayerAff t j).1 : ℝ) +
          ((highTileLayerAff t j).2 : ℝ) * ((p : ℝ) / (n : ℝ)))) with h | h
      · rw [min_eq_left h]; exact (min_le_left _ _).trans (by linarith only [])
      · rw [min_eq_right h]; exact (min_le_right _ _))
  -- Combine row penalty bound + 18 layer bounds
  have hpen := two_mul_sixRowPenalty_le n p t.q k30 hn hp hqk hfl30.2.2
  have hsum18 : (∑ j ∈ Finset.Icc 1 18,
      min ((rank n : ℝ)) (((slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℝ))) ≤
      (n : ℝ) * (∑ j ∈ Finset.Icc 1 18, min (15 : ℝ)
        ((((highTileLayerAff t j).1 : ℝ) + ((highTileLayerAff t j).2 : ℝ) * ((p : ℝ) / (n : ℝ))) / 2)) +
      102060 := by
    calc ∑ j ∈ Finset.Icc 1 18,
          min ((rank n : ℝ)) (((slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℝ))
        ≤ ∑ j ∈ Finset.Icc 1 18,
            ((n : ℝ) * min (15 : ℝ)
              ((((highTileLayerAff t j).1 : ℝ) + ((highTileLayerAff t j).2 : ℝ) * ((p : ℝ) / (n : ℝ))) / 2) +
            5670) := Finset.sum_le_sum hlayer_bound
      _ = (n : ℝ) * (∑ j ∈ Finset.Icc 1 18, min (15 : ℝ)
            ((((highTileLayerAff t j).1 : ℝ) + ((highTileLayerAff t j).2 : ℝ) * ((p : ℝ) / (n : ℝ))) / 2)) +
          102060 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc]; norm_num
  unfold highTileMajorant
  linarith only [hexp_le, hpen, hsum18]

/-! ## Section 5: Combining the 8 certified high shards & main rate theorem (`C₁ ≤ 7206/1000`) -/

def allHighTiles : List HighTile :=
  (((((((OddZetaSix.HighData.Shard0.shard0Tiles ++
         OddZetaSix.HighData.Shard1.shard1Tiles) ++
         OddZetaSix.HighData.Shard2.shard2Tiles) ++
         OddZetaSix.HighData.Shard3.shard3Tiles) ++
         OddZetaSix.HighData.Shard4.shard4Tiles) ++
         OddZetaSix.HighData.Shard5.shard5Tiles) ++
         OddZetaSix.HighData.Shard6.shard6Tiles) ++
         OddZetaSix.HighData.Shard7.shard7Tiles)

theorem allHighTiles_valid :
    checkHighShard 7 2 55 1 540399306362 allHighTiles = true := by
  unfold allHighTiles
  have h01 := checkHighShard_append_eq (u3 := 10590003672) rfl
    OddZetaSix.HighData.Shard0.shard0_valid OddZetaSix.HighData.Shard1.shard1_valid
  have h02 := checkHighShard_append_eq (u3 := 19105246971) rfl
    h01 OddZetaSix.HighData.Shard2.shard2_valid
  have h03 := checkHighShard_append_eq (u3 := 32859492255) rfl
    h02 OddZetaSix.HighData.Shard3.shard3_valid
  have h04 := checkHighShard_append_eq (u3 := 51680592296) rfl
    h03 OddZetaSix.HighData.Shard4.shard4_valid
  have h05 := checkHighShard_append_eq (u3 := 91817948433) rfl
    h04 OddZetaSix.HighData.Shard5.shard5_valid
  have h06 := checkHighShard_append_eq (u3 := 197470331115) rfl
    h05 OddZetaSix.HighData.Shard6.shard6_valid
  exact checkHighShard_append_eq (u3 := 540399306362) rfl
    h06 OddZetaSix.HighData.Shard7.shard7_valid

/-- Exceptional prime set for the high band: empty for `n ≥ N₀`. -/
private def highExceptional (N₀ n : ℕ) : Finset ℕ :=
  if n < N₀ then sixCutoffPrimes n else ∅

/-- Generic high-band rate theorem for any certified `List HighTile` covering `[7/2, 55]`. -/
theorem sixHighBand_rate_of_shard (ts : List HighTile) (uTotal : ℕ)
    (hval : checkHighShard 7 2 55 1 uTotal ts = true)
    (hcert : ((uTotal : ℝ) / (certDen : ℝ)) / 750 ≤ (7206 : ℝ) / 1000) :
    ∀ δ > 0, ∀ᶠ n : ℕ in atTop,
      sixBandPrimeCost n ((7 : ℝ) / 2) 55 / sixNorm n ≤ (7206 : ℝ) / 1000 + δ := by
  unfold checkHighShard at hval
  obtain ⟨hall_chk, hUsum⟩ := checkHighRun_spec hval
  simp only [zero_add] at hUsum
  let L := ts.length
  let getTile (j : ℕ) : HighTile := ts[j]?.getD ⟨7, 2, 55, 1, 0, [], 0⟩
  have htile_mem : ∀ j < L, getTile j ∈ ts := by
    intro j hj
    dsimp [getTile]; rw [List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
  let lo (j : ℕ) : ℝ := ((getTile j).ln : ℝ) / ((getTile j).ld : ℝ)
  let hi (j : ℕ) : ℝ := ((getTile j).rn : ℝ) / ((getTile j).rd : ℝ)
  let f (j : ℕ) (x : ℝ) : ℝ := highTileMajorant (getTile j) x
  let maxD : ℕ := highMaxDen ts
  let N₀ : ℕ := max 20 (55 * maxD + 1)
  let E : ℕ → Finset ℕ := highExceptional N₀
  have hEsub : ∀ n, E n ⊆ sixCutoffPrimes n := by
    intro n; dsimp only [E]; unfold highExceptional; split_ifs
    · exact Finset.Subset.rfl
    · exact Finset.empty_subset _
  have hEcard : ∀ᶠ n : ℕ in atTop, (E n).card ≤ 0 := by
    filter_upwards [eventually_ge_atTop N₀] with n hn
    dsimp only [E]; unfold highExceptional; simp [show ¬ n < N₀ by omega]
  have hpw := sixBandPrimeCost_rate_of_piecewise_majorant (Finset.range L) ((7 : ℝ) / 2) 55
    (by norm_num) (by norm_num) lo hi f
    (by
      intro j hj
      have hpm := htile_mem j (Finset.mem_range.mp hj)
      obtain ⟨hld, _, _, h35, _, _, _⟩ := highTileMajorant_nonneg_and_integral _ (hall_chk _ hpm)
      have hldR : (0 : ℝ) < ((getTile j).ld : ℝ) := by exact_mod_cast hld
      dsimp [lo]
      have h1 : (7 : ℝ) / 2 ≤ ((getTile j).ln : ℝ) / ((getTile j).ld : ℝ) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hldR]
        have : 7 * (getTile j).ld ≤ (getTile j).ln * 2 := by omega
        exact_mod_cast this
      linarith)
    (by
      intro j hj
      have hpm := htile_mem j (Finset.mem_range.mp hj)
      obtain ⟨hld, hrd, hlt, _, _, _, _⟩ := highTileMajorant_nonneg_and_integral _ (hall_chk _ hpm)
      have hldR : (0 : ℝ) < ((getTile j).ld : ℝ) := by exact_mod_cast hld
      have hrdR : (0 : ℝ) < ((getTile j).rd : ℝ) := by exact_mod_cast hrd
      dsimp [lo, hi]
      exact ((div_lt_div_iff₀ hldR hrdR).mpr (by exact_mod_cast hlt)).le)
    (by
      intro j hj
      have hpm := htile_mem j (Finset.mem_range.mp hj)
      obtain ⟨_, hrd, _, _, h55, _, _⟩ := highTileMajorant_nonneg_and_integral _ (hall_chk _ hpm)
      have hrdR : (0 : ℝ) < ((getTile j).rd : ℝ) := by exact_mod_cast hrd
      dsimp [hi]; rw [div_le_iff₀ hrdR]; exact_mod_cast h55)
    (by
      intro j _
      dsimp [f, highTileMajorant]
      apply Continuous.continuousOn
      apply Continuous.add (by fun_prop)
      apply continuous_finsetSum; intro k _; fun_prop)
    (by
      intro j hj x hx
      have hpm := htile_mem j (Finset.mem_range.mp hj)
      obtain ⟨_, _, _, _, _, hnn, _⟩ := highTileMajorant_nonneg_and_integral _ (hall_chk _ hpm)
      exact hnn x hx)
    (102060 : ℝ) (by norm_num) E 0 hEsub hEcard
    (by
      intro n hn p hpS hpE
      have hp_mem := Finset.mem_filter.mp hpS
      have hp_pr : p.Prime := (Nat.mem_primesLE.mp hp_mem.1).2
      have hp_le_55 : (p : ℝ) ≤ 55 * (n : ℝ) :=
        (Nat.le_floor_iff (by positivity)).mp (Nat.mem_primesLE.mp hp_mem.1).1
      have hp_gt_35 : ((7 : ℝ) / 2) * (n : ℝ) < (p : ℝ) := hp_mem.2
      have hp_cut : p ∈ sixCutoffPrimes n := by
        rw [sixCutoffPrimes, Nat.mem_primesLE]; exact ⟨by exact_mod_cast hp_le_55, hp_pr⟩
      have hnN0 : N₀ ≤ n := by
        by_contra hlt; push Not at hlt
        apply hpE
        dsimp only [E]; unfold highExceptional; simp only [hlt, ite_true]
        exact hp_cut
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hp_gt_n : n < p := by
        have : (n : ℝ) < (p : ℝ) := by linarith
        exact_mod_cast this
      have hsq : 140 * n + 2 < p ^ 2 := by
        have hn20 : 20 ≤ n := (le_max_left _ _).trans hnN0
        have h7n : 7 * n < 2 * p := by
          have : 7 * (n : ℝ) < 2 * (p : ℝ) := by linarith
          exact_mod_cast this
        nlinarith
      have hp_gt_55D : 55 * maxD < p := by
        have h1 : 55 * maxD + 1 ≤ n := (le_max_right _ _).trans hnN0
        omega
      have hx_lo : ((7 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) < (p : ℝ) / (n : ℝ) := by
        push_cast; rw [lt_div_iff₀ hnR]; linarith
      have hx_lt_55 : (p : ℝ) / (n : ℝ) < ((55 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
        push_cast; rw [div_one, div_lt_iff₀ hnR]
        by_contra hge
        have heq : p = 55 * n := by
          have : (p : ℝ) = 55 * (n : ℝ) := by linarith
          exact_mod_cast this
        have h55_dvd : p ∣ 55 * n := ⟨1, by omega⟩
        rcases hp_pr.dvd_mul.mp h55_dvd with h1 | h2
        · have h55le := Nat.le_of_dvd (by omega) h1
          have hmaxD1 : 1 ≤ maxD := by
            dsimp [maxD, highMaxDen]
            have : ∀ (init : ℕ) (xs : List HighTile), init ≤ xs.foldl (fun m t => max m (max t.ld t.rd)) init := by
              intro init xs; induction xs generalizing init with
              | nil => exact le_rfl
              | cons a r ih => exact (le_max_left _ _).trans (ih _)
            exact this 1 ts
          omega
        · exact absurd (Nat.le_of_dvd hn h2) (not_le.mpr hp_gt_n)
      have hx_ne : ∀ t ∈ ts, (p : ℝ) / (n : ℝ) ≠ (t.rn : ℝ) / (t.rd : ℝ) := by
        intro t htm heq
        obtain ⟨_, hrd, _, _, h55t, _, _⟩ := highTileMajorant_nonneg_and_integral t (hall_chk t htm)
        have hrdR : (0 : ℝ) < (t.rd : ℝ) := by exact_mod_cast hrd
        have hmulR : (p : ℝ) * (t.rd : ℝ) = (t.rn : ℝ) * (n : ℝ) := by
          have := (div_eq_div_iff hnR.ne' hrdR.ne').mp heq; linarith
        have hmulN : p * t.rd = t.rn * n := by exact_mod_cast hmulR
        have hdvd : p ∣ t.rn * n := ⟨t.rd, by linarith⟩
        rcases hp_pr.dvd_mul.mp hdvd with h1 | h2
        · have hrn_pos : 0 < t.rn := by
            by_contra h0; have : t.rn = 0 := by omega
            rw [this, zero_mul] at hmulN; have := Nat.mul_pos hp_pr.pos hrd; omega
          have hle_rn := Nat.le_of_dvd hrn_pos h1
          have hrd_le := (highMaxDen_ge ts t htm).2
          have : t.rn ≤ 55 * maxD := h55t.trans (Nat.mul_le_mul_left 55 hrd_le)
          omega
        · exact absurd (Nat.le_of_dvd hn h2) (not_le.mpr hp_gt_n)
      obtain ⟨t, htm, htlo, hthi⟩ := checkHighRun_cover hval hx_lo hx_lt_55 hx_ne
      obtain ⟨j, hjL, hj_eq⟩ := List.mem_iff_getElem.mp htm
      have hget_eq : getTile j = t := by
        dsimp [getTile]; rw [List.getElem?_eq_getElem hjL]; exact hj_eq
      refine ⟨j, Finset.mem_range.mpr hjL, ?_, ?_, ?_⟩
      · dsimp [lo]; rw [hget_eq]; exact (lt_div_iff₀ hnR).mp htlo
      · dsimp [hi]; rw [hget_eq]; exact ((div_lt_iff₀ hnR).mp hthi).le
      · have : Fact p.Prime := ⟨hp_pr⟩
        dsimp [f]; rw [hget_eq]
        exact highTile_discrete_bound n p hn hsq t (hall_chk t htm) htlo hthi)
  have hint_bound : (∑ j ∈ Finset.range L, ∫ x in lo j..hi j, f j x) / 750 ≤ (7206 : ℝ) / 1000 := by
    have hsum_le : (∑ j ∈ Finset.range L, ∫ x in lo j..hi j, f j x) ≤ (uTotal : ℝ) / (certDen : ℝ) := by
      have hsum_map : (uTotal : ℝ) = ∑ j ∈ Finset.range L, ((getTile j).uNum : ℝ) := by
        rw [← hUsum, ← Nat.cast_sum]
        exact_mod_cast list_map_sum_eq_range ts ⟨7, 2, 55, 1, 0, [], 0⟩ (·.uNum)
      rw [hsum_map, Finset.sum_div]
      apply Finset.sum_le_sum; intro j hj
      have hpm := htile_mem j (Finset.mem_range.mp hj)
      exact (highTileMajorant_nonneg_and_integral _ (hall_chk _ hpm)).2.2.2.2.2.2
    have hdiv := div_le_div_of_nonneg_right hsum_le (by norm_num : (0 : ℝ) ≤ 750)
    exact hdiv.trans hcert
  intro δ hδ
  filter_upwards [hpw δ hδ] with n hn
  exact hn.trans (by linarith)

/-- **Stage 2B Middle/High Band Bound**: on `(7/2) * n < p ≤ 55 * n`,
`sixBandPrimeCost n (7/2) 55 / sixNorm n ≤ 7206 / 1000 + δ` eventually. -/
theorem sixHighBand_rate_le :
    ∀ δ > 0, ∀ᶠ n : ℕ in atTop,
      sixBandPrimeCost n ((7 : ℝ) / 2) 55 / sixNorm n ≤ (7206 : ℝ) / 1000 + δ :=
  sixHighBand_rate_of_shard allHighTiles 540399306362 allHighTiles_valid
    (by unfold certDen; norm_num)

end OddZetaSix
