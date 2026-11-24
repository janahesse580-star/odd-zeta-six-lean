import OddZetaSix.SixRationalBounds
import OddZetaSix.SixPhaseBridge

/-!
# Computable Rational Verifier for the Slim 4-Bin Analytic Certificate

Provides the kernel-decidable (`decide +kernel`, zero `native_decide`) verifier and
soundness proofs for certifying the 8 rational endpoint ceilings on `y ∈ [0, 2]`:
- Exact grouped representation of `sixPhaseConstant`, `sixPhase`, and `sixPhaseDerivative`
  (9 nontrivial constant terms, 24 distinct positive `d` shifts).
- Directed rounded `log` and `arctan` evaluation via `SixRationalBounds`.
- Contiguous cell-chain checker `checkCellChain` verifying all 8 `(bin, side)` endpoints
  simultaneously on each cell `[l, r] ⊆ [0, 2]`.

Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix

open Finset

/-! ## Frozen slim 4-bin parameters and rational targets -/

def sixSlimRoots : Fin 4 → Fin 2 → ℚ :=
  ![![4 / 25, 21 / 100],
    ![4 / 25, 1 / 4],
    ![4 / 25, 7 / 25],
    ![4 / 25, 3 / 10]]

def sixSlimCaps : Fin 4 → Fin 2 → ℚ :=
  ![![-878 / 100, -8925 / 1000],
    ![-8925 / 1000, -9035 / 1000],
    ![-9025 / 1000, -9115 / 1000],
    ![-9105 / 1000, -9165 / 1000]]

def sixBinKnotQ (b : Fin 4) (side : Fin 2) : ℚ :=
  3 * ((b.val + side.val : ℕ) : ℚ) / 40

theorem sixBinKnotQ_cast (b : Fin 4) (side : Fin 2) :
    (sixBinKnotQ b side : ℝ) = sixBinKnot b side := by
  unfold sixBinKnotQ sixBinKnot
  push_cast; rfl

theorem sixSlimRoots_bounds (b : Fin 4) (j : Fin 2) :
    0 ≤ (sixSlimRoots b j : ℝ) ∧ (sixSlimRoots b j : ℝ) ≤ 3 / 10 := by
  fin_cases b <;> fin_cases j <;> norm_num [sixSlimRoots]

/-! ## Grouped exact representations of `sixPhaseConstant`, `sixPhase`, and `sixPhaseDerivative` -/

/-- The 9 nontrivial `(r, mult)` terms of `sixPhaseConstant` (omitting `r = 1` where `log 1 = 0`). -/
def sixConstTerms : List (ℚ × ℤ) :=
  [(14 / 25, 1), (16 / 25, 2), (17 / 25, 1), (19 / 25, 1), (4 / 5, -4),
   (41 / 50, -2), (21 / 25, 1), (43 / 50, -2), (23 / 25, 1)]

/-- The 24 grouped `(d, mult)` terms of `sixPhase` and `sixPhaseDerivative`. -/
def sixPhaseTerms : List (ℚ × ℤ) :=
  [(1 / 50, 5), (39 / 50, 3), (4 / 5, 1), (21 / 25, 1), (22 / 25, 5),
   (23 / 25, 1), (24 / 25, 1), (49 / 50, 2), (1, 1), (26 / 25, 1),
   (53 / 50, 2), (11 / 10, 1), (83 / 50, -1), (17 / 10, -2), (43 / 25, -1),
   (44 / 25, -1), (89 / 50, -2), (9 / 5, -1), (46 / 25, -1), (47 / 25, -5),
   (48 / 25, -1), (49 / 25, -1), (99 / 50, -3), (139 / 50, 5)]

theorem sixPhaseConstant_eq_list :
    sixPhaseConstant =
      (sixConstTerms.map fun t => (t.2 : ℝ) * (t.1 : ℝ) * Real.log (t.1 : ℝ)).sum := by
  unfold sixPhaseConstant sixConstTerms
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, sixZero, sixOffset,
    Matrix.cons_val_zero, Matrix.cons_val_succ, List.map, List.sum_cons, List.sum_nil]
  norm_num [Real.log_one]
  ring

theorem sixPhase_eq_list (y : ℝ) :
    sixPhase y = sixPhaseConstant +
      (sixPhaseTerms.map fun t => (t.2 : ℝ) * sixPhaseX (t.1 : ℝ) y).sum +
      3 * Real.pi * y := by
  unfold sixPhase sixPhaseTerms
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, sixZero, sixOffset,
    Matrix.cons_val_zero, Matrix.cons_val_succ, List.map, List.sum_cons, List.sum_nil]
  norm_num
  ring

theorem sixPhaseDerivative_eq_list (y : ℝ) :
    sixPhaseDerivative y = 3 * Real.pi -
      (sixPhaseTerms.map fun t => (t.2 : ℝ) * Real.arctan (y / (t.1 : ℝ))).sum := by
  unfold sixPhaseDerivative sixPhaseTerms
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, sixZero, sixOffset,
    Matrix.cons_val_zero, Matrix.cons_val_succ, List.map, List.sum_cons, List.sum_nil]
  norm_num
  have hsimp :
      50 * y / 139 = y / (139 / 50) ∧
      50 * y / 99 = y / (99 / 50) ∧ 50 * y / 39 = y / (39 / 50) ∧
      50 * y / 98 = y / (49 / 25) ∧ 50 * y / 40 = y / (4 / 5) ∧
      50 * y / 96 = y / (48 / 25) ∧ 50 * y / 42 = y / (21 / 25) ∧
      50 * y / 94 = y / (47 / 25) ∧ 50 * y / 44 = y / (22 / 25) ∧
      50 * y / 92 = y / (46 / 25) ∧ 50 * y / 46 = y / (23 / 25) ∧
      50 * y / 90 = y / (9 / 5) ∧ 50 * y / 48 = y / (24 / 25) ∧
      50 * y / 89 = y / (89 / 50) ∧ 50 * y / 49 = y / (49 / 50) ∧
      50 * y / 88 = y / (44 / 25) ∧
      50 * y / 86 = y / (43 / 25) ∧ 50 * y / 52 = y / (26 / 25) ∧
      50 * y / 85 = y / (17 / 10) ∧ 50 * y / 53 = y / (53 / 50) ∧
      50 * y / 83 = y / (83 / 50) ∧ 50 * y / 55 = y / (11 / 10) ∧
      50 * y = y / (1 / 50) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring
  rw [hsimp.1, hsimp.2.1, hsimp.2.2.1, hsimp.2.2.2.1, hsimp.2.2.2.2.1, hsimp.2.2.2.2.2.1,
    hsimp.2.2.2.2.2.2.1, hsimp.2.2.2.2.2.2.2.1, hsimp.2.2.2.2.2.2.2.2.1,
    hsimp.2.2.2.2.2.2.2.2.2.1, hsimp.2.2.2.2.2.2.2.2.2.2.1, hsimp.2.2.2.2.2.2.2.2.2.2.2.1,
    hsimp.2.2.2.2.2.2.2.2.2.2.2.2.1, hsimp.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsimp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hsimp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsimp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hsimp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsimp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hsimp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsimp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsimp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsimp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
  ring

/-! ## Computable directed-rounded evaluators -/

/-- Heuristic binary exponent for `log` range reduction; validity is verified explicitly. -/
def log2Exp (q : ℚ) : ℤ :=
  let k0 : ℤ := (Nat.log2 q.num.natAbs : ℤ) - (Nat.log2 q.den : ℤ)
  let m := RationalLogBounds.mantissa q k0
  if m < 1 then k0 - 1 else if 2 < m then k0 + 1 else k0

/-- Computable directed bound for `Real.log q` (`isUpper = true` gives upper bound, `false` lower). -/
def qLogBound (isUpper : Bool) (q : ℚ) (n d : ℕ) : Option ℚ :=
  let k := log2Exp q
  if 0 < d ∧ 0 < q ∧ 1 ≤ RationalLogBounds.mantissa q k ∧ RationalLogBounds.mantissa q k ≤ 2 then
    some (if isUpper then RationalLogBounds.roundedUpper q k n d
          else RationalLogBounds.roundedLower q k n d)
  else none

theorem qLogBound_upper_sound {q : ℚ} {n d : ℕ} {hi : ℚ}
    (h : qLogBound true q n d = some hi) : Real.log (q : ℝ) ≤ (hi : ℝ) := by
  dsimp only [qLogBound] at h
  by_cases hc : 0 < d ∧ 0 < q ∧ 1 ≤ RationalLogBounds.mantissa q (log2Exp q) ∧
      RationalLogBounds.mantissa q (log2Exp q) ≤ 2
  · rw [ite_eq_left hc] at h
    simp only [↓reduceIte, Option.some.injEq] at h
    rw [← h]
    exact (RationalLogBounds.rounded_sound q (log2Exp q) n d hc.1 hc.2.1 ⟨hc.2.2.1, hc.2.2.2⟩).2
  · rw [ite_eq_right hc] at h; cases h

theorem qLogBound_lower_sound {q : ℚ} {n d : ℕ} {lo : ℚ}
    (h : qLogBound false q n d = some lo) : (lo : ℝ) ≤ Real.log (q : ℝ) := by
  dsimp only [qLogBound] at h
  by_cases hc : 0 < d ∧ 0 < q ∧ 1 ≤ RationalLogBounds.mantissa q (log2Exp q) ∧
      RationalLogBounds.mantissa q (log2Exp q) ≤ 2
  · rw [ite_eq_left hc] at h
    simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
    rw [← h]
    exact (RationalLogBounds.rounded_sound q (log2Exp q) n d hc.1 hc.2.1 ⟨hc.2.2.1, hc.2.2.2⟩).1
  · rw [ite_eq_right hc] at h; cases h

/-- Certified rational upper bound on `sixPhaseConstant`. -/
def sixConstUpper : ℚ := -290837 / 1000000

def qConstSumUpper (terms : List (ℚ × ℤ)) : Option ℚ :=
  match terms with
  | [] => some 0
  | (r, m) :: rest =>
    match qLogBound (0 ≤ m) r 6 1000000, qConstSumUpper rest with
    | some lv, some sv => some ((m : ℚ) * r * lv + sv)
    | _, _ => none

private theorem qConstSumUpper_sound (terms : List (ℚ × ℤ))
    (hr : ∀ t ∈ terms, 0 ≤ t.1) {u : ℚ} (h : qConstSumUpper terms = some u) :
    (terms.map fun t => (t.2 : ℝ) * (t.1 : ℝ) * Real.log (t.1 : ℝ)).sum ≤ (u : ℝ) := by
  induction terms generalizing u with
  | nil => simp [qConstSumUpper] at h; subst h; simp
  | cons hd tl ih =>
    rcases hd with ⟨r, m⟩
    have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast hr (r, m) (by simp)
    have htl : ∀ t ∈ tl, 0 ≤ t.1 := fun t ht => hr t (by simp [ht])
    unfold qConstSumUpper at h
    cases hl : qLogBound (decide (0 ≤ m)) r 6 1000000 with
    | none => simp [hl] at h
    | some lv =>
      cases hs : qConstSumUpper tl with
      | none => simp [hl, hs] at h
      | some sv =>
        simp [hl, hs] at h; subst h
        simp only [List.map_cons, List.sum_cons]
        push_cast
        have ih' := ih htl hs
        have hterm : (m : ℝ) * (r : ℝ) * Real.log (r : ℝ) ≤ (m : ℝ) * (r : ℝ) * (lv : ℝ) := by
          by_cases hm : 0 ≤ m
          · rw [decide_eq_true hm] at hl
            have h1 := qLogBound_upper_sound hl
            have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm
            exact mul_le_mul_of_nonneg_left h1 (mul_nonneg hmR hr0)
          · rw [decide_eq_false hm] at hl
            have h1 := qLogBound_lower_sound hl
            have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge hm
            exact mul_le_mul_of_nonpos_left h1 (mul_nonpos_of_nonpos_of_nonneg hmR hr0)
        linarith

def checkSixConstUpper : Bool :=
  match qConstSumUpper sixConstTerms with
  | some u => decide (u ≤ sixConstUpper)
  | none => false

private theorem sixConstTerms_nonneg : ∀ t ∈ sixConstTerms, 0 ≤ t.1 := by
  decide +kernel

private theorem sixPhaseTerms_pos : ∀ t ∈ sixPhaseTerms, 0 < t.1 := by
  decide +kernel

theorem sixConstUpper_sound (h : checkSixConstUpper = true) :
    sixPhaseConstant ≤ (sixConstUpper : ℝ) := by
  unfold checkSixConstUpper at h
  cases hu : qConstSumUpper sixConstTerms with
  | none => simp [hu] at h
  | some u =>
    simp [hu] at h
    have hle : (u : ℝ) ≤ sixConstUpper := by exact_mod_cast h
    rw [sixPhaseConstant_eq_list]
    exact (qConstSumUpper_sound sixConstTerms sixConstTerms_nonneg hu).trans hle

theorem sixConstUpper_ok : checkSixConstUpper = true := by decide +kernel

theorem sixPhaseConstant_le_upper : sixPhaseConstant ≤ (sixConstUpper : ℝ) :=
  sixConstUpper_sound sixConstUpper_ok

/-! ## Cellwise computable phase, derivative, and pair-modulus bounds -/

def qPhaseTermsUpper (terms : List (ℚ × ℤ)) (y : ℚ) : Option ℚ :=
  match terms with
  | [] => some 0
  | (d, m) :: rest =>
    let q := d ^ 2 + y ^ 2
    match qLogBound (0 ≤ m) q 5 100000, qPhaseTermsUpper rest y with
    | some lv, some sv =>
      let av := if 0 ≤ m then RationalArctanBounds.roundedLower (y / d) 5 100000
                else RationalArctanBounds.roundedUpper (y / d) 5 100000
      some ((m : ℚ) * ((d / 2) * lv - y * av) + sv)
    | _, _ => none

private theorem qPhaseTermsUpper_sound (terms : List (ℚ × ℤ))
    (hd : ∀ t ∈ terms, 0 < t.1) {y : ℚ} (hy : 0 ≤ y) {u : ℚ}
    (h : qPhaseTermsUpper terms y = some u) :
    (terms.map fun t => (t.2 : ℝ) * sixPhaseX (t.1 : ℝ) (y : ℝ)).sum ≤ (u : ℝ) := by
  induction terms generalizing u with
  | nil => simp [qPhaseTermsUpper] at h; subst h; simp
  | cons hd_t tl ih =>
    rcases hd_t with ⟨d, m⟩
    have hd0 : 0 < d := hd (d, m) (by simp)
    have hd0R : (0 : ℝ) < d := by exact_mod_cast hd0
    have hyR : (0 : ℝ) ≤ y := by exact_mod_cast hy
    have htl : ∀ t ∈ tl, 0 < t.1 := fun t ht => hd t (by simp [ht])
    unfold qPhaseTermsUpper at h
    cases hl : qLogBound (decide (0 ≤ m)) (d ^ 2 + y ^ 2) 5 100000 with
    | none => simp [hl] at h
    | some lv =>
      cases hs : qPhaseTermsUpper tl y with
      | none => simp [hl, hs] at h
      | some sv =>
        simp only [hl, hs, Option.some.injEq] at h
        subst h
        simp only [List.map_cons, List.sum_cons]
        have ih' := ih htl hs
        have hqR : ((d ^ 2 + y ^ 2 : ℚ) : ℝ) = (d : ℝ) ^ 2 + (y : ℝ) ^ 2 := by push_cast; ring
        have hatan := RationalArctanBounds.rounded_sound (y / d) 5 100000 (by norm_num)
          (div_nonneg hy hd0.le)
        have hdivR : ((y / d : ℚ) : ℝ) = (y : ℝ) / (d : ℝ) := by push_cast; rfl
        rw [hdivR] at hatan
        have hterm : (m : ℝ) * sixPhaseX (d : ℝ) (y : ℝ) ≤
            (((m : ℚ) * ((d / 2) * lv - y *
              (if 0 ≤ m then RationalArctanBounds.roundedLower (y / d) 5 100000
               else RationalArctanBounds.roundedUpper (y / d) 5 100000)) : ℚ) : ℝ) := by
          unfold sixPhaseX
          by_cases hm : 0 ≤ m
          · rw [decide_eq_true hm] at hl
            simp only [ite_eq_left hm]
            push_cast
            have hlog := qLogBound_upper_sound hl; rw [hqR] at hlog
            have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm
            have h1 : (d : ℝ) / 2 * Real.log ((d : ℝ) ^ 2 + (y : ℝ) ^ 2) -
                (y : ℝ) * Real.arctan ((y : ℝ) / (d : ℝ)) ≤
                (d : ℝ) / 2 * (lv : ℝ) -
                  (y : ℝ) * (RationalArctanBounds.roundedLower (y / d) 5 100000 : ℝ) := by
              have ha := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ (d : ℝ) / 2)
              have hb := mul_le_mul_of_nonneg_left hatan.1 hyR
              linarith
            exact mul_le_mul_of_nonneg_left h1 hmR
          · rw [decide_eq_false hm] at hl
            simp only [ite_eq_right hm]
            push_cast
            have hlog := qLogBound_lower_sound hl; rw [hqR] at hlog
            have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge hm
            have h1 : (d : ℝ) / 2 * (lv : ℝ) -
                (y : ℝ) * (RationalArctanBounds.roundedUpper (y / d) 5 100000 : ℝ) ≤
                (d : ℝ) / 2 * Real.log ((d : ℝ) ^ 2 + (y : ℝ) ^ 2) -
                  (y : ℝ) * Real.arctan ((y : ℝ) / (d : ℝ)) := by
              have ha := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ (d : ℝ) / 2)
              have hb := mul_le_mul_of_nonneg_left hatan.2 hyR
              linarith
            exact mul_le_mul_of_nonpos_left h1 hmR
        push_cast at hterm ⊢
        linarith

def qPhaseUpper (y : ℚ) : Option ℚ :=
  match qPhaseTermsUpper sixPhaseTerms y with
  | some s => some (RationalLogBounds.roundUp 100000
      (sixConstUpper + s + 3 * RationalArctanBounds.piUpper * y))
  | none => none

theorem qPhaseUpper_sound {y u : ℚ} (hy : 0 ≤ y) (h : qPhaseUpper y = some u) :
    sixPhase (y : ℝ) ≤ (u : ℝ) := by
  unfold qPhaseUpper at h
  cases hs : qPhaseTermsUpper sixPhaseTerms y with
  | none => simp [hs] at h
  | some s =>
    simp only [hs, Option.some.injEq] at h
    subst h
    have hsum := qPhaseTermsUpper_sound sixPhaseTerms sixPhaseTerms_pos hy hs
    have hc := sixPhaseConstant_le_upper
    have hpi := RationalArctanBounds.pi_sound.2
    have hyR : (0 : ℝ) ≤ y := by exact_mod_cast hy
    have hru : ((sixConstUpper + s + 3 * RationalArctanBounds.piUpper * y : ℚ) : ℝ) ≤
        (RationalLogBounds.roundUp 100000
          (sixConstUpper + s + 3 * RationalArctanBounds.piUpper * y) : ℝ) := by
      exact_mod_cast RationalLogBounds.le_roundUp 100000 (by norm_num) _
    rw [sixPhase_eq_list]
    push_cast at hru
    have h3 : 3 * Real.pi * (y : ℝ) ≤ 3 * (RationalArctanBounds.piUpper : ℝ) * (y : ℝ) := by
      nlinarith
    linarith

def qDerivTermsLower (terms : List (ℚ × ℤ)) (l r : ℚ) : ℚ :=
  match terms with
  | [] => 0
  | (d, m) :: rest =>
    let av := if 0 ≤ m then RationalArctanBounds.roundedLower (l / d) 5 100000
              else RationalArctanBounds.roundedUpper (r / d) 5 100000
    (m : ℚ) * av + qDerivTermsLower rest l r

def qDerivTermsUpper (terms : List (ℚ × ℤ)) (l r : ℚ) : ℚ :=
  match terms with
  | [] => 0
  | (d, m) :: rest =>
    let av := if 0 ≤ m then RationalArctanBounds.roundedUpper (r / d) 5 100000
              else RationalArctanBounds.roundedLower (l / d) 5 100000
    (m : ℚ) * av + qDerivTermsUpper rest l r

private theorem qDerivTermsLower_sound (terms : List (ℚ × ℤ))
    (hd : ∀ t ∈ terms, 0 < t.1) {l r : ℚ} (hl0 : 0 ≤ l) (hlr : l ≤ r)
    {x : ℝ} (hxl : (l : ℝ) ≤ x) (hxr : x ≤ (r : ℝ)) :
    (qDerivTermsLower terms l r : ℝ) ≤
      (terms.map fun t => (t.2 : ℝ) * Real.arctan (x / (t.1 : ℝ))).sum := by
  induction terms with
  | nil => simp [qDerivTermsLower]
  | cons hd_t tl ih =>
    rcases hd_t with ⟨d, m⟩
    have hd0 : 0 < d := hd (d, m) (by simp)
    have hd0R : (0 : ℝ) < d := by exact_mod_cast hd0
    have hr0 : 0 ≤ r := hl0.trans hlr
    have ih' := ih (fun t ht => hd t (by simp [ht]))
    unfold qDerivTermsLower
    simp only [List.map_cons, List.sum_cons]
    have hterm : (((m : ℚ) * (if 0 ≤ m then RationalArctanBounds.roundedLower (l / d) 5 100000
        else RationalArctanBounds.roundedUpper (r / d) 5 100000) : ℚ) : ℝ) ≤
        (m : ℝ) * Real.arctan (x / (d : ℝ)) := by
      by_cases hm : 0 ≤ m
      · simp only [ite_eq_left hm]; push_cast
        have h1 := (RationalArctanBounds.rounded_sound (l / d) 5 100000 (by norm_num)
          (div_nonneg hl0 hd0.le)).1
        have h2 := Real.arctan_mono (div_le_div_of_nonneg_right hxl hd0R.le)
        rw [Rat.cast_div] at h1
        exact mul_le_mul_of_nonneg_left (h1.trans h2) (by exact_mod_cast hm)
      · simp only [ite_eq_right hm]; push_cast
        have h1 := (RationalArctanBounds.rounded_sound (r / d) 5 100000 (by norm_num)
          (div_nonneg hr0 hd0.le)).2
        have h2 := Real.arctan_mono (div_le_div_of_nonneg_right hxr hd0R.le)
        rw [Rat.cast_div] at h1
        exact mul_le_mul_of_nonpos_left (h2.trans h1) (by exact_mod_cast le_of_not_ge hm)
    push_cast at hterm ⊢; linarith

private theorem qDerivTermsUpper_sound (terms : List (ℚ × ℤ))
    (hd : ∀ t ∈ terms, 0 < t.1) {l r : ℚ} (hl0 : 0 ≤ l) (hlr : l ≤ r)
    {x : ℝ} (hxl : (l : ℝ) ≤ x) (hxr : x ≤ (r : ℝ)) :
    (terms.map fun t => (t.2 : ℝ) * Real.arctan (x / (t.1 : ℝ))).sum ≤
      (qDerivTermsUpper terms l r : ℝ) := by
  induction terms with
  | nil => simp [qDerivTermsUpper]
  | cons hd_t tl ih =>
    rcases hd_t with ⟨d, m⟩
    have hd0 : 0 < d := hd (d, m) (by simp)
    have hd0R : (0 : ℝ) < d := by exact_mod_cast hd0
    have hr0 : 0 ≤ r := hl0.trans hlr
    have ih' := ih (fun t ht => hd t (by simp [ht]))
    unfold qDerivTermsUpper
    simp only [List.map_cons, List.sum_cons]
    have hterm : (m : ℝ) * Real.arctan (x / (d : ℝ)) ≤
        (((m : ℚ) * (if 0 ≤ m then RationalArctanBounds.roundedUpper (r / d) 5 100000
          else RationalArctanBounds.roundedLower (l / d) 5 100000) : ℚ) : ℝ) := by
      by_cases hm : 0 ≤ m
      · simp only [ite_eq_left hm]; push_cast
        have h1 := (RationalArctanBounds.rounded_sound (r / d) 5 100000 (by norm_num)
          (div_nonneg hr0 hd0.le)).2
        have h2 := Real.arctan_mono (div_le_div_of_nonneg_right hxr hd0R.le)
        rw [Rat.cast_div] at h1
        exact mul_le_mul_of_nonneg_left (h2.trans h1) (by exact_mod_cast hm)
      · simp only [ite_eq_right hm]; push_cast
        have h1 := (RationalArctanBounds.rounded_sound (l / d) 5 100000 (by norm_num)
          (div_nonneg hl0 hd0.le)).1
        have h2 := Real.arctan_mono (div_le_div_of_nonneg_right hxl hd0R.le)
        rw [Rat.cast_div] at h1
        exact mul_le_mul_of_nonpos_left (h1.trans h2) (by exact_mod_cast le_of_not_ge hm)
    push_cast at hterm ⊢; linarith

def qDerivUpper (l r : ℚ) : ℚ :=
  RationalLogBounds.roundUp 100000 (3 * RationalArctanBounds.piUpper - qDerivTermsLower sixPhaseTerms l r)

def qDerivLower (l r : ℚ) : ℚ :=
  RationalLogBounds.roundDown 100000 (3 * RationalArctanBounds.piLower - qDerivTermsUpper sixPhaseTerms l r)

theorem qDerivUpper_sound {l r : ℚ} (hl0 : 0 ≤ l) (hlr : l ≤ r)
    {x : ℝ} (hxl : (l : ℝ) ≤ x) (hxr : x ≤ (r : ℝ)) :
    sixPhaseDerivative x ≤ (qDerivUpper l r : ℝ) := by
  have h1 := qDerivTermsLower_sound sixPhaseTerms sixPhaseTerms_pos hl0 hlr hxl hxr
  have hpi := RationalArctanBounds.pi_sound.2
  have hru : ((3 * RationalArctanBounds.piUpper - qDerivTermsLower sixPhaseTerms l r : ℚ) : ℝ) ≤
      (qDerivUpper l r : ℝ) := by
    exact_mod_cast RationalLogBounds.le_roundUp 100000 (by norm_num) _
  rw [sixPhaseDerivative_eq_list]
  push_cast at hru
  linarith

theorem qDerivLower_sound {l r : ℚ} (hl0 : 0 ≤ l) (hlr : l ≤ r)
    {x : ℝ} (hxl : (l : ℝ) ≤ x) (hxr : x ≤ (r : ℝ)) :
    (qDerivLower l r : ℝ) ≤ sixPhaseDerivative x := by
  have h1 := qDerivTermsUpper_sound sixPhaseTerms sixPhaseTerms_pos hl0 hlr hxl hxr
  have hpi := RationalArctanBounds.pi_sound.1
  have hrd : (qDerivLower l r : ℝ) ≤
      ((3 * RationalArctanBounds.piLower - qDerivTermsUpper sixPhaseTerms l r : ℚ) : ℝ) := by
    exact_mod_cast RationalLogBounds.roundDown_le 100000 (by norm_num) _
  rw [sixPhaseDerivative_eq_list]
  push_cast at hrd
  linarith

/-- Rational upper bound on `sixAdaptivePairModulus (69 / 50) a y` for `y ∈ [l, r]`, rounded up. -/
def qPairModUpper (l r a : ℚ) : ℚ :=
  let f1 := (max |l ^ 2 - a ^ 2| |r ^ 2 - a ^ 2|) ^ 2
  let f2 := (r + a) ^ 2 + 4 * (69 / 50) ^ 2
  let f3 := max ((l - a) ^ 2) ((r - a) ^ 2) + 4 * (69 / 50) ^ 2
  RationalLogBounds.roundUp 100000 (f1 * f2 * f3)

theorem qPairModUpper_sound {l r a : ℚ} (hl0 : 0 ≤ l) (ha0 : 0 ≤ a)
    {y : ℝ} (hyl : (l : ℝ) ≤ y) (hyr : y ≤ (r : ℝ)) :
    sixAdaptivePairModulus (69 / 50) (a : ℝ) y ≤ (qPairModUpper l r a : ℝ) := by
  have hlR : (0 : ℝ) ≤ l := by exact_mod_cast hl0
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha0
  have hy0 : 0 ≤ y := hlR.trans hyl
  have hru : ((((max |l ^ 2 - a ^ 2| |r ^ 2 - a ^ 2|) ^ 2 *
      ((r + a) ^ 2 + 4 * (69 / 50) ^ 2) *
      (max ((l - a) ^ 2) ((r - a) ^ 2) + 4 * (69 / 50) ^ 2) : ℚ)) : ℝ) ≤
      (qPairModUpper l r a : ℝ) := by
    exact_mod_cast RationalLogBounds.le_roundUp 100000 (by norm_num) _
  have hf1 : (y ^ 2 - (a : ℝ) ^ 2) ^ 2 ≤
      (max |(l : ℝ) ^ 2 - (a : ℝ) ^ 2| |(r : ℝ) ^ 2 - (a : ℝ) ^ 2|) ^ 2 := by
    have hly : (l : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith
    have hry : y ^ 2 ≤ (r : ℝ) ^ 2 := by nlinarith
    have habs : |y ^ 2 - (a : ℝ) ^ 2| ≤
        max |(l : ℝ) ^ 2 - (a : ℝ) ^ 2| |(r : ℝ) ^ 2 - (a : ℝ) ^ 2| := by
      rw [abs_le]; constructor
      · have h1 := neg_abs_le ((l : ℝ) ^ 2 - (a : ℝ) ^ 2)
        have h2 := le_max_left |(l : ℝ) ^ 2 - (a : ℝ) ^ 2| |(r : ℝ) ^ 2 - (a : ℝ) ^ 2|
        linarith
      · have h1 := le_abs_self ((r : ℝ) ^ 2 - (a : ℝ) ^ 2)
        have h2 := le_max_right |(l : ℝ) ^ 2 - (a : ℝ) ^ 2| |(r : ℝ) ^ 2 - (a : ℝ) ^ 2|
        linarith
    rw [← sq_abs (y ^ 2 - (a : ℝ) ^ 2)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hf2 : (y + (a : ℝ)) ^ 2 + 4 * (69 / 50 : ℝ) ^ 2 ≤
      ((r : ℝ) + (a : ℝ)) ^ 2 + 4 * (69 / 50 : ℝ) ^ 2 := by
    nlinarith
  have hf3 : (y - (a : ℝ)) ^ 2 + 4 * (69 / 50 : ℝ) ^ 2 ≤
      max (((l : ℝ) - (a : ℝ)) ^ 2) (((r : ℝ) - (a : ℝ)) ^ 2) + 4 * (69 / 50 : ℝ) ^ 2 := by
    have hsq : (y - (a : ℝ)) ^ 2 ≤ max (((l : ℝ) - (a : ℝ)) ^ 2) (((r : ℝ) - (a : ℝ)) ^ 2) := by
      rcases le_total y (a : ℝ) with hya | hay
      · exact le_max_of_le_left (by nlinarith)
      · exact le_max_of_le_right (by nlinarith)
    linarith
  apply le_trans _ hru
  unfold sixAdaptivePairModulus
  push_cast
  gcongr

/-! ## Cell structure, simultaneous 8-endpoint checker, and chain coverage -/

structure AnalyticCell where
  l : ℚ
  r : ℚ
  useLeft : Bool
  deriving DecidableEq, Repr

def sixCellPhiOpt (c : AnalyticCell) : Option ℚ :=
  if c.useLeft then
    match qPhaseUpper c.l with
    | some pl => some (pl + max 0 (qDerivUpper c.l c.r) * (c.r - c.l))
    | none => none
  else
    match qPhaseUpper c.r with
    | some pr => some (pr + max 0 (-(qDerivLower c.l c.r)) * (c.r - c.l))
    | none => none

/-- Simultaneous verification of all 8 `(bin, side)` endpoints on one cell `[c.l, c.r]`. -/
def checkAnalyticCell (c : AnalyticCell) : Bool :=
  if 0 ≤ c.l ∧ c.l < c.r ∧ c.r ≤ 2 then
    match sixCellPhiOpt c,
      qLogBound true (qPairModUpper c.l c.r (4 / 25)) 5 100000,
      qLogBound true (qPairModUpper c.l c.r (21 / 100)) 5 100000,
      qLogBound true (qPairModUpper c.l c.r (1 / 4)) 5 100000,
      qLogBound true (qPairModUpper c.l c.r (7 / 25)) 5 100000,
      qLogBound true (qPairModUpper c.l c.r (3 / 10)) 5 100000 with
    | some phiU, some lp0, some lp1, some lp2, some lp3, some lp4 =>
      let b0 := lp0 + lp1
      let b1 := lp0 + lp2
      let b2 := lp0 + lp3
      let b3 := lp0 + lp4
      decide (
        phiU + (sixBinKnotQ 0 0 / 4) * b0 ≤ sixSlimCaps 0 0 ∧
        phiU + (sixBinKnotQ 0 1 / 4) * b0 ≤ sixSlimCaps 0 1 ∧
        phiU + (sixBinKnotQ 1 0 / 4) * b1 ≤ sixSlimCaps 1 0 ∧
        phiU + (sixBinKnotQ 1 1 / 4) * b1 ≤ sixSlimCaps 1 1 ∧
        phiU + (sixBinKnotQ 2 0 / 4) * b2 ≤ sixSlimCaps 2 0 ∧
        phiU + (sixBinKnotQ 2 1 / 4) * b2 ≤ sixSlimCaps 2 1 ∧
        phiU + (sixBinKnotQ 3 0 / 4) * b3 ≤ sixSlimCaps 3 0 ∧
        phiU + (sixBinKnotQ 3 1 / 4) * b3 ≤ sixSlimCaps 3 1)
    | _, _, _, _, _, _ => false
  else false

theorem checkAnalyticCell_sound (c : AnalyticCell) (h : checkAnalyticCell c = true)
    (b : Fin 4) (side : Fin 2) {y : ℝ}
    (hyl : (c.l : ℝ) ≤ y) (hyr : y ≤ (c.r : ℝ))
    (hpos : ∀ j : Fin 2, 0 < sixAdaptivePairModulus (69 / 50) (sixSlimRoots b j : ℝ) y) :
    sixPhasePotential (fun j => (sixSlimRoots b j : ℝ)) (sixBinKnot b side) y ≤
      (sixSlimCaps b side : ℝ) := by
  unfold checkAnalyticCell at h
  by_cases hc : 0 ≤ c.l ∧ c.l < c.r ∧ c.r ≤ 2
  swap
  · simp [hc] at h
  rw [ite_eq_left hc] at h
  rcases hc with ⟨hl0, hlr, _hr2⟩
  have hlr' : c.l ≤ c.r := hlr.le
  have hr0 : 0 ≤ c.r := hl0.trans hlr'
  have hphi_bound : ∀ {phiU : ℚ}, sixCellPhiOpt c = some phiU → sixPhase y ≤ (phiU : ℝ) := by
    intro phiU hopt
    unfold sixCellPhiOpt at hopt
    have hcont : ContinuousOn sixPhase (Set.Icc (c.l : ℝ) (c.r : ℝ)) := fun x _ =>
      (sixPhase_hasDerivAt x).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ sixPhase (interior (Set.Icc (c.l : ℝ) (c.r : ℝ))) := fun x _ =>
      (sixPhase_hasDerivAt x).differentiableAt.differentiableWithinAt
    by_cases huse : c.useLeft = true
    · simp only [huse, ↓reduceIte] at hopt
      cases hpl : qPhaseUpper c.l with
      | none => simp [hpl] at hopt
      | some pl =>
        simp only [hpl, Option.some.injEq] at hopt; subst hopt
        have h1 := qPhaseUpper_sound hl0 hpl
        have hmvt := (convex_Icc (c.l : ℝ) (c.r : ℝ)).image_sub_le_mul_sub_of_deriv_le
          (C := (qDerivUpper c.l c.r : ℝ)) hcont hdiff
          (fun x hx => by
            have hx' := interior_subset hx
            rw [(sixPhase_hasDerivAt x).deriv]
            exact qDerivUpper_sound hl0 hlr' hx'.1 hx'.2)
          (c.l : ℝ) ⟨le_rfl, by exact_mod_cast hlr'⟩ y ⟨hyl, hyr⟩ hyl
        have hm1 : (qDerivUpper c.l c.r : ℝ) ≤ max (0 : ℝ) (qDerivUpper c.l c.r : ℝ) :=
          le_max_right _ _
        have hm2 : 0 ≤ max (0 : ℝ) (qDerivUpper c.l c.r : ℝ) := le_max_left _ _
        push_cast
        have hstep1 : (qDerivUpper c.l c.r : ℝ) * (y - (c.l : ℝ)) ≤
            max (0 : ℝ) (qDerivUpper c.l c.r : ℝ) * ((c.r : ℝ) - (c.l : ℝ)) := by
          calc _ ≤ max (0 : ℝ) (qDerivUpper c.l c.r : ℝ) * (y - (c.l : ℝ)) :=
                mul_le_mul_of_nonneg_right hm1 (by linarith)
            _ ≤ max (0 : ℝ) (qDerivUpper c.l c.r : ℝ) * ((c.r : ℝ) - (c.l : ℝ)) :=
                mul_le_mul_of_nonneg_left (by linarith) hm2
        linarith
    · simp only [huse, Bool.false_eq_true, ↓reduceIte] at hopt
      cases hpr : qPhaseUpper c.r with
      | none => simp [hpr] at hopt
      | some pr =>
        simp only [hpr, Option.some.injEq] at hopt; subst hopt
        have h1 := qPhaseUpper_sound hr0 hpr
        have hmvt := (convex_Icc (c.l : ℝ) (c.r : ℝ)).mul_sub_le_image_sub_of_le_deriv
          (C := (qDerivLower c.l c.r : ℝ)) hcont hdiff
          (fun x hx => by
            have hx' := interior_subset hx
            rw [(sixPhase_hasDerivAt x).deriv]
            exact qDerivLower_sound hl0 hlr' hx'.1 hx'.2)
          y ⟨hyl, hyr⟩ (c.r : ℝ) ⟨by exact_mod_cast hlr', le_rfl⟩ hyr
        have hm1 : -(qDerivLower c.l c.r : ℝ) ≤ max (0 : ℝ) (-(qDerivLower c.l c.r : ℝ)) :=
          le_max_right _ _
        have hm2 : 0 ≤ max (0 : ℝ) (-(qDerivLower c.l c.r : ℝ)) := le_max_left _ _
        push_cast
        have hstep1 : -(qDerivLower c.l c.r : ℝ) * ((c.r : ℝ) - y) ≤
            max (0 : ℝ) (-(qDerivLower c.l c.r : ℝ)) * ((c.r : ℝ) - (c.l : ℝ)) := by
          calc _ ≤ max (0 : ℝ) (-(qDerivLower c.l c.r : ℝ)) * ((c.r : ℝ) - y) :=
                mul_le_mul_of_nonneg_right hm1 (by linarith)
            _ ≤ max (0 : ℝ) (-(qDerivLower c.l c.r : ℝ)) * ((c.r : ℝ) - (c.l : ℝ)) :=
                mul_le_mul_of_nonneg_left (by linarith) hm2
        linarith
  cases hphi : sixCellPhiOpt c with
  | none => rw [hphi] at h; simp at h
  | some phiU =>
    cases h0 : qLogBound true (qPairModUpper c.l c.r (4 / 25)) 5 100000 with
    | none => rw [hphi, h0] at h; simp at h
    | some lp0 =>
      cases h1 : qLogBound true (qPairModUpper c.l c.r (21 / 100)) 5 100000 with
      | none => rw [hphi, h0, h1] at h; simp at h
      | some lp1 =>
        cases h2 : qLogBound true (qPairModUpper c.l c.r (1 / 4)) 5 100000 with
        | none => rw [hphi, h0, h1, h2] at h; simp at h
        | some lp2 =>
          cases h3 : qLogBound true (qPairModUpper c.l c.r (7 / 25)) 5 100000 with
          | none => rw [hphi, h0, h1, h2, h3] at h; simp at h
          | some lp3 =>
            cases h4 : qLogBound true (qPairModUpper c.l c.r (3 / 10)) 5 100000 with
            | none => rw [hphi, h0, h1, h2, h3, h4] at h; simp at h
            | some lp4 =>
              rw [hphi, h0, h1, h2, h3, h4] at h
              dsimp only at h
              rw [decide_eq_true_eq] at h
              have hphiR := hphi_bound hphi
              have hlog_pair : ∀ (a : ℚ) (lp : ℚ), 0 ≤ a →
                  qLogBound true (qPairModUpper c.l c.r a) 5 100000 = some lp →
                  0 < sixAdaptivePairModulus (69 / 50) (a : ℝ) y →
                  Real.log (sixAdaptivePairModulus (69 / 50) (a : ℝ) y) ≤ (lp : ℝ) := by
                intro a lp ha0 hq hp
                exact (Real.log_le_log hp (qPairModUpper_sound hl0 ha0 hyl hyr)).trans
                  (qLogBound_upper_sound hq)
              have hcomb : ∀ (b' : Fin 4) (s' : Fin 2) (a1 lp1 : ℚ),
                  sixSlimRoots b' 1 = a1 → 0 ≤ a1 →
                  qLogBound true (qPairModUpper c.l c.r a1) 5 100000 = some lp1 →
                  phiU + (sixBinKnotQ b' s' / 4) * (lp0 + lp1) ≤ sixSlimCaps b' s' →
                  (∀ j : Fin 2, 0 < sixAdaptivePairModulus (69 / 50) (sixSlimRoots b' j : ℝ) y) →
                  sixPhasePotential (fun j => (sixSlimRoots b' j : ℝ)) (sixBinKnot b' s') y ≤
                    (sixSlimCaps b' s' : ℝ) := by
                intro b' s' a1 lp1 h1eq h1a hlp1 hcapq hpos'
                have h0eq : sixSlimRoots b' 0 = 4 / 25 := by fin_cases b' <;> rfl
                have hl0' := hlog_pair (4 / 25) lp0 (by norm_num) h0 (by rw [← h0eq]; exact hpos' 0)
                have hl1' := hlog_pair a1 lp1 h1a hlp1 (by rw [← h1eq]; exact hpos' 1)
                have hq : ((phiU + sixBinKnotQ b' s' / 4 * (lp0 + lp1) : ℚ) : ℝ) ≤
                    (sixSlimCaps b' s' : ℝ) := by exact_mod_cast hcapq
                have ht0 : 0 ≤ (sixBinKnotQ b' s' : ℝ) / 4 := by
                  rw [sixBinKnotQ_cast]; unfold sixBinKnot; positivity
                unfold sixPhasePotential
                rw [Fin.sum_univ_two]
                dsimp only
                rw [h0eq, h1eq, ← sixBinKnotQ_cast b' s']
                push_cast at hq ⊢
                linarith [mul_le_mul_of_nonneg_left (add_le_add hl0' hl1') ht0]
              fin_cases b <;> fin_cases side
              · exact hcomb 0 0 (21 / 100) lp1 rfl (by norm_num) h1 h.1 hpos
              · exact hcomb 0 1 (21 / 100) lp1 rfl (by norm_num) h1 h.2.1 hpos
              · exact hcomb 1 0 (1 / 4) lp2 rfl (by norm_num) h2 h.2.2.1 hpos
              · exact hcomb 1 1 (1 / 4) lp2 rfl (by norm_num) h2 h.2.2.2.1 hpos
              · exact hcomb 2 0 (7 / 25) lp3 rfl (by norm_num) h3 h.2.2.2.2.1 hpos
              · exact hcomb 2 1 (7 / 25) lp3 rfl (by norm_num) h3 h.2.2.2.2.2.1 hpos
              · exact hcomb 3 0 (3 / 10) lp4 rfl (by norm_num) h4 h.2.2.2.2.2.2.1 hpos
              · exact hcomb 3 1 (3 / 10) lp4 rfl (by norm_num) h4 h.2.2.2.2.2.2.2 hpos

/-- Contiguous non-empty cell-chain verifier covering `[start, stop]`. -/
def checkCellChain (start stop : ℚ) : List AnalyticCell → Bool
  | [] => false
  | [c] => decide (c.l = start ∧ c.r = stop) && checkAnalyticCell c
  | c :: rest => decide (c.l = start) && checkAnalyticCell c && checkCellChain c.r stop rest

theorem checkCellChain_sound (start stop : ℚ) (cells : List AnalyticCell)
    (h : checkCellChain start stop cells = true)
    (b : Fin 4) (side : Fin 2) {y : ℝ}
    (hy0 : (start : ℝ) ≤ y) (hy1 : y ≤ (stop : ℝ))
    (hpos : ∀ j : Fin 2, 0 < sixAdaptivePairModulus (69 / 50) (sixSlimRoots b j : ℝ) y) :
    sixPhasePotential (fun j => (sixSlimRoots b j : ℝ)) (sixBinKnot b side) y ≤
      (sixSlimCaps b side : ℝ) := by
  induction cells generalizing start with
  | nil => simp [checkCellChain] at h
  | cons c rest ih =>
    cases rest with
    | nil =>
      simp only [checkCellChain, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨⟨hcl, hcr⟩, hcell⟩
      exact checkAnalyticCell_sound c hcell b side (by rw [hcl]; exact hy0) (by rw [hcr]; exact hy1) hpos
    | cons c2 rest2 =>
      simp only [checkCellChain, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨⟨hcl, hcell⟩, hrest⟩
      by_cases hyr : y ≤ (c.r : ℝ)
      · exact checkAnalyticCell_sound c hcell b side (by rw [hcl]; exact hy0) hyr hpos
      · exact ih c.r hrest (le_of_not_ge hyr)

end OddZetaSix
