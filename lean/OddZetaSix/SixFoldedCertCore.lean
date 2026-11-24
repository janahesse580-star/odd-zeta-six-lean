/-!
# Pure-Integer Folded Arithmetic Certificate Core (Zero Mathlib Imports)

Defines the compact certificate structures and ultra-fast pure `Nat`/`Int`
kernel checkers for both:
1. The periodic small-prime band (`[0, 1]` in `τ = {n/p}`, 12 folded radii);
2. The middle/high prime band (`[7/2, 55]` in `x = p/n`, 12 folded radii +
   `O(1)` 4-candidate refined slot cost + bit-packed `Nat` histogram + `N(v)`
   joint capacity integral).

Zero Mathlib imports, zero `List.set` inner mutations, zero `native_decide`,
zero `sorry`.
-/

set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix.CertCore

/-! ## Shared problem constants (`local50-45-209`) -/

/-- Fixed denominator `D = 10^8` for per-piece ceiling rational upper bounds. -/
def certDen : Nat := 100000000

/-- The 12 distinct centered radii (8 pole radii + 4 zero radii). -/
def radiusValNat : Nat → Nat
  | 0 => 14
  | 1 => 16
  | 2 => 17
  | 3 => 19
  | 4 => 20
  | 5 => 21
  | 6 => 23
  | 7 => 25
  | 8 => 27
  | 9 => 29
  | 10 => 30
  | _ => 70

/-- Pole block multiplicity for each of the 12 radii (`0` for the 4 zero-only radii). -/
def poleMultNat : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 1
  | 6 => 1
  | 7 => 5
  | _ => 0

/-- Signed weight in `B_+(τ, w) = max(0, 4 - v_fact + ∑ wt_i * Δ(r_i, τ, w))`. -/
def signedWeightNat : Nat → Int
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 1
  | 6 => 1
  | 7 => 5
  | 8 => 1
  | 9 => 1
  | 10 => 3
  | _ => -5

/-- Precomputed powers `256^v` for `v = 0..18` (bit-packed 19-bin histogram in a single `Nat`). -/
def pow256 : Nat → Nat
  | 0 => 1
  | 1 => 256
  | 2 => 65536
  | 3 => 16777216
  | 4 => 4294967296
  | 5 => 1099511627776
  | 6 => 281474976710656
  | 7 => 72057594037927936
  | 8 => 18446744073709551616
  | 9 => 4722366482869645213696
  | 10 => 1208925819614629174706176
  | 11 => 309485009821345068724781056
  | 12 => 79228162514264337593543950336
  | 13 => 20282409603651670423947251286016
  | 14 => 5192296858534827628530496329220096
  | 15 => 1329227995784915872903807060280344576
  | 16 => 340282366920938463463374607431768211456
  | 17 => 87112285931760246646623899502532662132736
  | _ => 22300745198530623141535718272648361505980416

/-- Ceiling integer division `⌈num / den⌉` for `den > 0`. -/
def ceilDiv (num den : Nat) : Nat :=
  if den = 0 then 0 else (num + den - 1) / den

/-- Check that `perm : List Nat` is a permutation of `[0, ..., 11]`. -/
def isPerm12 (perm : List Nat) : Bool :=
  let rec hasAll (k : Nat) : Bool :=
    match k with
    | 0 => true
    | k' + 1 => perm.contains k' && hasAll k'
  perm.length == 12 && hasAll 12

/-- Inverse lookup: index of `target` in `perm` (returns `12` if absent). -/
def indexOfNat (xs : List Nat) (target : Nat) : Nat :=
  let rec go : List Nat → Nat → Nat
    | [], _ => 12
    | h :: t, idx => if h == target then idx else go t (idx + 1)
  go xs 0

/-- Pure-integer affine ordering check `c0 + c1 * x ≤ d0 + d1 * x` at both endpoints
`ln/ld` and `rn/rd` (`ld, rd > 0`). -/
def affLE (ln ld rn rd : Nat) (c0 c1 d0 d1 : Int) : Bool :=
  c0 * (ld : Int) + c1 * (ln : Int) ≤ d0 * (ld : Int) + d1 * (ln : Int) &&
  c0 * (rd : Int) + c1 * (rn : Int) ≤ d0 * (rd : Int) + d1 * (rn : Int)

/-- Pure-integer check that a list of affine lines `(c0, c1)` is nondecreasing on `[ln/ld, rn/rd]`. -/
def checkSortedLines (ln ld rn rd : Nat) : List (Int × Int) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
      affLE ln ld rn rd a.1 a.2 b.1 b.2 && checkSortedLines ln ld rn rd (b :: rest)

/-- Pure-integer ceiling upper bound on `D * ∫_{ln/ld}^{rn/rd} (a0 + a1 * x) dx`
assuming `a0 + a1 * x ≥ 0` on `[ln/ld, rn/rd]`. -/
def affIntCeil (a0 a1 : Int) (ln ld rn rd D : Nat) : Nat :=
  let dx : Int := (rn : Int) * (ld : Int) - (ln : Int) * (rd : Int)
  let sum2 : Int := 2 * a0 * (ld : Int) * (rd : Int) +
    a1 * ((ln : Int) * (rd : Int) + (rn : Int) * (ld : Int))
  let num : Int := dx * sum2
  let den : Nat := 2 * (ld * rd) * (ld * rd)
  if num ≤ 0 then 0 else ceilDiv (num.toNat * D) den

/-! ## Part 1: Periodic Small-Prime Certificate (`τ ∈ [0, 1]`) -/

/-- One crossing-free 12-line piece on `[ln/ld, rn/rd] ⊆ [0, 1]`. -/
structure PeriodicPiece where
  ln : Nat
  ld : Nat
  rn : Nat
  rd : Nat
  perm : List Nat
  a0 : Int
  a1 : Int
  fbarNum : Nat
  c0Num : Nat
  deriving DecidableEq, Repr

/-- Midpoint floor `⌊m * τ⌋` at `τ = (ln/ld + rn/rd)/2`. -/
def periodicFloorVal (m ln ld rn rd : Nat) : Nat :=
  (m * (ln * rd + rn * ld)) / (2 * ld * rd)

/-- Check that `q = ⌊m * τ⌋` is constant across `[ln/ld, rn/rd]`. -/
def periodicFloorOk (m q ln ld rn rd : Nat) : Bool :=
  q * ld ≤ m * ln && m * rn ≤ (q + 1) * rd

/-- For radius `r` and `q2 = ⌊2 * r * τ⌋`, the doubled folded line `2 * L_r(τ) = c0 + c1 * τ ∈ [0, 1]`. -/
def periodicLine2 (rad q2 : Nat) : Int × Int :=
  let q := q2 / 2
  if q2 % 2 == 0 then
    (-2 * (q : Int), 2 * (rad : Int))
  else
    (2 * ((q + 1 : Nat) : Int), -2 * (rad : Int))

/-- Value of `Δ(rad, τ, w)` on strip `g ∈ 0..12` given `q2 = ⌊2 * rad * τ⌋` and `pos = rank(rad)`. -/
def periodicDelta (q2 pos g : Nat) : Int :=
  let q : Int := (q2 / 2 : Nat)
  if q2 % 2 == 0 then
    2 * q + (if g ≤ pos then 1 else 0)
  else
    2 * q + (if g ≤ pos then 1 else 2)

/-- Compute the 12-period weighted upper bound (in units of `1 / certDen`) for one piece `(a0, a1)`
on `[ln/ld, rn/rd]`, using the pure-rational left-endpoint weight `x^{-2} + (6 x^3)^{-1}` on
`t ∈ [max(2/7, k + l), k + r]` for `k = 0..11`. -/
def periodic12Ceil (a0 a1 : Int) (ln ld rn rd : Nat) : Nat :=
  let rec go (k acc : Nat) : Nat :=
    match k with
    | 0 => acc
    | k' + 1 =>
      let clip : Bool := k' == 0 && 7 * ln < 2 * ld
      let uln : Nat := if clip then 2 else ln
      let uld : Nat := if clip then 7 else ld
      let acc' :=
        if uln * rd < rn * uld then
          let xn : Nat := k' * uld + uln
          let xd : Nat := uld
          let dx : Int := (rn : Int) * (uld : Int) - (uln : Int) * (rd : Int)
          let sum2 : Int := 2 * a0 * (uld : Int) * (rd : Int) +
            a1 * ((uln : Int) * (rd : Int) + (rn : Int) * (uld : Int))
          let numI : Int := dx * sum2
          let denI : Nat := 2 * (uld * rd) * (uld * rd)
          let wNum : Nat := 6 * xd * xd * xn + xd * xd * xd
          let wDen : Nat := 6 * xn * xn * xn
          let contrib : Nat :=
            if numI ≤ 0 then 0
            else ceilDiv (numI.toNat * wNum * certDen) (denI * wDen)
          acc + contrib
        else acc
      go k' acc'
  go 12 0

/-- Complete pure-integer validity check for one `PeriodicPiece`. -/
def checkPeriodicPiece (p : PeriodicPiece) : Bool :=
  if p.ld == 0 || p.rd == 0 || !(p.ln * p.rd < p.rn * p.ld) then false
  else if !isPerm12 p.perm then false
  else
    -- 1. Compute and check the 12 `q2` floors + 3 zero factorial floors
    let q0 := periodicFloorVal 28 p.ln p.ld p.rn p.rd
    let q1 := periodicFloorVal 32 p.ln p.ld p.rn p.rd
    let q2 := periodicFloorVal 34 p.ln p.ld p.rn p.rd
    let q3 := periodicFloorVal 38 p.ln p.ld p.rn p.rd
    let q4 := periodicFloorVal 40 p.ln p.ld p.rn p.rd
    let q5 := periodicFloorVal 42 p.ln p.ld p.rn p.rd
    let q6 := periodicFloorVal 46 p.ln p.ld p.rn p.rd
    let q7 := periodicFloorVal 50 p.ln p.ld p.rn p.rd
    let q8 := periodicFloorVal 54 p.ln p.ld p.rn p.rd
    let q9 := periodicFloorVal 58 p.ln p.ld p.rn p.rd
    let q10 := periodicFloorVal 60 p.ln p.ld p.rn p.rd
    let q11 := periodicFloorVal 140 p.ln p.ld p.rn p.rd
    let z41 := periodicFloorVal 41 p.ln p.ld p.rn p.rd
    let z43 := periodicFloorVal 43 p.ln p.ld p.rn p.rd
    let floorsOk :=
      periodicFloorOk 28 q0 p.ln p.ld p.rn p.rd &&
      periodicFloorOk 32 q1 p.ln p.ld p.rn p.rd &&
      periodicFloorOk 34 q2 p.ln p.ld p.rn p.rd &&
      periodicFloorOk 38 q3 p.ln p.ld p.rn p.rd &&
      periodicFloorOk 40 q4 p.ln p.ld p.rn p.rd &&
      periodicFloorOk 42 q5 p.ln p.ld p.rn p.rd &&
      periodicFloorOk 46 q6 p.ln p.ld p.rn p.rd &&
      periodicFloorOk 50 q7 p.ln p.ld p.rn p.rd &&
      periodicFloorOk 54 q8 p.ln p.ld p.rn p.rd &&
      periodicFloorOk 58 q9 p.ln p.ld p.rn p.rd &&
      periodicFloorOk 60 q10 p.ln p.ld p.rn p.rd &&
      periodicFloorOk 140 q11 p.ln p.ld p.rn p.rd &&
      periodicFloorOk 41 z41 p.ln p.ld p.rn p.rd &&
      periodicFloorOk 43 z43 p.ln p.ld p.rn p.rd
    if !floorsOk then false
    else
      let getQ2 : Nat → Nat
        | 0 => q0 | 1 => q1 | 2 => q2 | 3 => q3 | 4 => q4 | 5 => q5
        | 6 => q6 | 7 => q7 | 8 => q8 | 9 => q9 | 10 => q10 | _ => q11
      -- Note: z40 == q4 (since 2 * 20 = 40!)
      let vPole : Int :=
        (q0 : Int) + 2 * (q1 : Int) + (q2 : Int) + (q3 : Int) +
        2 * (q4 : Int) + (q5 : Int) + (q6 : Int) + 5 * (q7 : Int)
      let vFact : Int := vPole - 2 * (3 * (q4 : Int) + (z41 : Int) + (z43 : Int))
      let pts : List (Int × Int) :=
        (0, 0) :: p.perm.map (fun idx => periodicLine2 (radiusValNat idx) (getQ2 idx)) ++ [(1, 0)]
      if !checkSortedLines p.ln p.ld p.rn p.rd pts then false
      else
        let p0 := indexOfNat p.perm 0
        let p1 := indexOfNat p.perm 1
        let p2 := indexOfNat p.perm 2
        let p3 := indexOfNat p.perm 3
        let p4 := indexOfNat p.perm 4
        let p5 := indexOfNat p.perm 5
        let p6 := indexOfNat p.perm 6
        let p7 := indexOfNat p.perm 7
        let p8 := indexOfNat p.perm 8
        let p9 := indexOfNat p.perm 9
        let p10 := indexOfNat p.perm 10
        let p11 := indexOfNat p.perm 11
        let rec sumStrips (g : Nat) (rem : List (Int × Int)) (a0 a1 : Int) : Int × Int :=
          match rem with
          | u :: v :: rest =>
            let val : Int := (4 - vFact)
              + periodicDelta q0 p0 g + 2 * periodicDelta q1 p1 g
              + periodicDelta q2 p2 g + periodicDelta q3 p3 g
              + 2 * periodicDelta q4 p4 g + periodicDelta q5 p5 g
              + periodicDelta q6 p6 g + 5 * periodicDelta q7 p7 g
              + periodicDelta q8 p8 g + periodicDelta q9 p9 g
              + 3 * periodicDelta q10 p10 g - 5 * periodicDelta q11 p11 g
            let B : Int := if val ≤ 0 then 0 else val
            sumStrips (g + 1) (v :: rest) (a0 + B * (v.1 - u.1)) (a1 + B * (v.2 - u.2))
          | _ => (a0, a1)
        let stripSum := sumStrips 0 pts 0 0
        if stripSum.1 != p.a0 || stripSum.2 != p.a1 then false
        else
          let nonnegL := 0 ≤ p.a0 * (p.ld : Int) + p.a1 * (p.ln : Int)
          let nonnegR := 0 ≤ p.a0 * (p.rd : Int) + p.a1 * (p.rn : Int)
          let fbarOk := affIntCeil p.a0 p.a1 p.ln p.ld p.rn p.rd certDen ≤ p.fbarNum
          let c0Ok := periodic12Ceil p.a0 p.a1 p.ln p.ld p.rn p.rd ≤ p.c0Num
          nonnegL && nonnegR && fbarOk && c0Ok

/-- Contiguous periodic shard checker with exact endpoint match (enables trivial `append` composition). -/
def checkPeriodicRun (curN curD endN endD accF accC fbarTotal c0Total : Nat) :
    List PeriodicPiece → Bool
  | [] => curN == endN && curD == endD && accF == fbarTotal && accC == c0Total
  | p :: rest =>
      p.ln == curN && p.ld == curD &&
      checkPeriodicPiece p &&
      checkPeriodicRun p.rn p.rd endN endD (accF + p.fbarNum) (accC + p.c0Num) fbarTotal c0Total rest

def checkPeriodicShard (startN startD endN endD fbarTotal c0Total : Nat)
    (ps : List PeriodicPiece) : Bool :=
  checkPeriodicRun startN startD endN endD 0 0 fbarTotal c0Total ps

private theorem checkPeriodicRun_shift (curN curD endN endD aF aC bF bC fT cT : Nat)
    (ps : List PeriodicPiece) :
    checkPeriodicRun curN curD endN endD (aF + bF) (aC + bC) (aF + fT) (aC + cT) ps =
    checkPeriodicRun curN curD endN endD bF bC fT cT ps := by
  induction ps generalizing curN curD bF bC with
  | nil =>
    simp only [checkPeriodicRun]
    have h1 : (aF + bF == aF + fT) = (bF == fT) := by
      cases h : (bF == fT) <;> simp_all
    have h2 : (aC + bC == aC + cT) = (bC == cT) := by
      cases h : (bC == cT) <;> simp_all
    rw [h1, h2]
  | cons p rest ih =>
    simp only [checkPeriodicRun, Nat.add_assoc]
    rw [ih]

theorem checkPeriodicShard_append {n0 d0 n1 d1 n2 d2 f1 c1 f2 c2 : Nat}
    {ps1 ps2 : List PeriodicPiece}
    (h1 : checkPeriodicShard n0 d0 n1 d1 f1 c1 ps1 = true)
    (h2 : checkPeriodicShard n1 d1 n2 d2 f2 c2 ps2 = true) :
    checkPeriodicShard n0 d0 n2 d2 (f1 + f2) (c1 + c2) (ps1 ++ ps2) = true := by
  unfold checkPeriodicShard at *
  suffices h : ∀ curN curD accF accC,
      checkPeriodicRun curN curD n1 d1 accF accC f1 c1 ps1 = true →
      checkPeriodicRun curN curD n2 d2 accF accC (f1 + f2) (c1 + c2) (ps1 ++ ps2) = true from
    h n0 d0 0 0 h1
  clear h1
  induction ps1 with
  | nil =>
    intro curN curD accF accC h
    simp only [checkPeriodicRun, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
    simp only [List.nil_append]
    have hsh := checkPeriodicRun_shift curN curD n2 d2 accF accC 0 0 f2 c2 ps2
    simp only [Nat.add_zero] at hsh
    rw [hsh]
    exact h2
  | cons p rest ih =>
    intro curN curD accF accC h
    simp only [List.cons_append, checkPeriodicRun, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih p.rn p.rd (accF + p.fbarNum) (accC + p.c0Num) h.2⟩

theorem checkPeriodicShard_append_eq {n0 d0 n1 d1 n2 d2 f1 c1 f2 c2 f3 c3 : Nat}
    {ps1 ps2 : List PeriodicPiece}
    (hf : f1 + f2 = f3) (hc : c1 + c2 = c3)
    (h1 : checkPeriodicShard n0 d0 n1 d1 f1 c1 ps1 = true)
    (h2 : checkPeriodicShard n1 d1 n2 d2 f2 c2 ps2 = true) :
    checkPeriodicShard n0 d0 n2 d2 f3 c3 (ps1 ++ ps2) = true := by
  subst hf; subst hc
  exact checkPeriodicShard_append h1 h2

/-! ## Part 2: Middle/High Prime Certificate (`x = p/n ∈ [7/2, 55]`) -/

/-- One flat high-band tile on `[ln/ld, rn/rd] ⊆ [7/2, 55]` using `joint q`. -/
structure HighTile where
  ln : Nat
  ld : Nat
  rn : Nat
  rd : Nat
  q : Nat
  perm : List Nat
  uNum : Nat
  deriving DecidableEq, Repr

/-- Midpoint floor `⌊num / x⌋` at `x = (ln/ld + rn/rd)/2`. -/
def highFloorVal (num ln ld rn rd : Nat) : Nat :=
  (2 * num * ld * rd) / (ln * rd + rn * ld)

/-- Check that `q = ⌊num / x⌋` is constant across `[ln/ld, rn/rd]`. -/
def highFloorOk (num q ln ld rn rd : Nat) : Bool :=
  q * rn ≤ num * rd && num * ld ≤ (q + 1) * ln

/-- For radius `rad` and `q2 = ⌊2 * rad / x⌋`, the doubled folded line `2 * L_r(x) = c0 + c1 * x ∈ [0, x]`. -/
def highLine2 (rad q2 : Nat) : Int × Int :=
  let q := q2 / 2
  if q2 % 2 == 0 then
    (2 * (rad : Int), -2 * (q : Int))
  else
    (-2 * (rad : Int), 2 * ((q + 1 : Nat) : Int))

/-- `O(1)` 4-candidate refined order cost `C_{k, r}` (provably equal to `SixLocalSlots.sixRefinedOrderCost`). -/
def refinedOrderCostO1 (m : Nat) (baseVal : Int) (daZero : Bool) (numAliases : Nat)
    (iEven iOdd r : Nat) : Nat :=
  let evalL (l ind : Nat) : Nat :=
    let d := m - 1 - l - r
    let d' := if daZero then min d numAliases else d
    let v : Int := (r : Int) - baseVal + (d' : Int) + ((l + 5 : Nat) : Int) * (ind : Int)
    if v ≤ 0 then 0 else v.toNat
  let Lmax := m - 1 - r
  let maxEven := if Lmax % 2 == 0 then Lmax else Lmax - 1
  let b0 := evalL 0 iEven
  let b1 := if maxEven > 0 then max b0 (evalL maxEven iEven) else b0
  if Lmax ≥ 1 then
    let b2 := max b1 (evalL 1 iOdd)
    let maxOdd := if Lmax % 2 == 1 then Lmax else Lmax - 1
    if maxOdd > 1 then max b2 (evalL maxOdd iOdd) else b2
  else b1

/-- Accumulate the `m` refined slot costs `[B_{k, 0}, ..., B_{k, m-1}]` directly into a
bit-packed `Nat` histogram (`∑ hist[v] * 256^v`).
When `daZero == false`, all `m` slots share a single constant cost `B` (O(1) single addition!). -/
def addBranchSlotsPacked (m : Nat) (baseVal : Int) (daZero : Bool) (numAliases : Nat)
    (iEven iOdd : Nat) (packedHist : Nat) : Nat :=
  if !daZero then
    let v : Int := (m : Int) - 1 - baseVal + 5 * (iEven : Int)
    let b : Nat := if v ≤ 0 then 0 else min v.toNat 18
    if b == 0 then packedHist else packedHist + m * pow256 b
  else
    let rec go (rem curMax acc : Nat) : Nat :=
      match rem with
      | 0 => acc
      | r + 1 =>
        let c := refinedOrderCostO1 m baseVal true numAliases iEven iOdd r
        let b := max curMax c
        let acc' := if b == 0 then acc else acc + pow256 (min b 18)
        go r b acc'
    go m 0 packedHist

/-- Decode suffix counts `N(v) = #{slots with cost ≥ v}` for `v = 1..18` from a bit-packed histogram,
and evaluate `cap_j = max(min(q, N(j)), max_{k : q+k < N(j+2k)} (q+k+1))` for a single `j ∈ 1..18`. -/
def packedToSuffixCounts (packedHist : Nat) : List Nat :=
  -- Build `[N(0)=0, N(1), ..., N(18)]` in one backward pass (18 GMP shifts/mods)
  let rec go (v running : Nat) (acc : List Nat) : List Nat :=
    match v with
    | 0 => 0 :: acc
    | v' + 1 =>
      let cnt := (packedHist / pow256 (v' + 1)) % 256
      let running' := running + cnt
      go v' running' (running' :: acc)
  go 18 0 []

/-- Compute `cap_j = #{r : w_r - 2 * max(0, r - q) ≥ j}` from `Nlist = [0, N(1), ..., N(18)]`
using pure structural recursion on `Nat` (ZERO `WellFounded.fix` kernel overhead!). -/
def jointCapFromN (Nlist : List Nat) (q j : Nat) : Nat :=
  let rec go (steps k best : Nat) : Nat :=
    match steps with
    | 0 => best
    | s + 1 =>
      let vv := j + 2 * k
      if vv > 18 then best
      else
        let nv := Nlist.getD vv 0
        let best' := if q + k < nv then max best (q + k + 1) else best
        go s (k + 1) best'
  go 10 0 (min q (Nlist.getD j 0))

/-- Exact pure-integer ceiling upper bound on `D * ∫_{ln/ld}^{rn/rd} min(15, (u0 + u1 * x) / 2) dx`. -/
def capIntCeil (u0 u1 : Int) (ln ld rn rd D : Nat) : Nat :=
  let va : Int := u0 * (ld : Int) + u1 * (ln : Int)
  let vb : Int := u0 * (rd : Int) + u1 * (rn : Int)
  let capL : Int := 30 * (ld : Int)
  let capR : Int := 30 * (rd : Int)
  let dx : Int := (rn : Int) * (ld : Int) - (ln : Int) * (rd : Int)
  if va ≤ capL && vb ≤ capR then
    let num : Int := dx * (va * (rd : Int) + vb * (ld : Int))
    let den : Nat := 4 * (ld * rd) * (ld * rd)
    if num ≤ 0 then 0 else ceilDiv (num.toNat * D) den
  else if capL ≤ va && capR ≤ vb then
    let num : Int := 15 * dx
    let den : Nat := ld * rd
    if num ≤ 0 then 0 else ceilDiv (num.toNat * D) den
  else if va < capL && capR < vb then
    let s : Nat := u1.toNat
    let diff : Int := capL - va
    let num : Int := 60 * (ld : Int) * (s : Int) * dx - (rd : Int) * diff * diff
    let den : Nat := 4 * ld * ld * rd * s
    if num ≤ 0 then 0 else ceilDiv (num.toNat * D) den
  else
    let s : Nat := (-u1).toNat
    let diff : Int := capR - vb
    let num : Int := 60 * (rd : Int) * (s : Int) * dx - (ld : Int) * diff * diff
    let den : Nat := 4 * ld * rd * rd * s
    if num ≤ 0 then 0 else ceilDiv (num.toNat * D) den

/-- Sum `∑_{k=q+1}^{K} k` in O(1): `K*(K+1)/2 - q*(q+1)/2`. -/
def sumRangeIcc (q K : Nat) : Nat :=
  K * (K + 1) / 2 - q * (q + 1) / 2

/-- Complete ultra-fast pure-integer validity check for one flat `HighTile`. -/
def checkHighTile (t : HighTile) : Bool :=
  if t.ld == 0 || t.rd == 0 || !(t.ln * t.rd < t.rn * t.ld) then false
  else if !(7 * t.ld ≤ 2 * t.ln) || !(t.rn ≤ 55 * t.rd) then false
  else if !isPerm12 t.perm then false
  else
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
    let floorsOk :=
      t.q ≤ k30 &&
      highFloorOk 30 k30 t.ln t.ld t.rn t.rd &&
      highFloorOk 28 q0 t.ln t.ld t.rn t.rd &&
      highFloorOk 32 q1 t.ln t.ld t.rn t.rd &&
      highFloorOk 34 q2 t.ln t.ld t.rn t.rd &&
      highFloorOk 38 q3 t.ln t.ld t.rn t.rd &&
      highFloorOk 40 q4 t.ln t.ld t.rn t.rd &&
      highFloorOk 42 q5 t.ln t.ld t.rn t.rd &&
      highFloorOk 46 q6 t.ln t.ld t.rn t.rd &&
      highFloorOk 50 q7 t.ln t.ld t.rn t.rd &&
      highFloorOk 54 q8 t.ln t.ld t.rn t.rd &&
      highFloorOk 58 q9 t.ln t.ld t.rn t.rd &&
      highFloorOk 60 q10 t.ln t.ld t.rn t.rd &&
      highFloorOk 140 q11 t.ln t.ld t.rn t.rd &&
      highFloorOk 41 z41 t.ln t.ld t.rn t.rd &&
      highFloorOk 43 z43 t.ln t.ld t.rn t.rd
    if !floorsOk then false
    else
      let getQ2 : Nat → Nat
        | 0 => q0 | 1 => q1 | 2 => q2 | 3 => q3 | 4 => q4 | 5 => q5
        | 6 => q6 | 7 => q7 | 8 => q8 | 9 => q9 | 10 => q10 | _ => q11
      let vPole : Int :=
        (q0 : Int) + 2 * (q1 : Int) + (q2 : Int) + (q3 : Int) +
        2 * (q4 : Int) + (q5 : Int) + (q6 : Int) + 5 * (q7 : Int)
      let vFact : Int := vPole - 2 * (3 * (q4 : Int) + (z41 : Int) + (z43 : Int))
      let pts : List (Int × Int) :=
        (0, 0) :: t.perm.map (fun idx => highLine2 (radiusValNat idx) (getQ2 idx)) ++ [(0, 1)]
      if !checkSortedLines t.ln t.ld t.rn t.rd pts then false
      else
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
        let k25 : Nat := q7 / 2
        let q30 : Nat := q10 / 2
        let s30 : Nat := q10 % 2
        -- Compute list of `(w0, w1, Nlist)` for each active strip `g ∈ 0..12`
        let deltaOf (qv pv g : Nat) : Nat :=
          let qr := qv / 2
          if qv % 2 == 0 then 2 * qr + (if g ≤ pv then 1 else 0)
          else 2 * qr + (if g ≤ pv then 1 else 2)
        let mkPlus (m g : Nat) : Nat :=
          let f (qv pv mult : Nat) : Nat :=
            let qr := qv / 2
            if m < qr || (m == qr && (qv % 2 == 1 || g ≤ pv)) then mult else 0
          f q0 p0 1 + f q1 p1 2 + f q2 p2 1 + f q3 p3 1 +
          f q4 p4 2 + f q5 p5 1 + f q6 p6 1 + f q7 p7 5
        let mkMinus (m g : Nat) : Nat :=
          let f (qv pv mult : Nat) : Nat :=
            let qr := qv / 2
            if m ≤ qr || (m == qr + 1 && qv % 2 == 1 && pv < g) then mult else 0
          f q0 p0 1 + f q1 p1 2 + f q2 p2 1 + f q3 p3 1 +
          f q4 p4 2 + f q5 p5 1 + f q6 p6 1 + f q7 p7 5
        -- Strip summary: either `fast (Np, B)` (O(1), 94.1% of all strips!) or `gen Nlist` (5.9% at large x)
        let rec buildStrips (g : Nat) (rem : List (Int × Int)) :
            List (Int × Int × Sum (Nat × Nat) (List Nat)) :=
          match rem with
          | u :: v :: rest =>
            let w0 : Int := v.1 - u.1
            let w1 : Int := v.2 - u.2
            let tail := buildStrips (g + 1) (v :: rest)
            if w0 == 0 && w1 == 0 then tail
            else
              let Np : Nat :=
                deltaOf q0 p0 g + 2 * deltaOf q1 p1 g + deltaOf q2 p2 g + deltaOf q3 p3 g +
                2 * deltaOf q4 p4 g + deltaOf q5 p5 g + deltaOf q6 p6 g + 5 * deltaOf q7 p7 g
              let Nz : Nat :=
                5 * deltaOf q11 p11 g - (deltaOf q8 p8 g + deltaOf q9 p9 g + 3 * deltaOf q10 p10 g)
              let lt30 : Bool := g ≤ p10
              let f30Plus : Nat := q30 + (if s30 == 1 && !lt30 then 1 else 0)
              let f30Minus : Nat := q30 - (if s30 == 0 && !lt30 then 1 else 0)
              if 15 ≤ Np && 1 ≤ f30Plus then
                let bInt : Int := 4 + (Np : Int) - (Nz : Int) - vFact
                let B : Nat := if bInt ≤ 0 then 0 else bInt.toNat
                (w0, w1, Sum.inl (Np, B)) :: tail
              else
                let rec addPlus (remM : Nat) (h : Nat) : Nat :=
                  match remM with
                  | 0 => h
                  | m + 1 =>
                    let mk := mkPlus m g
                    let h' :=
                      if mk == 0 then h
                      else
                        let right := m + f30Plus
                        let left := f30Minus - m
                        let da := Np - mk
                        let baseVal : Int := vFact + (Nz : Int) - (da : Int)
                        let iE := if 1 ≤ right then 1 else 0
                        let iO := if left < right then 1 else 0
                        addBranchSlotsPacked mk baseVal (da == 0) Nz iE iO h
                    addPlus m h'
                let rec addMinus (remM : Nat) (h : Nat) : Nat :=
                  match remM with
                  | 0 => h
                  | m0 + 1 =>
                    let m := m0 + 1
                    let mk := mkMinus m g
                    let h' :=
                      if mk == 0 then h
                      else
                        let right := m + f30Minus
                        let left := f30Plus - m
                        let da := Np - mk
                        let baseVal : Int := vFact + (Nz : Int) - (da : Int)
                        let iE := if 1 ≤ right then 1 else 0
                        let iO := if left < right then 1 else 0
                        addBranchSlotsPacked mk baseVal (da == 0) Nz iE iO h
                    addMinus m0 h'
                let packed := addMinus (k25 + 1) (addPlus (k25 + 1) 0)
                let Nlist := packedToSuffixCounts packed
                (w0, w1, Sum.inr Nlist) :: tail
          | _ => []
        let strips := buildStrips 0 pts
        -- Sum capped integrals for `j = 1..18` directly (NO `List.set`!)
        let rec sumCaps (j : Nat) (acc : Nat) : Nat :=
          match j with
          | 0 => acc
          | j' + 1 =>
            let rec accumJ : List (Int × Int × Sum (Nat × Nat) (List Nat)) → Int → Int → Int × Int
              | [], u0, u1 => (u0, u1)
              | (w0, w1, info) :: rest, u0, u1 =>
                let mult := match info with
                  | Sum.inl (Np, B) => if j' + 1 ≤ B then min Np (t.q + 1 + (B - (j' + 1)) / 2) else 0
                  | Sum.inr Nlist => jointCapFromN Nlist t.q (j' + 1)
                if mult == 0 then accumJ rest u0 u1
                else accumJ rest (u0 + (mult : Int) * w0) (u1 + (mult : Int) * w1)
            let ab := accumJ strips 0 0
            sumCaps j' (acc + capIntCeil ab.1 ab.2 t.ln t.ld t.rn t.rd certDen)
        let p0 : Int := 30 * ((k30 - t.q : Nat) : Int)
        let p1 : Int := -((sumRangeIcc t.q k30 : Nat) : Int)
        let perCeil : Nat := affIntCeil p0 p1 t.ln t.ld t.rn t.rd certDen
        let capCeil : Nat := sumCaps 18 0
        perCeil + capCeil ≤ t.uNum

/-- Contiguous high-band shard checker with exact endpoint match (enables trivial `append` composition). -/
def checkHighRun (curN curD endN endD accU uTotal : Nat) : List HighTile → Bool
  | [] => curN == endN && curD == endD && accU == uTotal
  | t :: rest =>
      t.ln == curN && t.ld == curD &&
      checkHighTile t &&
      checkHighRun t.rn t.rd endN endD (accU + t.uNum) uTotal rest

def checkHighShard (startN startD endN endD uTotal : Nat) (ts : List HighTile) : Bool :=
  checkHighRun startN startD endN endD 0 uTotal ts

private theorem checkHighRun_shift (curN curD endN endD aU bU uT : Nat)
    (ts : List HighTile) :
    checkHighRun curN curD endN endD (aU + bU) (aU + uT) ts =
    checkHighRun curN curD endN endD bU uT ts := by
  induction ts generalizing curN curD bU with
  | nil =>
    simp only [checkHighRun]
    have h : (aU + bU == aU + uT) = (bU == uT) := by
      cases hb : (bU == uT) <;> simp_all
    rw [h]
  | cons t rest ih =>
    simp only [checkHighRun, Nat.add_assoc]
    rw [ih]

theorem checkHighShard_append {n0 d0 n1 d1 n2 d2 u1 u2 : Nat}
    {ts1 ts2 : List HighTile}
    (h1 : checkHighShard n0 d0 n1 d1 u1 ts1 = true)
    (h2 : checkHighShard n1 d1 n2 d2 u2 ts2 = true) :
    checkHighShard n0 d0 n2 d2 (u1 + u2) (ts1 ++ ts2) = true := by
  unfold checkHighShard at *
  suffices h : ∀ curN curD accU,
      checkHighRun curN curD n1 d1 accU u1 ts1 = true →
      checkHighRun curN curD n2 d2 accU (u1 + u2) (ts1 ++ ts2) = true from
    h n0 d0 0 h1
  clear h1
  induction ts1 with
  | nil =>
    intro curN curD accU h
    simp only [checkHighRun, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
    simp only [List.nil_append]
    have hsh := checkHighRun_shift curN curD n2 d2 accU 0 u2 ts2
    simp only [Nat.add_zero] at hsh
    rw [hsh]
    exact h2
  | cons t rest ih =>
    intro curN curD accU h
    simp only [List.cons_append, checkHighRun, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih t.rn t.rd (accU + t.uNum) h.2⟩

theorem checkHighShard_append_eq {n0 d0 n1 d1 n2 d2 u1 u2 u3 : Nat}
    {ts1 ts2 : List HighTile}
    (hu : u1 + u2 = u3)
    (h1 : checkHighShard n0 d0 n1 d1 u1 ts1 = true)
    (h2 : checkHighShard n1 d1 n2 d2 u2 ts2 = true) :
    checkHighShard n0 d0 n2 d2 u3 (ts1 ++ ts2) = true := by
  subst hu
  exact checkHighShard_append h1 h2

end OddZetaSix.CertCore
