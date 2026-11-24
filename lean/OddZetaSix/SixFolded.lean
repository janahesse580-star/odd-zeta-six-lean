import OddZetaSix.SixSmallPrimes
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort

/-!
# Stage 2A (File 3): Doubled-Integer Folded Cauchy–Binet Framework

Implements the purely algebraic doubled Cauchy–Binet valuation framework
(`zeta6_irrationality_proof.tex`, §2.2) without ramified field extensions:

1. `DoubledValAtLeast` / `DoubledFormalValAtLeast` (`2 * v_p(x) ≥ a`) and exact
   Cauchy–Binet expansion `cauchy_binet_det_mul` over any commutative ring `R`.
2. **Doubled Cauchy–Binet valuation theorem** (`doubled_cauchy_binet_formalValAtLeast`):
   if `2 * v_p^G(W u v) ≥ -(B u + B v)` and every nonzero `h`-minor of `Y` satisfies
   `2 * v_p(det Y_{*,I}) - ∑_{u ∈ I} B u ≥ -U`, then
   `FormalValAtLeast p (-U) (det (Y_C * W * Y_Cᵀ))`.
3. **Folded residue classes** `foldMod p hp x : Fin (p / 2 + 1)` for odd prime `p`,
   integer re-expansion of `Y_q` on each folded class via `SixTaylor` eq. (7), and
   descending class-weight sorting yielding:
   - `folded_joint_formalValAtLeast`: full folded joint capacity bound with layer cap `min h`
     for arbitrary `q : ℕ`;
   - `unfolded_formalValAtLeast`: unfolded direct bound with layer cap `min h` for arbitrary `q : ℕ`;
   - `coarse_tail_sum_le_four_mul` (`∀ B ≤ 18, ∑_{k=1}^B (B - 2k) ≤ 4B`) and
     `folded_periodic_coarse_formalValAtLeast`: single-line coarse periodic bound
     `(2 * h / p + 5) * ∑ c, B_max c` (taking `q = 2 * h / p`).
-/

noncomputable section
set_option autoImplicit false

namespace OddZetaSix

open Polynomial Finset

/-! ## Doubled-integer `p`-adic valuation floors (avoiding ramified extensions) -/

/-- Doubled zero-safe `p`-adic valuation floor: `x = 0 ∨ a ≤ 2 * v_p(x)`. -/
def DoubledValAtLeast (p : ℕ) (a : ℤ) (x : ℚ) : Prop :=
  x = 0 ∨ a ≤ 2 * padicValRat p x

/-- Coefficientwise doubled Gauss valuation floor on `SixPolynomial`. -/
def DoubledFormalValAtLeast (p : ℕ) (a : ℤ) (F : SixPolynomial) : Prop :=
  ∀ m : Fin 6 →₀ ℕ, DoubledValAtLeast p a (F.coeff m)

theorem doubledValAtLeast_zero (p : ℕ) (a : ℤ) : DoubledValAtLeast p a 0 := Or.inl rfl

theorem doubledValAtLeast_one (p : ℕ) [Fact p.Prime] : DoubledValAtLeast p 0 1 :=
  Or.inr (by simp)

theorem doubledValAtLeast_mono {p : ℕ} {a b : ℤ} {x : ℚ}
    (h : DoubledValAtLeast p a x) (hab : b ≤ a) : DoubledValAtLeast p b x :=
  h.elim Or.inl (fun hx => Or.inr (hab.trans hx))

theorem doubledValAtLeast_neg {p : ℕ} {a : ℤ} {x : ℚ}
    (h : DoubledValAtLeast p a x) : DoubledValAtLeast p a (-x) := by
  rcases h with rfl | h
  · simpa using doubledValAtLeast_zero p a
  · exact Or.inr (by simpa using h)

theorem doubledValAtLeast_of_valAtLeast {p : ℕ} {a : ℤ} {x : ℚ}
    (h : ValAtLeast p a x) : DoubledValAtLeast p (2 * a) x :=
  h.elim Or.inl (fun hx => Or.inr (by linarith))

theorem valAtLeast_of_doubled_two_mul {p : ℕ} {a : ℤ} {x : ℚ}
    (h : DoubledValAtLeast p (2 * a) x) : ValAtLeast p a x :=
  h.elim Or.inl (fun hx => Or.inr (by omega))

theorem doubledValAtLeast_add {p : ℕ} [Fact p.Prime] {a : ℤ} {x y : ℚ}
    (hx : DoubledValAtLeast p a x) (hy : DoubledValAtLeast p a y) :
    DoubledValAtLeast p a (x + y) := by
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  rcases hx with rfl | hx
  · simpa using hy
  rcases hy with rfl | hy
  · exact Or.inr (by simpa using hx)
  right
  have hmin := padicValRat.min_le_padicValRat_add (p := p) hxy
  have h1 : a ≤ 2 * min (padicValRat p x) (padicValRat p y) := by omega
  linarith

theorem doubledValAtLeast_mul {p : ℕ} [Fact p.Prime] {a b : ℤ} {x y : ℚ}
    (hx : DoubledValAtLeast p a x) (hy : DoubledValAtLeast p b y) :
    DoubledValAtLeast p (a + b) (x * y) := by
  by_cases hx0 : x = 0
  · simp [hx0, doubledValAtLeast_zero]
  by_cases hy0 : y = 0
  · simp [hy0, doubledValAtLeast_zero]
  right
  rw [padicValRat.mul hx0 hy0]
  have hx' := hx.resolve_left hx0
  have hy' := hy.resolve_left hy0
  linarith

theorem doubledValAtLeast_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → ℚ) (a : ℤ) (hf : ∀ i ∈ s, DoubledValAtLeast p a (f i)) :
    DoubledValAtLeast p a (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using doubledValAtLeast_zero p a
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact doubledValAtLeast_add (hf i (mem_insert_self _ _))
      (ih (fun j hj => hf j (mem_insert_of_mem hj)))

theorem doubledFormalValAtLeast_zero (p : ℕ) (a : ℤ) : DoubledFormalValAtLeast p a 0 :=
  fun m => by simp [doubledValAtLeast_zero]

theorem doubledFormalValAtLeast_one (p : ℕ) [Fact p.Prime] : DoubledFormalValAtLeast p 0 1 := by
  intro m
  exact doubledValAtLeast_of_valAtLeast (formalValAtLeast_one p m)

theorem doubledFormalValAtLeast_mono {p : ℕ} {a b : ℤ} {F : SixPolynomial}
    (h : DoubledFormalValAtLeast p a F) (hab : b ≤ a) : DoubledFormalValAtLeast p b F :=
  fun m => doubledValAtLeast_mono (h m) hab

theorem doubledFormalValAtLeast_neg {p : ℕ} {a : ℤ} {F : SixPolynomial}
    (h : DoubledFormalValAtLeast p a F) : DoubledFormalValAtLeast p a (-F) := by
  intro m; rw [MvPolynomial.coeff_neg]; exact doubledValAtLeast_neg (h m)

theorem doubledFormalValAtLeast_add {p : ℕ} [Fact p.Prime] {a : ℤ} {F G : SixPolynomial}
    (hF : DoubledFormalValAtLeast p a F) (hG : DoubledFormalValAtLeast p a G) :
    DoubledFormalValAtLeast p a (F + G) := by
  intro m
  have h : (F + G).coeff m = F.coeff m + G.coeff m := by simp
  rw [h]
  exact doubledValAtLeast_add (hF m) (hG m)

theorem doubledFormalValAtLeast_mul {p : ℕ} [Fact p.Prime] {a b : ℤ} {F G : SixPolynomial}
    (hF : DoubledFormalValAtLeast p a F) (hG : DoubledFormalValAtLeast p b G) :
    DoubledFormalValAtLeast p (a + b) (F * G) := by
  intro m
  rw [MvPolynomial.coeff_mul]
  exact doubledValAtLeast_sum _ _ _ (fun x _ => doubledValAtLeast_mul (hF x.1) (hG x.2))

theorem doubledFormalValAtLeast_C_mul {p : ℕ} [Fact p.Prime] {a b : ℤ} {c : ℚ}
    {F : SixPolynomial} (hc : DoubledValAtLeast p a c) (hF : DoubledFormalValAtLeast p b F) :
    DoubledFormalValAtLeast p (a + b) (MvPolynomial.C c * F) := by
  intro m
  rw [MvPolynomial.coeff_C_mul]
  exact doubledValAtLeast_mul hc (hF m)

theorem doubledFormalValAtLeast_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → SixPolynomial) (a : ℤ) (hf : ∀ i ∈ s, DoubledFormalValAtLeast p a (f i)) :
    DoubledFormalValAtLeast p a (∑ i ∈ s, f i) := by
  intro m
  rw [MvPolynomial.coeff_sum]
  exact doubledValAtLeast_sum s (fun i => (f i).coeff m) a (fun i hi => hf i hi m)

theorem doubledFormalValAtLeast_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → SixPolynomial) (a : ι → ℤ) (hf : ∀ i ∈ s, DoubledFormalValAtLeast p (a i) (f i)) :
    DoubledFormalValAtLeast p (∑ i ∈ s, a i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using doubledFormalValAtLeast_one p
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact doubledFormalValAtLeast_mul (hf i (mem_insert_self _ _))
      (ih (fun j hj => hf j (mem_insert_of_mem hj)))

theorem formalValAtLeast_of_doubled_two_mul {p : ℕ} {a : ℤ} {F : SixPolynomial}
    (h : DoubledFormalValAtLeast p (2 * a) F) : FormalValAtLeast p a F :=
  fun m => valAtLeast_of_doubled_two_mul (h m)

theorem doubledFormalValAtLeast_of_formal {p : ℕ} {a : ℤ} {F : SixPolynomial}
    (h : FormalValAtLeast p a F) : DoubledFormalValAtLeast p (2 * a) F :=
  fun m => doubledValAtLeast_of_valAtLeast (h m)

/-! ## Exact Cauchy–Binet formula over any commutative ring -/

/-- Row-multilinear injective expansion of `det (A * B)` for any finite inner index `α`. -/
theorem det_mul_eq_sum_injective {R : Type*} [CommRing R] {h : ℕ}
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix (Fin h) α R) (B : Matrix α (Fin h) R) :
    (A * B).det =
      ∑ f ∈ (Finset.univ : Finset (Fin h → α)).filter Function.Injective,
        (∏ i : Fin h, A i (f i)) * (B.submatrix f id).det := by
  classical
  have hfull : (A * B).det =
      ∑ f : Fin h → α, (∏ i : Fin h, A i (f i)) * (B.submatrix f id).det := by
    let D := (Matrix.detRowAlternating (R := R) (n := Fin h)).toMultilinearMap
    have hmul : A * B = fun i => ∑ j : α, A i j • B j := by
      ext i k
      simp [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change D (A * B) = _
    rw [hmul, D.map_sum]
    apply Finset.sum_congr rfl; intro f _
    rw [D.map_smul_univ]; rfl
  rw [hfull, Finset.sum_filter]
  apply Finset.sum_congr rfl; intro f _
  by_cases hf : Function.Injective f
  · simp [hf]
  · simp only [hf, ite_false]
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
    have h0 : (B.submatrix f id).det = 0 :=
      Matrix.det_zero_of_row_eq hne (congrArg B hij)
    rw [h0, mul_zero]

/-- Canonical monotone embedding `Fin h ↪ Fin m` of an `h`-element subset `s ⊆ Fin m`. -/
def subsetEmb {h m : ℕ} (s : Finset (Fin m)) (hs : s.card = h) : Fin h ↪o Fin m :=
  s.orderEmbOfFin hs

/-- **Exact Cauchy–Binet formula**: for any `A : Matrix (Fin h) (Fin m) R` and
`B : Matrix (Fin m) (Fin h) R`,
`det (A * B) = ∑ I ∈ powersetCard h univ, det (A_{*, I}) * det (B_{I, *})`. -/
theorem cauchy_binet_det_mul {R : Type*} [CommRing R] {h m : ℕ}
    (A : Matrix (Fin h) (Fin m) R) (B : Matrix (Fin m) (Fin h) R) :
    (A * B).det =
      ∑ I ∈ ((Finset.univ : Finset (Fin m)).powersetCard h).attach,
        (A.submatrix id (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2)).det *
          (B.submatrix (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2) id).det := by
  classical
  rw [det_mul_eq_sum_injective]
  let P := (((Finset.univ : Finset (Fin m)).powersetCard h).attach ×ˢ
    (Finset.univ : Finset (Equiv.Perm (Fin h))))
  have hbij : (∑ f ∈ (Finset.univ : Finset (Fin h → Fin m)).filter Function.Injective,
      (∏ i : Fin h, A i (f i)) * (B.submatrix f id).det) =
      ∑ x ∈ P,
        (∏ i : Fin h, A i (subsetEmb x.1.1 (Finset.mem_powersetCard.mp x.1.2).2 (x.2 i))) *
          (B.submatrix (subsetEmb x.1.1 (Finset.mem_powersetCard.mp x.1.2).2 ∘ x.2) id).det := by
    symm
    apply Finset.sum_bij
      (fun x _ => fun i => subsetEmb x.1.1 (Finset.mem_powersetCard.mp x.1.2).2 (x.2 i))
    · intro x _
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (subsetEmb _ _).injective.comp x.2.injective⟩
    · intro x₁ _ x₂ _ heq
      have himg : x₁.1.1 = x₂.1.1 := by
        have h1 : Finset.univ.image (fun i => subsetEmb x₁.1.1 (Finset.mem_powersetCard.mp x₁.1.2).2 (x₁.2 i)) =
            x₁.1.1 := by
          ext u
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
          · intro hu
            have hmem : u ∈ Set.range (subsetEmb x₁.1.1 (Finset.mem_powersetCard.mp x₁.1.2).2) := by
              rw [subsetEmb, Finset.range_orderEmbOfFin]; exact hu
            obtain ⟨j, rfl⟩ := hmem
            exact ⟨x₁.2.symm j, by simp⟩
        have h2 : Finset.univ.image (fun i => subsetEmb x₂.1.1 (Finset.mem_powersetCard.mp x₂.1.2).2 (x₂.2 i)) =
            x₂.1.1 := by
          ext u
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
          · intro hu
            have hmem : u ∈ Set.range (subsetEmb x₂.1.1 (Finset.mem_powersetCard.mp x₂.1.2).2) := by
              rw [subsetEmb, Finset.range_orderEmbOfFin]; exact hu
            obtain ⟨j, rfl⟩ := hmem
            exact ⟨x₂.2.symm j, by simp⟩
        rw [← h1, ← h2, heq]
      have hx1 : x₁.1 = x₂.1 := Subtype.ext himg
      apply Prod.ext hx1
      rcases x₁ with ⟨I₁, σ₁⟩
      rcases x₂ with ⟨I₂, σ₂⟩
      dsimp only at hx1 heq
      subst hx1
      exact Equiv.ext fun i => (subsetEmb _ _).injective (congrFun heq i)
    · intro f hf
      have hinj : Function.Injective f := (Finset.mem_filter.mp hf).2
      let s : Finset (Fin m) := Finset.univ.image f
      have hs : s.card = h := by rw [Finset.card_image_of_injective _ hinj]; simp
      have hs_mem : s ∈ (Finset.univ : Finset (Fin m)).powersetCard h :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hs⟩
      have hsurj : ∀ i : Fin h, ∃ j : Fin h, subsetEmb s hs j = f i := by
        intro i
        have hmem : f i ∈ Set.range (subsetEmb s hs) := by
          rw [subsetEmb, Finset.range_orderEmbOfFin]
          exact Finset.mem_image_of_mem f (Finset.mem_univ i)
        exact hmem
      choose σ_fun hσ_fun using hsurj
      have hσ_inj : Function.Injective σ_fun := by
        intro i₁ i₂ h
        apply hinj
        rw [← hσ_fun i₁, ← hσ_fun i₂, h]
      let σ : Equiv.Perm (Fin h) := Equiv.ofBijective σ_fun (Finite.injective_iff_bijective.mp hσ_inj)
      refine ⟨(⟨s, hs_mem⟩, σ), Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_univ _⟩, ?_⟩
      funext i
      exact hσ_fun i
    · intro x _
      rfl
  rw [hbij, Finset.sum_product]
  apply Finset.sum_congr rfl; intro I _
  have hperm : ∀ σ : Equiv.Perm (Fin h),
      (B.submatrix (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2 ∘ σ) id).det =
        (Equiv.Perm.sign σ : ℤ) •
          (B.submatrix (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2) id).det := by
    intro σ
    have hsub : B.submatrix (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2 ∘ σ) id =
        (B.submatrix (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2) id).submatrix σ id := by
      ext i j; rfl
    rw [hsub, Matrix.det_permute]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hdetA : (A.submatrix id (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2)).det =
      ∑ σ : Equiv.Perm (Fin h),
        (Equiv.Perm.sign σ : ℤ) •
          ∏ i : Fin h, A i (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2 (σ i)) := by
    rw [← Matrix.det_transpose, Matrix.det_apply]
    apply Finset.sum_congr rfl; intro σ _
    congr 1
  rw [hdetA, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro σ _
  rw [hperm σ]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-! ## Doubled Cauchy–Binet valuation theorem for `Y * W * Yᵀ` -/

/-- **Doubled Cauchy–Binet valuation theorem** (zero ramified extensions):
If `2 * v_p^G(W u v) ≥ -(B u + B v)` and every nonzero `h`-minor of `Y` satisfies
`2 * v_p(det Y_{*, I}) - ∑_{u ∈ I} B u ≥ -U`, then
`FormalValAtLeast p (-U) (det (Y_C * W * Y_Cᵀ))`. -/
theorem doubled_cauchy_binet_formalValAtLeast {p h m : ℕ} [Fact p.Prime]
    (Y : Matrix (Fin h) (Fin m) ℚ)
    (W : Matrix (Fin m) (Fin m) SixPolynomial)
    (B : Fin m → ℕ) (U : ℤ)
    (hW : ∀ u v : Fin m, DoubledFormalValAtLeast p (-((B u + B v : ℕ) : ℤ)) (W u v))
    (hY : ∀ (I : Finset (Fin m)) (hI : I.card = h),
      (Y.submatrix id (subsetEmb I hI)).det ≠ 0 →
      -U ≤ 2 * padicValRat p (Y.submatrix id (subsetEmb I hI)).det -
        ∑ u ∈ I, (B u : ℤ)) :
    FormalValAtLeast p (-U)
      (Y.map MvPolynomial.C * W * (Y.map MvPolynomial.C).transpose).det := by
  apply formalValAtLeast_of_doubled_two_mul
  have hexp : (Y.map MvPolynomial.C * W * (Y.map MvPolynomial.C).transpose).det =
      ∑ I ∈ ((Finset.univ : Finset (Fin m)).powersetCard h).attach,
        ∑ J ∈ ((Finset.univ : Finset (Fin m)).powersetCard h).attach,
          MvPolynomial.C
            ((Y.submatrix id (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2)).det *
             (Y.submatrix id (subsetEmb J.1 (Finset.mem_powersetCard.mp J.2).2)).det) *
          (W.submatrix (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2)
            (subsetEmb J.1 (Finset.mem_powersetCard.mp J.2).2)).det := by
    rw [Matrix.mul_assoc, cauchy_binet_det_mul]
    apply Finset.sum_congr rfl; intro I _
    have hright : ((W * (Y.map MvPolynomial.C).transpose).submatrix
        (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2) id).det =
        ∑ J ∈ ((Finset.univ : Finset (Fin m)).powersetCard h).attach,
          (W.submatrix (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2)
            (subsetEmb J.1 (Finset.mem_powersetCard.mp J.2).2)).det *
          ((Y.map MvPolynomial.C).submatrix id
            (subsetEmb J.1 (Finset.mem_powersetCard.mp J.2).2)).det := by
      have hsub : (W * (Y.map MvPolynomial.C).transpose).submatrix
          (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2) id =
          W.submatrix (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2) id *
            (Y.map MvPolynomial.C).transpose := by
        ext i j; rfl
      rw [hsub, cauchy_binet_det_mul]
      apply Finset.sum_congr rfl; intro J _
      congr 1
      rw [← Matrix.det_transpose]
      congr 1
    rw [hright, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro J _
    have hYC : ∀ K : {x // x ∈ (Finset.univ : Finset (Fin m)).powersetCard h},
        ((Y.map (MvPolynomial.C : ℚ →+* SixPolynomial)).submatrix id
          (subsetEmb K.1 (Finset.mem_powersetCard.mp K.2).2)).det =
        (MvPolynomial.C : ℚ →+* SixPolynomial) (Y.submatrix id
          (subsetEmb K.1 (Finset.mem_powersetCard.mp K.2).2)).det := by
      intro K
      have hmap : (Y.map (MvPolynomial.C : ℚ →+* SixPolynomial)).submatrix id
          (subsetEmb K.1 (Finset.mem_powersetCard.mp K.2).2) =
          (MvPolynomial.C : ℚ →+* SixPolynomial).mapMatrix
            (Y.submatrix id (subsetEmb K.1 (Finset.mem_powersetCard.mp K.2).2)) := by
        ext i j; rfl
      rw [hmap, ← RingHom.map_det]
    rw [hYC I, hYC J, map_mul]
    ring
  rw [hexp]
  apply doubledFormalValAtLeast_sum; intro I _
  apply doubledFormalValAtLeast_sum; intro J _
  have hIcard : I.1.card = h := (Finset.mem_powersetCard.mp I.2).2
  have hJcard : J.1.card = h := (Finset.mem_powersetCard.mp J.2).2
  let dI := (Y.submatrix id (subsetEmb I.1 hIcard)).det
  let dJ := (Y.submatrix id (subsetEmb J.1 hJcard)).det
  by_cases hdI : dI = 0
  · simp [dI, hdI, doubledFormalValAtLeast_zero]
  by_cases hdJ : dJ = 0
  · simp [dJ, hdJ, doubledFormalValAtLeast_zero]
  have hWsub : DoubledFormalValAtLeast p
      (-(∑ u ∈ I.1, (B u : ℤ)) - ∑ v ∈ J.1, (B v : ℤ))
      (W.submatrix (subsetEmb I.1 hIcard) (subsetEmb J.1 hJcard)).det := by
    rw [Matrix.det_apply]
    apply doubledFormalValAtLeast_sum; intro σ _
    have hprod := doubledFormalValAtLeast_prod (Finset.univ : Finset (Fin h))
      (fun i => W (subsetEmb I.1 hIcard (σ i)) (subsetEmb J.1 hJcard i))
      (fun i => -((B (subsetEmb I.1 hIcard (σ i)) + B (subsetEmb J.1 hJcard i) : ℕ) : ℤ))
      (fun i _ => hW _ _)
    have hsum_eq : (∑ i : Fin h,
        -((B (subsetEmb I.1 hIcard (σ i)) + B (subsetEmb J.1 hJcard i) : ℕ) : ℤ)) =
        -(∑ u ∈ I.1, (B u : ℤ)) - ∑ v ∈ J.1, (B v : ℤ) := by
      have hI_sum : (∑ i : Fin h, (B (subsetEmb I.1 hIcard (σ i)) : ℤ)) =
          ∑ u ∈ I.1, (B u : ℤ) := by
        rw [Equiv.sum_comp σ (fun i => (B (subsetEmb I.1 hIcard i) : ℤ))]
        have himg : Finset.univ.image (subsetEmb I.1 hIcard) = I.1 := by
          ext u
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
          · intro hu
            have hmem : u ∈ Set.range (subsetEmb I.1 hIcard) := by
              rw [subsetEmb, Finset.range_orderEmbOfFin]; exact hu
            exact hmem
        conv_rhs => rw [← himg]
        rw [Finset.sum_image (fun _ _ _ _ h => (subsetEmb I.1 hIcard).injective h)]
      have hJ_sum : (∑ i : Fin h, (B (subsetEmb J.1 hJcard i) : ℤ)) =
          ∑ v ∈ J.1, (B v : ℤ) := by
        have himg : Finset.univ.image (subsetEmb J.1 hJcard) = J.1 := by
          ext u
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
          · intro hu
            have hmem : u ∈ Set.range (subsetEmb J.1 hJcard) := by
              rw [subsetEmb, Finset.range_orderEmbOfFin]; exact hu
            exact hmem
        conv_rhs => rw [← himg]
        rw [Finset.sum_image (fun _ _ _ _ h => (subsetEmb J.1 hJcard).injective h)]
      push_cast
      simp only [neg_add, Finset.sum_add_distrib, Finset.sum_neg_distrib, hI_sum, hJ_sum]
      ring
    rw [hsum_eq] at hprod
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]; exact hprod
    · rw [hs, Units.neg_smul, one_smul]; exact doubledFormalValAtLeast_neg hprod
  have hY_I := hY I.1 hIcard hdI
  have hY_J := hY J.1 hJcard hdJ
  have hdIJ : DoubledValAtLeast p (2 * padicValRat p dI + 2 * padicValRat p dJ) (dI * dJ) := by
    right
    rw [padicValRat.mul hdI hdJ]
    ring_nf; exact le_rfl
  have hcomb := doubledFormalValAtLeast_C_mul hdIJ hWsub
  exact doubledFormalValAtLeast_mono hcomb (by linarith)

/-! ## Layer-cake cap lemma, descending sort prefix bound, and coarse tail bound -/

/-- Layer-cake upper bound for any integer `z ≤ 18`: `z ≤ ∑_{j=1}^{18} [j ≤ z]`. -/
theorem int_le_layer_sum (z : ℤ) (hz : z ≤ 18) :
    z ≤ ∑ j ∈ Finset.Icc 1 18, if (j : ℤ) ≤ z then (1 : ℤ) else 0 := by
  by_cases h0 : z ≤ 0
  · exact h0.trans (Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num))
  · have hz1 : 1 ≤ z := by omega
    interval_cases z <;> decide

/-- Selecting at most `h` elements from a finite set `S` with weights `w ≤ 18` yields sum
bounded by `∑_{j=1}^{18} min h #{x ∈ S | j ≤ w x}`. -/
theorem sum_subset_le_layer_cap {α : Type*} [DecidableEq α]
    (S A : Finset α) (hAS : A ⊆ S) (h : ℕ) (hcard : A.card ≤ h)
    (w : α → ℤ) (hw : ∀ x ∈ S, w x ≤ 18) :
    (∑ x ∈ A, w x) ≤
      ∑ j ∈ Finset.Icc 1 18, (min h (S.filter (fun x => (j : ℤ) ≤ w x)).card : ℤ) := by
  calc
    (∑ x ∈ A, w x)
        ≤ ∑ x ∈ A, ∑ j ∈ Finset.Icc 1 18, if (j : ℤ) ≤ w x then (1 : ℤ) else 0 :=
          Finset.sum_le_sum (fun x hx => int_le_layer_sum (w x) (hw x (hAS hx)))
    _ = ∑ j ∈ Finset.Icc 1 18, ∑ x ∈ A, if (j : ℤ) ≤ w x then (1 : ℤ) else 0 :=
          Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.Icc 1 18, (min h (S.filter (fun x => (j : ℤ) ≤ w x)).card : ℤ) := by
          apply Finset.sum_le_sum; intro j _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
          have h1 : (A.filter (fun x => (j : ℤ) ≤ w x)).card ≤ h :=
            (Finset.card_filter_le _ _).trans hcard
          have h2 : (A.filter (fun x => (j : ℤ) ≤ w x)).card ≤
              (S.filter (fun x => (j : ℤ) ≤ w x)).card :=
            Finset.card_le_card (Finset.filter_subset_filter _ hAS)
          exact_mod_cast le_min h1 h2

/-- Elementary 2-line bound for slim periodic certificates:
`∀ B ≤ 18, ∑_{k=1}^B (B - 2*k) ≤ 4 * B` (natural-number truncated subtraction). -/
theorem coarse_tail_sum_le_four_mul (B : ℕ) (hB : B ≤ 18) :
    (∑ k ∈ Finset.Icc 1 B, (B - 2 * k)) ≤ 4 * B := by
  interval_cases B <;> decide

/-- Weights of a finite set `S` sorted in non-increasing order. -/
def descWeights {α : Type*} (S : Finset α) (B : α → ℕ) : List ℕ :=
  (S.toList.map B).mergeSort (fun a b => decide (b ≤ a))

/-- The `r`-th largest weight in `S` (0-indexed; `0` if `r ≥ S.card`). -/
def nthDescWeight {α : Type*} (S : Finset α) (B : α → ℕ) (r : ℕ) : ℕ :=
  (descWeights S B).getD r 0

private theorem descWeights_length {α : Type*} (S : Finset α) (B : α → ℕ) :
    (descWeights S B).length = S.card := by
  unfold descWeights
  rw [List.length_mergeSort, List.length_map, Finset.length_toList]

private theorem descWeights_perm {α : Type*} (S : Finset α) (B : α → ℕ) :
    (descWeights S B).Perm (S.toList.map B) :=
  List.mergeSort_perm _ _

private theorem descWeights_antitone {α : Type*} (S : Finset α) (B : α → ℕ) :
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

private theorem list_sum_eq_finset_sum_getD (l : List ℕ) :
    l.sum = ∑ r ∈ range l.length, l.getD r 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.sum_cons, List.length_cons, Finset.sum_range_succ', List.getD_cons_zero,
      List.getD_cons_succ, ih, add_comm]

private theorem finset_sum_eq_descWeights_sum {α : Type*} (S : Finset α) (B : α → ℕ) :
    (∑ u ∈ S, B u) = ∑ r ∈ range S.card, nthDescWeight S B r := by
  have h1 : (∑ u ∈ S, B u) = (S.toList.map B).sum := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]; rfl
  rw [h1, ← (descWeights_perm S B).sum_eq, list_sum_eq_finset_sum_getD, descWeights_length]
  rfl

private theorem list_countP_ge_eq_card_filter {α : Type*} (S : Finset α) (B : α → ℕ) (t : ℕ) :
    (descWeights S B).countP (fun v => decide (t ≤ v)) =
      (S.filter (fun u => t ≤ B u)).card := by
  rw [(descWeights_perm S B).countP_eq, List.countP_map]
  have hnodup : S.toList.Nodup := Finset.nodup_toList S
  rw [← Finset.length_toList (S.filter (fun u => t ≤ B u)), List.countP_eq_length_filter]
  have hperm : (S.filter (fun u => t ≤ B u)).toList.Perm
      (S.toList.filter (fun u => decide (t ≤ B u))) := by
    rw [List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (hnodup.filter _)]
    intro u
    simp [Finset.mem_toList, Finset.mem_filter]
  rw [hperm.length_eq]
  rfl

/-- Selecting `s = A.card` elements `A ⊆ S` has weight sum at most the sum of the `s`
largest weights of `S`. -/
theorem sum_subset_le_descWeights_prefix {α : Type*} [DecidableEq α]
    (S A : Finset α) (hAS : A ⊆ S) (B : α → ℕ) :
    (∑ u ∈ A, B u) ≤ ∑ r ∈ range A.card, nthDescWeight S B r := by
  rw [finset_sum_eq_descWeights_sum A B]
  apply Finset.sum_le_sum
  intro r hr
  have hrA : r < (descWeights A B).length := by rw [descWeights_length]; exact mem_range.mp hr
  have hrS : r < (descWeights S B).length := by
    rw [descWeights_length]
    exact (mem_range.mp hr).trans_le (Finset.card_le_card hAS)
  unfold nthDescWeight
  rw [List.getD_eq_getElem _ _ hrA, List.getD_eq_getElem _ _ hrS]
  by_contra hlt
  push Not at hlt
  let t : ℕ := (descWeights A B)[r]
  -- At least `r + 1` elements of `descWeights A B` are `≥ t`
  have hA_cnt : r + 1 ≤ (descWeights A B).countP (fun v => decide (t ≤ v)) := by
    have hcount_eq : (descWeights A B).countP (fun v => decide (t ≤ v)) =
        ((range (descWeights A B).length).filter
          (fun j => decide (t ≤ (descWeights A B).getD j 0))).card := by
      -- Prove via induction on any list `l`
      have hgen : ∀ (l : List ℕ) (p : ℕ → Bool),
          l.countP p = ((range l.length).filter (fun j => p (l.getD j 0))).card := by
        intro l p
        induction l with
        | nil => simp
        | cons x xs ih =>
          rw [List.countP_cons, List.length_cons, ih]
          have hsplit : (range (xs.length + 1)).filter (fun j => p ((x :: xs).getD j 0)) =
              (if p x then {0} else ∅) ∪
                ((range xs.length).filter (fun j => p (xs.getD j 0))).image (· + 1) := by
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
      exact hgen _ _
    rw [hcount_eq]
    have hsub : range (r + 1) ⊆ (range (descWeights A B).length).filter
        (fun j => decide (t ≤ (descWeights A B).getD j 0)) := by
      intro j hj
      have hjr : j ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hjlen : j < (descWeights A B).length := hjr.trans_lt hrA
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨hjlen, ?_⟩
      rw [List.getD_eq_getElem _ _ hjlen]
      simp [t, descWeights_antitone A B j r hjlen hrA hjr]
    simpa using Finset.card_le_card hsub
  -- At most `r` elements of `descWeights S B` are `≥ t`
  have hS_cnt : (descWeights S B).countP (fun v => decide (t ≤ v)) ≤ r := by
    have hgen : ∀ (l : List ℕ) (p : ℕ → Bool),
        l.countP p = ((range l.length).filter (fun j => p (l.getD j 0))).card := by
      intro l p
      induction l with
      | nil => simp
      | cons x xs ih =>
        rw [List.countP_cons, List.length_cons, ih]
        have hsplit : (range (xs.length + 1)).filter (fun j => p ((x :: xs).getD j 0)) =
            (if p x then {0} else ∅) ∪
              ((range xs.length).filter (fun j => p (xs.getD j 0))).image (· + 1) := by
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
    have hsub : (range (descWeights S B).length).filter
        (fun j => decide (t ≤ (descWeights S B).getD j 0)) ⊆ range r := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      rw [Finset.mem_range]
      by_contra hjge
      push Not at hjge
      have hget := hj.2
      rw [List.getD_eq_getElem _ _ hj.1] at hget
      have hge : t ≤ (descWeights S B)[j] := by simpa using hget
      have hle := descWeights_antitone S B r j hrS hj.1 hjge
      omega
    simpa using Finset.card_le_card hsub
  rw [list_countP_ge_eq_card_filter] at hA_cnt hS_cnt
  have hmono : (A.filter (fun u => t ≤ B u)).card ≤ (S.filter (fun u => t ≤ B u)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hAS)
  omega

theorem nthDescWeight_le_bound {α : Type*} (S : Finset α) (B : α → ℕ) (M : ℕ)
    (hB : ∀ u ∈ S, B u ≤ M) (r : ℕ) : nthDescWeight S B r ≤ M := by
  unfold nthDescWeight
  by_cases hr : r < (descWeights S B).length
  · rw [List.getD_eq_getElem _ _ hr]
    have hmem : (descWeights S B)[r] ∈ descWeights S B := List.getElem_mem hr
    have hmem' : (descWeights S B)[r] ∈ S.toList.map B := (descWeights_perm S B).subset hmem
    obtain ⟨u, hu, heq⟩ := List.mem_map.mp hmem'
    rw [← heq]
    exact hB u (Finset.mem_toList.mp hu)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hr)]
    exact Nat.zero_le _

/-! ## Folded residue classes modulo odd prime `p` and row-scaled minor bounds -/

/-- Folded residue class `foldMod p hp x ∈ {0, 1, ..., p / 2}` (equals `{0, ..., (p-1)/2}` for odd `p`). -/
def foldMod (p : ℕ) (hp : 0 < p) (x : ℤ) : Fin (p / 2 + 1) :=
  let r := (x % (p : ℤ)).toNat
  if h : r ≤ p / 2 then ⟨r, by omega⟩
  else ⟨p - r, by omega⟩

/-- Sign `±1` aligning `x` with its folded representative `foldMod p hp x` modulo `p`. -/
def foldSign (p : ℕ) (x : ℤ) : ℤ :=
  if (x % (p : ℤ)).toNat ≤ p / 2 then 1 else -1

theorem foldMod_congruence (p : ℕ) (hp : 0 < p) (x : ℤ) :
    (p : ℤ) ∣ foldSign p x * x - ((foldMod p hp x).val : ℤ) := by
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have h0 : 0 ≤ x % (p : ℤ) := Int.emod_nonneg x hpZ.ne'
  have hlt : x % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos x hpZ
  have hdiv := Int.mul_ediv_add_emod x (p : ℤ)
  have hto : (((x % (p : ℤ)).toNat : ℕ) : ℤ) = x % (p : ℤ) := Int.toNat_of_nonneg h0
  unfold foldSign foldMod
  dsimp only
  split_ifs with h
  · refine ⟨x / (p : ℤ), ?_⟩
    rw [one_mul, hto]
    linarith
  · refine ⟨-(x / (p : ℤ) + 1), ?_⟩
    have hrle : (x % (p : ℤ)).toNat ≤ p := by omega
    rw [Nat.cast_sub hrle, hto]
    linarith

/-- Row-scaling penalty `∑_{i < h} (⌊2i/p⌋ - q)_+`. -/
def sixRowPenalty (h p q : ℕ) : ℕ :=
  ∑ i : Fin h, (2 * i.val / p - q)

theorem sixRowPenalty_eq_zero_of_ge (h p q : ℕ) (hq : 2 * h / p ≤ q) :
    sixRowPenalty h p q = 0 := by
  unfold sixRowPenalty
  apply Finset.sum_eq_zero; intro i _
  have hle : 2 * i.val / p ≤ 2 * h / p := Nat.div_le_div_right (by have := i.isLt; omega)
  omega

/-- General `evenBasis` Taylor-jet evaluation matrix `Y_{i, u} = p^(a u) * E_i^[a u](x u)`. -/
def evalJetMatrix (p h m : ℕ) (x : Fin m → ℤ) (a : Fin m → ℕ) : Matrix (Fin h) (Fin m) ℚ :=
  fun i u => (p : ℚ) ^ (a u) * taylorCoeff (evenBasis i.val) (x u : ℚ) (a u)

/-- Row-scaled jet matrix `Y_q = D_q * Y`. -/
def scaledJetMatrix (p h m q : ℕ) (x : Fin m → ℤ) (a : Fin m → ℕ) : Matrix (Fin h) (Fin m) ℚ :=
  Matrix.diagonal (fun i : Fin h => (p : ℚ) ^ (2 * i.val / p - q)) * evalJetMatrix p h m x a

theorem padicValRat_scaledJetMinor {p h m q : ℕ} [Fact p.Prime]
    (x : Fin m → ℤ) (a : Fin m → ℕ) (I : Finset (Fin m)) (hI : I.card = h)
    (hne : ((evalJetMatrix p h m x a).submatrix id (subsetEmb I hI)).det ≠ 0) :
    padicValRat p ((scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI)).det =
      (sixRowPenalty h p q : ℤ) +
        padicValRat p ((evalJetMatrix p h m x a).submatrix id (subsetEmb I hI)).det := by
  have hp : p.Prime := Fact.out
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hsub : (scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI) =
      Matrix.diagonal (fun i : Fin h => (p : ℚ) ^ (2 * i.val / p - q)) *
        (evalJetMatrix p h m x a).submatrix id (subsetEmb I hI) := by
    ext i j; simp [scaledJetMatrix, Matrix.diagonal_mul]
  rw [hsub, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  have hpow_ne : (p : ℚ) ^ sixRowPenalty h p q ≠ 0 := pow_ne_zero _ hpne
  change padicValRat p ((p : ℚ) ^ sixRowPenalty h p q * _) = _
  rw [padicValRat.mul hpow_ne hne]
  congr 1
  induction sixRowPenalty h p q with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, padicValRat.mul (pow_ne_zero k hpne) hpne, ih, padicValRat.self hp.one_lt]
    push_cast; ring

/-- Any `s` distinct natural numbers have sum of `(j - q)_+` at least `∑_{r < s} (r - q)_+`. -/
private theorem sum_sub_ge_sum_range {s q : ℕ} (f : Fin s → ℕ) (hf : Function.Injective f) :
    (∑ r ∈ range s, (r - q : ℕ)) ≤ ∑ k : Fin s, (f k - q : ℕ) := by
  let S : Finset ℕ := Finset.univ.image f
  have hScard : S.card = s := by rw [Finset.card_image_of_injective _ hf]; simp
  have hsum_img : (∑ k : Fin s, (f k - q : ℕ)) = ∑ n ∈ S, (n - q : ℕ) := by
    rw [Finset.sum_image (fun _ _ _ _ h => hf h)]
  rw [hsum_img]
  let e : Fin s ↪o ℕ := S.orderEmbOfFin hScard
  have he_ge : ∀ r : Fin s, r.val ≤ e r := by
    intro r
    cases s with
    | zero => exact Fin.elim0 r
    | succ s' =>
      induction r using Fin.inductionOn with
      | zero => exact Nat.zero_le _
      | succ r ih =>
        have hlt : e r.castSucc < e r.succ := e.strictMono Fin.castSucc_lt_succ
        have hr : r.castSucc.val = r.val := rfl
        have hs : r.succ.val = r.val + 1 := rfl
        omega
  have hsum_emb : (∑ n ∈ S, (n - q : ℕ)) = ∑ r : Fin s, (e r - q : ℕ) := by
    symm
    have himg : Finset.univ.image e = S := by
      ext n
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨r, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
      · intro hn
        have : n ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hn
        exact this
    rw [← himg, Finset.sum_image (fun _ _ _ _ h => e.injective h)]
  rw [hsum_emb, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_le_sum (fun r _ => Nat.sub_le_sub_right (he_ge r) q)

/-- **Key unfolded minor valuation lower bound**: for any prime `p` with `2 * h < p ^ 2`,
every `h`-minor `det (Y_q)_{*, I}` satisfies `ValAtLeast p (∑ u ∈ I, (a u - q))`. -/
theorem valAtLeast_unfolded_scaledJetMinor {p h m q : ℕ} [Fact p.Prime]
    (hsq : 2 * h < p ^ 2) (x : Fin m → ℤ) (a : Fin m → ℕ)
    (I : Finset (Fin m)) (hI : I.card = h) :
    ValAtLeast p (∑ u ∈ I, ((a u - q : ℕ) : ℤ))
      ((scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI)).det := by
  rw [Matrix.det_apply]
  apply valAtLeast_sum; intro σ _
  have hprod := valAtLeast_prod (Finset.univ : Finset (Fin h))
    (fun i => (scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI) (σ i) i)
    (fun i => ((a (subsetEmb I hI i) - q : ℕ) : ℤ))
    (fun i _ => by
      simp only [scaledJetMatrix, evalJetMatrix, Matrix.submatrix_apply, id_eq, Matrix.diagonal_mul]
      have h2i : 2 * (σ i).val < p ^ 2 := by have := (σ i).isLt; omega
      exact valAtLeast_p_pow_evenBasis_taylor_shift p (σ i).val q h2i _ _)
  have hsum_eq : (∑ i : Fin h, ((a (subsetEmb I hI i) - q : ℕ) : ℤ)) =
      ∑ u ∈ I, ((a u - q : ℕ) : ℤ) := by
    have himg : Finset.univ.image (subsetEmb I hI) = I := by
      ext u
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
      · intro hu
        have : u ∈ Set.range (subsetEmb I hI) := by rw [subsetEmb, Finset.range_orderEmbOfFin]; exact hu
        exact this
    conv_rhs => rw [← himg]
    rw [Finset.sum_image (fun _ _ _ _ h => (subsetEmb I hI).injective h)]
  rw [hsum_eq] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact hprod
  · rw [hs, Units.neg_smul, one_smul]; exact valAtLeast_neg hprod

/-- **Key folded minor valuation lower bound**: for any prime `p` with `2 * h < p ^ 2`
and any `h`-subset `I` of columns, the row-scaled minor `det (Y_q)_{*, I}` satisfies
`ValAtLeast p (∑ c, ∑ r ∈ range (classCard c), (r - q))`. -/
theorem valAtLeast_folded_scaledJetMinor {p h m q : ℕ} [Fact p.Prime]
    (hsq : 2 * h < p ^ 2) (x : Fin m → ℤ) (a : Fin m → ℕ)
    (I : Finset (Fin m)) (hI : I.card = h) :
    let hp := (Fact.out : p.Prime).pos
    let classCard : Fin (p / 2 + 1) → ℕ :=
      fun c => (I.filter (fun u => foldMod p hp (x u) = c)).card
    ValAtLeast p (∑ c : Fin (p / 2 + 1), ∑ r ∈ range (classCard c), ((r - q : ℕ) : ℤ))
      ((scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI)).det := by
  intro hp classCard
  have hpPrime : p.Prime := Fact.out
  let C := Fin (p / 2 + 1)
  let D := 2 * h
  let Z : Matrix (Fin h) (C × Fin D) ℚ := fun i cj =>
    (p : ℚ) ^ (2 * i.val / p - q) *
      ((p : ℚ) ^ cj.2.val * taylorCoeff (evenBasis i.val) ((cj.1.val : ℤ) : ℚ) cj.2.val)
  let T : Matrix (C × Fin D) (Fin h) ℚ := fun cj k =>
    let u := subsetEmb I hI k
    if foldMod p hp (x u) = cj.1 ∧ a u ≤ cj.2.val then
      (foldSign p (x u) : ℚ) ^ (a u) *
        (cj.2.val.choose (a u) : ℚ) *
        ((((foldSign p (x u) * x u : ℤ) : ℚ) - ((cj.1.val : ℤ) : ℚ)) / (p : ℚ)) ^ (cj.2.val - a u)
    else 0
  -- Step 1: exact factorization `(Y_q)_{*, I} = Z * T`
  have hfact : (scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI) = Z * T := by
    ext i k
    let u := subsetEmb I hI k
    let c₀ := foldMod p hp (x u)
    let sgn := foldSign p (x u)
    rw [Matrix.submatrix_apply, id_eq, scaledJetMatrix, Matrix.diagonal_mul, Matrix.mul_apply]
    dsimp only [evalJetMatrix, Z, T]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single c₀]
    · have h2i : 2 * i.val < D := by have := i.isLt; omega
      have hsgn : (p : ℚ) ^ (a u) * taylorCoeff (evenBasis i.val) (x u : ℚ) (a u) =
          (sgn : ℚ) ^ (a u) *
            ((p : ℚ) ^ (a u) * taylorCoeff (evenBasis i.val) ((sgn * x u : ℤ) : ℚ) (a u)) := by
        dsimp [sgn, foldSign]
        split_ifs
        · simp
        · simp only [Int.cast_neg, Int.cast_one, neg_one_mul,
            p_pow_taylorCoeff_evenBasis_neg]
          rw [← mul_assoc, ← mul_pow]; norm_num
      rw [hsgn, p_pow_taylorCoeff_evenBasis_shift p hpPrime.ne_zero i.val
        ((sgn * x u : ℤ) : ℚ) ((c₀.val : ℤ) : ℚ) (a u), Finset.mul_sum, Finset.mul_sum]
      have hzero_hi : ∀ j : ℕ, 2 * i.val < j →
          taylorCoeff (evenBasis i.val) ((c₀.val : ℤ) : ℚ) j = 0 := by
        intro j hj
        unfold taylorCoeff
        apply coeff_eq_zero_of_natDegree_lt
        rw [taylor_apply]
        exact natDegree_comp_le.trans_lt (by
          rw [natDegree_X_add_C, mul_one]
          exact (evenBasis_natDegree_le i.val).trans_lt hj)
      rw [Fin.sum_univ_eq_sum_range (fun j =>
        (p : ℚ) ^ (2 * i.val / p - q) *
          ((p : ℚ) ^ j * taylorCoeff (evenBasis i.val) ((c₀.val : ℤ) : ℚ) j) *
        (if c₀ = c₀ ∧ a u ≤ j then
          (sgn : ℚ) ^ (a u) * (j.choose (a u) : ℚ) *
            ((((sgn * x u : ℤ) : ℚ) - ((c₀.val : ℤ) : ℚ)) / (p : ℚ)) ^ (j - a u)
        else 0)) D]
      symm
      rw [← Finset.sum_subset (show Finset.Icc (a u) (2 * i.val) ⊆ range D by
        intro j hj; rw [Finset.mem_Icc] at hj; exact mem_range.mpr (by omega))]
      · apply Finset.sum_congr rfl; intro j hj
        have haj : a u ≤ j := (Finset.mem_Icc.mp hj).1
        simp only [haj, and_self, ite_true]
        ring
      · intro j hj hnot
        rw [Finset.mem_Icc] at hnot
        by_cases haj : a u ≤ j
        · have hgt : 2 * i.val < j := by omega
          rw [hzero_hi j hgt]
          simp
        · simp [haj]
    · intro c _ hne
      apply Finset.sum_eq_zero; intro j _
      have hne' : ¬ foldMod p hp (x (subsetEmb I hI k)) = c := Ne.symm hne
      simp [hne']
    · intro h; exact (h (Finset.mem_univ _)).elim
  -- Step 2: every entry of `T` is an integer, hence `det (T_{f, *})` has `ValAtLeast p 0`
  have hT_int : ∀ (cj : C × Fin D) (k : Fin h), ValAtLeast p 0 (T cj k) := by
    intro cj k
    dsimp [T]
    split_ifs with hcond
    · have hdvd : (p : ℤ) ∣ foldSign p (x (subsetEmb I hI k)) * x (subsetEmb I hI k) - (cj.1.val : ℤ) := by
        rw [← hcond.1]
        exact foldMod_congruence p hp _
      obtain ⟨m₀, hm₀⟩ := shift_coeff_int_of_dvd hpPrime.ne_zero hdvd cj.2.val (a (subsetEmb I hI k))
      have heq : (foldSign p (x (subsetEmb I hI k)) : ℚ) ^ a (subsetEmb I hI k) *
          (cj.2.val.choose (a (subsetEmb I hI k)) : ℚ) *
          ((((foldSign p (x (subsetEmb I hI k)) * x (subsetEmb I hI k) : ℤ) : ℚ) -
            ((cj.1.val : ℤ) : ℚ)) / (p : ℚ)) ^ (cj.2.val - a (subsetEmb I hI k)) =
          ((foldSign p (x (subsetEmb I hI k)) ^ a (subsetEmb I hI k) * m₀ : ℤ) : ℚ) := by
        calc
          (foldSign p (x (subsetEmb I hI k)) : ℚ) ^ a (subsetEmb I hI k) *
              (cj.2.val.choose (a (subsetEmb I hI k)) : ℚ) *
              ((((foldSign p (x (subsetEmb I hI k)) * x (subsetEmb I hI k) : ℤ) : ℚ) -
                ((cj.1.val : ℤ) : ℚ)) / (p : ℚ)) ^ (cj.2.val - a (subsetEmb I hI k))
              = (foldSign p (x (subsetEmb I hI k)) : ℚ) ^ a (subsetEmb I hI k) *
                  ((cj.2.val.choose (a (subsetEmb I hI k)) : ℚ) *
                    ((((foldSign p (x (subsetEmb I hI k)) * x (subsetEmb I hI k) : ℤ) : ℚ) -
                      ((cj.1.val : ℤ) : ℚ)) / (p : ℚ)) ^ (cj.2.val - a (subsetEmb I hI k))) := by ring
          _ = (foldSign p (x (subsetEmb I hI k)) : ℚ) ^ a (subsetEmb I hI k) * (m₀ : ℚ) := by rw [hm₀]
          _ = _ := by push_cast; ring
      rw [heq]
      exact valAtLeast_intCast p _
    · exact valAtLeast_zero p 0
  have hTdet_int : ∀ f : Fin h → C × Fin D, ValAtLeast p 0 (T.submatrix f id).det := by
    intro f
    rw [Matrix.det_apply]
    apply valAtLeast_sum; intro σ _
    have hprod := valAtLeast_prod (Finset.univ : Finset (Fin h))
      (fun k => T (f (σ k)) k) (fun _ => 0) (fun k _ => hT_int _ _)
    simp only [Finset.sum_const_zero] at hprod
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]; exact hprod
    · rw [hs, Units.neg_smul, one_smul]; exact valAtLeast_neg hprod
  -- Step 3: expand `det (Z * T)` by injective selections `f : Fin h → C × Fin D`
  rw [hfact, det_mul_eq_sum_injective]
  apply valAtLeast_sum
  intro f hf
  have hfinj : Function.Injective f := (Finset.mem_filter.mp hf).2
  by_cases hdet0 : (T.submatrix f id).det = 0
  · rw [hdet0, mul_zero]; exact valAtLeast_zero p _
  -- Extract a permutation `σ` with nonzero product in `det (T.submatrix f id)`
  have hex_perm : ∃ σ : Equiv.Perm (Fin h),
      ∀ k : Fin h, (f (σ k)).1 = foldMod p hp (x (subsetEmb I hI k)) := by
    by_contra hall
    push Not at hall
    apply hdet0
    rw [Matrix.det_apply]
    apply Finset.sum_eq_zero; intro σ _
    obtain ⟨k, hk⟩ := hall σ
    have hTk0 : T (f (σ k)) k = 0 := by
      dsimp [T]; simp [Ne.symm hk]
    have hprod0 : (∏ j : Fin h, T (f (σ j)) j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) hTk0
    simp [hprod0]
  obtain ⟨σ, hσ⟩ := hex_perm
  -- Valuation of `∏ i, Z i (f i)`
  have hZprod : ValAtLeast p (∑ i : Fin h, (((f i).2.val - q : ℕ) : ℤ))
      (∏ i : Fin h, Z i (f i)) :=
    valAtLeast_prod Finset.univ (fun i => Z i (f i))
      (fun i => (((f i).2.val - q : ℕ) : ℤ))
      (fun i _ => by
        have h2i : 2 * i.val < p ^ 2 := by have := i.isLt; omega
        exact valAtLeast_p_pow_evenBasis_taylor_shift p i.val q h2i _ _)
  -- Reindex sum by `σ` and partition by folded class `c`
  have hsum_lower :
      (∑ c : C, ∑ r ∈ range (classCard c), ((r - q : ℕ) : ℤ)) ≤
        ∑ i : Fin h, (((f i).2.val - q : ℕ) : ℤ) := by
    rw [← Equiv.sum_comp σ (fun i => (((f i).2.val - q : ℕ) : ℤ))]
    have hpart : (∑ k : Fin h, (((f (σ k)).2.val - q : ℕ) : ℤ)) =
        ∑ c : C, ∑ k ∈ (Finset.univ : Finset (Fin h)).filter
          (fun k => foldMod p hp (x (subsetEmb I hI k)) = c),
          (((f (σ k)).2.val - q : ℕ) : ℤ) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun k : Fin h => foldMod p hp (x (subsetEmb I hI k)))
        (fun _ _ => Finset.mem_univ _)]
    rw [hpart]
    apply Finset.sum_le_sum; intro c _
    let S_c := (Finset.univ : Finset (Fin h)).filter
      (fun k => foldMod p hp (x (subsetEmb I hI k)) = c)
    have hcard_eq : S_c.card = classCard c := by
      dsimp [S_c, classCard]
      have himg : S_c.image (subsetEmb I hI) = I.filter (fun u => foldMod p hp (x u) = c) := by
        ext u
        simp only [Finset.mem_image, Finset.mem_filter, S_c, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨k, hk, rfl⟩
          exact ⟨Finset.orderEmbOfFin_mem _ _ _, hk⟩
        · rintro ⟨huI, huc⟩
          have hmem : u ∈ Set.range (subsetEmb I hI) := by
            rw [subsetEmb, Finset.range_orderEmbOfFin]; exact huI
          obtain ⟨k, rfl⟩ := hmem
          exact ⟨k, huc, rfl⟩
      rw [← himg, Finset.card_image_of_injective _ (subsetEmb I hI).injective]
    let e_c : Fin (classCard c) ↪o Fin h := S_c.orderEmbOfFin hcard_eq
    have hinj_c : Function.Injective (fun r : Fin (classCard c) => (f (σ (e_c r))).2.val) := by
      intro r₁ r₂ heq
      have hmem1 : e_c r₁ ∈ S_c := Finset.orderEmbOfFin_mem _ _ _
      have hmem2 : e_c r₂ ∈ S_c := Finset.orderEmbOfFin_mem _ _ _
      have hc1 : (f (σ (e_c r₁))).1 = c := (hσ _).trans (Finset.mem_filter.mp hmem1).2
      have hc2 : (f (σ (e_c r₂))).1 = c := (hσ _).trans (Finset.mem_filter.mp hmem2).2
      have hpair : f (σ (e_c r₁)) = f (σ (e_c r₂)) :=
        Prod.ext (hc1.trans hc2.symm) (Fin.ext heq)
      exact e_c.injective (σ.injective (hfinj hpair))
    have hsum_ec : (∑ k ∈ S_c, (((f (σ k)).2.val - q : ℕ) : ℤ)) =
        ∑ r : Fin (classCard c), (((f (σ (e_c r))).2.val - q : ℕ) : ℤ) := by
      symm
      have himg : Finset.univ.image e_c = S_c := by
        ext k
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨r, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
        · intro hk
          have : k ∈ Set.range e_c := by rw [Finset.range_orderEmbOfFin]; exact hk
          exact this
      rw [← himg, Finset.sum_image (fun _ _ _ _ h => e_c.injective h)]
    rw [hsum_ec]
    have hnat := sum_sub_ge_sum_range (q := q)
      (fun r : Fin (classCard c) => (f (σ (e_c r))).2.val) hinj_c
    exact_mod_cast hnat
  have hmul := valAtLeast_mul (valAtLeast_mono hZprod hsum_lower) (hTdet_int f)
  simpa using hmul

/-! ## The three certificate-facing valuation bounds (`joint`, `unfolded`, `coarse periodic`) -/

/-- **Standard Form 1: Folded joint capacity bound (with layer cap `min h`)**. -/
theorem folded_joint_formalValAtLeast {p h m : ℕ} [Fact p.Prime]
    (hsq : 2 * h < p ^ 2)
    (x : Fin m → ℤ) (a : Fin m → ℕ)
    (W : Matrix (Fin m) (Fin m) SixPolynomial)
    (B : Fin m → ℕ) (hB18 : ∀ u : Fin m, B u ≤ 18)
    (hW : ∀ u v : Fin m, DoubledFormalValAtLeast p (-((B u + B v : ℕ) : ℤ)) (W u v))
    (q : ℕ) :
    let hp := (Fact.out : p.Prime).pos
    let clsSet : Fin (p / 2 + 1) → Finset (Fin m) :=
      fun c => Finset.univ.filter (fun u => foldMod p hp (x u) = c)
    let slotPairs : Finset (Fin (p / 2 + 1) × Fin m) :=
      Finset.univ.filter (fun cr => cr.2.val < (clsSet cr.1).card)
    let inc : Fin (p / 2 + 1) × Fin m → ℤ := fun cr =>
      (nthDescWeight (clsSet cr.1) B cr.2.val : ℤ) - 2 * ((cr.2.val - q : ℕ) : ℤ)
    let U : ℤ := 2 * (sixRowPenalty h p q : ℤ) +
      ∑ j ∈ Finset.Icc 1 18, (min h (slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℤ)
    FormalValAtLeast p (-U)
      ((evalJetMatrix p h m x a).map MvPolynomial.C * W *
        ((evalJetMatrix p h m x a).map MvPolynomial.C).transpose).det := by
  intro hp clsSet slotPairs inc U
  apply doubled_cauchy_binet_formalValAtLeast (evalJetMatrix p h m x a) W B U hW
  intro I hI hne
  have hscaled_val := valAtLeast_folded_scaledJetMinor (p := p) (q := q) hsq x a I hI
  have hscaled_ne : ((scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI)).det ≠ 0 := by
    have hsub : (scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI) =
        Matrix.diagonal (fun i : Fin h => (p : ℚ) ^ (2 * i.val / p - q)) *
          (evalJetMatrix p h m x a).submatrix id (subsetEmb I hI) := by
      ext i j; simp [scaledJetMatrix, Matrix.diagonal_mul]
    rw [hsub, Matrix.det_mul, Matrix.det_diagonal]
    have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ hpne)) hne
  have hval_ge := valAtLeast_of_ne_zero hscaled_val hscaled_ne
  rw [padicValRat_scaledJetMinor x a I hI hne] at hval_ge
  let I_c : Fin (p / 2 + 1) → Finset (Fin m) :=
    fun c => I.filter (fun u => foldMod p hp (x u) = c)
  have hI_part : (∑ u ∈ I, (B u : ℤ)) = ∑ c : Fin (p / 2 + 1), ∑ u ∈ I_c c, (B u : ℤ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun u => foldMod p hp (x u))
      (fun _ _ => Finset.mem_univ _)]
  -- Bound each class sum by the sorted prefix of `clsSet c`
  have hB_le : (∑ u ∈ I, (B u : ℤ)) ≤
      ∑ c : Fin (p / 2 + 1), ∑ r ∈ range (I_c c).card,
        (nthDescWeight (clsSet c) B r : ℤ) := by
    rw [hI_part]
    apply Finset.sum_le_sum; intro c _
    have hsub : I_c c ⊆ clsSet c := Finset.filter_subset_filter _ (Finset.subset_univ _)
    exact_mod_cast sum_subset_le_descWeights_prefix (clsSet c) (I_c c) hsub B
  -- Combine into subset `A ⊆ slotPairs` of cardinality `h`
  let A : Finset (Fin (p / 2 + 1) × Fin m) :=
    Finset.univ.filter (fun cr => cr.2.val < (I_c cr.1).card)
  have hAS : A ⊆ slotPairs := by
    intro cr hcr
    rw [Finset.mem_filter] at hcr ⊢
    refine ⟨Finset.mem_univ _, hcr.2.trans_le ?_⟩
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  have hI_c_le : ∀ c : Fin (p / 2 + 1), (I_c c).card ≤ m := fun c =>
    (Finset.card_le_univ _).trans (by simp)
  have hA_card : A.card = h := by
    have hfib : A.card = ∑ c : Fin (p / 2 + 1),
        ((Finset.univ : Finset (Fin m)).filter (fun r => r.val < (I_c c).card)).card := by
      dsimp [A]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro c _
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hcard_c : ∀ c : Fin (p / 2 + 1),
        ((Finset.univ : Finset (Fin m)).filter (fun r => r.val < (I_c c).card)).card = (I_c c).card := by
      intro c
      have himg : ((Finset.univ : Finset (Fin m)).filter (fun r => r.val < (I_c c).card)).image Fin.val =
          range (I_c c).card := by
        ext k
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
        constructor
        · rintro ⟨r, hr, rfl⟩; exact hr
        · intro hk; exact ⟨⟨k, hk.trans_le (hI_c_le c)⟩, hk, rfl⟩
      rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]
    rw [hfib]
    simp_rw [hcard_c]
    have hpartI : (∑ c : Fin (p / 2 + 1), (I_c c).card) = I.card := by
      simpa only [Finset.card_eq_sum_ones] using
        Finset.sum_fiberwise_of_maps_to (s := I) (t := Finset.univ)
          (g := fun u => foldMod p hp (x u)) (f := fun _ => 1) (fun _ _ => Finset.mem_univ _)
    rw [hpartI, hI]
  have hsum_A : (∑ cr ∈ A, inc cr) =
      ∑ c : Fin (p / 2 + 1), ∑ r ∈ range (I_c c).card,
        ((nthDescWeight (clsSet c) B r : ℤ) - 2 * ((r - q : ℕ) : ℤ)) := by
    dsimp [A, inc]
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro c _
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun r _ => r.val)
    · intro r hr; exact mem_range.mpr (Finset.mem_filter.mp hr).2
    · intro r₁ _ r₂ _ h; exact Fin.ext h
    · intro k hk
      have hklt := mem_range.mp hk
      exact ⟨⟨k, hklt.trans_le (hI_c_le c)⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hklt⟩, rfl⟩
    · intro r _; rfl
  have hinc_le : ∀ cr ∈ slotPairs, inc cr ≤ 18 := by
    intro cr _
    dsimp [inc]
    have h18 := nthDescWeight_le_bound (clsSet cr.1) B 18 (fun u _ => hB18 u) cr.2.val
    omega
  have hlayer := sum_subset_le_layer_cap slotPairs A hAS h hA_card.le inc hinc_le
  rw [hsum_A] at hlayer
  have hsub_sum : (∑ c : Fin (p / 2 + 1), ∑ r ∈ range (I_c c).card,
      ((nthDescWeight (clsSet c) B r : ℤ) - 2 * ((r - q : ℕ) : ℤ))) =
      (∑ c : Fin (p / 2 + 1), ∑ r ∈ range (I_c c).card, (nthDescWeight (clsSet c) B r : ℤ)) -
      2 * (∑ c : Fin (p / 2 + 1), ∑ r ∈ range (I_c c).card, ((r - q : ℕ) : ℤ)) := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsub_sum] at hlayer
  dsimp only [U]
  linarith

/-- **Standard Form 2: Unfolded direct capacity bound (with layer cap `min h`)**. -/
theorem unfolded_formalValAtLeast {p h m : ℕ} [Fact p.Prime]
    (hsq : 2 * h < p ^ 2)
    (x : Fin m → ℤ) (a : Fin m → ℕ)
    (W : Matrix (Fin m) (Fin m) SixPolynomial)
    (B : Fin m → ℕ) (hB18 : ∀ u : Fin m, B u ≤ 18)
    (hW : ∀ u v : Fin m, DoubledFormalValAtLeast p (-((B u + B v : ℕ) : ℤ)) (W u v))
    (q : ℕ) :
    let inc : Fin m → ℤ := fun u => (B u : ℤ) - 2 * ((a u - q : ℕ) : ℤ)
    let U : ℤ := 2 * (sixRowPenalty h p q : ℤ) +
      ∑ j ∈ Finset.Icc 1 18,
        (min h ((Finset.univ : Finset (Fin m)).filter (fun u => (j : ℤ) ≤ inc u)).card : ℤ)
    FormalValAtLeast p (-U)
      ((evalJetMatrix p h m x a).map MvPolynomial.C * W *
        ((evalJetMatrix p h m x a).map MvPolynomial.C).transpose).det := by
  intro inc U
  apply doubled_cauchy_binet_formalValAtLeast (evalJetMatrix p h m x a) W B U hW
  intro I hI hne
  have hscaled_val := valAtLeast_unfolded_scaledJetMinor (p := p) (q := q) hsq x a I hI
  have hscaled_ne : ((scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI)).det ≠ 0 := by
    have hsub : (scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI) =
        Matrix.diagonal (fun i : Fin h => (p : ℚ) ^ (2 * i.val / p - q)) *
          (evalJetMatrix p h m x a).submatrix id (subsetEmb I hI) := by
      ext i j; simp [scaledJetMatrix, Matrix.diagonal_mul]
    rw [hsub, Matrix.det_mul, Matrix.det_diagonal]
    have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ hpne)) hne
  have hval_ge := valAtLeast_of_ne_zero hscaled_val hscaled_ne
  rw [padicValRat_scaledJetMinor x a I hI hne] at hval_ge
  have hlayer := sum_subset_le_layer_cap (Finset.univ : Finset (Fin m)) I (Finset.subset_univ I)
    h hI.le inc (fun u _ => by dsimp [inc]; have := hB18 u; omega)
  have hinc_sum : (∑ u ∈ I, inc u) =
      (∑ u ∈ I, (B u : ℤ)) - 2 * ∑ u ∈ I, ((a u - q : ℕ) : ℤ) := by
    simp only [inc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hinc_sum] at hlayer
  dsimp only [U]
  linarith

/-- **Standard Form 3: Coarse periodic single-line bound** (for slim small-prime certificates).
Takes `q = 2 * h / p` (zeroing the row penalty) and applies `coarse_tail_sum_le_four_mul`
to obtain `-v_p^G(det (Y * W * Yᵀ)) ≤ (2 * h / p + 5) * ∑ c, B_max c`. -/
theorem folded_periodic_coarse_formalValAtLeast {p h m : ℕ} [Fact p.Prime]
    (hsq : 2 * h < p ^ 2)
    (x : Fin m → ℤ) (a : Fin m → ℕ)
    (W : Matrix (Fin m) (Fin m) SixPolynomial)
    (B : Fin m → ℕ)
    (B_max : Fin (p / 2 + 1) → ℕ)
    (hB_dom : ∀ u : Fin m, B u ≤ B_max (foldMod p (Fact.out : p.Prime).pos (x u)))
    (hB18 : ∀ c : Fin (p / 2 + 1), B_max c ≤ 18)
    (hW : ∀ u v : Fin m, DoubledFormalValAtLeast p (-((B u + B v : ℕ) : ℤ)) (W u v)) :
    let U : ℤ := ((2 * h / p + 5 : ℕ) : ℤ) * ∑ c : Fin (p / 2 + 1), (B_max c : ℤ)
    FormalValAtLeast p (-U)
      ((evalJetMatrix p h m x a).map MvPolynomial.C * W *
        ((evalJetMatrix p h m x a).map MvPolynomial.C).transpose).det := by
  intro U
  let hp := (Fact.out : p.Prime).pos
  let q := 2 * h / p
  apply doubled_cauchy_binet_formalValAtLeast (evalJetMatrix p h m x a) W B U hW
  intro I hI hne
  have hscaled_val := valAtLeast_folded_scaledJetMinor (p := p) (q := q) hsq x a I hI
  have hscaled_ne : ((scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI)).det ≠ 0 := by
    have hsub : (scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI) =
        Matrix.diagonal (fun i : Fin h => (p : ℚ) ^ (2 * i.val / p - q)) *
          (evalJetMatrix p h m x a).submatrix id (subsetEmb I hI) := by
      ext i j; simp [scaledJetMatrix, Matrix.diagonal_mul]
    rw [hsub, Matrix.det_mul, Matrix.det_diagonal]
    have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ hpne)) hne
  have hval_ge := valAtLeast_of_ne_zero hscaled_val hscaled_ne
  rw [padicValRat_scaledJetMinor x a I hI hne, sixRowPenalty_eq_zero_of_ge h p q le_rfl,
    Nat.cast_zero, zero_add] at hval_ge
  let I_c : Fin (p / 2 + 1) → Finset (Fin m) :=
    fun c => I.filter (fun u => foldMod p hp (x u) = c)
  have hI_part : (∑ u ∈ I, (B u : ℤ)) = ∑ c : Fin (p / 2 + 1), ∑ u ∈ I_c c, (B u : ℤ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun u => foldMod p hp (x u))
      (fun _ _ => Finset.mem_univ _)]
  have hclass_bound : ∀ c : Fin (p / 2 + 1),
      (∑ u ∈ I_c c, (B u : ℤ)) - 2 * (∑ r ∈ range (I_c c).card, ((r - q : ℕ) : ℤ)) ≤
        ((q + 5 : ℕ) : ℤ) * (B_max c : ℤ) := by
    intro c
    have hBsum : (∑ u ∈ I_c c, (B u : ℤ)) ≤ ((I_c c).card : ℤ) * (B_max c : ℤ) := by
      calc
        (∑ u ∈ I_c c, (B u : ℤ))
            ≤ ∑ _u ∈ I_c c, (B_max c : ℤ) := by
              apply Finset.sum_le_sum; intro u hu
              have huc := (Finset.mem_filter.mp hu).2
              exact_mod_cast (huc ▸ hB_dom u)
        _ = ((I_c c).card : ℤ) * (B_max c : ℤ) := by simp
    have hrew : ((I_c c).card : ℤ) * (B_max c : ℤ) -
        2 * (∑ r ∈ range (I_c c).card, ((r - q : ℕ) : ℤ)) =
        ∑ r ∈ range (I_c c).card, ((B_max c : ℤ) - 2 * ((r - q : ℕ) : ℤ)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum]
    -- Bound `∑ r ∈ range s, (B_max c - 2*(r - q))` by `(q + 5) * B_max c` for ANY `s : ℕ`
    have hprefix_le : ∀ s : ℕ,
        (∑ r ∈ range s, ((B_max c : ℤ) - 2 * ((r - q : ℕ) : ℤ))) ≤
          ((q + 5 : ℕ) : ℤ) * (B_max c : ℤ) := by
      intro s
      have hterm_le : ∀ r : ℕ,
          ((B_max c : ℤ) - 2 * ((r - q : ℕ) : ℤ)) ≤
            if r ≤ q then (B_max c : ℤ)
            else if r ≤ q + B_max c then ((B_max c - 2 * (r - q) : ℕ) : ℤ)
            else 0 := by
        intro r
        split_ifs with h1 h2
        · have : r - q = 0 := by omega
          simp [this]
        · omega
        · omega
      have hle1 : (∑ r ∈ range s, ((B_max c : ℤ) - 2 * ((r - q : ℕ) : ℤ))) ≤
          ∑ r ∈ range (max s (q + B_max c + 1)),
            (if r ≤ q then (B_max c : ℤ)
             else if r ≤ q + B_max c then ((B_max c - 2 * (r - q) : ℕ) : ℤ)
             else 0) := by
        calc
          (∑ r ∈ range s, ((B_max c : ℤ) - 2 * ((r - q : ℕ) : ℤ)))
              ≤ ∑ r ∈ range s,
                  (if r ≤ q then (B_max c : ℤ)
                   else if r ≤ q + B_max c then ((B_max c - 2 * (r - q) : ℕ) : ℤ)
                   else 0) := Finset.sum_le_sum (fun r _ => hterm_le r)
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left _ _))
                (fun r _ _ => by split_ifs <;> positivity)
      -- Drop terms with `r > q + B_max c` (all `0`)
      have hdrop : (∑ r ∈ range (max s (q + B_max c + 1)),
          (if r ≤ q then (B_max c : ℤ)
           else if r ≤ q + B_max c then ((B_max c - 2 * (r - q) : ℕ) : ℤ)
           else 0)) =
          ∑ r ∈ range (q + B_max c + 1),
            (if r ≤ q then (B_max c : ℤ)
             else ((B_max c - 2 * (r - q) : ℕ) : ℤ)) := by
        symm
        rw [← Finset.sum_subset (Finset.range_mono (le_max_right s (q + B_max c + 1)))]
        · apply Finset.sum_congr rfl; intro r hr
          have hrle : r ≤ q + B_max c := Nat.lt_succ_iff.mp (mem_range.mp hr)
          by_cases h1 : r ≤ q
          · simp [h1]
          · simp [h1, hrle]
        · intro r _ hnot
          have hrgt : q + B_max c < r := by rw [mem_range] at hnot; omega
          have h1 : ¬ r ≤ q := by omega
          have h2 : ¬ r ≤ q + B_max c := by omega
          simp [h1, h2]
      -- Split `range (q + B_max c + 1)` into `range (q + 1)` and `Ico (q + 1) (q + B_max c + 1)`
      have hsplit : (∑ r ∈ range (q + B_max c + 1),
          (if r ≤ q then (B_max c : ℤ) else ((B_max c - 2 * (r - q) : ℕ) : ℤ))) =
          ((q + 1 : ℕ) : ℤ) * (B_max c : ℤ) +
          ∑ k ∈ Finset.Icc 1 (B_max c), ((B_max c - 2 * k : ℕ) : ℤ) := by
        rw [← Nat.Ico_zero_eq_range,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le (q + 1)) (by omega : q + 1 ≤ q + B_max c + 1)]
        congr 1
        · rw [Nat.Ico_zero_eq_range]
          have : ∀ r ∈ range (q + 1),
              (if r ≤ q then (B_max c : ℤ) else ((B_max c - 2 * (r - q) : ℕ) : ℤ)) = (B_max c : ℤ) := by
            intro r hr; simp [Nat.lt_succ_iff.mp (mem_range.mp hr)]
          rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        · apply Finset.sum_bij (fun r _ => r - q)
          · intro r hr; rw [Finset.mem_Ico] at hr; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          · intro r₁ hr₁ r₂ hr₂ h; rw [Finset.mem_Ico] at hr₁ hr₂; omega
          · intro k hk; rw [Finset.mem_Icc] at hk
            exact ⟨q + k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro r hr; rw [Finset.mem_Ico] at hr
            have hnot : ¬ r ≤ q := by omega
            simp [hnot]
      have htail : (∑ k ∈ Finset.Icc 1 (B_max c), ((B_max c - 2 * k : ℕ) : ℤ)) ≤
          4 * (B_max c : ℤ) := by
        exact_mod_cast coarse_tail_sum_le_four_mul (B_max c) (hB18 c)
      calc
        (∑ r ∈ range s, ((B_max c : ℤ) - 2 * ((r - q : ℕ) : ℤ)))
            ≤ ((q + 1 : ℕ) : ℤ) * (B_max c : ℤ) +
                ∑ k ∈ Finset.Icc 1 (B_max c), ((B_max c - 2 * k : ℕ) : ℤ) := by
              rw [← hsplit, ← hdrop]; exact hle1
        _ ≤ ((q + 1 : ℕ) : ℤ) * (B_max c : ℤ) + 4 * (B_max c : ℤ) := by linarith
        _ = ((q + 5 : ℕ) : ℤ) * (B_max c : ℤ) := by push_cast; ring
    linarith [hprefix_le (I_c c).card]
  have hsum_all := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (p / 2 + 1))))
    (fun c _ => hclass_bound c)
  rw [Finset.sum_sub_distrib, ← hI_part, ← Finset.mul_sum, ← Finset.mul_sum] at hsum_all
  dsimp only [U]
  linarith

end OddZetaSix
