import OddZetaSix.ZetaTail
import Mathlib.NumberTheory.Real.Irrational

/-!
# Target Theorem Statement for the Six-Value Odd Zeta Window

Locks the exact target theorem signature using Mathlib's standard
`riemannZeta` (no custom zeta definition). Proves the equivalence between
the indexed `Fin 6` formulation and the standard `Finset` statement.
-/

noncomputable section
set_option autoImplicit false

namespace OddZetaSix

/-- The six target odd weights `{7, 9, 11, 13, 15, 17}`. -/
def sixOddWeights : Finset ℕ := {7, 9, 11, 13, 15, 17}

/-- The exact target theorem statement for the repository:
at least one of `ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17)` is irrational,
stated directly in terms of Mathlib's `riemannZeta`. -/
def SixZetaIrrationalityStatement : Prop :=
  ∃ s ∈ sixOddWeights, Irrational ((riemannZeta (s : ℂ)).re)

/-- Equivalent expanded form matching `OddZetaMixed.exists_irrational_riemannZeta_seven_to_nineteen`. -/
theorem sixZetaIrrationalityStatement_iff :
    SixZetaIrrationalityStatement ↔
      ∃ s ∈ ({7, 9, 11, 13, 15, 17} : Finset ℕ),
        Irrational ((riemannZeta (s : ℂ)).re) :=
  Iff.rfl

theorem sixOddWeights_index_iff (s : ℕ) :
    s ∈ sixOddWeights ↔ ∃ i : Fin 6, s = 7 + 2 * i.val := by
  constructor
  · intro hs
    simp only [sixOddWeights, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> norm_num [sixOddWeights]

theorem sixZeta_irrational_iff_standard :
    (∃ i : Fin 6, Irrational (sixZetaValues i)) ↔ SixZetaIrrationalityStatement := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨7 + 2 * i.val, (sixOddWeights_index_iff _).mpr ⟨i, rfl⟩,
      (sixZetaValues_eq_re_riemannZeta i) ▸ hi⟩
  · rintro ⟨s, hs, hi⟩
    obtain ⟨i, rfl⟩ := (sixOddWeights_index_iff s).mp hs
    exact ⟨i, (sixZetaValues_eq_re_riemannZeta i).symm ▸ hi⟩

end OddZetaSix
