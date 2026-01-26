import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card

variable {V : Type*}

@[simp]
theorem set_union_subset_is_set {s₁ s₂ : Finset V} [DecidableEq V] : s₁ ∪ (s₂ ∩ s₁) = s₁ := by
  ext x
  constructor
  · intro h
    simp only [Finset.mem_union] at h
    cases h with
    | inl h => exact h
    | inr h => exact Finset.mem_of_mem_inter_right h
  · intro h
    exact Finset.mem_union_left (s₂ ∩ s₁) h

theorem fintype_card_eq_zero_iff_univ_empty [Fintype V] :
    (Fintype.card V = 0) ↔ (@Finset.univ V _ = ∅) := by
  constructor
  · have h1 : ∅ ⊆ @Finset.univ V _ := by exact Finset.empty_subset Finset.univ
    contrapose
    intro ne_emptyset
    have neq : ¬((@Finset.univ V _ ⊆ ∅) ∧ (∅ ⊆ @Finset.univ V _)) :=
      (not_iff_not.mpr Finset.Subset.antisymm_iff).mp ne_emptyset
    cases Classical.em (@Finset.univ V _ ⊆ ∅) with
    | inl h =>
        have _ : @Finset.univ V _ ⊆ ∅ ∧ ∅ ⊆ @Finset.univ V _ := ⟨h, h1⟩
        contradiction
    | inr h =>
        obtain ⟨x, _⟩ := Finset.not_subset.mp h
        have _ : Nonempty V := Nonempty.intro x
        exact Fintype.card_ne_zero
  · intro univ_empty
    exact Fintype.card_eq_zero_iff.mpr (Finset.univ_eq_empty_iff.mp univ_empty)
