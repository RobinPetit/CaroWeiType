import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim1
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim3
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Lemmas

open SimpleGraph
open Finset

namespace CaroWeiType
namespace AB
namespace Bipartition

variable {V : Type} [Fintype V] [DecidableEq V]

private lemma _Claim4 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {û : V} (hû : û ∈ AB.toFinset)
    (hv : ∀ w ∈ AB.toFinset, γ G AB û ≤ γ G AB w) (hγû : f G AB û ≤ (G.degree û) * γ G AB û)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  refine Claim1 (AB.mem_toFinset.mpr hû) hG ih ?_
  suffices f G AB û ≤ ∑ w ∈ G.neighborFinset û, γ G AB û by
    refine le_trans this (sum_le_sum fun x hx ↦ hv _ ?_)
    exact hG <| G.mem_support.mpr ⟨û, Adj.symm <| mem_neighborFinset .. |>.mp hx⟩
  refine le_of_le_of_eq hγû ?_
  simp only [sum_const', card_neighborFinset_eq_degree]

lemma Claim4 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    (∀ v, (AB.A v → (G.degree v = 2 ∨ G.degree v = 3)) ∧ (AB.B v → G.degree v = 2))
      ∨ Objective G AB := by
  if hAB : AB.toFinset.Nonempty then
    obtain ⟨û, hû, hmin⟩ := exists_argmin hAB (γ G AB ·)
    if hdû : G.degree û ≤ 1 then
      exact Or.inr <| Claim3 hG (AB.mem_toFinset.mpr hû) hdû ih
    else if hγû : f G AB û ≤ (G.degree û) * γ G AB û then
      exact Or.inr <| _Claim4 hG hû hmin hγû ih
    else
      have hne := ne_of_lt <| not_le.mp hγû
      have hγû : 1 / 10 ≤ γ G AB û := by
        rcases AB.mem_toFinset.mpr hû with hA | hB
        · suffices G.degree û ≤ 3 by
            have : G.degree û = 2 ∨ G.degree û = 3 := by lia
            simp only [γ, hA, ↓reduceDIte]
            rcases this with hdû | hdû
            · rw [hdû, γA2']; linarith
            · rw [hdû, γA3']
          by_contra
          have := γA_eq_of_four_le_d (by lia : 4 ≤ G.degree û)
          simp only [f, γ, hA, ↓reduceDIte, this] at hne
          rw [fA_eq_of_three_le_d (by lia : 3 ≤ G.degree û)] at hne
          have {a b : ℝ} (ha : a ≠ 0) : a * (2 / (a * b)) = 2 / b := by grind
          rw [this] at hne
          · exact hne rfl |>.elim
          · simp only [ne_eq, Nat.cast_eq_zero]
            lia
        · simp only [f, γ, hB, not_A_of_B, ↓reduceDIte] at hne
          nth_rewrite 3 [fB] at hne
          rw [γB_eq_of_one_le_d (by linarith : 1 ≤ G.degree û)] at hne
          have {a b : ℝ} (ha : a ≠ 0) : a * (1 / (a * b)) = 1 / b := by grind
          rw [this] at hne
          · exact hne rfl |>.elim
          · simp only [ne_eq, Nat.cast_eq_zero]
            lia
      if HA4 : ∃ v, AB.A v ∧ G.degree v = 4 then
        obtain ⟨v, hAv, hdv⟩ := HA4
        have hv : v ∈ AB.toFinset := AB.mem_toFinset.mp <| Or.inl hAv
        refine Or.inr <| _Claim4 hG hv ?_ ?_ ih
        · exact fun w hw ↦ le_trans (γA4 hAv hdv ▸ hγû) (hmin _ hw)
        · simp only [γ, f, hAv, ↓reduceDIte]
          rw [γA_eq_of_four_le_d (le_of_eq hdv.symm)]
          rw [fA_eq_of_three_le_d (by linarith : 3 ≤ G.degree v)]
          refine le_of_eq ?_
          have {a b : ℝ} (ha : a ≠ 0) : a * (2 / (a * b)) = 2 / b := by grind
          simp only [this, hdv, Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
      else if H : ∀ v ∈ AB.toFinset, 2 ≤ G.degree v then
        refine Or.inl fun v ↦ ⟨fun hAv ↦ ?_, fun hBv ↦ ?_⟩
        · suffices G.degree v ≤ 3 by
            grind [AB.mem_toFinset.mp <| Or.inl hAv]
          have : ¬(5 ≤ G.degree v) := by
            by_contra
            have := γA_decreasing this (by omega)
            have hobj := hγû.trans (hmin v <| AB.mem_toFinset.mp <| Or.inl hAv)
            simp only [γ, hAv, ↓reduceDIte] at hobj
            linarith [γA5']
          suffices G.degree v ≠ 4 by lia
          simp only [not_exists, not_and] at HA4
          exact HA4 v hAv
        · by_contra
          have hdv : 3 ≤ G.degree v := by grind [AB.mem_toFinset.mp <| Or.inr hBv]
          have :=
            hγû.trans <| hmin v (hG <| degree_pos_iff_mem_support .. |>.mp <| Nat.zero_lt_of_lt hdv)
          simp only [γ, hBv, not_A_of_B, ↓reduceDIte] at this
          have := this.trans <| γB_decreasing hdv (by omega)
          simp only [Nat.add_one_sub_one, fB, Nat.cast_two, Nat.cast_three] at this
          linarith
      else
        simp only [not_forall, not_le] at H
        obtain ⟨v, hv, hdv⟩ := H
        exact Or.inr <| Claim3 hG (AB.mem_toFinset.mpr hv) (Nat.le_of_lt_succ hdv) ih
  else
    simp only [not_nonempty_iff_eq_empty] at hAB
    refine Or.inl <| fun v ↦ ⟨fun hAv ↦ ?_, fun hBv ↦ ?_⟩
    · exact notMem_empty v (hAB ▸ AB.mem_toFinset.mp <| Or.inl hAv) |>.elim
    · exact notMem_empty v (hAB ▸ AB.mem_toFinset.mp <| Or.inr hBv) |>.elim

lemma Claim4' {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    (∀ v ∈ AB.toFinset,
      (AB.A v ∧ G.degree v = 2) ∨ (AB.A v ∧ G.degree v = 3) ∨ (AB.B v ∧ G.degree v = 2))
      ∨ Objective G AB := by
  by_contra
  simp only [not_or, not_forall, not_and] at this
  obtain ⟨⟨v, hv, ⟨hA2, hA3, hB2⟩⟩, hobj⟩ := this
  have := Claim4 hG ih
  simp only [hobj, or_false] at this
  obtain ⟨h₁, h₂⟩ := this v
  rcases AB.mem_toFinset.mpr hv with hA | hB <;> grind

lemma Corollary4 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    (∀ v ∈ AB.toFinset, 1 / 3 ≤ f G AB v ∧ f G AB v ≤ 3 / 5 ∧ 1 / 10 ≤ γ G AB v ∧ γ G AB v ≤ 7 / 30)
      ∨ Objective G AB := by
  cases Claim4' hG ih with
  | inr h => exact Or.inr h
  | inl h => ?_
  refine Or.inl <| fun v hv ↦ ?_
  rcases h v hv with ⟨hAv, hdv⟩ | ⟨hAv, hdv⟩ | ⟨hBv, hdv⟩
  · simp only [fA2 hAv hdv, γA2 hAv hdv]; grind
  · simp only [fA3 hAv hdv, γA3 hAv hdv]; grind
  · simp only [fB2 hBv hdv, γB2 hBv hdv]; grind

end Bipartition
end AB
end CaroWeiType
