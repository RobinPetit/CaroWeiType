import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim1
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim6
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim9
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim10
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim14

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

lemma Claim15 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û : Fin n} (hû : IsVstar G ABC û)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨ 4 ≤ G.degree û := by
  cases Claim14 hG hû ih with
  | inl h => exact Or.inl h
  | inr h => ?_
  obtain ⟨hA2, hdû, hfû, hNû⟩ := h
  if hdû : 4 ≤ G.degree û then
    exact Or.inr hdû
  else if hC2 : ∃ w, ABC.C w ∧ G.degree w = 2 then
    obtain ⟨w, hCw, hdw⟩ := hC2
    exact Or.inl <| Claim6 hG ih ⟨w, hdw, not_A_of_C hCw⟩
  else
    simp only [not_exists, not_and] at hC2
    have := one_le_deg_of_vstar hû
    have hdû : G.degree û = 3 := by lia
    have hAû : ABC.A û := by
      have hABC := mem_ABC_of_vstar hû
      have hneBC3 := And.intro (ne_B3_of_vstar hû) (ne_C3_of_vstar hû)
      simp only [hdû, and_true] at hneBC3
      simp only [mem_iff, hneBC3, or_self, or_false] at hABC
      exact hABC
    refine Or.inl ?_
    have hABC {u v : Fin n} (huv : u ∈ G.neighborFinset v) : u ∈ ABC :=
      ABC.mem_toFinset.mpr <| hG
        <| G.mem_support.mpr ⟨_, Adj.symm <| G.mem_neighborFinset .. |>.mp huv⟩
    if hNvC : ∃ w ∈ G.neighborFinset û, ABC.C w ∧ G.degree w = 3 then
      obtain ⟨w, hw, hCw, hdw⟩ := hNvC
      refine Corollary1 hG (G.mem_neighborFinset .. |>.mp hw).symm ih ?_
      simp only [γA3 hAû hdû, fC3 hCw hdw, le_refl]
    else
      simp only [not_exists, not_and] at hNvC
      obtain ⟨w, hw, hdw, hAw⟩ := hNû
      have hBw : ABC.B w := by
        let hobj := hABC hw
        simp only [mem_iff, hAw, hNvC _ hw |>.mt <| not_not_intro hdw, or_false, false_or] at hobj
        exact hobj
      obtain ⟨x, y, z, hxyz, hγzy, hγyx⟩ := neighborFinset_eq_deg3 (γ G ABC ·) hdw
      have hγ {u : Fin n} (hu : u ∈ G.neighborFinset w) (hγu : γ G ABC u = 0) :
          Objective G ABC ∨ ABC.B u ∧ G.degree u = 3 := by
        let hobj := γ_eq_0_iff (hABC hu) (one_le_degree_of_mem_neighborFinset' hu) |>.mp hγu
        rcases hobj with h | h | h
        · exact Or.inr h.symm
        · exact Or.inl <| Corollary9 hG hBw hdw ih ⟨u, G.mem_neighborFinset .. |>.mp hu, h.2⟩
        · exact hC2 _ h.2 h.1 |>.elim
      if hγy : γ G ABC y = 0 then
        have hγz : γ G ABC z = 0 := le_antisymm (le_of_le_of_eq hγzy hγy) γ_nonneg
        have hyw : y ∈ G.neighborFinset w := by
          simp only [hxyz, mem_insert, mem_singleton, true_or, or_true]
        have hzw : z ∈ G.neighborFinset w := by
          simp only [hxyz, mem_insert, mem_singleton, or_true]
        match hγ hyw hγy, hγ hzw hγz with
        | Or.inl h, _ => exact h
        | _, Or.inl h => exact h
        | Or.inr h₁, Or.inr h₂ => ?_
        refine Claim10 hG hBw hdw ih ⟨y, z, by grind [degree], ?_, ?_, h₁.1, h₂.1, h₁.2, h₂.2⟩
        · exact G.mem_neighborFinset .. |>.mp hyw
        · exact G.mem_neighborFinset .. |>.mp hzw
      else
        have hw : w ∈ ABC := by simp only [mem_iff, hBw, true_or, or_true]
        refine Claim1 hw hG ih ?_
        suffices f G ABC w ≤ γ G ABC y + γ G ABC x by
          grind [degree]
        rw [fB3 hBw hdw]
        calc (1 : ℝ) / 3
          _ = 1 / 6 + 1 / 6 := by linarith
          _ = γ G ABC û + γ G ABC û := by rw [γA3 hAû hdû]
          _ ≤ γ G ABC y + γ G ABC y := by
            refine add_le_add ?_ ?_ <;> {
              have hy : y ∈ G.neighborFinset w := by
                simp only [hxyz, mem_insert, mem_singleton, true_or, or_true]
              exact γ_vstar_le_γ hû (hABC hy) hγy
            }
          _ ≤ γ G ABC y + γ G ABC x := by
            exact add_le_add_right hγyx _

end Tripartition
end ABC
end CaroWeiType
