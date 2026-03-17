import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

lemma Claim0 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (W : Finset (Fin n)) (hWABC' : W ∩ ABC.toFinset ≠ ∅)
    (h : eval G ABC ≤ eval (G.deleteIncidencesOf W) (ABC \ W))
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  have h' : (ABC \ W).card < ABC.card := by
    simp only [Tripartition.card, Tripartition.toFinset, Tripartition.mem_iff]
    refine Finset.card_lt_card ⟨?_, ?_⟩
    · intro x
      simp only [Tripartition.sdiff, Tripartition.mem_iff, mem_filter,
        mem_univ, true_and]
      grind
    · intro h
      obtain ⟨w, hw⟩ := @Classical.choice ↑(W ∩ ABC.toFinset) (Nonempty.to_subtype (by grind))
      simp only [mem_inter] at hw
      let hobj := h hw.2
      simp [Tripartition.sdiff] at hobj
      grind
  obtain ⟨s, ⟨hs1, hs2, hs3, hs4⟩⟩ := ih (G.deleteIncidencesOf W) (ABC \ W) h'
  have hsW : s ∩ W = ∅ := by
    simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff] at hs1
    ext x
    simp only [mem_inter, notMem_empty, iff_false, not_and]
    intro hx
    let hobj := hs1 hx
    simp only [Tripartition.mem_iff, mem_filter, mem_univ, true_and] at hobj
    grind
  refine ⟨s, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [Tripartition.toFinset, Tripartition.mem_iff] at hs1 ⊢
    exact subset_trans hs1 Tripartition.toFinset_mono
  · exact InducesForest_mono' _ _ _ hsW hs2.1
  · intro x hx
    suffices #((G.deleteIncidencesOf W).neighborFinset x ∩ s) = #(G.neighborFinset x ∩ s) by
      exact this ▸ (hs2.2 x hx)
    refine congrArg _ ?_
    ext y
    simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_inter, mem_neighborFinset,
      inf_adj, iInf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and,
      not_or, ne_eq, and_congr_left_iff, and_iff_left_iff_imp]
    intro hy hxy
    refine ⟨fun z ↦ ⟨fun hz ↦ ⟨hxy, fun _ ↦ ?_⟩, hxy.ne⟩, hxy.ne⟩
    constructor <;> exact ne_of_mem_finset_empty_inter _ _ hsW (by simp [hx, hy]) hz |>.symm
  · simp only [respects] at hs3 ⊢
    intro w hw
    have heq : #((G.deleteIncidencesOf W).neighborFinset w ∩ s) = #(G.neighborFinset w ∩ s) := by
      refine congrArg _ ?_
      ext u
      constructor
      · intro hu
        simp only [deleteIncidencesOf, mem_inter, mem_neighborFinset, inf_adj, iInf_adj,
          ne_eq] at hu ⊢
        exact ⟨hu.1.1,  hu.2⟩
      · intro hu
        simp only [mem_inter, mem_neighborFinset, deleteIncidencesOf, deleteIncidenceSet,
          incidenceSet, inf_adj, iInf_adj, deleteEdges_adj, ne_eq] at hu ⊢
        refine ⟨⟨hu.1, ⟨fun v ↦ ⟨fun hv ↦ ⟨hu.1, ?_⟩, hu.1.ne⟩, hu.1.ne⟩⟩, hu.2⟩
        intro this
        simp only [Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff] at this
        rcases this.2 <;>
          { rename_i hv';
            have _ : v ∈ s ∩ W := by { subst hv'; simp [mem_inter, hv, hw, hu.2]; }; grind }
    have hwW : w ∉ W := by
      let hobj := hs1 hw
      simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff,
        mem_filter, mem_univ, true_and] at hobj
      grind
    simp only [degree_in]
    refine ⟨?_, ?_, ?_⟩
    · exact fun hAw ↦ heq.symm ▸ (hs3 w hw).1   ⟨hAw, hwW⟩
    · exact fun hBw ↦ heq.symm ▸ (hs3 w hw).2.1 ⟨hBw, hwW⟩
    · exact fun hCw ↦ heq.symm ▸ (hs3 w hw).2.2 ⟨hCw, hwW⟩
  · exact le_trans h hs4

end Tripartition
end ABC
end CaroWeiType
