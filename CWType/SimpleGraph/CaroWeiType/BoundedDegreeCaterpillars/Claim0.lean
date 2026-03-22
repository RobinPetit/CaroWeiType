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
  have h' : (ABC \ W).card < ABC.card := sdiff_card ABC hWABC'
  obtain ⟨s, ⟨hs1, hs2, hs3, hs4⟩⟩ := ih (G.deleteIncidencesOf W) (ABC \ W) h'
  have hsW : s ∩ W = ∅ := by grind [sdiff_toFinset]
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · simp only [Tripartition.toFinset, Tripartition.mem_iff] at hs1 ⊢
    exact subset_trans hs1 toFinset_mono
  · exact InducesForest_mono' _ _ _ hsW hs2
  · intro x hx
    suffices (G.deleteIncidencesOf W).degree_in s x = G.degree_in s x by
      rw [← this]
      have hxW : x ∉ W := fun hxW ↦ by grind [hsW ▸ mem_inter.mpr ⟨hx, hxW⟩]
      refine ⟨?_, ?_, ?_⟩
      · exact fun h ↦ hs3 x hx |>.1 ⟨h, hxW⟩
      · exact fun h ↦ hs3 x hx |>.2.1 ⟨h, hxW⟩
      · exact fun h ↦ hs3 x hx |>.2.2 ⟨h, hxW⟩
    rw [degree_in]
    refine congrArg _ ?_
    ext y
    simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_inter, mem_neighborFinset,
      inf_adj, iInf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and,
      not_or, ne_eq, and_congr_left_iff, and_iff_left_iff_imp]
    intro hy hxy
    refine ⟨fun z ↦ ⟨fun hz ↦ ⟨hxy, fun _ ↦ ?_⟩, hxy.ne⟩, hxy.ne⟩
    constructor <;> exact ne_of_mem_finset_empty_inter _ _ hsW (by simp [hx, hy]) hz |>.symm
  · exact le_trans h hs4

end Tripartition
end ABC
end CaroWeiType
