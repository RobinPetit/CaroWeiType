import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas

open SimpleGraph
open Finset

namespace CaroWeiType
namespace ABC
namespace Tripartition

variable {V : Type} [Fintype V] [DecidableEq V]

lemma Claim0 {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V} [ABC.Decidable]
    {W : Finset V} (hWABC' : W ∩ ABC.toFinset ≠ ∅)
    (hG : G.support ⊆ ABC.toFinset)
    (h : eval G ABC ≤ eval (G.deleteIncidencesOf W) (ABC \ W))
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  have h' : (ABC \ W).card < ABC.card := sdiff_card ABC hWABC'
  obtain ⟨s, ⟨hs1, hs2, hs3, hs4⟩⟩ := ih (G.deleteIncidencesOf W) (ABC \ W) (hsupp_mono hG) h'
  have hsW : s ∩ W = ∅ := by grind [sdiff_toFinset]
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · simp only [Tripartition.toFinset] at hs1 ⊢
    exact subset_trans hs1 toFinset_mono
  · exact InducesForest_graph_mono' hsW hs2
  · intro x hx
    suffices (G.deleteIncidencesOf W).degree_in s x = G.degree_in s x by
      rw [← this]
      have hxW : x ∉ W := fun hxW ↦ notMem_empty _ <| hsW ▸ mem_inter.mpr ⟨hx, hxW⟩
      refine ⟨?_, ?_, ?_⟩
      · exact fun h ↦ hs3 x hx |>.1 ⟨h, hxW⟩
      · exact fun h ↦ hs3 x hx |>.2.1 ⟨h, hxW⟩
      · exact fun h ↦ hs3 x hx |>.2.2 ⟨h, hxW⟩
    refine congrArg Finset.card ?_
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
