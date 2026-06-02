import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas

import CWType.SimpleGraph.CaroWeiType.Calc

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
  obtain ⟨s, ⟨hs, hsf, hsresp, hscard⟩⟩ :=
    ih (G.deleteIncidencesOf W) (ABC \ W) (hsupp_mono hG) (ABC.sdiff_card hWABC')
  have hsW : s ∩ W = ∅ := by grind [sdiff_toFinset]
  refine ⟨s, subset_trans hs toFinset_mono, InducesForest_graph_mono' hsW hsf, ?_, h.trans hscard⟩
  intro x hx
  have hxW : x ∉ W := fun hxW ↦ notMem_empty _ <| hsW ▸ mem_inter.mpr ⟨hx, hxW⟩
  rw [← degree_in_deleteIncidencesOf s W (inter_comm s W ▸ hsW) hxW]
  refine ⟨?_, ?_, ?_⟩
  · exact fun h ↦ hsresp x hx |>.1 ⟨h, hxW⟩
  · exact fun h ↦ hsresp x hx |>.2.1 ⟨h, hxW⟩
  · exact fun h ↦ hsresp x hx |>.2.2 ⟨h, hxW⟩

lemma sum_sdiff_singleton_eval {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V} {X : Finset V}
    {v : V} (hv : v ∈ X) (hNv : G.neighborFinset v ⊆ X) :
    ∑ w ∈ X, f G ABC w
      = ∑ w ∈ X \ {v}, f (G.deleteIncidencesOf {v}) (ABC \ {v}) w
        + ∑ w ∈ G.neighborFinset v, (f G ABC w - f (G.deleteIncidencesOf {v}) (ABC \ {v}) w)
        + f G ABC v := by
  refine sum_sdiff_singleton G (fun G v _ ↦ f G ABC v) hv hNv ?_ |>.trans ?_
  · intro w hw
    simp only
    refine f_congr_degree _ _ _ ?_
    refine congrArg Finset.card ?_
    refine Eq.symm <| neighborFinset_eq_delelteIncidencesOf_of_empty_inter_neighborFinset ?_ ?_
    · simp only [inter_singleton_eq_empty_iff]
      refine not_mem_neighborFinset_symm <| notMem_mono ?_ (mem_sdiff.mp hw |>.2)
      intro u hu
      refine mem_closed_neighborFinset_iff.mpr <| Or.inr ⟨v, mem_singleton.mpr rfl, ?_⟩
      exact mem_neighborFinset .. |>.mp hu
    · exact notMem_mono G.closed_neighborFinset_contains_Finset (mem_sdiff.mp hw |>.2)
  · simp only [add_left_inj]
    refine add_congr ?_ ?_
    · exact sum_congr rfl fun w hw ↦ f_eq_sdiff <| mem_sdiff.mp hw |>.2
    · refine sum_congr rfl fun w hw ↦ sub_right_inj.mpr <| f_eq_sdiff ?_
      exact notMem_singleton.mpr <| ne_of_mem_neighborFinset hw

lemma sum_eq_sum_demote_finset {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {ABC : Tripartition V} [ABC.Decidable] {s X : Finset V} (hX : s ⊆ X) :
    ∑ x ∈ X, f G ABC x
      = ∑ x ∈ X, f G (ABC.demote_finset s) x
        + ∑ x ∈ s, (f G ABC x - f G (ABC.demote_finset s) x) := by
  classical
  refine Eq.symm <| add_eq_of_eq_sub' <| Eq.symm ?_
  rw [← sum_sub_distrib, ← sum_sdiff hX, add_eq_right]
  refine sum_eq_zero fun x hx ↦ ?_
  exact sub_eq_zero_of_eq <| f_eq_of_demote_finset_of_notMem G ABC (mem_sdiff.mp hx |>.2)

end Tripartition
end ABC
end CaroWeiType
