import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Lemmas

import CWType.SimpleGraph.CaroWeiType.Calc

open SimpleGraph
open Finset

namespace CaroWeiType
namespace AB
namespace Bipartition

variable {V : Type} [Fintype V] [DecidableEq V]

lemma Claim0 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    {W : Finset V} (hWAB' : W ∩ AB.toFinset ≠ ∅)
    (hG : G.support ⊆ AB.toFinset)
    (h : eval G AB ≤ eval (G.deleteIncidencesOf W) (AB \ W))
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  obtain ⟨s, ⟨hs, hsf, hsresp, hscard⟩⟩ :=
    ih (G.deleteIncidencesOf W) (AB \ W) (hsupp_mono hG) (AB.sdiff_card hWAB')
  have hsW : s ∩ W = ∅ := by grind [sdiff_toFinset]
  refine ⟨s, subset_trans hs toFinset_mono, ?_, ?_, h.trans hscard⟩
  · intro x hx y hy hne
    simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe, Set.mem_setOf_eq,
      not_and, cancel_imp_of_and] at hx hy
    have hxW : x ∉ W := notMem_of_empty_inter_of_mem' hsW hx.1
    have hyW : y ∉ W := notMem_of_empty_inter_of_mem' hsW hy.1
    refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj hxW hyW |>.mt ?_
    refine hsf ?_ ?_ hne
    · simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe, Set.mem_setOf_eq,
        hx.1, true_and]
      exact ne_of_eq_of_ne (degree_in_deleteIncidencesOf s W (inter_comm s W ▸ hsW) hxW) hx.2
    · simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe, Set.mem_setOf_eq,
        hy.1, true_and]
      exact ne_of_eq_of_ne (degree_in_deleteIncidencesOf s W (inter_comm s W ▸ hsW) hyW) hy.2
  · intro x hxs hBx y hys hyx
    have hxW : x ∉ W := fun hxW ↦ notMem_empty _ <| hsW ▸ mem_inter.mpr ⟨hxs, hxW⟩
    have hyW : y ∉ W := fun hxW ↦ notMem_empty _ <| hsW ▸ mem_inter.mpr ⟨hys, hxW⟩
    obtain ⟨hA'y, hd'y⟩ :=
      hsresp x hxs ⟨hBx, hxW⟩ y hys <| deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj hyW hxW hyx
    refine ⟨hA'y.1, ?_⟩
    exact le_of_eq_of_le (degree_in_deleteIncidencesOf s W (inter_comm s W ▸ hsW) hyW).symm hd'y

lemma sum_sdiff_singleton_eval {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} {X : Finset V}
    {v : V} (hv : v ∈ X) (hNv : G.neighborFinset v ⊆ X) :
    ∑ w ∈ X, f G AB w
      = ∑ w ∈ X \ {v}, f (G.deleteIncidencesOf {v}) (AB \ {v}) w
        + ∑ w ∈ G.neighborFinset v, (f G AB w - f (G.deleteIncidencesOf {v}) (AB \ {v}) w)
        + f G AB v := by
  refine sum_sdiff_singleton G (fun G v _ ↦ f G AB v) hv hNv ?_ |>.trans ?_
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
    {AB : Bipartition V} [AB.Decidable] (s X : Finset V) (hX : s ⊆ X) :
    ∑ x ∈ X, f G AB x
      = ∑ x ∈ X, f G (AB.demote_finset s) x
        + ∑ x ∈ s, (f G AB x - f G (AB.demote_finset s) x) := by
  classical
  refine Eq.symm <| add_eq_of_eq_sub' <| Eq.symm ?_
  rw [← sum_sub_distrib, ← sum_sdiff hX, add_eq_right]
  refine sum_eq_zero fun x hx ↦ ?_
  exact sub_eq_zero_of_eq <| f_eq_of_demote_finset_of_notMem G AB (mem_sdiff.mp hx |>.2)

end Bipartition
end AB
end CaroWeiType
