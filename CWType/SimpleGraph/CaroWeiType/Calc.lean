import CWType.SimpleGraph.CaroWeiType.Lemmas

namespace Finset

lemma split_sum {α β ι : Type*} [DecidableEq ι] [Ring β] {f : ι → β} (s : Finset α) (s' : Finset ι)
    {g : α → Finset ι} (h : s.sup g = s')
    (h' : ∀ x y, x ≠ y → g x ∩ g y = ∅) :
    ∑ x ∈ s', f x = ∑ x ∈ s, ∑ y ∈ g x, f y := by
  induction s using Finset.cons_induction generalizing s' with
  | empty =>
    simp_all only [ne_eq, Finset.sup_empty, Finset.bot_eq_empty, Finset.sum_empty,
      not_false_eq_true, implies_true]
    rw [← h, Finset.sum_empty]
  | cons y _s hys ih => ?_
  simp only [Finset.sum_cons]
  simp only [Finset.sup_cons, Finset.sup_eq_union'] at h
  rw [← ih _ rfl, ← h]
  rw [Finset.sum_union]
  refine Finset.disjoint_iff_inter_eq_empty.mpr ?_
  ext u
  simp only [Finset.notMem_empty, iff_false, Finset.mem_inter, not_and', Finset.mem_sup]
  intro ⟨x, hxs, hx⟩
  exact notMem_of_mem_of_empty_inter hx <| h' _ _ (ne_of_mem_of_not_mem hxs hys)

lemma sum_disjoint_union {α β : Type*} [DecidableEq α] [Ring β] {s s' t : Finset α} {f : α → β}
    (ht : t = s ∪ s') (hss' : s ∩ s' = ∅) :
    ∑ x ∈ s, f x + ∑ x ∈ s', f x = ∑ x ∈ t, f x := by
  refine Eq.symm <| Eq.trans ?_ sum_union_inter
  simp only [ht, hss', sum_empty, add_zero]

end Finset

open SimpleGraph
open Finset

lemma sum_sdiff_singleton {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {f : ℕ → ℝ} {X : Finset V}
    {v : V} (hv : v ∈ X) (hNv : G.neighborFinset v ⊆ X) :
    ∑ w ∈ X, f (G.degree w)
      = ∑ w ∈ X \ {v}, f ((G.deleteIncidencesOf {v}).degree w)
        + ∑ w ∈ G.neighborFinset v, (f (G.degree w) - f ((G.deleteIncidencesOf {v}).degree w))
        + f (G.degree v) := by
  calc _
    _ = ∑ w ∈ X \ G.closed_neighborFinset_of_Finset {v}, f (G.degree w)
        + ∑ w ∈ G.closed_neighborFinset_of_Finset {v}, f (G.degree w) := by
      refine Eq.symm (sum_sdiff ?_)
      intro w hw
      have := mem_closed_neighborFinset_iff.mp hw
      grind [mem_neighborFinset]
    _ = ∑ w ∈ X \ G.closed_neighborFinset_of_Finset {v}, f ((G.deleteIncidencesOf {v}).degree w)
        + ∑ w ∈ G.closed_neighborFinset_of_Finset {v}, f (G.degree w) := by
      simp only [add_left_inj]
      refine sum_congr rfl fun w hw ↦ ?_
      refine congrArg (f ∘ Finset.card) ?_
      refine Eq.symm <| neighborFinset_eq_delelteIncidencesOf_of_empty_inter_neighborFinset ?_ ?_
      · simp only [inter_singleton_eq_empty_iff]
        refine not_mem_neighborFinset_symm <| notMem_mono ?_ (mem_sdiff.mp hw |>.2)
        intro u hu
        refine mem_closed_neighborFinset_iff.mpr <| Or.inr ⟨v, mem_singleton.mpr rfl, ?_⟩
        exact mem_neighborFinset .. |>.mp hu
      · exact notMem_mono G.closed_neighborFinset_contains_Finset (mem_sdiff.mp hw |>.2)
    _ = (∑ w ∈ X \ G.closed_neighborFinset_of_Finset {v}, f ((G.deleteIncidencesOf {v}).degree w)
        + ∑ w ∈ G.neighborFinset v, f ((G.deleteIncidencesOf {v}).degree w))
        - ∑ w ∈ G.neighborFinset v, f ((G.deleteIncidencesOf {v}).degree w)
        + ∑ w ∈ G.closed_neighborFinset_of_Finset {v}, f (G.degree w) := by
      linarith
    _ = ∑ w ∈ X \ {v}, f ((G.deleteIncidencesOf {v}).degree w)
        - ∑ w ∈ G.neighborFinset v, f ((G.deleteIncidencesOf {v}).degree w)
        + ∑ w ∈ G.closed_neighborFinset_of_Finset {v}, f (G.degree w) := by
      simp only [add_left_inj, sub_left_inj]
      rw [closed_neighborFinset_of_singleton_eq]
      refine sum_disjoint_union ?_ (by grind)
      grind [ne_of_mem_neighborFinset]
    _ = ∑ w ∈ X \ {v}, f ((G.deleteIncidencesOf {v}).degree w)
        - ∑ w ∈ G.neighborFinset v, f ((G.deleteIncidencesOf {v}).degree w)
        + (∑ w ∈ G.neighborFinset v, f (G.degree w) + f (G.degree v)) := by
      rw [closed_neighborFinset_of_singleton_eq]
      simp only [union_singleton, mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true,
        sum_insert, add_right_inj]
      rw [add_comm]
  simp only [sum_sub_distrib]
  grind

