import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim0

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

lemma Claim1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : v ∈ ABC) (hG : G.support.toFinset ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    f G ABC v ≤ ∑ w ∈ G.neighborFinset v, γ G ABC w → Objective G ABC := by
  have hNv : G.neighborFinset v ⊆ ABC.toFinset := by
    intro u hu
    refine hG <| Set.mem_toFinset.mpr ?_
    refine G.mem_support.mpr ⟨v, ?_⟩
    exact G.mem_neighborFinset .. |>.mp <| mem_neighborFinset_symm hu
  have hNv' : G.neighborFinset v ⊆ (ABC \ {v}).toFinset := by
    rw [sdiff_toFinset]
    intro w hw
    refine mem_sdiff.mpr ⟨hNv hw, ?_⟩
    simp only [mem_singleton, ne_of_mem_neighborFinset _ hw, not_false_eq_true]
  intro h
  have hvABC : {v} ∩ ABC.toFinset ≠ ∅ := by
    refine nonempty_iff_ne_empty.mp ⟨v, ?_⟩
    simp only [← coe_mem_toFinset, hv, singleton_inter_of_mem, mem_singleton]
  refine Claim0 hvABC hG ?_ ih
  calc eval G ABC
    _ = ∑ x ∈ (ABC \ {v}).toFinset, f G ABC x + f G ABC v := by
      rw [sdiff_toFinset, ← sum_singleton (f G ABC ·) _]
      exact Eq.symm <| sum_sdiff <| singleton_subset_iff.mpr <| ABC.coe_mem_toFinset .. |>.mp hv
    _ = ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v, f G ABC x
      + ∑ x ∈ G.neighborFinset v, f G ABC x + f G ABC v := by
      simp only [add_left_inj]
      refine Eq.symm <| sum_sdiff ?_
      intro x hx
      have hxnev : x ≠ v := G.mem_neighborFinset .. |>.mp hx |>.ne'
      refine Tripartition.coe_mem_toFinset .. |>.mp ?_
      refine (ABC.mem_sdiff_iff _).mpr ⟨ABC.coe_mem_toFinset.mpr <| hNv hx, ?_⟩
      simp only [mem_singleton, hxnev, not_false_eq_true]
    _ = ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v, f G ABC x
        + (∑ x ∈ G.neighborFinset v, f G ABC x + f G ABC v) := by
      lia
    _ ≤ ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v, f G ABC x
        + (∑ x ∈ G.neighborFinset v, f G ABC x
        + ∑ x ∈ G.neighborFinset v, γ G ABC x) := by
      exact add_le_add_right (add_le_add_right h _) _
    _ = ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v, f G ABC x
        + ∑ x ∈ G.neighborFinset v, (f G ABC x + γ G ABC x) := by
      simp only [add_right_inj]
      exact Eq.symm <| sum_add_distrib
    _ = ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v, f G ABC x
        + ∑ x ∈ G.neighborFinset v, f (G.deleteIncidencesOf {v}) (ABC \ {v}) x := by
      simp only [add_right_inj]
      refine sum_congr rfl ?_
      intro x hx
      exact Eq.symm <| f_deleteIncidencesOf_singleton ABC G (G.mem_neighborFinset .. |>.mp hx)
    _ = ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v, f G (ABC \ {v}) x
        + ∑ x ∈ G.neighborFinset v, f (G.deleteIncidencesOf {v}) (ABC \ {v}) x := by
      simp only [add_left_inj]
      refine sum_congr rfl ?_
      intro x hx
      refine Eq.symm <| f_eq_in_sdiff G ABC ?_
      exact mem_sdiff.mp (ABC.sdiff_toFinset ▸ mem_sdiff.mp hx |>.1) |>.2
    _ = ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v,
          f (G.deleteIncidencesOf {v}) (ABC \ {v}) x
        + ∑ x ∈ G.neighborFinset v, f (G.deleteIncidencesOf {v}) (ABC \ {v}) x := by
      simp only [add_left_inj]
      refine sum_congr rfl ?_
      intro x hx
      suffices (G.deleteIncidencesOf {v}).degree x = G.degree x by
        simp only [f, Tripartition.sdiff_eq, inter_assoc, inter_self, fA, fB, one_div, fC,
          dite_eq_ite, this]
      refine congrArg Finset.card ?_
      ext w
      simp only [mem_sdiff, sdiff_toFinset] at hx
      if hwv : w ∈ ({v} : Finset _) then
        simp only [mem_singleton] at hwv
        simp only [mem_neighborFinset, not_mem_neighborFinset_symm <| hwv ▸ hx.2, iff_false]
        exact not_adj_symm <| deleteIncidencesOf_notadj _ (mem_singleton.mpr hwv)
      else
        exact (deleteIncidencesOf_mem_neighborFinset_iff_of_notMem hwv hx.1.2).symm
    _ = ∑ x ∈ (ABC \ {v}).toFinset, f (G.deleteIncidencesOf {v}) (ABC \ {v}) x := by
      rw [add_comm]
      have hobj := sum_inter_add_sum_diff (ABC \ {v}).toFinset (G.neighborFinset v)
        (f (G.deleteIncidencesOf {v}) (ABC \ {v}) ·)
      have this : (ABC \ {v}).toFinset ∩ G.neighborFinset v = G.neighborFinset v := by
        refine inter_eq_right.mpr ?_
        intro w hw
        simp only [sdiff_toFinset]
        refine mem_sdiff.mpr ⟨hNv hw, ?_⟩
        simp only [mem_singleton, ne_of_mem_neighborFinset _ hw, not_false_eq_true]
      rw [this] at hobj
      exact hobj

lemma Corollary1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v w : Fin n} (hG : G.support.toFinset ⊆ ABC.toFinset)
    (hw : G.Adj v w)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    f G ABC v ≤ γ G ABC w → Objective G ABC := by
  let hv := ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨w, hw⟩
  intro h
  refine Claim1 hv hG ih <| le_trans h ?_
  calc γ G ABC w
    _ = ∑ x ∈ {w}, γ G ABC x := Eq.symm <| sum_singleton ..
    _ = 0 + ∑ x ∈ {w}, γ G ABC x := by simp only [zero_add, sum_singleton]
    _ ≤ ∑ x ∈ G.neighborFinset v \ {w}, γ G ABC x + ∑ x ∈ {w}, γ G ABC x := by
      exact add_le_add_left (sum_nonneg (fun _ _ ↦ γ_nonneg)) _
    _ = ∑ x ∈ G.neighborFinset v, γ G ABC x := by
      exact sum_sdiff <| singleton_subset_iff.mpr <| G.mem_neighborFinset .. |>.mpr hw

end Tripartition
end ABC
end CaroWeiType
