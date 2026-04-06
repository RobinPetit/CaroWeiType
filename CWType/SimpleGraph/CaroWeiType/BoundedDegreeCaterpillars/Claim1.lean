import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim0

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

lemma Claim1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (v : Fin n) (hv : v ∈ ABC) (hNv : G.neighborFinset v ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    f G ABC v ≤ ∑ w ∈ G.neighborFinset v, γ G ABC w → Objective G ABC := by
  intro h
  refine Claim0 G ABC {v} ?_ ?_ ih
  · suffices {v} ∩ ABC.toFinset = {v} by
      rw [this]
      exact singleton_ne_empty _
    simp [hv, Tripartition.toFinset]
  · calc eval G ABC
      _ = ∑ x ∈ (ABC \ {v}).toFinset, f G ABC x + f G ABC v := by
        have h : (ABC \ {v}).toFinset = ABC.toFinset \ {v} := by
          ext x
          simp only [toFinset, sdiff, mem_singleton, mem_iff, and_or_3, mem_filter, mem_univ,
            true_and, mem_sdiff]
        rw [h]
        rw [← sum_singleton (f G ABC) v]
        refine Eq.symm <| sum_sdiff <| singleton_subset_iff.mpr ?_
        exact Tripartition.coe_mem_toFinset .. |>.mp hv
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
          let hobj := mem_sdiff.mp hx |>.1
          simp [Tripartition.sdiff, Tripartition.toFinset] at hobj
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
        simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_neighborFinset,
          mem_singleton, iInf_iInf_eq_left, inf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet,
          Sym2.mem_iff, not_and, not_or, and_self_left, and_iff_left_iff_imp, forall_self_imp]
        intro hxw
        constructor
        · simp [Tripartition.sdiff, Tripartition.toFinset] at hx
          grind
        · intro this
          subst this
          let hnotvx := (not_iff_not.mpr (G.mem_neighborFinset _ _)).mp <| mem_sdiff.mp hx |>.2
          exact hnotvx hxw.symm |>.elim
      _ = ∑ x ∈ (ABC \ {v}).toFinset, f (G.deleteIncidencesOf {v}) (ABC \ {v}) x := by
        rw [add_comm]
        let hobj := @sum_inter_add_sum_diff
          (Fin n) ℝ _ _ (ABC \ {v}).toFinset (G.neighborFinset v)
          (fun x ↦ f (G.deleteIncidencesOf {v}) (ABC \ {v}) x)
        have this : (ABC \ {v}).toFinset ∩ G.neighborFinset v = G.neighborFinset v := by
          ext w
          constructor
          · exact mem_of_mem_inter_right
          · intro hw
            simp only [Tripartition.toFinset, Tripartition.mem_iff, mem_inter,
              mem_filter, mem_univ, true_and, hw, and_true, Tripartition.sdiff]
            have _ : w ∉ ({v} : Finset _) := by
              simp only [mem_neighborFinset, mem_singleton] at hw ⊢
              exact hw.ne'
            have _ : ABC.A w ∨ ABC.B w ∨ ABC.C w := by
              refine ABC.mem_iff.mp ?_
              exact ABC.coe_mem_toFinset.mpr <| hNv hw
            grind
        rw [this] at hobj
        exact hobj

lemma Corollary1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (v w : Fin n) (hv : v ∈ ABC) (hNv : G.neighborFinset v ⊆ ABC.toFinset)
    (hw : G.Adj v w)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    f G ABC v ≤ γ G ABC w → Objective G ABC := by
  intro h
  refine Claim1 G ABC v hv hNv ih <| le_trans h ?_
  calc γ G ABC w
    _ = ∑ x ∈ {w}, γ G ABC x := Eq.symm <| sum_singleton ..
    _ = 0 + ∑ x ∈ {w}, γ G ABC x := by simp only [zero_add, sum_singleton]
    _ ≤ ∑ x ∈ G.neighborFinset v \ {w}, γ G ABC x + ∑ x ∈ {w}, γ G ABC x := by
      exact add_le_add_left (sum_nonneg (fun _ _ ↦ γ_nonneg G ABC)) _
    _ = ∑ x ∈ G.neighborFinset v, γ G ABC x := by
      exact sum_sdiff <| singleton_subset_iff.mpr <| G.mem_neighborFinset .. |>.mpr hw

end Tripartition
end ABC
end CaroWeiType
