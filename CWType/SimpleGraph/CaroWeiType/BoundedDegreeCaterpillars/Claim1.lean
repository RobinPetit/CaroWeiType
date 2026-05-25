import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim0

open SimpleGraph
open Finset

namespace CaroWeiType
namespace ABC
namespace Tripartition

variable {V : Type} [Fintype V] [DecidableEq V]

lemma Claim1 {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V} [ABC.Decidable]
    {v : V} (hv : v ∈ ABC) (hG : G.support ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    f G ABC v ≤ ∑ w ∈ G.neighborFinset v, γ G ABC w → Objective G ABC := by
  have hNv : G.neighborFinset v ⊆ ABC.toFinset :=
    fun u hu ↦ hG <| G.mem_support.mpr ⟨v, Adj.symm <| G.mem_neighborFinset .. |>.mp <| hu⟩
  have hNv' : G.neighborFinset v ⊆ (ABC \ {v}).toFinset := by
    rw [sdiff_toFinset]
    exact fun w hw ↦ mem_sdiff.mpr ⟨hNv hw, notMem_singleton_of_mem_neighborFinset hw⟩
  intro h
  have hvABC : {v} ∩ ABC.toFinset ≠ ∅ := by
    rw [singleton_inter_of_mem <| ABC.mem_toFinset.mp hv]
    exact singleton_ne_empty v
  refine Claim0 hvABC hG ?_ ih
  simp only [eval]
  refine le_of_eq_of_le (sum_sdiff_singleton_eval (ABC.mem_toFinset.mp hv) hNv) ?_
  rw [ABC.sdiff_toFinset]
  suffices ∑ w ∈ G.neighborFinset v,
      (f G ABC w - f (G.deleteIncidencesOf {v}) (ABC \ {v}) w) + f G ABC v ≤ 0 by
    grind
  refine le_neg_iff_add_nonpos_left.mp (h.trans ?_)
  rw [← sum_neg_distrib _]
  refine sum_le_sum fun w hw ↦ ?_
  simp only [neg_sub]
  refine le_of_eq ?_
  suffices (G.deleteIncidencesOf {v}).degree w = G.degree w - 1 by
    have hw' : w ∉ ({v} : Finset _) := notMem_singleton_of_mem_neighborFinset hw
    have hw : w ∈ ABC.toFinset :=
      mem_def.mpr <| hG <| G.mem_support.mpr ⟨v, Adj.symm <| mem_neighborFinset .. |>.mp hw⟩
    rcases ABC.mem_toFinset.mpr hw with hA | hB | hC
    · have hA' : (ABC \ {v}).A w := ⟨hA, hw'⟩
      simp only [γ, f, hA, hA', ↓reduceDIte, this]
    · have hB' : (ABC \ {v}).B w := ⟨hB, hw'⟩
      simp only [γ, f, hB, hB', not_A_of_B, ↓reduceDIte, this]
    · have hC' : (ABC \ {v}).C w := ⟨hC, hw'⟩
      simp only [γ, f, hC, hC', not_A_of_C, not_B_of_C, ↓reduceDIte, this]
  refine Nat.eq_sub_of_add_eq <| Eq.symm ?_
  exact degree_deleteIncidencesOf_neighbor_singleton G <| mem_neighborFinset .. |>.mp hw

lemma Corollary1 {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V} [ABC.Decidable]
    {v w : V} (hG : G.support ⊆ ABC.toFinset) (hw : G.Adj v w)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    f G ABC v ≤ γ G ABC w → Objective G ABC := by
  let hv := ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨w, hw⟩
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
