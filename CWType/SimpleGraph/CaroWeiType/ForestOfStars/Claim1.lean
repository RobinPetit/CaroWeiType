import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim0

import CWType.SimpleGraph.CaroWeiType.Calc

open SimpleGraph
open Finset

namespace CaroWeiType
namespace AB
namespace Bipartition

variable {V : Type} [Fintype V] [DecidableEq V]

lemma Claim1 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    {v : V} (hv : v ∈ AB) (hG : G.support ⊆ AB.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    f G AB v ≤ ∑ w ∈ G.neighborFinset v, γ G AB w → Objective G AB := by
  have hNv : G.neighborFinset v ⊆ AB.toFinset :=
    fun u hu ↦ hG <| G.mem_support.mpr ⟨v, Adj.symm <| G.mem_neighborFinset .. |>.mp <| hu⟩
  have hNv' : G.neighborFinset v ⊆ (AB \ {v}).toFinset := by
    rw [sdiff_toFinset]
    exact fun w hw ↦ mem_sdiff.mpr ⟨hNv hw, notMem_singleton_of_mem_neighborFinset hw⟩
  intro h
  have hvABC : {v} ∩ AB.toFinset ≠ ∅ := by
    rw [singleton_inter_of_mem <| AB.mem_toFinset.mp hv]
    exact singleton_ne_empty v
  refine Claim0 hvABC hG ?_ ih
  simp only [eval]
  refine le_of_eq_of_le (sum_sdiff_singleton_eval (AB.mem_toFinset.mp hv) hNv) ?_
  rw [AB.sdiff_toFinset]
  suffices ∑ w ∈ G.neighborFinset v,
      (f G AB w - f (G.deleteIncidencesOf {v}) (AB \ {v}) w) + f G AB v ≤ 0 by
    grind
  refine le_neg_iff_add_nonpos_left.mp (h.trans ?_)
  rw [← sum_neg_distrib _]
  refine sum_le_sum fun w hw ↦ ?_
  simp only [neg_sub]
  refine le_of_eq ?_
  suffices (G.deleteIncidencesOf {v}).degree w = G.degree w - 1 by
    have hw' : w ∉ ({v} : Finset _) := notMem_singleton_of_mem_neighborFinset hw
    have hw : w ∈ AB.toFinset :=
      mem_def.mpr <| hG <| G.mem_support.mpr ⟨v, Adj.symm <| mem_neighborFinset .. |>.mp hw⟩
    rcases AB.mem_toFinset.mpr hw with hA | hB
    · have hA' : (AB \ {v}).A w := ⟨hA, hw'⟩
      simp only [γ, f, hA, hA', ↓reduceDIte, this]
    · have hB' : (AB \ {v}).B w := ⟨hB, hw'⟩
      simp only [γ, f, hB, hB', not_A_of_B, ↓reduceDIte, this]
  refine Nat.eq_sub_of_add_eq <| Eq.symm ?_
  exact degree_deleteIncidencesOf_neighbor_singleton G <| mem_neighborFinset .. |>.mp hw

lemma Corollary1 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    {v w : V} (hG : G.support ⊆ AB.toFinset) (hw : G.Adj v w)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    f G AB v ≤ γ G AB w → Objective G AB := by
  let hv := AB.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨w, hw⟩
  intro h
  refine Claim1 hv hG ih <| le_trans h ?_
  calc γ G AB w
    _ = ∑ x ∈ {w}, γ G AB x := Eq.symm <| sum_singleton ..
    _ = 0 + ∑ x ∈ {w}, γ G AB x := by simp only [zero_add, sum_singleton]
    _ ≤ ∑ x ∈ G.neighborFinset v \ {w}, γ G AB x + ∑ x ∈ {w}, γ G AB x := by
      exact add_le_add_left (sum_nonneg (fun _ _ ↦ γ_nonneg)) _
    _ = ∑ x ∈ G.neighborFinset v, γ G AB x := by
      exact sum_sdiff <| singleton_subset_iff.mpr <| G.mem_neighborFinset .. |>.mpr hw

end Bipartition
end AB
end CaroWeiType
