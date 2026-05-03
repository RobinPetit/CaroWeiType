import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Operations
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim5
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim8

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

lemma Claim9 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {v : Fin n} (hBv : ABC.B v) (hdv : G.degree v = 3)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    (∃ w, G.Adj v w ∧ f G ABC w ≤ 1 / 6) → Objective G ABC := by
  intro ⟨w, hvw, hfw⟩
  obtain ⟨x, y, z, hNv, hzy, hyx⟩ := neighborFinset_eq_deg3 (f G ABC ·) hdv
  have h₁' : G.Adj v x :=
    G.mem_neighborFinset .. |>.mp <| by simp only [hNv, mem_insert, mem_singleton, true_or]
  have h₂' : G.Adj v y :=
    G.mem_neighborFinset .. |>.mp <| by simp only [hNv, mem_insert, mem_singleton, true_or, or_true]
  have h₃' : G.Adj v z :=
    G.mem_neighborFinset .. |>.mp <| by simp only [hNv, mem_insert, mem_singleton, or_true]
  have hneNv : x ≠ y ∧ x ≠ z ∧ y ≠ z := by
    rw [degree] at hdv
    exact pairwise_ne_of_triplet (hNv ▸ hdv)
  obtain ⟨H₁, H₂, H₃⟩ := hneNv
  if hℓ : ℓ G ABC x + ℓ G ABC y > 1 / 6 then
    exact Claim8 G ABC hG ih hBv hdv h₁'.symm h₂'.symm H₁ hyx hℓ
  else
    have hNv' : G.neighborFinset v = {z, x, y} := by grind
    refine objective_of_B3 hG hdv hBv hNv' ih ?_
    have := hNv ▸ G.mem_neighborFinset .. |>.mpr hvw
    have hfz : f G ABC z ≤ 1 / 6 := by grind
    simp only [not_lt] at hℓ
    calc _
      _ ≤ - 1 / 6 + ∑ u ∈ {x, y}, (f G ABC u -
        f ((fromEdgeSet (G.edgeSet ∪ {s(x, y)})).deleteIncidencesOf {z}) ((ABC \ {z}).promote v) u)
          := by
        linarith
      _ ≤ - 1 / 6 + ∑ u ∈ {x, y}, ℓ G ABC u := by
        simp only [add_le_add_iff_left]
        refine sum_le_sum ?_
        intro u hu
        refine Δf_le_ℓ_of_Δdeg_le_1 ?_ ?_
        · have : (fromEdgeSet (G.edgeSet ∪ {s(x, y)})).degree u ≤ G.degree u + 1 := by
            refine le_trans fromEdgeSet_union_degree_le' ?_
            simp only [add_le_add_iff_left]
            exact fromEdgeSet_singleton_degree_le_1
          refine le_trans deleteIncidencesOf_degree_le this
        · have huABC : u ∈ ABC := by
            refine ABC.mem_toFinset.mpr <| mem_def.mpr <| hG <| G.mem_support.mpr ⟨v, ?_⟩
            refine Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
          have huv : u ∉ ({v} : Finset _) :=
            notMem_singleton.mpr <| ne_of_mem_of_not_mem (by grind) (G.notMem_neighborFinset_self v)
          have huz : u ∉ ({z} : Finset _) := by grind [degree]
          rcases huABC with hAu | hBu | hCu
          · have hA' : ((ABC \ {z}).promote v).A u := Or.inl ⟨hAu, huz⟩
            simp only [hAu, hA', and_true, true_or]
          · have hB' : ((ABC \ {z}).promote v).B u := Or.inl ⟨⟨hBu, huz⟩, huv⟩
            simp only [hBu, hB', not_A_of_B, and_true, true_or, or_true]
          · have hC' : ((ABC \ {z}).promote v).C u := ⟨⟨hCu, huz⟩, huv⟩
            simp only [hCu, hC', not_A_of_C, not_B_of_C, and_true, or_true]
      _ ≤ 0 := by grind [degree]
    exact sum_nonneg fun _ _ ↦ γ_nonneg

lemma Corollary9 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {v : Fin n} (hBv : ABC.B v) (hdv : G.degree v = 3)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    (∃ w, G.Adj v w ∧ ABC.C w) → Objective G ABC := by
  intro ⟨w, hvw, hCw⟩
  if hdw : G.degree w ≤ 1 then
    refine Claim5 hG ih ⟨w, ?_, hdw⟩
    exact ABC.mem_toFinset.mpr <| hG <| G.mem_support |>.mpr ⟨v, hvw.symm⟩
  else
    refine Claim9 hG hBv hdv ih ⟨w, hvw, ?_⟩
    refine fC_le_16_if_2_le_deg hCw ?_
    simp only [not_le] at hdw
    exact Nat.succ_le_of_lt hdw

end Tripartition
end ABC
end CaroWeiType
