import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim1
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim3
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim5

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

lemma Claim6 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    (∃ v, G.degree v = 2 ∧ ¬ABC.A v) → Objective G ABC := by
  intro h
  if hwdeg : ∃ w ∈ ABC, G.degree w ≤ 1 then
    refine Claim5 hG ih hwdeg
  else
  simp only [not_exists, not_and, not_le] at hwdeg
  obtain ⟨v, hdegv, hAv⟩ := h
  obtain ⟨u, w, huw, hle⟩ := neighborFinset_eq_deg2' (f G ABC ·) hdegv
  have hABC {x} : 0 < G.degree x → x ∈ ABC := by
    intro h
    refine ABC.mem_toFinset.mpr <| hG <| G.degree_pos_iff_mem_support x |>.mp h
  have hv : v ∈ ABC := hABC <| Nat.lt_of_sub_eq_succ hdegv
  have hw : w ∈ ABC := by
    refine hABC <| (G.degree_pos_iff_exists_adj _).mpr ⟨v, ?_⟩
    refine Adj.symm <| G.mem_neighborFinset .. |>.mp ?_
    grind
  have hu : u ∈ ABC := by
    refine hABC <| (G.degree_pos_iff_exists_adj _).mpr ⟨v, ?_⟩
    refine Adj.symm <| G.mem_neighborFinset .. |>.mp ?_
    grind
  have hBCv : ABC.B v ∨ ABC.C v := by grind [ABC.mem_iff.mp hv]
  have sum_Nv_eq {φ : Fin n → ℝ} : ∑ x ∈ {u, w}, φ x = φ u + φ w := by
    refine sum_pair ?_
    intro heq; subst heq
    simp only [mem_singleton, insert_eq_of_mem] at huw
    have : #({u} : Finset _) = 2 := huw ▸ hdegv
    grind
  rcases hBCv with hB | hC
  · if h₁ : f G ABC w ≤ 1 / 2 then
      have hvw : G.Adj v w := G.mem_neighborFinset .. |>.mp (huw ▸ by simp)
      have hw : 0 < G.degree w := by
        refine (degree_pos_iff_exists_adj G w).mpr ⟨v, Adj.symm ?_⟩
        refine G.mem_neighborFinset .. |>.mp (huw ▸ by simp)
      exact Corollary1 hG hvw.symm ih (γB2 hB hdegv ▸ h₁)
    else
      simp only [not_le] at h₁
      obtain ⟨hAw, hdegw⟩ := A2_of_f_lt_12_of_2_le_deg (hwdeg _ hw) hw h₁
      obtain ⟨hAu, hdegu⟩ := by
        refine A2_of_f_lt_12_of_2_le_deg (hwdeg _ hu) hu ?_
        exact lt_of_lt_of_le h₁ hle
      refine Claim1 hv hG ih ?_
      rw [fB2 hB hdegv, huw, sum_Nv_eq, γA2 hAu hdegu, γA2 hAw hdegw]
      grind
  · if hf₂ : f G ABC u + f G ABC w ≤ 5 / 6 then
      refine Claim3 hv hG ih ?_
      rw [huw, sum_Nv_eq, fC2 hC hdegv]
      exact le_trans hf₂ (by grind)
    else
      have hfu : f G ABC u > 5 / 12 := by
        suffices 2 * f G ABC u > 5 / 6 by grind
        calc 2 * f G ABC u
          _ = f G ABC u + f G ABC u := two_mul _
          _ ≥ f G ABC u + f G ABC w := by simp only [ge_iff_le, add_le_add_iff_left, hle]
          _ > 5 / 6 := not_le.mp hf₂
      have hvu : G.Adj v u := G.mem_neighborFinset .. |>.mp (by grind)
      refine Corollary1 hG hvu ih ?_
      rw [fC2 hC hdegv]
      obtain ⟨hAu, hdegu⟩ := (A2_or_A3_of_f_lt_25_of_2_le_deg (hwdeg _ hu) hu (by grind))
      rcases hdegu with hu | hu <;> simp only [γA2 hAu, γA3 hAu, hu, le_refl]

end Tripartition
end ABC
end CaroWeiType
