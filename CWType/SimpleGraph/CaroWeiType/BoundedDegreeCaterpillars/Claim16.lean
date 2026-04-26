import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim1
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim6
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim9
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim13
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim15

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

lemma Claim16 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) {û v : Fin n} (hû : IsVstar G ABC û) (hCv : ABC.C v)
    (hdv : G.degree v = 3)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨
      (¬(ABC.A û ∧ G.degree û = 4) ∧
        ¬(ABC.A û ∧ G.degree û = 5) ∧ ¬(ABC.B û ∧ G.degree û = 4)) := by
  obtain ⟨x, y, z, hxyz, hfzy, hfyx⟩ := neighborFinset_eq_deg3 (γ G ABC ·) hdv
  if hγz : γ G ABC z = 0 then
    have hzv : z ∈ G.neighborFinset v := by simp only [hxyz, mem_insert, mem_singleton, or_true]
    have hdz : 1 ≤ G.degree z := one_le_degree_of_mem_neighborFinset' hzv
    have hzABC : z ∈ ABC :=
      ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr
        <| G.degree_pos_iff_mem_support _ |>.mp hdz
    refine Or.inl ?_
    have hzv : G.Adj z v := Adj.symm <| G.mem_neighborFinset .. |>.mp hzv
    rcases γ_eq_0_iff hzABC hdz |>.mp hγz with ⟨hdz, hz⟩ | ⟨hdz, hz⟩ | ⟨hdz, hz⟩
    · exact Corollary9 hG hz hdz ih ⟨v, hzv, hCv⟩
    · exact Claim13 hG hzv hz hdz hCv hdv ih
    · exact Claim6 hG ih ⟨z, hdz, not_A_of_C hz⟩
  else if hγû : 1 / 18 ≤ γ G ABC û then
    refine Or.inl <| Claim1 (Or.inr <| Or.inr hCv) hG ih ?_
    calc f G ABC v
      _ ≤ γ G ABC û + γ G ABC û + γ G ABC û := by linarith [fC3 hCv hdv]
      _ ≤ γ G ABC x + γ G ABC y + γ G ABC z := by
        have hw : ∀ w ∈ ({x, y, z} : Finset _), γ G ABC û ≤ γ G ABC w := by
          intro w hw
          refine γ_vstar_le_γ hû ?_ (by grind)
          refine ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr ?_
          rw [← hxyz] at hw
          exact (degree_pos_iff_mem_support G w).mp <| one_le_degree_of_mem_neighborFinset' hw
        refine add_le_add (add_le_add ?_ ?_) ?_ <;> {
          refine hw _ ?_
          simp only [mem_insert, mem_singleton, or_true, true_or]
        }
    grind [degree]
  else
    simp only [not_le] at hγû
    if h : (ABC.A û ∧ G.degree û = 4) ∨ (ABC.A û ∧ G.degree û = 5) ∨ (ABC.B û ∧ G.degree û = 4) then
      rcases h with h | h | h
      · rw [γA4 h.1 h.2] at hγû
        linarith
      · rw [γA5 h.1 h.2] at hγû
        linarith
      · rw [γB4 h.1 h.2] at hγû
        linarith
    else
      grind

lemma Corollary16 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) {û v : Fin n} (hû : IsVstar G ABC û) (hCv : ABC.C v)
    (hdv : G.degree v = 3)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨ (f G ABC û ≤ 2 / 7 ∧ γ G ABC û ≤ 1 / 21) := by
  match Claim15 hG hû ih, Claim16 hG hû hCv hdv ih with
  | Or.inl h, _ => exact Or.inl h
  | _, Or.inl h => exact Or.inl h
  | Or.inr hdû, Or.inr h => ?_
  rcases ABC.coe_mem_toFinset.mpr hû.1.1 with hAû | hBû | hCû
  · simp only [not_B_of_A, hAû, true_and, false_and, not_false_eq_true, and_true] at h
    have hdû : 6 ≤ G.degree û := by lia
    refine Or.inr ⟨?_, ?_⟩
    · refine le_trans f_le_fA <| le_of_le_of_eq (fA_decreasing hdû) (by lia)
    · refine le_trans (γ_le_γA_of_four_le_deg (by lia)) ?_
      have H : 3 ≤ G.degree û := by lia
      exact le_of_le_of_eq (γA_decreasing_of_three_le_degree hdû (by linarith)) (by grind)
  · have hdû : 5 ≤ G.degree û := by lia
    refine Or.inr ⟨?_, ?_⟩
    · simp only [f, hBû, not_A_of_B, ↓reduceDIte]
      refine le_trans (fB_decreasing hdû) ?_
      grind
    · simp only [γ, hBû, not_A_of_B, ↓reduceDIte]
      refine le_trans (γB_decreasing_of_four_le_degree hdû (by linarith)) (by grind)
  · refine Or.inr ⟨?_, ?_⟩
    · simp only [f, hCû, not_A_of_C, not_B_of_C, ↓reduceDIte]
      refine le_trans (fC_decreasing hdû) ?_
      grind
    · simp only [γ, hCû, not_A_of_C, not_B_of_C, ↓reduceDIte]
      refine le_trans (γC_decreasing_of_four_le_degree hdû (by linarith)) (by grind)

end Tripartition
end ABC
end CaroWeiType
