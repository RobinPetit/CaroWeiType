import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.ABC
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claims

namespace CaroWeiType
namespace ABC

open Tripartition
open Finset
open SimpleGraph

private lemma exists_argmin {α : Type*} {s : Finset α} (hs : s.Nonempty) {f : α → ℝ} :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y := by
  classical
  induction s using Finset.induction_on_min_value f with
  | h0 => simp only [Finset.not_nonempty_empty] at hs
  | step a s' ha hmin ih => ?_
  refine ⟨a, mem_insert_self .., ?_⟩
  intro y hy
  simp only [mem_insert] at hy
  rcases hy with hy | hy
  · simp only [hy, le_refl]
  · exact hmin _ hy

theorem ABCLemma {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    (hG : G.support.toFinset ⊆ ABC.toFinset) :
    Objective G ABC := by
  induction hcard : ABC.card using Nat.strong_induction_on generalizing G ABC with | h k ih
  if hk : k = 0 then
    refine ⟨∅, ?_, ?_, ?_, ?_⟩ <;>
    simp [respects, card_eq_zero.mp <| hk ▸ hcard, InducesForest, IsDegenerateSet]
  else
  have ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC' :=
    fun G' _ ABC' hsupp' hcardABC' ↦ ih ABC'.card (hcard ▸ hcardABC') G' ABC' hsupp' rfl
  let W := {v | v ∈ ABC.toFinset ∧ 0 < γ G ABC v}
  if hW : W = ∅ then
    have H : ∀ v ∈ ABC.toFinset, γ G ABC v = 0 := by
      intro v hv
      rcases lt_or_eq_of_le <| @γ_nonneg _ G _ ABC v with hγ | hγ
      · have hvW : v ∈ W := by simp only [Set.mem_setOf_eq, W, hv, hγ, true_and]
        have : W.Nonempty := Set.nonempty_of_mem hvW
        grind
      · exact hγ.symm
    have : ABC.toFinset.card = k := by
      rw [← hcard]
      rfl
    have : ABC.toFinset ≠ ∅ :=
      not_iff_not.mpr card_eq_zero |>.mp <| ne_of_eq_of_ne hcard hk
    if hv : ∃ v, ABC.C v then
      obtain ⟨v, hv⟩ := hv
      if hdv : G.degree v ≤ 1 then
        exact Claim5 hG ih ⟨v, Or.inr <| Or.inr hv, hdv⟩
      else
        simp only [not_le] at hdv
        have _ : γ G ABC v = 0 := H _ (ABC.coe_mem_toFinset.mp <| Or.inr <| Or.inr hv)
        let hobj := γ_eq_0_iff (Or.inr <| Or.inr hv) hdv |>.mp
          <| H _ (ABC.coe_mem_toFinset.mp <| Or.inr <| Or.inr hv)
        simp only [hv, and_true, not_B_of_C, and_false, false_or] at hobj
        rcases hobj with hdv | hdv
        · obtain ⟨w, hvw⟩ := G.degree_pos_iff_exists_adj v |>.mp <| by lia
          if hdw : G.degree w ≤ 1 then
            refine Claim5 hG ih ⟨w, ?_, hdw⟩
            refine ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr ?_
            exact G.degree_pos_iff_mem_support _ |>.mp <| Adj.degree_pos_left hvw.symm
          else
            simp only [not_le] at hdw
            have hw : w ∈ ABC := by
              refine ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr ?_
              exact (degree_pos_iff_mem_support G w).mp <| Adj.degree_pos_left hvw.symm
            have hγw : γ G ABC w = 0 := H _ <| ABC.coe_mem_toFinset.mp hw
            let hobj := γ_eq_0_iff hw hdw |>.mp hγw
            rcases hobj with ⟨hdw, hw⟩ | ⟨hdw, hw⟩ | ⟨hdw, hw⟩
            · exact Corollary9 hG hw hdw ih ⟨v, hvw.symm, hv⟩
            · exact Claim13 hG hvw hv hdv hw hdw ih
            · exact Claim6 hG ih ⟨w, hdw, not_A_of_C hw⟩
        · exact Claim6 hG ih ⟨v, hdv, not_A_of_C hv⟩
    else
      have hW : Objective G ABC ∨ ∀ x ∈ ABC, ABC.B x ∧ G.degree x = 3 := by
        suffices ∀ x ∈ ABC, Objective G ABC ∨ (ABC.B x ∧ G.degree x = 3) by grind
        intro x hx
        if hdx : G.degree x ≤ 1 then
          exact Or.inl <| Claim5 hG ih ⟨x, hx, hdx⟩
        else
          simp only [not_le] at hdx
          let hobj := γ_eq_0_iff hx hdx |>.mp <| H _ <| ABC.coe_mem_toFinset.mp hx
          grind
      rcases hW with hW | hW
      · exact hW
      · if ABC.toFinset = ∅ then
          grind only
        else
          obtain ⟨v, hv⟩ := nonempty_def.mp <| nonempty_iff_ne_empty.mpr this
          obtain ⟨hBv, hdv⟩ := hW v (ABC.coe_mem_toFinset.mpr hv)
          obtain ⟨x, y, z, H, _⟩ := neighborFinset_eq_deg3' (G.degree ·) hdv
          have : (ABC.B x ∧ G.degree x = 3) ∧ (ABC.B y ∧ G.degree y = 3) := by
            refine ⟨?_, ?_⟩ <;> {
              refine hW _ <| ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr ?_
              refine G.mem_support.mpr ⟨v, Adj.symm <| G.mem_neighborFinset .. |>.mp ?_⟩
              simp only [H, mem_insert, mem_singleton, true_or, or_true]
            }
          obtain ⟨⟨hBx, hdx⟩, ⟨hBy, hdy⟩⟩ := this
          refine Claim10 hG hBv hdv ih ⟨x, y, by grind [degree], ?_, ?_, hBx, hBy, hdx, hdy⟩
          · refine G.mem_neighborFinset .. |>.mp
              <| by simp only [H, mem_insert, mem_singleton, true_or]
          · refine G.mem_neighborFinset .. |>.mp
              <| by simp only [H, mem_insert, mem_singleton, true_or, or_true]
  else
    sorry

end ABC
end CaroWeiType
