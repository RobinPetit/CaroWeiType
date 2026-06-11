import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim4
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Lemmas

open SimpleGraph
open Finset

namespace CaroWeiType
namespace AB
namespace Bipartition

variable {V : Type} [Fintype V] [DecidableEq V]

lemma Claim5 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {v w : V} (hBv : AB.B v) (hBw : AB.B w) (hvw : G.Adj v w)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  cases Claim4 hG ih with
  | inr h => exact h
  | inl h => ?_
  have hdv := h _ |>.2 hBv
  have hdw := h _ |>.2 hBw
  obtain ⟨x, hx, hxnew⟩ := Finset_get_other (le_of_eq hdv.symm) w
  have hNv : G.neighborFinset v = {w, x} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy
      exact hy.elim (mem_neighborFinset .. |>.mpr <| · ▸ hvw) (· ▸ hx)
    · rw [card_pair hxnew, ← degree, hdv]
  if hγx : 1 / 6 ≤ γ G AB x then
    refine Claim1 (Or.inr hBv) hG ih ?_
    suffices f G AB v ≤ γ G AB w + γ G AB x by
      exact le_of_le_of_eq this (by grind)
    rw [fB2 hBv hdv, γB2 hBw hdw]
    linarith
  else
    have hA3x : AB.A x ∧ G.degree x = 3 := by
      have := h x
      have hABx : x ∈ AB := by
        refine AB.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨v, ?_⟩
        exact Adj.symm <| mem_neighborFinset .. |>.mp hx
      rcases hABx with hAx | hBx
      · refine ⟨hAx, ?_⟩
        rcases this.1 hAx with hdx | hdx
        · simp only [not_le, γA2 hAx hdx] at hγx
          linarith
        · exact hdx
      · have hdx := this.2 hBx
        simp only [not_le, γB2 hBx hdx] at hγx
        linarith
    obtain ⟨hAx, hdx⟩ := hA3x
    if hxw : G.Adj x w then
      have hdx' : 3 ≤ #(G.neighborFinset x) := hdx ▸ le_refl _
      obtain ⟨z, hz, hvnez, hwnez⟩ := Finset_get_other_other hdx' v w
      have hNx : G.neighborFinset x = {v, w, z} := by
        refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
        · intro u hu
          grind [Adj.symm, mem_neighborFinset]
        · rw [← degree, hdx]
          grind [Adj.ne]
      cases Claim4' hG ih with
      | inr h => exact h
      | inl h => ?_
      refine Corollary2 {v, x} pair_nonempty ?_ ?_ hG ih ?_ ?_
      · intro u hu
        simp only [mem_insert, mem_singleton] at hu
        rcases hu with hu | hu
        · exact AB.mem_toFinset.mp <| Or.inr (hu ▸ hBv)
        · exact hG <| G.mem_support.mpr ⟨v, Adj.symm <| mem_neighborFinset .. |>.mp <| hu ▸ hx⟩
      · exact respects_pair' hAx
      · exact InducesForestOfStars_pair
      · have : G.closed_neighborFinset_of_Finset {v, x} = {v, w, x, z} := by
          simp only [closed_neighborFinset_of_pair_eq, hNv, hNx]
          grind
        rw [this, card_pair <| Ne.symm <| ne_of_mem_neighborFinset hx, Nat.cast_two]
        suffices 2 ≥ f G AB v + f G AB w + f G AB x + f G AB z by
          refine le_of_eq_of_le ?_ this
          refine sum_quadruplet ?_ ?_ ?_ ?_ ?_ (Ne.symm <| ne_of_mem_neighborFinset hz) <;> grind
        simp only [fB2 hBv hdv, fB2 hBw hdw, fA3 hAx hdx]
        suffices f G AB z ≤ 5 / 6 by linarith
        have hABz : z ∈ AB.toFinset := by
          refine hG <| G.mem_support.mpr ⟨x, Adj.symm <| mem_neighborFinset .. |>.mp <| hNx ▸ ?_⟩
          grind
        rcases h _ hABz with ⟨hAz, hdz⟩ | ⟨hAz, hdz⟩ | ⟨hBz, hdz⟩
        · simp only [fA2 hAz hdz]
          linarith
        · simp only [fA3 hAz hdz]
          linarith
        · simp only [fB2 hBz hdz]
          linarith
    else
      cases Claim4' hG ih with
      | inr h => exact h
      | inl h => ?_
      refine Claim2' _ (singleton_nonempty v) ?_ ?_ hG ih ?_ ?_
      · exact singleton_subset_iff.mpr <| AB.mem_toFinset.mp <| Or.inr hBv
      · exact respects_singleton
      · exact InducesForestOfStars_singleton
      · rw [card_singleton, Nat.cast_one, closed_neighborFinset_of_singleton_eq, hNv]
        suffices 1 ≥ f G AB w + f G AB x + f G AB v - ∑ w ∈ G.N2_of_Finset {v}, γ G AB w by
          grind [ne_of_mem_neighborFinset]
        suffices H : 2 ≤ #(G.N2_of_Finset {v}) by
          simp only [fB2 hBv hdv, fB2 hBw hdw, fA3 hAx hdx]
          suffices 1 / 6 ≤ ∑ w ∈ G.N2_of_Finset {v}, γ G AB w by linarith
          suffices ∑ w ∈ G.N2_of_Finset {v}, (1 : ℝ) / 10 ≤ ∑ w ∈ G.N2_of_Finset {v}, γ G AB w by
            refine le_trans ?_ this
            simp only [sum_const']
            have : (2 : ℝ) ≤ #(G.N2_of_Finset {v}) := Nat.ofNat_le_cast.mpr H
            linarith
          refine sum_le_sum fun w hw ↦ ?_
          have hw' : w ∈ AB.toFinset := by
            obtain ⟨_, _, u, _, hwu, _⟩ := mem_N2_of_Finset_iff.mp hw |>.2.2
            exact hG <| G.mem_support.mpr ⟨_, hwu⟩
          rcases h _ hw' with ⟨hAw, hdw⟩ | ⟨hAw, hdw⟩ | ⟨hBw, hdw⟩ <;> grind [γA2, γA3, γB2]
        suffices (G.neighborFinset x \ {v}) ⊆ G.N2_of_Finset {v} by
          have H : #(G.neighborFinset x \ {v}) = 2 := by
            rw [card_sdiff, ← degree, hdx, singleton_inter_of_mem <| mem_neighborFinset_symm hx,
              card_singleton]
          refine H ▸ card_le_card this
        intro u hu
        simp only [mem_sdiff, mem_neighborFinset, mem_singleton] at hu
        refine mem_N2_of_Finset_iff.mpr ⟨?_, ?_, ?_⟩
        · exact notMem_singleton.mpr hu.2
        · simp only [mem_singleton, forall_eq]
          intro huv
          have huNv := hNv ▸ mem_neighborFinset .. |>.mpr huv.symm
          simp only [mem_insert, mem_singleton, hu.1.ne', or_false] at huNv
          exact hxw (huNv ▸ hu.1)
        · simp only [mem_singleton, exists_eq_left]
          refine ⟨x, ne_of_mem_neighborFinset hx, hu.1.symm, ?_⟩
          exact Adj.symm <| mem_neighborFinset .. |>.mp hx

end Bipartition
end AB
end CaroWeiType
