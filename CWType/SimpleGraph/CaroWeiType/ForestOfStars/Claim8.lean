import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim2
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim6
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Lemmas

open SimpleGraph
open Finset

namespace CaroWeiType
namespace AB
namespace Bipartition

variable {V : Type} [Fintype V] [DecidableEq V]

lemma Claim8 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (hne : u ≠ w)
    (hdu : G.degree u = 2) (hdv : G.degree v = 2) (hdw : G.degree w = 2)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  cases Claim6' hG ih with
  | inr h => exact h
  | inl h => ?_
  have H {z : V} (hz : z ∈ AB.toFinset) : AB.A z := by rcases h _ hz with h | h <;> exact h.1
  have H' {z : V} (hAz : AB.A z) : z ∈ AB.toFinset := AB.mem_toFinset.mp <| Or.inl hAz
  have hAu : AB.A u := H <| hG <| G.mem_support.mpr ⟨v, huv⟩
  have hAv : AB.A v := H <| hG <| G.mem_support.mpr ⟨w, hvw⟩
  have hAw : AB.A w := H <| hG <| G.mem_support.mpr ⟨v, hvw.symm⟩
  have hNv : G.neighborFinset v = {u, w} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [card_pair hne, ← degree, hdv]
  if huw : G.Adj u w then
    refine Corollary2 {u, v} pair_nonempty ?_ (respects_pair hAu) hG ih InducesForestOfStars_pair ?_
    · intro z hz
      simp only [mem_insert, mem_singleton] at hz
      grind
    · rw [card_pair huv.ne, Nat.cast_two]
      suffices G.closed_neighborFinset_of_Finset {u, v} = {u, v, w} by
        rw [this]
        suffices 2 ≥ f G AB u + f G AB v + f G AB w by
          refine le_of_eq_of_le ?_ this
          grind [Adj.ne]
        rw [fA2 hAu hdu, fA2 hAv hdv, fA2 hAw hdw]
        linarith
      have hNu : G.neighborFinset u = {v, w} := by
        refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
        · grind [mem_neighborFinset]
        · rw [card_pair hvw.ne, ← degree, hdu]
      rw [closed_neighborFinset_of_pair_eq, hNu, hNv]
      grind
  else
    obtain ⟨x, hx, hvnex⟩ := Finset_get_other (le_of_eq <| hdu.symm) v
    obtain ⟨y, hy, hvney⟩ := Finset_get_other (le_of_eq <| hdw.symm) v
    have hNu : G.neighborFinset u = {x, v} := by
      refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
      · grind [mem_neighborFinset, Adj.symm]
      · rw [card_pair hvnex.symm, ← degree, hdu]
    have hNw : G.neighborFinset w = {v, y} := by
      refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
      · grind [mem_neighborFinset, Adj.symm]
      · rw [card_pair hvney, ← degree, hdw]
    if hxeqy : x = y then
      refine Corollary2 {u, v, w} ?_ ?_ ?_ hG ih ?_ ?_
      · exact insert_nonempty ..
      · intro z hz
        simp only [mem_insert, mem_singleton] at hz
        grind
      · intro z hz hBz
        grind [not_B_of_A]
      · exact InducesForestOfStars_triplet huv hvw huw
      · rw [card_triplet' huv.ne hne hvw.ne, Nat.cast_three]
        suffices G.closed_neighborFinset_of_Finset {u, v, w} = {u, v, w, x} by
          rw [this]
          suffices 3 ≥ f G AB u + f G AB v + f G AB w + f G AB x by
            refine le_of_eq_of_le ?_ this
            refine sum_quadruplet ?_ ?_ ?_ ?_ ?_ ?_ <;> grind [Adj.ne, ne_of_mem_neighborFinset]
          rw [fA2 hAu hdu, fA2 hAv hdv, fA2 hAw hdw]
          suffices f G AB x ≤ 3 / 5 by linarith
          have hx : x ∈ AB.toFinset :=
            hG <| G.mem_support.mpr ⟨u, Adj.symm <| mem_neighborFinset .. |>.mp hx⟩
          rcases h _ hx with ⟨hAx, hdx⟩ | ⟨hAx, hdx⟩
          · simp only [fA2 hAx hdx, le_refl]
          · simp only [fA3 hAx hdx]
            linarith
        rw [closed_neighborFinset_of_triplet_eq, hNu, hNv, hNw]
        have : {u, w} ∪ {x, v} ∪ {u, v, w} = ({u, v, w, x} : Finset _) := by grind
        grind
    else
      refine Corollary2 {u, v, w} ?_ ?_ ?_ hG ih ?_ ?_
      · exact insert_nonempty u {v, w}
      · grind
      · intro z hz hBz
        grind [not_B_of_A]
      · exact InducesForestOfStars_triplet huv hvw huw
      · rw [card_triplet' huv.ne hne hvw.ne, Nat.cast_three]
        suffices G.closed_neighborFinset_of_Finset {u, v, w} = {x, u, v, w, y} by
          rw [this, ge_iff_le]
          have : ∑ v ∈ {x, u, v, w, y}, f G AB v ≤ ∑ v ∈ {x, u, v, w, y}, 3 / 5 := by
            refine sum_le_sum fun z hz ↦ ?_
            have hz : z ∈ AB.toFinset := by
              have : z ∈ ({x, y} : Finset _) ∨ z ∈ ({u, v, w} : Finset _) := by
                grind
              rcases this with hz | hz
              · simp only [mem_insert, mem_singleton] at hz
                rcases hz with hz | hz
                · refine hG <| G.mem_support.mpr ⟨u, hz ▸ ?_⟩
                  exact Adj.symm <| mem_neighborFinset .. |>.mp hx
                · refine hG <| G.mem_support.mpr ⟨w, hz ▸ ?_⟩
                  exact Adj.symm <| mem_neighborFinset .. |>.mp hy
              · grind
            rcases h _ hz with ⟨hAz, hdz⟩ | ⟨hAz, hdz⟩
            · simp only [fA2 hAz hdz, le_refl]
            · simp only [fA3 hAz hdz]
              linarith
          refine le_trans this ?_
          simp only [sum_const']
          suffices #{x, u, v, w, y} ≤ 5 by
            clear * - this
            refine le_trans ?_ (?_ : (5 : ℕ) * (3 / (5 : ℝ)) ≤ 3)
            · simp only [Nat.cast_ofNat, Nat.ofNat_pos, div_pos_iff_of_pos_left,
                mul_le_mul_iff_left₀, Nat.cast_le_ofNat, this]
            · grind
          grind
        rw [closed_neighborFinset_of_triplet_eq, hNu, hNv, hNw]
        grind

end Bipartition
end AB
end CaroWeiType
