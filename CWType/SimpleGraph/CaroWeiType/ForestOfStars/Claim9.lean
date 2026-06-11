import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim2
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim6
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim7
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim8
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Lemmas

open SimpleGraph
open Finset

namespace CaroWeiType
namespace AB
namespace Bipartition

variable {V : Type} [Fintype V] [DecidableEq V]

private lemma _ok_if_adj_xy {G : SimpleGraph V} [DecidableRel G.Adj]
    {AB : Bipartition V} [AB.Decidable] (hG : G.support ⊆ AB.toFinset)
    {u v x y : V} (hxu : G.Adj x u) (huv : G.Adj u v) (hvy : G.Adj v y) (hxy : G.Adj x y)
    (hAu : AB.A u) (hAv : AB.A v) (hAy : AB.A y) (hdy : G.degree y = 3)
    (hdu : G.degree u = 2) (hdv : G.degree v = 2) (hvnex : v ≠ x) (huney : u ≠ y)
    (h : ∀ v ∈ AB.toFinset, AB.A v ∧ G.degree v = 2 ∨ AB.A v ∧ G.degree v = 3)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  have hu : u ∈ AB.toFinset := hG <| G.mem_support.mpr ⟨v, huv⟩
  have hv : v ∈ AB.toFinset := hG <| G.mem_support.mpr ⟨u, huv.symm⟩
  have hx' : x ∈ AB.toFinset := hG <| G.mem_support.mpr ⟨_, hxy⟩
  have hy' : y ∈ AB.toFinset := hG <| G.mem_support.mpr ⟨_, hxy.symm⟩
  have hNu : G.neighborFinset u = {x, v} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [card_pair hvnex.symm, ← degree, hdu]
  have hNv : G.neighborFinset v = {u, y} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [card_pair huney, ← degree, hdv]
  refine Corollary2 {u, v, y} ?_ ?_ ?_ hG ih ?_ ?_
  · exact insert_nonempty u {v, y}
  · grind
  · intro z hz hBz
    grind [not_B_of_A]
  · refine InducesForestOfStars_triplet huv hvy ?_
    refine not_iff_not.mpr (mem_neighborFinset ..) |>.mp ?_
    suffices G.neighborFinset u = {x, v} by grind [Adj.ne]
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [card_pair hvnex.symm, ← degree, hdu]
  · obtain ⟨z, hz, hxnez, hvnez⟩ := Finset_get_other_other (le_of_eq <| hdy.symm) x v
    have hNy : G.neighborFinset y = {v, x, z} := by
      refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
      · grind [mem_neighborFinset, Adj.symm]
      · rw [card_triplet' hvnex hvnez hxnez, ← degree, hdy]
    rw [card_triplet' huv.ne huney hvy.ne, Nat.cast_three]
    suffices G.closed_neighborFinset_of_Finset {u, v, y} = {u, v, x, y, z} by
      rw [this, ge_iff_le]; clear this
      have : ∑ v ∈ {u, v, x, y, z}, f G AB v ≤ ∑ v ∈ {u, v, x, y, z}, 3 / 5 := by
        refine sum_le_sum fun w hw ↦ ?_
        have hz : w ∈ AB.toFinset := by
          have : w ∈ ({u, v} : Finset _) ∨ w ∈ ({x, y, z} : Finset _) := by
            grind
          rcases this with hw | hw
          · grind
          · simp only [mem_insert, mem_singleton] at hw
            rcases hw with hw | hw | hw
            · exact hG <| G.mem_support.mpr ⟨u, hw ▸ hxu⟩
            · exact hG <| G.mem_support.mpr ⟨v, hw ▸ hvy.symm⟩
            · refine hG <| G.mem_support.mpr ⟨y, ?_⟩
              exact Adj.symm <| mem_neighborFinset .. |>.mp <| hw ▸ hz
        rcases h _ hz with ⟨hAz, hdz⟩ | ⟨hAz, hdz⟩
        · simp only [fA2 hAz hdz, le_refl]
        · simp only [fA3 hAz hdz]
          linarith
      refine le_trans this ?_
      simp only [sum_const']
      suffices #{u, v, x, y, z} ≤ 5 by
        clear * - this
        refine le_trans ?_ (?_ : (5 : ℕ) * (3 / (5 : ℝ)) ≤ 3)
        · simp only [Nat.cast_ofNat, Nat.ofNat_pos, div_pos_iff_of_pos_left,
            mul_le_mul_iff_left₀, Nat.cast_le_ofNat, this]
        · grind
      grind
    rw [closed_neighborFinset_of_triplet_eq, hNu, hNv, hNy]
    have : {v, x, z} ∪ {u, v, y} = ({u, v, x, y, z} : Finset _) := by
      grind
    grind

lemma Claim9 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {u v : V} (huv : G.Adj u v)
    (hdu : G.degree u = 2) (hdv : G.degree v = 2)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  match Claim6' hG ih, Corollary4 hG ih with
  | Or.inr h, _ => exact h
  | _, Or.inr h' => exact h'
  | Or.inl h, Or.inl h' => ?_
  have hu : u ∈ AB.toFinset := hG <| G.mem_support.mpr ⟨v, huv⟩
  have hv : v ∈ AB.toFinset := hG <| G.mem_support.mpr ⟨u, huv.symm⟩
  obtain ⟨x, hx, hvnex⟩ := Finset_get_other (le_of_eq <| hdu.symm) v
  obtain ⟨y, hy, huney⟩ := Finset_get_other (le_of_eq <| hdv.symm) u
  have hx' : x ∈ AB.toFinset :=
    hG <| G.mem_support.mpr ⟨_, Adj.symm <| mem_neighborFinset .. |>.mp hx⟩
  have hy' : y ∈ AB.toFinset :=
    hG <| G.mem_support.mpr ⟨_, Adj.symm <| mem_neighborFinset .. |>.mp hy⟩
  have hvy := G.mem_neighborFinset .. |>.mp hy
  have hux := G.mem_neighborFinset .. |>.mp hx
  have hNu : G.neighborFinset u = {x, v} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset]
    · rw [card_pair hvnex.symm, ← degree, hdu]
  have hNv : G.neighborFinset v = {u, y} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [card_pair huney, ← degree, hdv]
  if hxeqy : x = y then
    subst hxeqy
    rcases h _ hx' with ⟨hAx, hdx⟩ | ⟨hAx, hdx⟩
    · exact Claim8 hG huv hvy huney hdu hdv hdx ih
    · exact Claim7 hG hvy hux.symm huv.ne' hdx hdv hdu ih
  else
    match h _ hx', h _ hy' with
    | Or.inl ⟨hAx, hdx⟩, _ => exact Claim8 hG huv.symm hux hvnex hdv hdu hdx ih
    | _, Or.inl ⟨hAy, hdy⟩ => exact Claim8 hG huv hvy huney hdu hdv hdy ih
    | Or.inr ⟨hAx, hdx⟩, Or.inr ⟨hAy, hdy⟩ => ?_
    have H {z : V} (hz : z ∈ G.support) : AB.A z := by
      rcases h _ (hG hz) with ⟨hA, _⟩ | ⟨hA, _⟩ <;> exact hA
    have hAu : AB.A u := H <| G.mem_support.mpr ⟨v, huv⟩
    have hAv : AB.A v := H <| G.mem_support.mpr ⟨u, huv.symm⟩
    if hxy : G.Adj x y then
      exact _ok_if_adj_xy hG hux.symm huv hvy hxy hAu hAv hAy hdy hdu hdv hvnex huney h ih
    else
      refine Claim2' {u, v} pair_nonempty (by grind) ?_ hG ih InducesForestOfStars_pair ?_
      · exact respects_pair (H <| G.mem_support.mpr ⟨_, huv⟩)
      · rw [card_pair huv.ne, Nat.cast_two, closed_neighborFinset_of_pair_eq, hNu, hNv]
        have : {x, v} ∪ {u, y} ∪ {u, v} = ({u, v, x, y} : Finset _) := by grind
        rw [this]; clear this
        have : ∑ v ∈ {u, v, x, y}, f G AB v = 11 / 5 := by
          suffices f G AB u + f G AB v + f G AB x + f G AB y = 11 / 5 by
            grind
          simp only [fA2 hAu hdu, fA2 hAv hdv, fA3 hAx hdx, fA3 hAy hdy]
          linarith
        suffices 1 / 5 ≤ ∑ w ∈ G.N2_of_Finset {u, v}, γ G AB w by
          linarith
        suffices ∑ w ∈ G.N2_of_Finset {u, v}, 1 / 10 ≤ ∑ w ∈ G.N2_of_Finset {u, v}, γ G AB w by
          refine le_trans ?_ this
          suffices 2 ≤ #(G.N2_of_Finset {u, v}) by
            have : 1 / (5 : ℝ) ≤ (2 : ℕ) * (1  / 10) := by grind
            refine le_trans this ?_
            clear this
            simp only [Nat.cast_ofNat, one_div, sum_const', inv_pos, Nat.ofNat_pos, this,
              mul_le_mul_iff_left₀, Nat.ofNat_le_cast]
          obtain ⟨x', hx', hunex'⟩ := Finset_get_other (by grind : 2 ≤ G.degree x) u
          obtain ⟨x'', hx'', hunex'', hx'nex''⟩ :=
            Finset_get_other_other (le_of_eq <| hdx.symm) u x'
          have : G.neighborFinset x = {u, x', x''} := by
            refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
            · grind [mem_neighborFinset, Adj.symm]
            · rw [card_triplet' hunex' hunex'' hx'nex'', ← degree, hdx]
          rw [← card_pair hx'nex'']
          refine card_le_card ?_
          intro w hw
          refine mem_N2_of_Finset_iff.mpr ⟨?_, ⟨?_, ?_⟩⟩
          · have : ¬G.Adj v x := by
              rw [← mem_neighborFinset, hNv]
              grind
            grind [mem_neighborFinset, Adj.symm]
          · suffices w ∉ G.neighborFinset u ∪ G.neighborFinset v by
              grind [mem_neighborFinset, Adj.symm]
            rw [hNu, hNv]
            grind [ne_of_mem_neighborFinset, Adj.symm, mem_neighborFinset]
          · refine ⟨u, mem_insert_self .., x, ?_, ?_, Adj.symm <| mem_neighborFinset .. |>.mp hx⟩
            · grind [ne_of_mem_neighborFinset]
            · grind [mem_neighborFinset, Adj.symm]
        refine sum_le_sum fun w hw ↦ ?_
        refine h' _ ?_ |>.2.2.1
        obtain ⟨w', _, _, _, H, _⟩ := mem_N2_of_Finset_iff'.mp hw |>.2
        refine hG <| G.mem_support.mpr ⟨_, H⟩

end Bipartition
end AB
end CaroWeiType
