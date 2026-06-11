import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim6
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim9
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim10
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Lemmas

open SimpleGraph
open Finset

namespace CaroWeiType
namespace AB
namespace Bipartition

variable {V : Type} [Fintype V] [DecidableEq V]

private lemma closed_Nv {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V}
    (hNv : G.neighborFinset v = {u, w}) :
    {u, w, v} = G.closed_neighborFinset_of_Finset {v} := by
  rw [closed_neighborFinset_of_singleton_eq]
  grind

private lemma closed_Nuvw {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V}
    (hNv : G.neighborFinset v = {u, w}) :
    G.closed_neighborFinset_of_Finset {u, w, v}
      = G.N2_of_Finset {v} ∪ G.closed_neighborFinset_of_Finset {v} := by
  rw [closed_Nv hNv, N2_of_Finset]
  exact Eq.symm <| sdiff_union_of_subset closed_neighborFinset_contains_Finset

private lemma _common_neighbor {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V}
    (hNv : G.neighborFinset v = {u, w}) (huw : ¬G.Adj u w) (hunew : u ≠ w)
    (hdu : G.degree u = 3) (hdw : G.degree w = 3) (H : #(G.N2_of_Finset {v}) = 3) :
    ∃ x ∈ G.neighborFinset u ∩ G.neighborFinset w, x ≠ v := by
  obtain ⟨x, hx, hvnex⟩ := Finset_get_other (by linarith : 2 ≤ G.degree u) v
  if hxw : x ∈ G.neighborFinset w then
    exact ⟨x, mem_inter.mpr ⟨hx, hxw⟩, hvnex.symm⟩
  else
    obtain ⟨y, hy, hvney, hxney⟩ := Finset_get_other_other (by linarith : 3 ≤ G.degree u) v x
    have hNu : G.neighborFinset u = {v, x, y} := by
      refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
      · suffices v ∈ G.neighborFinset u by grind
        exact mem_neighborFinset_symm <| by grind
      · rw [card_triplet' hvnex hvney hxney, ← degree, hdu]
    if hyw : y ∈ G.neighborFinset w then
      exact ⟨y, mem_inter.mpr ⟨hy, hyw⟩, hvney.symm⟩
    else
      have : #(G.neighborFinset w \ G.neighborFinset u) = 2 := by
        rw [card_sdiff, ← degree, hdw]
        suffices G.neighborFinset u ∩ G.neighborFinset w = {v} by
          rw [this, card_singleton]
        refine subset_antisymm ?_ ?_
        · intro z
          simp only [hNu, mem_inter, mem_insert, mem_singleton, and_imp]
          intro hz hzw
          rcases hz with hz | hz | hz
          · exact hz
          · exact hxw (hz ▸ hzw) |>.elim
          · exact hyw (hz ▸ hzw) |>.elim
        · refine singleton_subset_iff.mpr <| mem_inter.mpr ⟨?_, ?_⟩
          <;> exact mem_neighborFinset_symm <| by grind
      obtain ⟨x', y', hx'ney', h⟩ :=
        Finset_card_eq_two_iff (G.neighborFinset w \ G.neighborFinset u) this
      suffices ({x, y} ∪ {x', y'}) ⊆ G.N2_of_Finset {v} by
        have := card_le_card this
        grind
      intro z hz
      refine mem_N2_of_Finset_iff'.mpr ?_
      rcases mem_union.mp hz with hz | hz
      · refine ⟨?_, ?_⟩
        · rw [← closed_Nv hNv]
          grind [ne_of_mem_neighborFinset, degree, mem_neighborFinset]
        · simp only [mem_singleton, exists_eq_left]
          refine ⟨u, ?_⟩
          grind [ne_of_mem_neighborFinset, degree, mem_neighborFinset, Adj.symm]
      · obtain ⟨hzw, hzu⟩ := mem_sdiff.mp (h ▸ hz)
        refine ⟨?_, ?_⟩
        · rw [← closed_Nv hNv]
          have : z ≠ u := by
            refine ne_of_ne_congr (· ∈ G.neighborFinset w) ?_
            simp only [hzw, mem_neighborFinset, not_adj_symm huw, ne_eq, eq_iff_iff, iff_false,
              not_true_eq_false, not_false_eq_true]
          have : z ≠ v := ne_of_ne_congr (· ∈ G.neighborFinset u) (by grind)
          have : z ≠ w := ne_of_mem_neighborFinset hzw
          grind
        · simp only [mem_singleton, exists_eq_left]
          refine ⟨w, ?_, ?_, ?_⟩
          · grind [ne_of_mem_neighborFinset]
          · exact Adj.symm <| mem_neighborFinset .. |>.mp hzw
          · exact Adj.symm <| mem_neighborFinset .. |>.mp <| by grind

private lemma _Claim11 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    {v : V} (h : #(G.N2_of_Finset {v}) ≤ 2)
    (h' : ∀ z ∈ G.N2_of_Finset {v}, AB.A z ∧ G.degree z = 3) :
    ∑ x ∈ G.N2_of_Finset {v}, f G AB x ≤ 7 / 5 := by
  have : ∑ x ∈ G.N2_of_Finset {v}, f G AB x = ∑ x ∈ G.N2_of_Finset {v}, 1 / 2 := by
    refine sum_congr rfl fun x hx ↦ ?_
    obtain ⟨hAx, hdx⟩ := h' x hx
    rw [fA3 hAx hdx]
  rw [this]; clear this
  simp only [sum_const']
  refine @le_trans _ _ _ (2 * (1 / (2 : ℝ))) _ ?_ (by linarith)
  refine mul_le_mul_of_nonneg ?_ (le_refl _) (Nat.cast_nonneg' _) zero_le_one_half
  rw [← Nat.cast_two, Nat.cast_le]
  exact h

lemma Claim11 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {v : V} (hdv : G.degree v = 2) (h : #(G.N2_of_Finset {v}) < 4)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  match Claim6' hG ih with
  | Or.inr h' => exact h'
  | Or.inl h' => ?_
  have h' : ∀ v ∈ AB.toFinset, AB.A v ∧ (G.degree v = 2 ∨ G.degree v = 3) := by grind
  obtain ⟨u, hvu⟩ : G.neighborFinset v |>.Nonempty := by
    refine card_ne_zero.mp <| ?_
    simp only [card_neighborFinset_eq_degree, hdv, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  obtain ⟨w, hvw, hunew⟩ := Finset_get_other (le_of_eq hdv.symm) u
  have hNv : G.neighborFinset v = {u, w} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind
    · rw [card_pair hunew, ← degree, hdv]
  simp only [mem_neighborFinset] at hvu hvw
  obtain ⟨hAu, hdu⟩ := h' u (hG <| G.mem_support.mpr ⟨v, hvu.symm⟩)
  obtain ⟨hAv, _⟩ := h' v (hG <| G.mem_support.mpr ⟨w, hvw⟩)
  obtain ⟨hAw, hdw⟩ := h' w (hG <| G.mem_support.mpr ⟨v, hvw.symm⟩)
  match hdu, hdw with
  | Or.inl hdu, _ => exact Claim9 hG hvu hdv hdu ih
  | _, Or.inl hdw => exact Claim9 hG hvw hdv hdw ih
  | Or.inr hdu, Or.inr hdw => ?_
  if huw : G.Adj u w then
    match Claim10 hG hvu.symm hvw huw ih with
    | Or.inr H => exact H
    | Or.inl ⟨_, hdv', _⟩ => ?_
    linarith
  else
    if H : ∃ z ∈ G.N2_of_Finset {v}, G.degree z = 2 then
      obtain ⟨z, hz, hdz⟩ := H
      have := mem_N2_of_Finset_iff.mp hz
      simp only [mem_singleton, exists_eq_left] at this
      obtain ⟨z', hz'nev, hzz', hz'v⟩ := this |>.2.2
      refine Claim7 hG hzz' hz'v this.1 ?_ hdz hdv ih
      suffices z' ∈ G.neighborFinset v by grind
      exact mem_neighborFinset .. |>.mpr hz'v.symm
    else
      simp only [not_exists, not_and] at H
      have H : ∀ x ∈ G.N2_of_Finset {v}, AB.A x ∧ G.degree x = 3 := by
        intro x hx
        obtain ⟨hAx, hdx⟩ :=
          h' x (hG <| G.degree_pos_iff_mem_support _ |>.mp <| one_le_degree_of_mem_N2 hx)
        refine ⟨hAx, ?_⟩
        rcases hdx with hdx | hdx
        · exact H _ hx hdx |>.elim
        · exact hdx
      refine Claim2' {u, w, v} ?_ ?_ ?_ hG ih ?_ ?_
      · exact insert_nonempty ..
      · exact fun _ _ ↦ hG <| G.degree_pos_iff_mem_support _ |>.mp <| by grind
      · refine respects_of_A <| by grind
      · exact InducesForestOfStars_triplet_of_nonadj huw
      · rw [card_triplet' hunew hvu.ne' hvw.ne', Nat.cast_three, closed_Nuvw hNv,
          sum_union <| disjoint_iff_inter_eq_empty.mpr N2_inter_Nle1_empty, ← closed_Nv hNv,
          sum_triplet hunew hvu.ne' hvw.ne', fA3 hAu hdu, fA2 hAv hdv, fA3 hAw hdw]
        suffices ∑ x ∈ G.N2_of_Finset {v}, f G AB x - ∑ w ∈ G.N2_of_Finset {u, w, v}, γ G AB w
            ≤ 7 / 5 by
          linarith
        if H' : #(G.N2_of_Finset {v}) ≤ 2 then
          have : 0 ≤ ∑ w ∈ G.N2_of_Finset {u, w, v}, γ G AB w := sum_nonneg fun _ _ ↦ γ_nonneg
          suffices ∑ x ∈ G.N2_of_Finset {v}, f G AB x ≤ 7 / 5 by
            linarith
          exact _Claim11 H' H
        else
          have H' : #(G.N2_of_Finset {v}) = 3 := by lia
          obtain ⟨x, hx, hxnev⟩ := _common_neighbor hNv huw hunew hdu hdw H'
          obtain ⟨y, hy, hvney, hxney⟩ := Finset_get_other_other (le_of_eq <| hdu.symm) v x
          obtain ⟨z, hz, hvnez, hxnez⟩ := Finset_get_other_other (le_of_eq <| hdw.symm) v x
          have hNu : G.neighborFinset u = {v, x, y} := by
            refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
            · grind [mem_neighborFinset_symm]
            · rw [← degree, hdu, card_triplet' hxnev.symm hvney hxney]
          have hNw : G.neighborFinset w = {v, x, z} := by
            refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
            · grind [mem_neighborFinset_symm]
            · rw [← degree, hdw, card_triplet' hxnev.symm hvnez hxnez]
          have hN2v : G.N2_of_Finset {v} = {x, y, z} := by
            rw [N2_of_Finset, ← closed_Nv hNv, closed_neighborFinset_of_triplet_eq, hNv]
            have H : ({v, x, y} ∪ {v, x, z} ∪ {u, w} ∪ {u, w, v})
                = ({u, v, w, x, y, z} : Finset _) := by
              clear * - u v w x y z
              grind
            suffices {x, y, z} ∩ {u, w, v} = (∅ : Finset _) by
              have : ({u, v, w, x, y, z} : Finset _) = {u, w, v} ∪ {x, y, z} := by grind
              rw [hNu, hNw, H, this, union_sdiff_distrib, Finset.sdiff_self, empty_union]
              clear this
              refine subset_antisymm ?_ ?_
              · exact sdiff_subset
              · exact fun _ h ↦ mem_sdiff.mpr ⟨h, notMem_of_mem_of_empty_inter h this⟩
            suffices v ∉ ({x, y, z} : Finset _) ∧ w ∉ ({x, y, z} : Finset _)
                ∧ u ∉ ({x, y, z} : Finset _) by
              by_contra
              obtain ⟨x', hx'⟩ := nonempty_iff_ne_empty.mpr this
              obtain ⟨hx'₁, hx'₂⟩ := mem_inter.mp hx'
              simp only [mem_insert, mem_singleton] at hx'₂
              rcases hx'₂ with hx' | hx' | hx' <;> grind
            grind [ne_of_mem_neighborFinset, degree, mem_neighborFinset, Adj.symm]
          obtain ⟨hAx, hdx⟩ := H x (by grind)
          obtain ⟨hAy, hdy⟩ := H y (by grind)
          obtain ⟨hAz, hdz⟩ := H z (by grind)
          have : ∑ x ∈ G.N2_of_Finset {v}, f G AB x = ∑ x ∈ G.N2_of_Finset {v}, 1 / 2 := by
            refine sum_congr rfl fun x hx ↦ ?_
            obtain ⟨hAx, hdx⟩ := H _ hx
            rw [fA3 hAx hdx]
          simp only [this, sum_const', H', Nat.cast_three]; clear this
          suffices 1 / 10 ≤ ∑ w ∈ G.N2_of_Finset {u, w, v}, γ G AB w by linarith
          suffices (G.N2_of_Finset {u, w, v}).Nonempty by
            obtain ⟨x', hx'⟩ := this
            have : 1 / 10 ≤ γ G AB x' := by
              obtain ⟨hAx', hdx'⟩ :=
                h' x' (hG <| G.degree_pos_iff_mem_support _ |>.mp <| one_le_degree_of_mem_N2 hx')
              rcases hdx' with hdx' | hdx'
              · rw [γA2 hAx' hdx']
                linarith
              · rw [γA3 hAx' hdx']
            refine this.trans ?_
            rw [← sum_singleton (γ G AB ·)]
            refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ γ_nonneg
            exact singleton_subset_iff.mpr hx'
          by_contra hN2
          simp only [not_nonempty_iff_eq_empty] at hN2
          have hynez : y ≠ z := by grind
          have : G.neighborFinset z = {w, x, y} := by
            refine eq_of_subset_and_eq_card ?_ ?_
            · intro z' hz'
              have : z' ∉ G.N2_of_Finset {u, w, v} := by grind
              simp only [mem_N2_of_Finset_iff, not_and_or, Decidable.not_not, not_forall,
                not_exists] at this
              have hz'nev : z' ≠ v := by
                refine ne_of_ne_congr (· ∈ G.neighborFinset z) ?_
                simp only [hz', ne_eq, eq_iff_iff, true_iff]
                refine not_mem_neighborFinset_symm <| hNv ▸ ?_
                grind [mem_neighborFinset, Adj.symm, Adj.ne]
              have hz'neu : z' ≠ u := by
                refine ne_of_ne_congr (· ∈ G.neighborFinset z) ?_
                simp only [hz', ne_eq, eq_iff_iff, true_iff]
                exact not_mem_neighborFinset_symm (by grind)
              rcases this with h | h | h
              · suffices z' = w by grind
                grind
              · obtain ⟨u', hu', hz'u'⟩ := h
                simp only [mem_insert, mem_singleton] at hu'
                rcases hu' with hu' | hu' | hu'
                · subst hu'
                  have := mem_neighborFinset_symm <| mem_neighborFinset .. |>.mpr hz'u'
                  grind
                · subst hu'
                  have := mem_neighborFinset_symm <| mem_neighborFinset .. |>.mpr hz'u'
                  grind [ne_of_mem_neighborFinset]
                · subst hu'
                  have := mem_neighborFinset_symm <| mem_neighborFinset .. |>.mpr hz'u'
                  grind
              · have := h w
                simp only [mem_insert, mem_singleton, true_or, or_true, singleton_inter_of_mem,
                  ne_eq, singleton_ne_empty, not_false_eq_true, mem_of_singleton_inter_ne_emty,
                  not_true_eq_false, false_or] at this
                have := this z
                grind [mem_neighborFinset, Adj.symm]
            · rw [← degree, hdz, card_triplet']
              · exact Ne.symm <| ne_of_mem_neighborFinset <|  mem_inter.mp hx |>.2
              · refine ne_of_ne_congr (G.Adj u ·) ?_
                simp only [huw, ne_eq, eq_iff_iff, false_iff, Decidable.not_not]
                exact mem_neighborFinset .. |>.mp <| by grind
              · exact hxney
          obtain ⟨y', hy', huney', hzney'⟩ :=
            Finset_get_other_other (by linarith : 3 ≤ G.degree y) u z
          suffices y' = x by
            have hNx : {u, w, y, z} ⊆ G.neighborFinset x := by
              intro u' hu'
              simp only [mem_insert, mem_singleton] at hu'
              rcases hu' with h | h | h | h
              · refine mem_neighborFinset_symm <| ?_
                exact h ▸ mem_inter.mp hx |>.1
              · refine mem_neighborFinset_symm <| ?_
                exact h ▸ mem_inter.mp hx |>.2
              · rw [← this, h]
                exact mem_neighborFinset_symm hy'
              · exact mem_neighborFinset_symm (by grind)
            have := card_le_card hNx
            rw [← degree, hdx] at this
            rw [card_quadruplet] at this
            <;> grind [mem_neighborFinset, Adj.symm, Adj.ne]
          have hynew : y ≠ w := by grind [mem_neighborFinset, Adj.symm, Adj.ne]
          have hy'new : y' ≠ w := by
            refine ne_of_ne_congr (· ∈ G.neighborFinset y) ?_
            simp only [hy', ne_eq, eq_iff_iff, true_iff]
            exact not_mem_neighborFinset_symm <| by grind
          have hy'new : y' ≠ v := by
            refine ne_of_ne_congr (· ∈ G.neighborFinset y) ?_
            simp only [hy', ne_eq, eq_iff_iff, true_iff]
            refine not_mem_neighborFinset_symm ?_
            grind [mem_neighborFinset, Adj.symm, Adj.ne]
          have : y' ∉ G.N2_of_Finset {u, w, v} := by grind
          simp only [mem_N2_of_Finset_iff, not_and_or, Decidable.not_not, not_forall,
            not_exists] at this
          rcases this with h | h | h
          · grind
          · obtain ⟨u', hu', hy'u'⟩ := h
            simp only [mem_insert, mem_singleton] at hu'
            rcases hu' with h | h | h
            · subst h
              have := hNu ▸ mem_neighborFinset .. |>.mpr hy'u'.symm
              grind [ne_of_mem_neighborFinset]
            · subst h
              have := hNw ▸ mem_neighborFinset .. |>.mpr hy'u'.symm
              grind
            · subst h
              have := hNv ▸ mem_neighborFinset .. |>.mpr hy'u'.symm
              grind
          · have := h u
            simp only [mem_singleton, inter_insert_of_mem, ne_eq, insert_ne_empty,
              not_false_eq_true, mem_of_singleton_inter_ne_emty, not_true_eq_false, mem_insert,
              false_or] at this
            have := this y
            grind [ne_of_mem_neighborFinset, mem_neighborFinset, Adj.symm, Adj.ne]

end Bipartition
end AB
end CaroWeiType
