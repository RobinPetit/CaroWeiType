import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim6
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim9
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Lemmas

open SimpleGraph
open Finset

namespace CaroWeiType
namespace AB
namespace Bipartition

variable {V : Type} [Fintype V]

private lemma _A3_of_f_le_fA3
    {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    {v : V} (hfv : f G AB v ≤ 1 / 2) (hv : (AB.A v ∧ G.degree v = 2) ∨ (AB.A v ∧ G.degree v = 3)) :
    AB.A v ∧ G.degree v = 3 := by
  rcases hv with ⟨hAv, hdv⟩ | ⟨hAv, hdv⟩
  · have three_ne_two : 3 ≠ 2 := by omega
    simp only [fA2 hAv hdv] at hfv
    linarith
  · exact ⟨hAv, hdv⟩

variable [DecidableEq V]

lemma InducesForestOfStars_of_union_deg_2_not_both_neighbors_in
    {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w) (hdu : G.degree u = 2)
    (hdv : G.degree v = 3) (hdw : G.degree w = 3) (hAv : AB.A v) (hAw : AB.A w)
    {s : Finset V} (hs : G.InducesForestOfStars s)
    (hsresp : respects s (G.deleteIncidencesOf {u}) ((AB \ {u}).demote_finset {v, w}))
    :
    G.InducesForestOfStars (s ∪ {u}) := by
  if hus : u ∈ s then
    exact (left_eq_union.mpr <| singleton_subset_iff.mpr hus) ▸ hs
  else
    have hs' : ¬{v, w} ⊆ s := by
      intro H
      obtain ⟨hvs, hws⟩ : v ∈ s ∧ w ∈ s := by grind
      have hA'v : (AB \ {u}).A v := ⟨hAv, notMem_singleton.mpr huv.ne'⟩
      have hA'w : (AB \ {u}).A w := ⟨hAw, notMem_singleton.mpr huw.ne'⟩
      refine not_A_of_B ((AB \ {u}).demote_finset_from_A  hA'w (by grind : w ∈ {v, w})) ?_
      refine hsresp v hvs ?_ w hws ?_ |>.1
      · exact (AB \ {u}).demote_finset_from_A hA'v (by grind)
      · refine deleteIncidencesOf_adj_iff_of_notMem ?_ ?_ |>.mp hvw.symm
        · exact notMem_singleton.mpr huw.ne'
        · exact notMem_singleton.mpr huv.ne'
    have hNu : G.neighborFinset u = {v, w} := by
      refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
      · grind [mem_neighborFinset]
      · rw [card_pair hvw.ne, ← degree, hdu]
    have : G.degree_in s u ≤ 2 := hdu ▸ degree_in_le_degree
    have : G.degree_in s u = 0 ∨ G.degree_in s u = 1 ∨ G.degree_in s u = 2 := by omega
    rcases this with hd'u | hd'u | hd'u
    · exact InducesForestOfStars_union_isolated hd'u hs
    · simp only [degree_in] at hd'u
      obtain ⟨x, hx, hx'⟩ := Finset_singleton_unique hd'u
      simp only at hx'
      simp only [hNu, mem_inter, mem_insert, mem_singleton] at hx
      obtain ⟨hx, hxs⟩ := hx
      if hd'x : G.degree_in s x = 0 then
        refine InducesForestOfStars_union_leaf' hd'u hxs ?_ (hd'x ▸ zero_ne_one) hs
        rcases hx with hx | hx
        · exact hx ▸ huv
        · exact hx ▸ huw
      else
        obtain ⟨z, hzneu, hznev, hznew, hzx⟩ :
            ∃ z, z ≠ u ∧ z ≠ v ∧ z ≠ w ∧ z ∈ G.neighborFinset x := by
          rcases hx with hx | hx
          · obtain ⟨z, hz, hunez, hwnez⟩ := Finset_get_other_other (by grind : 3 ≤ G.degree x) u w
            refine ⟨z, hunez.symm, hx ▸ ne_of_mem_neighborFinset hz, hwnez.symm, by grind⟩
          · obtain ⟨z, hz, hunez, hvnez⟩ := Finset_get_other_other (by grind : 3 ≤ G.degree x) u v
            refine ⟨z, hunez.symm, hvnez.symm, hx ▸ ne_of_mem_neighborFinset hz, by grind⟩
        have hNx : G.neighborFinset x = ({u, v, w, z} \ {x}) := by
          refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
          · grind [mem_neighborFinset, Adj.symm]
          · rw [← degree, card_sdiff]
            grind
        have hd'x : G.degree_in s x = 1 := by
          refine le_antisymm ?_ (by lia)
          rcases hx with hx | hx
          · obtain ⟨z, hz, hunez, hwnez⟩ := Finset_get_other_other (by grind : 3 ≤ G.degree x) u w
            have hNx : G.neighborFinset x = {u, w, z} := by
              refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
              · grind [mem_neighborFinset, Adj.symm]
              · rw [card_triplet' huw.ne hunez hwnez, ← degree, hx, hdv]
            rw [← card_singleton z]
            exact card_le_card <| by grind
          · obtain ⟨z, hz, hunez, hvnez⟩ := Finset_get_other_other (by grind : 3 ≤ G.degree x) u v
            have hNx : G.neighborFinset x = {u, v, z} := by
              refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
              · grind [mem_neighborFinset, Adj.symm]
              · rw [card_triplet' huv.ne hunez hvnez, ← degree, hx, hdw]
            rw [← card_singleton z]
            exact card_le_card <| by grind
        have hzs : z ∈ s := by
          obtain ⟨x', hx'⟩: (G.neighborFinset x ∩ s).Nonempty := card_ne_zero.mp <| by grind
          simp only [mem_inter, hNx, mem_sdiff, mem_singleton, mem_insert, mem_singleton] at hx'
          obtain ⟨⟨hx', hx'nex⟩, hx's⟩ := hx'
          rcases hx' with hx' | hx' | hx' | hx'
          · have : x' ≠ u := by
              refine ne_of_ne_congr (· ∈ s) ?_
              simp only [hus, hx's]
              exact true_ne_false
            exact this hx' |>.elim
          · grind
          · grind
          · exact hx' ▸ hx's
        refine InducesForestOfStars_union_leaf_on_K2 ?_ hd'u hd'x ?_ ?_ hzs hxs hzneu hs
        · refine le_antisymm ?_ ?_
          · refine le_of_eq_of_le ?_ (hsresp x hxs ?_ z hzs ?_ |>.2)
            · refine Eq.symm (degree_in_deleteIncidencesOf s {u} ?_ ?_)
              · exact singleton_inter_of_notMem hus
              · exact notMem_singleton.mpr hzneu
            · refine (AB \ {u}).demote_finset_from_A ⟨?_, ?_⟩ ?_ <;> grind
            · refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ ?_
              · exact notMem_singleton.mpr hzneu
              · grind
              · exact Adj.symm <| mem_neighborFinset .. |>.mp hzx
          · exact one_le_card.mpr ⟨x, mem_inter.mpr ⟨mem_neighborFinset_symm hzx, hxs⟩⟩
        · grind [Adj.symm]
        · exact (mem_neighborFinset .. |>.mp hzx).symm
    · simp only [degree_in, hNu] at hd'u
      grind

private lemma _A3 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hfwv : f G AB w ≤ f G AB v) (hfvu : f G AB v ≤ f G AB u)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    (G.degree u = 3 ∧ G.degree v = 3 ∧ G.degree w = 3) ∨ Objective G AB := by
  have hu : u ∈ AB.toFinset := hG <| G.mem_support.mpr ⟨_, huv⟩
  have hv : v ∈ AB.toFinset := hG <| G.mem_support.mpr ⟨_, hvw⟩
  have hw : w ∈ AB.toFinset := hG <| G.mem_support.mpr ⟨_, hvw.symm⟩
  match Claim6' hG ih with
  | Or.inr h => exact Or.inr h
  | Or.inl h => ?_
  rcases h _ hu with ⟨hAu, hdu⟩ | ⟨hAu, hdu⟩
  · have hNu : G.neighborFinset u = {v, w} := by
      refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
      · grind [mem_neighborFinset]
      · rw [card_pair hvw.ne, ← degree, hdu]
    cases h _ hv with
    | inl h' => exact Or.inr <| Claim9 hG huv hdu h'.2 ih
    | inr h' => ?_
    obtain ⟨hAv, hdv⟩ := h'
    cases h _ hw with
    | inl h' => exact Or.inr <| Claim9 hG huw hdu h'.2 ih
    | inr h' => ?_
    have ⟨hAw, hdw⟩ := h'
    refine Or.inr <| ?_
    obtain ⟨s, hs, hsf, hsresp, hscard⟩ := by
      refine ih (G.deleteIncidencesOf {u}) (AB \ {u} |>.demote_finset {v, w}) ?_ ?_
      · rw [← demote_finset_toFinset_eq]
        exact hsupp_mono hG
      · rw [← card_demote_finset_eq_card]
        exact AB.sdiff_card <| singleton_inter_ne_empty_iff.mpr hu
    rw [← demote_finset_toFinset_eq, sdiff_toFinset] at hs
    have hus : u ∉ s := inter_singleton_eq_empty_iff.mp <| disjoint_of_sdiff hs
    refine ⟨s ∪ {u}, ?_, ?_, ?_, ?_⟩
    · exact Finset.union_subset (subset_eq_inter hs) (singleton_subset_iff.mpr hu)
    · refine InducesForestOfStars_of_union_deg_2_not_both_neighbors_in
        huv hvw huw hdu hdv hdw hAv hAw ?_ hsresp
      exact InducesForestOfStars_graph_mono' (disjoint_of_sdiff hs) hsf
    · exact respects_of_A <| by grind
    · simp only [eval, ← demote_finset_toFinset_eq, sdiff_toFinset] at hscard
      calc _
        _ ≤ #s + ∑ x ∈ {v, w}, (f (G.deleteIncidencesOf {u}) (AB \ {u}) x -
            f (G.deleteIncidencesOf {u}) ((AB \ {u}).demote_finset {v, w}) x) +
            ∑ w ∈ G.neighborFinset u, (f G AB w - f (G.deleteIncidencesOf {u}) (AB \ {u}) w) +
            f G AB u := by
          have hNvAB : G.neighborFinset u ⊆ AB.toFinset :=
            fun x hx ↦ hG <| G.mem_support.mpr ⟨u, Adj.symm <| mem_neighborFinset .. |>.mp hx⟩
          rw [eval, sum_sdiff_singleton_eval hu hNvAB]
          rw [sum_eq_sum_demote_finset {v, w} _ (by grind)]
          simp only [sum_sub_distrib, add_le_add_iff_right, hscard]
      rw [card_union, inter_singleton_of_notMem hus, card_empty, tsub_zero, Nat.cast_add,
        card_singleton, Nat.cast_one]
      simp only [sum_sub_distrib, mem_singleton, hvw.ne, not_false_eq_true, sum_insert,
        sum_singleton, hNu, fA3 hAv hdv, fA3 hAw hdw, fA2 hAu hdu]
      suffices 3 / 5 ≤
            f (G.deleteIncidencesOf {u}) ((AB \ {u}).demote_finset {v, w}) v
            + f (G.deleteIncidencesOf {u}) ((AB \ {u}).demote_finset {v, w}) w by
        linarith
      rw [fB2, fB2]
      · linarith
      · exact demote_finset_B_of_A_of_mem _ ⟨hAw, notMem_singleton.mpr huw.ne'⟩ mem_pair'
      · rw [← G.degree_deleteIncidencesOf_neighbor_singleton' huw, hdw]
      · exact demote_finset_B_of_A_of_mem _ ⟨hAv, notMem_singleton.mpr huv.ne'⟩ mem_pair
      · rw [← G.degree_deleteIncidencesOf_neighbor_singleton' huv, hdv]
  · simp only [fA3 hAu hdu] at hfvu
    obtain ⟨hAv, hdv⟩ := _A3_of_f_le_fA3 hfvu (h _ hv)
    obtain ⟨hAw, hdw⟩ := _A3_of_f_le_fA3 (hfwv.trans hfvu) (h _ hw)
    exact Or.inl ⟨hdu, hdv, hdw⟩

private lemma _Claim10_of_diamond_A2_ {G : SimpleGraph V} [DecidableRel G.Adj]
    {AB : Bipartition V} [AB.Decidable] (hG : G.support ⊆ AB.toFinset)
    (u v w x z : V)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w) (hwz : G.Adj w z)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3) (hdw : G.degree w = 3)
    (hdx : G.degree x = 2) (hdz : G.degree z = 2)
    (hAu : AB.A u) (hAv : AB.A v) (hAw : AB.A w) (hAx : AB.A x) (hAz : AB.A z)
    (hNu : G.neighborFinset u = {v, w, x}) (hNv : G.neighborFinset v = {u, w, x})
    (hNw : G.neighborFinset w = {u, v, z})
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  refine Claim2' {u, v} pair_nonempty ?_ ?_ hG ih ?_ ?_
  · intro u' hu'
    simp only [mem_insert, mem_singleton] at hu'
    exact AB.mem_toFinset.mp <| Or.inl <| hu'.elim (· ▸ hAu) (· ▸ hAv)
  · exact respects_pair hAu
  · exact InducesForestOfStars_pair
  · rw [card_pair huv.ne, Nat.cast_two]
    have hN1 : G.closed_neighborFinset_of_Finset {u, v} = {u, v, w, x} := by
      rw [closed_neighborFinset_of_pair_eq, hNu, hNv]
      grind
    have : ∑ z ∈ {u, v, w, x}, f G AB z = f G AB u + f G AB v + f G AB w + f G AB x := by
      refine sum_quadruplet ?_ ?_ ?_ ?_ ?_ ?_ <;> grind [Adj.ne]
    rw [hN1, this, fA2 hAx hdx, fA3 hAu hdu, fA3 hAv hdv, fA3 hAw hdw]
    suffices 7 / 30 ≤ ∑ w ∈ G.N2_of_Finset {u, v}, γ G AB w by linarith
    have hN2 : {z} ⊆ G.N2_of_Finset {u, v} := by
      refine singleton_subset_iff.mpr ?_
      refine mem_N2_of_Finset_iff''.mpr ⟨?_, ⟨w, ?_, hwz.symm⟩⟩ -- <;> grind
      · rw [closed_neighborFinset_of_pair_eq, hNu, hNv]
        have : z ∉ ({u, v, w} : Finset _) := by grind [degree, ne_of_mem_neighborFinset]
        suffices z ≠ x by grind
        intro hzeqx
        have hNx : {u, v, w} ⊆ G.neighborFinset x :=
          fun _ _ ↦ mem_neighborFinset_symm <| by grind
        have := card_le_card hNx
        grind [degree]
      · exact mem_closed_neighborFinset_iff.mpr <| Or.inr ⟨u, by grind, huw⟩
    refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hN2 fun _ _ _ ↦ γ_nonneg)
    rw [sum_singleton, γA2 hAz hdz]

private lemma _union_reorder {α : Type*} [DecidableEq α] {s₁ s₂ s₃ s₄ s₅ s₆ : Finset α} :
    (s₁ ∪ s₂ ∪ s₃) ∪ (s₄ ∪ s₅ ∪ s₆) = (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₆) ∪ s₅ := by
  grind

private lemma _union_eq {α : Type*} [DecidableEq α] {u v w x y z x' : α} :
    {u, w, y} ∪ {u, v, z} ∪ {v, w} ∪ {u, x'} ∪ {x, x'}
      = ({u, v, w, x, y, z, x'} : Finset _) := by
  ext t
  simp only [union_insert, insert_union, singleton_union, ne_eq, singleton_inter_eq_empty_iff,
    mem_insert, mem_singleton, true_or, or_true, not_true_eq_false, not_false_eq_true,
    mem_of_singleton_inter_ne_emty, insert_eq_of_mem]
  grind

private lemma _union_eq' {α : Type*} [DecidableEq α] {u v w x x' : α} :
    {u, x'} ∪ {v, w, x} ∪ {u, v, x'} ∪ {x, u, w} = ({u, v, w, x, x'} : Finset _) := by
  ext u'
  simp only [union_insert, insert_union, singleton_union, ne_eq, singleton_inter_eq_empty_iff,
    mem_insert, mem_singleton, or_true, not_true_eq_false, not_false_eq_true,
    mem_of_singleton_inter_ne_emty, insert_eq_of_mem, true_or]
  grind

private lemma _union_eq'' {α : Type*} [DecidableEq α] {u v w x y x' : α} :
    {u, x'} ∪ {u, w, y} ∪ {v, w, x} ∪ {x, v, u} = {u, v, w} ∪ ({x, y, x'} : Finset _) := by
  ext u'
  simp only [union_insert, insert_union, singleton_union, ne_eq, singleton_inter_eq_empty_iff,
    mem_insert, mem_singleton, true_or, or_true, not_true_eq_false, not_false_eq_true,
    mem_of_singleton_inter_ne_emty, insert_eq_of_mem]
  grind

private lemma neighborhood_eq {G : SimpleGraph V} [DecidableRel G.Adj] {v x y z : V}
    (hdv : G.degree v = 3) (hxv : G.Adj x v) (hyv : G.Adj y v) (hzv : G.Adj z v)
    (hxney : x ≠ y) (hxnez : x ≠ z) (hynez : y ≠ z) :
    G.neighborFinset v = {x, y, z} := by
  refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
  · grind [mem_neighborFinset, Adj.symm]
  · grind [degree]

set_option maxHeartbeats 1000000 in  -- needed because lemma is a bit long
private lemma _Claim10_ {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset)
    (u v w x y : V)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w) (hux : G.Adj u x) (hvy : G.Adj v y)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3) (hdw : G.degree w = 3)
    (hdx : G.degree x = 2) (hdy : G.degree y = 2)
    (hxney : x ≠ y) (hx : x ∉ ({u, v, w} : Finset _)) (hy : y ∉ ({u, v, w} : Finset _))
    (h' : ∀ x ∈ AB.toFinset, AB.A x ∧ (G.degree x = 2 ∨ G.degree x = 3))
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  have hAu : AB.A u := h' _ (hG <| G.mem_support.mpr ⟨v, huv⟩) |>.1
  have hAv : AB.A v := h' _ (hG <| G.mem_support.mpr ⟨w, hvw⟩) |>.1
  have hAw : AB.A w := h' _ (hG <| G.mem_support.mpr ⟨u, huw.symm⟩) |>.1
  have hAx : AB.A x := h' _ (hG <| G.mem_support.mpr ⟨u, hux.symm⟩) |>.1
  have hAy : AB.A y := h' _ (hG <| G.mem_support.mpr ⟨v, hvy.symm⟩) |>.1
  have hNu : G.neighborFinset u = {v, w, x} := by
    refine neighborhood_eq hdu huv.symm huw.symm hux.symm hvw.ne ?_ ?_ <;> grind
  have hNv : G.neighborFinset v = {u, w, y} := by
    refine neighborhood_eq hdv huv hvw.symm hvy.symm huw.ne ?_ ?_ <;> grind
  obtain ⟨z, hNw⟩ :=
    neighborFinset_eq_deg3'' (mem_neighborFinset .. |>.mpr huw.symm)
        (mem_neighborFinset .. |>.mpr hvw.symm) huv.ne hdw
  if hxy : G.Adj x y then
    exact Claim9 hG hxy hdx hdy ih
  else
    if hNx : G.neighborFinset x ⊆ {u, v, w} then
      have hNx : G.neighborFinset x = {u, w} := by
        refine eq_of_subset_and_eq_card ?_ ?_
        · suffices v ∉ G.neighborFinset x by grind
          exact not_mem_neighborFinset_symm <| by grind
        · rw [← degree, hdx, card_pair huw.ne]
      have hNw : G.neighborFinset w = {u, v, x} := by
        refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
        · grind [mem_neighborFinset, mem_neighborFinset_symm]
        · rw [card_triplet' huv.ne hux.ne, ← degree, hdw]
          refine ne_of_ne_congr (G.degree ·) ?_
          simp only [hdv, hdx, ne_eq, Nat.succ_ne_self, not_false_eq_true]
      have hx : x ∈ AB := Or.inl <| by grind
      refine _Claim10_of_diamond_A2_ hG u w v x y huw hvw.symm huv hvy hdu hdw hdv hdx hdy
          hAu hAw hAv hAx hAy ?_ ?_ ?_ ih <;> grind [degree]
    else
      obtain ⟨x', hxx', hx'⟩ : ∃ x' ∈ G.neighborFinset x, x' ∉ ({u, v, w} : Finset _) :=
        Set.not_subset.mp hNx
      simp only [mem_neighborFinset] at hxx'
      obtain ⟨hAx', hdx'⟩ := h' x' (hG <| G.mem_support.mpr ⟨x, hxx'.symm⟩)
      cases hdx' with
      | inl hdx' => exact Claim9 hG hxx' hdx hdx' ih
      | inr hdx' => ?_
      have hNx : G.neighborFinset x = {u, x'} := by
        refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
        · grind [mem_neighborFinset, Adj.symm]
        · grind [degree]
      if hwt : G.Adj w x' then
        refine Corollary2 {x, u, w} (insert_nonempty ..) ?_ ?_ hG ih ?_ ?_
        · grind [AB.mem_iff, AB.mem_toFinset.mp]
        · exact respects_of_A <| by grind
        · refine InducesForestOfStars_triplet hux.symm huw ?_
          refine not_iff_not.mpr (mem_neighborFinset ..) |>.mp <| by grind [Adj.ne]
        · have hNw : G.neighborFinset w = {u, v, x'} := by
            refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
            · grind [mem_neighborFinset, Adj.symm]
            · rw [← degree, hdw]
              refine card_triplet' huv.ne ?_ ?_ <;> grind
          have : G.closed_neighborFinset_of_Finset {x, u, w} = {u, v, w, x, x'} := by
            rw [closed_neighborFinset_of_triplet_eq, hNx, hNu, hNw, _union_eq']
          have hxw : x ≠ w := by
            refine ne_of_ne_congr (G.degree ·) ?_
            simp only [hdx, hdw, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
          rw [card_triplet' hux.ne' hxw huw.ne, Nat.cast_three, this]
          suffices f G AB u + f G AB v + f G AB w + f G AB x + f G AB x' ≤ 3 by
            refine le_of_eq_of_le ?_ this
            have : ∑ z ∈ {u, v, w, x, x'}, f G AB z
                = ∑ z ∈ {u, v, w}, f G AB z + ∑ z ∈ {x, x'}, f G AB z := by
              grind
            rw [this]; clear this
            suffices ∑ z ∈ {x, x'}, f G AB z = f G AB x + f G AB x' by
              grind [Adj.ne, Adj.symm]
            exact sum_pair hxx'.ne
          simp only [fA3 hAu hdu, fA3 hAv hdv, fA3 hAw hdw, fA2 hAx hdx, fA3 hAx' hdx']
          linarith
      else if hzxy : z = x ∨ z = y then
        rcases hzxy with hzx | hzy
        · suffices G.neighborFinset x = {u, w} by grind
          refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
          · intro u' hu'
            simp only [mem_insert, mem_singleton] at hu'
            rcases hu' with hu' | hu'
            · refine mem_neighborFinset .. |>.mpr <| hu' ▸ hux.symm
            · grind [mem_neighborFinset_symm]
          · rw [card_pair huw.ne, ← degree, hdx]
        · refine _Claim10_of_diamond_A2_ hG v w u y x hvw huw.symm huv.symm hux hdv hdw hdu hdy hdx
            hAv hAw hAu hAy hAx ?_ ?_ ?_ ih <;> grind
      else if hNx' : G.neighborFinset x' ⊆ {u, v, w, x, y, z} then
        refine Corollary2 ({v, w} ∪ {x, x'}) ?_ ?_ ?_ hG ih ?_ ?_
        · exact Nonempty.inr <| by exact pair_nonempty
        · exact fun _ _ ↦ AB.mem_toFinset.mp <| Or.inl <| by grind
        · exact respects_of_A <| by grind
        · refine InducesForestOfStars_union_disjoint_neighborhoods ?_ ?_ ?_
          · exact InducesForestOfStars_pair
          · exact InducesForestOfStars_pair
          · intro x₁ hx₁ x₂ hx₂
            clear hNx' ih hG h' hAu hAv hAw hAx hAy
            simp only [mem_insert, mem_singleton] at hx₁ hx₂
            match hx₁, hx₂ with
            | Or.inl hx₁, Or.inl hx₂ =>
                refine not_iff_not.mpr (mem_neighborFinset ..) |>.mp <| hx₁ ▸ hx₂ ▸ ?_
                grind [degree]
            | Or.inl hx₁, Or.inr hx₂ =>
                refine not_iff_not.mpr (mem_neighborFinset ..) |>.mp <| hx₁ ▸ hx₂ ▸ ?_
                grind [Adj.symm]
            | Or.inr hx₁, Or.inl hx₂ =>
                refine not_iff_not.mpr (mem_neighborFinset ..) |>.mp <| hx₁ ▸ hx₂ ▸ ?_
                grind [Adj.symm]
            | Or.inr hx₁, Or.inr hx₂ =>
                grind [mem_neighborFinset, Adj.symm]
        · have : #({v, w} ∪ {x, x'}) = 4 := by grind [Adj.ne, Adj.symm, mem_neighborFinset]
          rw [this, Nat.cast_four]
          have : G.closed_neighborFinset_of_Finset ({v, w} ∪ {x, x'}) = {u, v, w, x, y, z, x'} := by
            rw [closed_neighborFinset_of_union, closed_neighborFinset_of_pair_eq, hNv, hNw]
            rw [closed_neighborFinset_of_pair_eq, hNx, _union_reorder, _union_eq]
            exact union_eq_left.mpr (subset_trans hNx' <| by grind)
          rw [this]; clear this
          have : ({u, v, w, x, y, z, x'} : Finset _) = {u, v, w} ∪ {x, y, z, x'} := by
            grind
          have hdisj : Disjoint ({u, v, w} : Finset _) {x, y, z, x'} := by
            refine disjoint_iff_inter_eq_empty.mpr ?_
            grind [Adj.ne, Adj.symm, mem_neighborFinset, degree]
          rw [this, sum_union hdisj]; clear this
          have : ∑ x ∈ {u, v, w}, f G AB x = f G AB u + f G AB v + f G AB w := by grind [Adj.ne]
          rw [this, fA3 hAu hdu, fA3 hAv hdv, fA3 hAw hdw]; clear this
          suffices ∑ x ∈ {x, y, z, x'}, f G AB x ≤ 5 / 2 by linarith
          have : ∑ x ∈ {x, y, z, x'}, f G AB x = f G AB x + f G AB y + f G AB z + f G AB x' := by
            refine sum_quadruplet hxney ?_ hxx'.ne ?_ ?_ ?_
            · grind only
            · grind only
            · refine ne_of_ne_congr (G.Adj x ·) ?_
              simp only [hxy, hxx', ne_eq, eq_iff_iff, iff_true, not_false_eq_true]
            · refine ne_of_ne_congr (G.Adj w ·) ?_
              simp only [hwt, ne_eq, eq_iff_iff, iff_false, Decidable.not_not]
              exact mem_neighborFinset .. |>.mp <| by grind
          rw [this, fA2 hAx hdx, fA2 hAy hdy, fA3 hAx' hdx']; clear this
          suffices f G AB z ≤ 3 / 5 by linarith
          obtain ⟨hAz, hdz⟩ := by
            refine h' z (hG <| G.mem_support.mpr ⟨w, ?_⟩)
            exact Adj.symm <| mem_neighborFinset .. |>.mp <| by grind
          rcases hdz with hdz | hdz
          · rw [fA2 hAz hdz]
          · rw [fA3 hAz hdz]
            linarith
      else
        have hN2card : 2 ≤ #(G.N2_of_Finset {x, v, u}) := by
          by_contra
          have : G.N2_of_Finset {x, v, u} = {z} := by
            refine Eq.symm <| eq_of_subset_and_ge_card ?_ ?_
            · refine singleton_subset_iff.mpr ?_
              refine mem_N2_of_Finset_iff'.mpr ⟨?_, ?_⟩
              · rw [closed_neighborFinset_of_triplet_eq, hNx, hNv, hNu]
                suffices z ∉ ({u, v, w} : Finset _) ∧ z ∉ ({x, y, x'} : Finset _) by
                  grind
                refine ⟨?_, ?_⟩
                · grind [ne_of_mem_neighborFinset, degree]
                · suffices z ≠ x' by grind
                  exact fun hzeqx' ↦ (hzeqx' ▸ hwt) <| mem_neighborFinset .. |>.mp <| by grind
              · refine ⟨u, by grind, w, ?_, ?_, huw.symm⟩
                · grind [Adj.ne, degree]
                · exact Adj.symm <| mem_neighborFinset .. |>.mp <| by grind
            · exact card_singleton w ▸ (Nat.le_of_lt_succ <| not_le.mp this)
          obtain ⟨x'', hx''x', hx''⟩ :
              ∃ x'' ∈ G.neighborFinset x', x'' ∉ ({u, v, w, x, y, z} : Finset _) := by
            exact Set.not_subset.mp hNx'
          suffices x'' ∈ G.N2_of_Finset {x, v, u} by grind
          refine mem_N2_of_Finset_iff'.mpr ⟨?_, ?_⟩
          · rw [closed_neighborFinset_of_triplet_eq, hNx, hNv, hNu]
            suffices x'' ≠ x' by grind
            exact ne_of_mem_neighborFinset hx''x'
          · refine ⟨x, by grind, x', by grind, ?_, hxx'.symm⟩
            exact Adj.symm <| mem_neighborFinset .. |>.mp hx''x'
        refine Claim2' {x, v, u} (insert_nonempty ..) ?_ ?_ hG ih ?_ ?_
        · clear * -hAu hAv hAx
          grind [AB.mem_iff, AB.mem_toFinset.mp]
        · clear * -hAu hAv hAx
          exact respects_of_A <| by grind
        · refine InducesForestOfStars_triplet_of_nonadj ?_
          refine not_iff_not.mpr (mem_neighborFinset ..) |>.mp <| by grind [Adj.ne]
        · have hxv : x ≠ v := by
            refine ne_of_ne_congr (G.degree ·) ?_
            simp only [hdx, hdv, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
          rw [card_triplet' hxv hux.ne' huv.ne', Nat.cast_three]
          have : ∑ z ∈ G.closed_neighborFinset_of_Finset {x, v, u}, f G AB z
              = f G AB u + f G AB v + f G AB w + f G AB x + f G AB y + f G AB x' := by
            have hdisj : Disjoint ({u, v, w} : Finset _) {x, y, x'} := by
              refine disjoint_iff_inter_eq_empty.mpr ?_
              grind [Adj.ne, degree]
            rw [closed_neighborFinset_of_triplet_eq, hNx, hNv, hNu, _union_eq'', sum_union hdisj]
            grind [Adj.ne, degree]
          simp only [this, fA3 hAu hdu, fA3 hAv hdv, fA3 hAw hdw, fA2 hAx hdx, fA2 hAy hdy,
            fA3 hAx' hdx']
          have : ∑ z ∈ G.N2_of_Finset {x, v, u}, 1 / 10
              ≤ ∑ z ∈ G.N2_of_Finset {x, v, u}, γ G AB z := by
            refine sum_le_sum fun z hz ↦ ?_
            obtain ⟨hAz, hdz⟩ :=
              h' _ (hG <| G.degree_pos_iff_mem_support _ |>.mp <| one_le_degree_of_mem_N2 hz)
            rcases hdz with hdz | hdz
            · simp only [γA2 hAz hdz]
              linarith
            · simp only [γA3 hAz hdz, le_refl]
          suffices 2 * (1 / 10) ≤ ∑ z ∈ G.N2_of_Finset {x, v, u}, γ G AB z by linarith
          refine le_trans ?_ this
          simp only [sum_const']
          refine mul_le_mul_of_nonneg ?_ (le_refl _) zero_le_two ?_
          · rw [← Nat.cast_two, Nat.cast_le]
            exact hN2card
          · exact zero_le_one_tenth

private lemma _Claim10 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) (u v w : V) (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hfwv : f G AB w ≤ f G AB v) (hfvu : f G AB v ≤ f G AB u)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    (G.degree u = 3 ∧ G.degree v = 3 ∧ G.degree w = 3
        ∧ (∀ x y, x ∈ G.closed_neighborFinset_of_Finset {u, v, w}
            → y ∈ G.closed_neighborFinset_of_Finset {u, v, w}
            → G.degree x = 2 → G.degree y = 2 → x = y))
      ∨ Objective G AB := by
  match _A3 hG huv hvw huw hfwv hfvu ih with
  | Or.inr h => exact Or.inr h
  | Or.inl ⟨hdu, hdv, hdw⟩ =>  ?_
  cases Claim6'  hG ih with
  | inr h => exact Or.inr h
  | inl h => ?_
  have h' : ∀ x ∈ AB.toFinset, AB.A x ∧ (G.degree x = 2 ∨ G.degree x = 3) := by grind
  have hABu : u ∈ AB.toFinset := hG <| G.mem_support.mpr ⟨v, huv⟩
  have hABv : v ∈ AB.toFinset := hG <| G.mem_support.mpr ⟨w, hvw⟩
  have hABw : w ∈ AB.toFinset := hG <| G.mem_support.mpr ⟨v, hvw.symm⟩
  have hAu : AB.A u := h' _ hABu |>.1
  have hAv : AB.A v := h' _ hABv |>.1
  have hAw : AB.A w := h' _ hABw |>.1
  simp only [hdu, hdv, hdw, true_and]
  refine forall_or_right.mp fun x ↦ ?_
  refine forall_or_right.mp fun y ↦ ?_
  if H : (x ∈ G.closed_neighborFinset_of_Finset {u, v, w} →
      y ∈ G.closed_neighborFinset_of_Finset {u, v, w} →
      G.degree x = 2 → G.degree y = 2 → x = y) then
    exact Or.inl H
  else
    simp only [Classical.not_imp] at H
    obtain ⟨hx, hy, hdx, hdy, hxney⟩ := H
    have hAx : AB.A x := h' _ (mem_of_subset_of_mem_closed_neighborhood hG (by grind) hx) |>.1
    have hAy : AB.A y := h' _ (mem_of_subset_of_mem_closed_neighborhood hG (by grind) hy) |>.1
    refine Or.inr ?_
    have Hx : x ∉ ({u, v, w} : Finset _) := by grind
    have Hy : y ∉ ({u, v, w} : Finset _) := by grind
    simp only [mem_closed_neighborFinset_iff, Hx, false_or] at hx
    obtain ⟨x', hx', hx'x⟩ := hx
    simp only [mem_closed_neighborFinset_iff, Hy, false_or] at hy
    obtain ⟨y', hy', hy'y⟩ := hy
    have hdx' : G.degree x' = 3 := by grind
    have hdy' : G.degree y' = 3 := by grind
    have hAx' : AB.A x' :=
      h' _ (hG <| (G.degree_pos_iff_mem_support x').mp <| hdx' ▸ three_pos) |>.1
    have hAy' : AB.A y' :=
      h' _ (hG <| (G.degree_pos_iff_mem_support y').mp <| hdy' ▸ three_pos) |>.1
    have hd'x : 2 ≤ G.degree x := by linarith
    obtain ⟨z', hz'⟩ : ∃ z', z' ∈ ({u, v, w} : Finset _) \ {x', y'} := by
      refine nonempty_def.mp <| card_ne_zero.mp ?_
      suffices 1 ≤ #({u, v, w} \ {x', y'}) by
        exact Nat.ne_zero_of_lt this
      have : #{u, v, w} = 3 := by grind [Adj.ne]
      rw [card_sdiff, this]
      suffices #({x', y'} ∩ {u, v, w}) ≤ 2 by
        lia
      exact le_trans (card_le_card inter_subset_left) card_le_two
    have : #{u, v, w} = 3 := by grind [Adj.ne]
    suffices x' ≠ y' by
      have Heq : ({u, v, w} : Finset _) = {x', y', z'} := by
        refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_ <;> grind
      refine _Claim10_ hG x' y' z' x y ?_ ?_ ?_ hx'x hy'y hdx' hdy' ?_ hdx hdy hxney
          (Heq ▸ Hx) (Heq ▸ Hy) h' ih
      <;> grind [Adj.symm]
    intro heq
    suffices {u, v, w, x, y} ⊆ G.closed_neighborFinset_of_Finset {x'} by
      have := card_le_card this
      rw [@card_closed_neighborFinset_singleton V G _ _ x', hdx'] at this
      grind
    grind [mem_closed_neighborFinset_iff, Adj.symm]

lemma Claim10 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    (G.degree u = 3 ∧ G.degree v = 3 ∧ G.degree w = 3
        ∧ (∀ x y, x ∈ G.closed_neighborFinset_of_Finset {u, v, w}
            → y ∈ G.closed_neighborFinset_of_Finset {u, v, w}
            → G.degree x = 2 → G.degree y = 2 → x = y))
      ∨ Objective G AB := by
  obtain ⟨hunev, hunew, hvnew⟩ : u ≠ v ∧ u ≠ w ∧ v ≠ w := by grind [Adj.ne]
  have : #{u, v, w} = 3 := by grind
  obtain ⟨x, y, z, h, hfxy, hfyz⟩ := sorted_triplet (f G AB ·) u v w
  have : #{x, y, z} = 3 := this ▸ congrArg Finset.card h
  obtain ⟨hxney, hynez, hxnez⟩ : x ≠ y ∧ y ≠ z ∧ x ≠ z := by grind [degree, Adj.ne, Adj.symm]
  have := by
    have : x ∈ ({u, v, w} : Finset _) := by grind
    have : y ∈ ({u, v, w} : Finset _) := by grind
    have : z ∈ ({u, v, w} : Finset _) := by grind
    refine _Claim10 hG z y x ?_ ?_ ?_ hfxy hfyz ih <;> grind [Adj.symm]
  have heq' : ({z, y, x} : Finset _) = {u, v, w} := by grind
  rw [← heq']
  cases this with
  | inr h => exact Or.inr h
  | inl h => ?_
  have hd : ∀ v' ∈ ({u, v, w} : Finset _), G.degree v' = 3 := by grind
  refine Or.inl <| by grind

end Bipartition
end AB
end CaroWeiType
