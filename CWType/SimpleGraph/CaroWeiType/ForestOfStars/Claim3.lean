import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim0
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim1
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim2
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Lemmas

open SimpleGraph
open Finset

namespace CaroWeiType
namespace AB
namespace Bipartition

variable {V : Type} [Fintype V] [DecidableEq V]

private lemma Claim3_0 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {v : V} (hv : v ∈ AB) (hdv : G.degree v = 0)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  obtain ⟨s, hs, hsf, hsresp, hscard⟩ := by
    refine ih G (AB \ {v}) (deleteIncidenceSet_of_isolated hdv ▸ hsupp_mono hG) ?_
    refine sdiff_card AB <| not_iff_not.mpr singleton_inter_eq_empty_iff |>.mpr <| not_not_intro ?_
    exact AB.mem_toFinset.mp hv
  have hscapv : s ∩ {v} = ∅ := by
    rw [AB.sdiff_toFinset] at hs
    refine inter_singleton_of_notMem fun hvs ↦ ?_
    exact false_of_ne <| notMem_singleton.mp <| mem_sdiff.mp (hs hvs) |>.2
  refine ⟨s ∪ {v}, ?_, ?_, ?_,?_⟩
  · intro u hu
    rcases mem_union.mp hu with hus | huv
    · exact mem_sdiff.mp ((AB.sdiff_toFinset ▸ hs) hus) |>.1
    · exact AB.mem_toFinset.mp <| mem_singleton.mp huv ▸ hv
  · exact InducesForestOfStars_union_singleton hdv hsf
  · intro u hu hBu w hw hwu
    have hunev : u ≠ v := by
      intro heq
      have : 1 ≤ 0 := hdv ▸ heq ▸ one_le_degree_of_adj' hwu
      linarith
    have hwnev : w ≠ v := by
      intro heq
      have : 1 ≤ 0 := hdv ▸ heq ▸ one_le_degree_of_adj hwu
      linarith
    simp only [union_singleton, mem_insert, hunev, hwnev, false_or] at hu hw
    have := hsresp u hu ⟨hBu, notMem_singleton.mpr hunev⟩ w hw hwu
    refine ⟨this.1.1, le_of_eq_of_le ?_ this.2⟩
    refine degree_in_union_eq ?_
    refine singleton_inter_of_notMem ?_
    intro h
    have := hdv ▸ one_le_degree_of_mem_neighborFinset' h
    linarith
  · have hNv : G.neighborFinset v = ∅ := card_eq_zero.mp hdv
    have := by
      refine @sum_sdiff_singleton_eval _ _ _ G _ AB AB.toFinset v (AB.mem_toFinset.mp hv) ?_
      exact hNv ▸ empty_subset _
    simp only [eval, this] at hscard ⊢
    calc _
      _ ≤ #s + f G AB v := by
        simp only [hNv, sum_empty, add_zero]
        refine add_le_add (le_of_eq_of_le ?_ hscard) (le_refl _)
        refine AB.sdiff_toFinset ▸ sum_congr rfl fun x hx ↦ f_congr_degree _ _ _ ?_
        exact degree_eq_of_eq <| deleteIncidenceSet_of_isolated hdv
    refine le_of_eq ?_
    rw [f_eq_one_of_degree_eq_zero G hv hdv, card_union, card_singleton, hscapv, card_empty]
    simp only [tsub_zero, Nat.cast_add, Nat.cast_one]

private lemma Claim3_1_of_A {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} (hdv : G.degree v = 1)
    {AB : Bipartition V} [AB.Decidable] (hG : G.support ⊆ AB.toFinset) (hAv : AB.A v)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  have hNv := degree_eq_one_iff_existsUnique_adj.mp hdv
  obtain ⟨w, hw⟩ := hNv |>.exists
  have hNv' : G.neighborFinset v = {w} := by
    ext u
    simp only [mem_neighborFinset, mem_singleton]
    exact ⟨fun hvu ↦ hNv.unique hvu hw, fun heq ↦ heq ▸ hw⟩
  have hABv : v ∈ AB.toFinset := AB.mem_toFinset.mp <| Or.inl hAv
  obtain ⟨s, hs, hsf, hsresp, hscard⟩ := by
    refine ih (G.deleteIncidencesOf {v}) (AB \ {v} |>.demote w) ?_ ?_
    · rw [← demote_toFinset_eq]
      exact hsupp_mono hG
    · rw [← card_demote_eq_card]
      refine sdiff_card AB ?_
      exact not_iff_not.mpr singleton_inter_eq_empty_iff |>.mpr <| Decidable.not_not.mpr <| hABv
  have hscapv : s ∩ {v} = ∅ := by
    rw [← demote_toFinset_eq, AB.sdiff_toFinset] at hs
    refine inter_singleton_of_notMem fun hvs ↦ ?_
    exact false_of_ne <| notMem_singleton.mp <| mem_sdiff.mp (hs hvs) |>.2
  have hvnotins : v ∉ s := inter_singleton_eq_empty_iff.mp hscapv
  have hsAB : s ⊆ AB.toFinset :=
    fun x hx ↦  mem_sdiff.mp (AB.sdiff_toFinset ▸ (AB \ {v}).demote_toFinset_eq ▸ hs hx) |>.1
  have Hw : ((AB \ {v}).demote w).B w := by
    refine demote_finset_B_of_mem _ ?_ (mem_singleton.mpr rfl)
    refine mem_sdiff_iff _ _ |>.mpr ⟨?_, notMem_singleton.mpr hw.ne'⟩
    exact AB.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨v, hw.symm⟩
  refine ⟨s ∪ {v}, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rcases mem_union.mp hu with hus | huv
    · rw [← demote_toFinset_eq, AB.sdiff_toFinset] at hs
      exact mem_sdiff.mp (hs hus) |>.1
    · exact AB.mem_toFinset.mp <| mem_singleton.mp huv ▸ AB.mem_toFinset.mpr hABv
  · if hd'v : G.degree_in s v = 0 then
      refine InducesForestOfStars_union_isolated hd'v ?_
      exact InducesForestOfStars_graph_mono' hscapv hsf
    else if hd'w : G.degree_in s w = 1 then
      have H : (G.neighborFinset v ∩ s) = G.neighborFinset v := by
        refine eq_of_subset_and_eq_card inter_subset_left ?_
        rw [← degree_in, ← degree, hdv]
        refine le_antisymm ?_ (Nat.one_le_iff_ne_zero.mpr hd'v)
        exact hdv ▸ degree_in_le_degree
      have hws : w ∈ s := by
        suffices w ∈ G.neighborFinset v by exact mem_inter.mp (H ▸ this) |>.2
        exact hNv' ▸ mem_singleton.mpr rfl
      obtain ⟨u, hu⟩ := Finset_singleton_unique hd'w |>.exists
      have huw : G.Adj u w := Adj.symm <| mem_neighborFinset .. |>.mp <| mem_inter.mp hu |>.1
      have hunev : u ≠ v := ne_of_mem_of_not_mem (mem_inter.mp hu |>.2) hvnotins
      have hd'u : G.degree_in s u = 1 := by
        refine le_antisymm ?_ ?_
        · refine le_of_eq_of_le ?_ <| hsresp w hws Hw u (mem_inter.mp hu |>.2) ?_ |>.2
          · refine Eq.symm <| degree_in_deleteIncidencesOf s {v} ?_ ?_
            · exact inter_comm s _ ▸ hscapv
            · exact notMem_singleton.mpr <| ne_of_mem_of_not_mem (mem_inter.mp hu |>.2) hvnotins
          · refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ huw
            · exact notMem_singleton.mpr hunev
            · exact notMem_singleton.mpr <| ne_of_mem_of_not_mem hws hvnotins
        · refine one_le_card.mpr ⟨w, mem_inter.mpr ⟨?_, hws⟩⟩
          exact mem_neighborFinset_symm <| mem_inter.mp hu |>.1
      refine InducesForestOfStars_union_leaf_on_K2 hd'u ?_ hd'w hw huw ?_ hws hunev ?_
      · rw [← card_singleton w]
        refine congrArg Finset.card ?_
        ext z
        simp only [hNv', mem_inter, mem_singleton, and_iff_left_iff_imp]
        exact (· ▸ hws)
      · exact mem_inter.mp hu |>.2
      · exact InducesForestOfStars_graph_mono' hscapv hsf
    else
      refine InducesForestOfStars_union_leaf hdv hw hd'w ?_
      exact InducesForestOfStars_graph_mono' hscapv hsf
  · intro u hu hBu u' hu' hu'u
    have hunev : u ≠ v := by
      refine ne_of_ne_congr AB.A ?_
      simp only [hAv, ne_eq, eq_iff_iff, iff_true, not_A_of_B hBu, not_false_eq_true]
    simp only [union_singleton, mem_insert, hunev, false_or] at hu hu'
    rcases hu' with hu' | hu'
    · subst hu'
      exact ⟨hAv, le_of_le_of_eq degree_in_le_degree hdv⟩
    · have hu'nev : u' ≠ v := ne_of_mem_of_not_mem hu' hvnotins
      obtain ⟨hA', hd'⟩ := by
        refine hsresp u hu (demote_B_of_B (AB \ {v}) ⟨hBu, notMem_singleton.mpr hunev⟩) u' hu' ?_
        refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ hu'u
        · exact notMem_singleton.mpr hu'nev
        · exact notMem_singleton.mpr hunev
      refine ⟨hA'.1.1, le_of_eq_of_le ?_ hd'⟩
      have : G.degree_in (s ∪ {v}) u' = G.degree_in s u' := by
        refine degree_in_union_eq <| singleton_inter_of_notMem ?_
        refine not_mem_neighborFinset_symm <| hNv' ▸ ?_
        refine notMem_singleton.mpr ?_
        refine ne_of_ne_congr ((AB \ {v}).demote w).A ?_
        simp only [hA', ne_eq, eq_iff_iff, true_iff, not_A_of_B Hw, not_false_eq_true]
      rw [this]
      refine Eq.symm <| degree_in_deleteIncidencesOf s {v} (inter_comm s _ ▸ hscapv) ?_
      exact notMem_singleton.mpr hu'nev
  · have Hw : {w} ⊆ AB.toFinset :=
      singleton_subset_iff.mpr <| mem_def.mpr <| hG <| G.mem_support.mpr ⟨v, hw.symm⟩
    refine le_of_eq_of_le (sum_eq_sum_demote_finset _ _ Hw) ?_
    have : G.neighborFinset v ⊆ AB.toFinset :=
      neighborFinset_subset_support.trans <| Set.toFinset_subset.mpr hG
    rw [sum_singleton, sum_sdiff_singleton_eval hABv this, hNv', sum_singleton]
    calc _
      _ = ∑ x ∈ AB.toFinset \ {v}, f (G.deleteIncidencesOf {v}) (AB.demote_finset {w} \ {v}) x
          - f (G.deleteIncidencesOf {v}) (AB.demote_finset {w} \ {v}) w
          + f G (AB.demote_finset {w}) v + f G AB w := by
        linarith
      _ ≤ #s - f (G.deleteIncidencesOf {v}) (AB.demote_finset {w} \ {v}) w
          + f G (AB.demote_finset {w}) v + f G AB w := by
        simp only [add_le_add_iff_right, sub_le_sub_iff_right]
        refine le_of_eq_of_le ?_ hscard
        simp only [eval]
        rw [← demote_toFinset_eq, sdiff_toFinset, ← sdiff_demote_eq_demote_sdiff]
    rw [card_union, hscapv, card_empty, card_singleton, tsub_zero, Nat.cast_add, Nat.cast_one]
    suffices f G AB w - f (G.deleteIncidencesOf {v}) (AB.demote_finset {w} \ {v}) w
          ≤ 1 / (6 : ℝ)  by
      have H : f G (AB.demote w) v = 5 / 6 := by
        have hA'v : (AB.demote w).A v := ⟨hAv, notMem_singleton.mpr hw.ne⟩
        simp only [f, hA'v, ↓reduceDIte, fA, hdv, one_ne_zero, ↓reduceIte]
      linarith
    have hB'w : (AB.demote w \ {v}).B w := by
      refine ⟨?_, notMem_singleton.mpr hw.ne'⟩
      exact demote_B_self _ <| AB.mem_toFinset.mpr <| singleton_subset_iff.mp Hw
    have hd'w : (G.deleteIncidencesOf {v}).degree w = G.degree w - 1 := by
      have : {v} ⊆ G.neighborFinset w :=
        singleton_subset_iff.mpr <| mem_neighborFinset .. |>.mpr hw.symm
      rw [degree_deleteIncidencesOf_neighbor _ this, card_singleton, add_tsub_cancel_right]
    rcases AB.mem_toFinset.mpr <| singleton_subset_iff.mp Hw with hA | hB
    · simp only [f, hA, not_A_of_B, hB'w, ↓reduceDIte, hd'w, fB]
      nth_rw 3 [← Nat.cast_one]
      have : G.degree w - 1 + 1 = G.degree w := Nat.sub_add_cancel <| one_le_degree_of_adj' hw
      rw [← Nat.cast_add, this, fA]
      split_ifs
      · linarith [one_le_degree_of_adj' hw]
      · rename_i h
        rw [h, ← Nat.cast_one, div_self]
        · linarith
        · rw [Nat.cast_one]
          exact one_ne_zero
      · rename_i h
        rw [h, Nat.cast_two]
        linarith
      · have : G.degree w = 3 ∨ G.degree w = 4 ∨ G.degree w = 5 ∨ 6 ≤ G.degree w := by lia
        rcases this with h | h | h | h
        · rw [h]; linarith
        · rw [h]; linarith
        · rw [h]; linarith
        · calc _
            _ ≤ 2 / (G.degree w : ℝ) - 1 / (G.degree w : ℝ) := by
              simp only [tsub_le_iff_right, sub_add_cancel]
              refine div_le_div₀ zero_le_two (le_refl _) ?_ le_add_one
              rw [← Nat.cast_zero, Nat.cast_lt]
              linarith
            _ ≤ 1 / (G.degree w : ℝ) := by
              lia
          refine one_div_le_one_div_of_le six_pos ?_
          have : (6 : ℝ) = ((6 : ℕ) : ℝ) := rfl
          rw [this, Nat.cast_le]
          exact h
    · simp only [f, hB, hB'w, not_A_of_B, ↓reduceDIte, hd'w]
      refine le_trans ?_ (by linarith : 0 ≤ 1 / (6 : ℝ))
      exact tsub_nonpos.mpr <| fB_decreasing <| Nat.sub_le ..

private lemma Claim3_1_of_B {G : SimpleGraph V} [DecidableRel G.Adj]
    {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {v : V} (hBv : AB.B v) (hdv : G.degree v = 1)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  have hNv := degree_eq_one_iff_existsUnique_adj.mp hdv
  obtain ⟨w, hw⟩ := hNv |>.exists
  have hNv' : G.neighborFinset v = {w} := by
    ext u
    simp only [mem_neighborFinset, mem_singleton]
    exact ⟨fun hvu ↦ hNv.unique hvu hw, fun heq ↦ heq ▸ hw⟩
  have hABv : v ∈ AB.toFinset := AB.mem_toFinset.mp <| Or.inr hBv
  if hfw : f G AB w ≤ 1 / 2 then
    refine Corollary1 hG hw.symm ih ?_
    simp only [γ, hBv, not_A_of_B, ↓reduceDIte, hdv, fB]
    linarith
  else
    rcases AB.mem_toFinset.mpr <| mem_def.mpr <| hG <| G.mem_support.mpr ⟨v, hw.symm⟩ with hA | hB
    · have : G.degree w < 3 := by
        have : fA 3 = 1 / 2 := by grind only [fA]
        refine fA_decreasing' (this ▸ ?_)
        refine lt_of_lt_of_eq (not_le.mp hfw) ?_
        simp only [f, hA, ↓reduceDIte]
      if hdw : G.degree w = 1 then
        have hNw := degree_eq_one_iff_existsUnique_adj.mp hdw
        have hNw' : G.neighborFinset w = {v} := by
          ext u
          simp only [mem_neighborFinset, mem_singleton]
          exact ⟨fun hwu ↦ hNw.unique hwu hw.symm, fun heq ↦ heq ▸ hw.symm⟩
        obtain ⟨s, hs, hsf, hsresp, hscard⟩ := by
          refine ih (G.deleteIncidencesOf {v, w}) (AB \ {v, w}) (hsupp_mono hG) ?_
          refine sdiff_card AB <| nonempty_iff_ne_empty.mp ⟨v, ?_⟩
          simp only [mem_inter, mem_singleton, inter_insert_of_mem, ne_eq, insert_ne_empty,
            not_false_eq_true, mem_of_singleton_inter_ne_emty, true_and]
          exact AB.mem_toFinset.mp <| Or.inr hBv
        rw [sdiff_toFinset] at hs
        refine ⟨s ∪ {v, w}, ?_, ?_, ?_, ?_⟩
        · refine union_subset hs fun u hu ↦ AB.mem_toFinset.mp ?_
          grind [AB.mem_iff]
        · refine InducesForestOfStars_union_disjoint_neighborhoods ?_ ?_ ?_
          · exact InducesForestOfStars_graph_mono' (disjoint_of_sdiff hs) hsf
          · exact InducesForestOfStars_pair
          · intro x hx y hy hxy
            simp only [mem_insert, mem_singleton] at hy
            rcases hy with hy | hy
            · rw [hy] at hxy
              have := hNv.unique hw hxy.symm
              grind
            · rw [hy] at hxy
              have := hNw.unique hw.symm hxy.symm
              grind
        · intro x hx hBx y hy hyx
          simp only [union_insert, union_singleton, mem_insert] at hx hy
          rcases hx with hx | hx | hx
          · have hy : y = w :=
              mem_singleton.mp <| hNv' ▸ mem_neighborFinset .. |>.mpr <| hx ▸ hyx.symm
            subst hy hx
            refine ⟨hA, ?_⟩
            rw [degree_in_union_of_empty_inter]
            · suffices G.degree_in s y = 0 by
                rw [this, zero_add]
                refine degree_in_subpair_le_one_of_mem ?_ ?_ <;> grind
              exact card_eq_zero.mpr (by grind)
            · grind
          · exact not_A_of_B hBx (hx ▸ hA) |>.elim
          · have hy : y ∈ s := by
              rcases hy with hy | hy | hy
              · have : w ≠ x := Ne.symm <| ne_of_mem_of_not_mem hx (by grind)
                exact this (eq_of_degree_eq_one hw (hy ▸ hyx) hdv) |>.elim
              · have : v ≠ x := Ne.symm <| ne_of_mem_of_not_mem hx (by grind)
                exact this (eq_of_degree_eq_one hw.symm (hy ▸ hyx) hdw) |>.elim
              · exact hy
            obtain ⟨hA'y, hd'y⟩ := by
              refine hsresp x hx ⟨hBx, by grind⟩ y hy ?_
              refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ hyx <;> grind
            refine ⟨hA'y.1, le_of_eq_of_le ?_ hd'y⟩
            rw [degree_in_union_of_empty_inter]
            · suffices G.degree_in {v, w} y = 0 by
                rw [this, add_zero]
                refine Eq.symm <| degree_in_deleteIncidencesOf _ _ ?_ ?_ <;> grind
              refine card_eq_zero.mpr (inter_comm _ {v, w} ▸ ?_)
              ext u
              simp only [mem_inter, mem_insert, mem_singleton, mem_neighborFinset, notMem_empty,
                iff_false, not_and]
              intro hu hyu
              rcases hu with hu | hu
              · have : y ≠ w := ne_of_mem_of_not_mem hy (by grind)
                exact this <| hNv.unique (hu ▸ hyu.symm) hw
              · have : y ≠ v := ne_of_mem_of_not_mem hy (by grind)
                exact this <| hNw.unique (hu ▸ hyu.symm) hw.symm
            · grind
        · have : s ∩ {v, w} = ∅ := by grind
          rw [card_union, card_pair hw.ne, this, card_empty, tsub_zero, Nat.cast_add, Nat.cast_two]
          calc _
            _ = ∑ x ∈ AB.toFinset \ {v, w}, f G AB x + ∑ x ∈ {v, w}, f G AB x :=
              Eq.symm <| sum_sdiff <| by grind [mem_iff, AB.mem_toFinset.mp]
            _ ≤ ∑ x ∈ AB.toFinset \ {v, w}, f G AB x + ∑ x ∈ {v, w}, 1 :=
              add_le_add_iff_left _ |>.mpr <| sum_le_sum fun x hx ↦ f_le_one
            _ = ∑ x ∈ AB.toFinset \ {v, w}, f G AB x + 2 := by
              simp only [sum_const, nsmul_eq_mul, mul_one, add_right_inj]
              rw [← Nat.cast_two, Nat.cast_inj]
              exact card_pair hw.ne
          simp only [add_le_add_iff_right]
          refine le_of_eq_of_le ?_ hscard
          rw [eval, AB.sdiff_toFinset]
          refine sum_congr rfl fun x hx ↦ f_congr ?_ ?_
          · refine degree_eq_deleteIncidencesOf_degree_of_inter_neighborhood_empty ?_ ?_
            · exact mem_sdiff.mp hx |>.2
            · ext y
              simp only [mem_inter, mem_insert, mem_singleton, mem_neighborFinset, notMem_empty,
                iff_false, not_and]
              intro hy hxy
              rcases hy with hy | hy
              · have : w ≠ x := by grind
                exact this <| eq_of_degree_eq_one hw (hy ▸ hxy.symm) hdv
              · have : v ≠ x := by grind
                exact this <| eq_of_degree_eq_one hw.symm (hy ▸ hxy.symm) hdw
          · grind [mem_iff, sdiff]
      else
        have hdw : G.degree w = 2 := by grind [one_le_degree_of_adj' hw]
        obtain ⟨u, hu, hvneu⟩ := Finset_get_other (le_of_eq hdw.symm) v
        have hfu : f G AB u ≤ 5 / 6 := f_le_five_sixths_of_one_le_degree
            <| one_le_degree_of_adj' <| mem_neighborFinset .. |>.mp hu
        refine Corollary2 {v, w} pair_nonempty ?_ (respects_pair' hA) hG ih
            InducesForestOfStars_pair ?_
        · refine fun z hz ↦ AB.mem_toFinset.mp ?_
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with hz | hz
          · exact Or.inr (hz ▸ hBv)
          · exact Or.inl (hz ▸ hA)
        · simp only [card_pair hw.ne, Nat.cast_ofNat, ge_iff_le]
          have hNF : G.closed_neighborFinset_of_Finset {v, w} = {v, w, u} := by
            suffices hNw' : G.neighborFinset w = {v, u} by
              rw [closed_neighborFinset_of_pair_eq, hNv', hNw']
              grind
            refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
            · grind [mem_neighborFinset, Adj.symm]
            · rw [card_pair hvneu, ← degree, hdw]
          rw [hNF]; clear hNF
          suffices f G AB v + f G AB w ≤ 7 / 6 by grind
          simp only [f, hBv, hA, not_A_of_B, ↓reduceDIte, hdv, hdw, fA, two_ne_zero,
            Nat.add_one_add_one_ne_one, ↓reduceIte, fB, Nat.cast_one]
          linarith
    · refine hfw ?_ |>.elim
      have : fB 1 = 1 / 2 := by
        simp only [fB, Nat.cast_one]
        linarith
      simp only [f, hB, not_A_of_B, ↓reduceDIte, ← this]
      refine fB_decreasing ?_
      exact one_le_degree_of_adj' hw

private lemma Claim3_1 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {v : V} (hv : v ∈ AB) (hdv : G.degree v = 1)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  have hABv : v ∈ AB.toFinset := AB.mem_toFinset.mp hv
  rcases hv with hA | hB
  · exact Claim3_1_of_A hdv hG hA ih
  · exact Claim3_1_of_B hG hB hdv ih

lemma Claim3 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {v : V} (hv : v ∈ AB) (hdv : G.degree v ≤ 1)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdv with hd0 | hd1
  · exact Claim3_0 hG hv hd0 ih
  · exact Claim3_1 hG hv hd1 ih

lemma Claim3' {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    (∀ v ∈ AB, 2 ≤ G.degree v) ∨ Objective G AB := by
  if h : ∀ v ∈ AB, 2 ≤ G.degree v then
    exact Or.inl h
  else
    simp only [not_forall, not_le] at h
    obtain ⟨v, hv, hdv⟩ := h
    exact Or.inr <| Claim3 hG hv (Nat.le_of_lt_succ hdv) ih

end Bipartition
end AB
end CaroWeiType
