import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim4
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim5
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Lemmas

open SimpleGraph
open Finset

namespace CaroWeiType
namespace AB
namespace Bipartition

variable {V : Type} [Fintype V] [DecidableEq V]

private lemma _Claim6 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {u v w : V} (hvw : G.Adj v w) (huw : G.Adj u w)
    (hBv : AB.B v) (hdv : G.degree v = 2) (hAw : AB.A w) (hdw : G.degree w = 3)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    (1 / 10 ≤ γ G AB u ∧ f G AB u ≤ 1 / 2) ∨ Objective G AB := by
  match Claim4' hG ih, Corollary4 hG ih with
  | Or.inr h, _ => exact Or.inr h
  | _, Or.inr h => exact Or.inr h
  | Or.inl h, Or.inl h' => ?_
  have hu : u ∈ AB.toFinset := hG <| G.mem_support.mpr ⟨w, huw⟩
  rcases h _ hu with ⟨hAu, hdu⟩ | ⟨hAu, hdu⟩ | ⟨hBu, hdu⟩
  · refine Or.inr <| Claim1 (Or.inl hAw) hG ih ?_
    obtain ⟨z, hz, hunez, hwnez⟩ := Finset_get_other_other (le_of_eq <| hdw.symm) u v
    suffices f G AB w ≤ γ G AB u + γ G AB v + γ G AB z by
      refine le_trans this ?_
      suffices {u, v, z} ⊆ G.neighborFinset w by
        refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg this fun _ _ _ ↦ γ_nonneg)
        have : u ≠ v := by
          refine ne_of_ne_congr AB.A ?_
          simp only [hAu, hBv, not_A_of_B]
          exact true_ne_false
        grind
      grind [mem_neighborFinset, Adj.symm]
    simp only [fA3 hAw hdw, γB2 hBv hdv, γA2 hAu hdu]
    suffices 1 / 10 ≤ γ G AB z by linarith
    refine h' _ ?_ |>.2.2.1
    refine hG <| G.mem_support.mpr ⟨w, Adj.symm <| mem_neighborFinset .. |>.mp hz⟩
  · refine Or.inl ?_
    simp only [γA3 hAu hdu, le_refl,fA3 hAu hdu, true_and]
  · refine Or.inl ?_
    simp only [γB2 hBu hdu, fB2 hBu hdu]
    refine ⟨?_, ?_⟩ <;> linarith

lemma Claim6 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {v : V} (hBv : AB.B v)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  cases Claim4' hG ih with
  | inr h => exact h
  | inl h => ?_
  have hdv : G.degree v = 2 := by
    have hobj := h v (AB.mem_toFinset.mp <| Or.inr hBv)
    simp only [hBv, not_A_of_B, false_and, false_or, true_and] at hobj
    exact hobj
  obtain ⟨u, w, hne, hNv⟩ := Finset_card_eq_two_iff _ hdv
  obtain ⟨w, u, H, hfuw⟩ := sorted_pair (f G AB ·) u w
  have hne : u ≠ w := by grind [pair_eq]
  rw [← H] at hNv; clear H
  if hfv : γ G AB u + γ G AB w < f G AB v then
    have hu : u ∈ AB.toFinset :=
      hG <| G.mem_support.mpr ⟨v, Adj.symm <| mem_neighborFinset .. |>.mp <| by grind⟩
    have hv : v ∈ AB.toFinset :=
      AB.mem_toFinset.mp <| Or.inr hBv
    have hw : w ∈ AB.toFinset :=
      hG <| G.mem_support.mpr ⟨v, Adj.symm <| mem_neighborFinset .. |>.mp <| by grind⟩
    cases Corollary4 hG ih with
    | inr h => exact h
    | inl H => ?_
    have : (AB.A w ∧ G.degree w = 3 ∧ AB.A u ∧ G.degree u = 3) ∨ Objective G AB := by
      simp only [fB2 hBv hdv] at hfv
      rcases h w hw with ⟨hAw, hdw⟩ | ⟨hAw, hdw⟩ | ⟨hBw, hdw⟩
      · simp only [γA2 hAw hdw] at hfv
        linarith [H u hu]
      · rcases h u hu with ⟨hAu, hdu⟩ | ⟨hAu, hdu⟩ | ⟨hBu, hdu⟩
        · simp only [γA2 hAu hdu] at hfv
          linarith [H w hw]
        · exact Or.inl ⟨hAw, hdw, hAu, hdu⟩
        · exact Or.inr <| Claim5 hG hBv hBu (mem_neighborFinset .. |>.mp <| by grind) ih
      · exact Or.inr <| Claim5 hG hBv hBw (mem_neighborFinset .. |>.mp <| by grind) ih
    cases this with
    | inr h => exact h
    | inl h => ?_
    obtain ⟨hAw, hdw, hAu, hdu⟩ := h
    if huw : G.Adj u w then
      refine Corollary2 {u, v} pair_nonempty (by grind) (respects_pair hAu) hG ih
          InducesForestOfStars_pair ?_
      rw [card_pair (by grind [ne_of_mem_neighborFinset]), Nat.cast_two]
      obtain ⟨x, hx, hvnex, hwnex⟩ := Finset_get_other_other (le_of_eq <| hdu.symm) v w
      suffices G.closed_neighborFinset_of_Finset {u, v} = {u, v, w, x} by
        rw [this]
        suffices 2 ≥ f G AB u + f G AB v + f G AB w + f G AB x by
          grind
        simp only [fB2 hBv hdv, fA3 hAu hdu, fA3 hAw hdw]
        suffices f G AB x ≤ 3 / 5 by linarith
        exact H _ (hG <| G.mem_support.mpr ⟨u, Adj.symm <| mem_neighborFinset .. |>.mp hx⟩) |>.2.1
      rw [closed_neighborFinset_of_pair_eq, hNv]
      suffices G.neighborFinset u = {v, w, x} by grind
      refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
      · intro z hz
        simp only [mem_insert, mem_singleton, mem_neighborFinset] at hz hx ⊢
        rcases hz with hz | hz | hz
        · exact (mem_neighborFinset .. |>.mp <| hz ▸ hNv ▸ pair_comm w u ▸ mem_insert_self ..).symm
        · exact hz ▸ huw
        · exact hz ▸ hx
      · grind [degree]
    else
      if hN2 : ∃ z ∈ G.N2_of_Finset {v}, 1 / 2 < f G AB z then
        obtain ⟨z, hz, hfz⟩ := hN2
        simp only [mem_N2_of_Finset_iff', closed_neighborFinset_of_singleton_eq, mem_union, not_or,
          hNv, mem_singleton, exists_eq_left] at hz
        obtain ⟨x, hx, hzx, hxv⟩ := hz.2
        have hx' : x ∈ ({w, u} : Finset _) := hNv ▸ mem_neighborFinset .. |>.mpr hxv.symm
        have := by refine _Claim6 hG hxv.symm hzx hBv hdv ?_ ?_ ih <;> grind
        grind
      else if hcardN2v : 4 ≤ #(G.N2_of_Finset {v}) then
        refine Claim2' _ (singleton_nonempty v) (singleton_subset_iff.mpr hv) respects_singleton
            hG ih InducesForestOfStars_singleton ?_
        simp only [card_singleton, Nat.cast_one, closed_neighborFinset_of_singleton_eq, hNv]
        have : ∑ z ∈ {w, u} ∪ {v}, f G AB z = f G AB w + f G AB u + f G AB v := by
          grind [ne_of_mem_neighborFinset]
        rw [this]; clear this
        simp only [fB2 hBv hdv, fA3 hAu hdu, fA3 hAw hdw]
        suffices 4 * (1 / 10) ≤ ∑ z ∈ G.N2_of_Finset {v}, γ G AB z by linarith
        have : ∑ z ∈ G.N2_of_Finset {v}, 1 / 10 ≤ ∑ z ∈ G.N2_of_Finset {v}, γ G AB z := by
          refine sum_le_sum fun z hz ↦ ?_
          refine H _ ?_ |>.2.2.1
          have := mem_N2_of_Finset_iff.mp hz |>.2.2
          simp only [mem_singleton, exists_eq_left] at this
          obtain ⟨y, _, hzy, _⟩ := this
          exact hG <| G.mem_support.mpr ⟨y, hzy⟩
        refine le_trans ?_ this
        simp only [sum_const']
        refine mul_le_mul_of_nonneg ?_ (le_refl _) zero_le_four (by linarith)
        simp only [Nat.ofNat_le_cast, hcardN2v]
      else
        refine Corollary2 (G.closed_neighborFinset_of_Finset {v}) ?_ ?_ ?_ hG ih ?_ ?_
        · exact ⟨v, mem_closed_neighborFinset_iff.mpr <| Or.inl <| mem_singleton.mpr rfl⟩
        · intro z hz
          simp only [mem_closed_neighborFinset_iff, mem_singleton] at hz
          rcases hz with hz | hz
          · exact hz ▸ hv
          · obtain ⟨v, _, hvz⟩ := hz
            exact hG <| G.mem_support.mpr ⟨v, hvz.symm⟩
        · intro z hz hBz y hy hyz
          simp only [mem_closed_neighborFinset_iff, mem_singleton, ← mem_neighborFinset,
            exists_eq_left, hNv, mem_insert] at hz hy
          have hz : z = v := by
            rcases hz with hz | hz | hz
            · exact hz
            · refine ne_of_ne_congr AB.A ?_ hz |>.elim
              simp only [hAw, not_A_of_B hBz]
              exact false_ne_true
            · refine ne_of_ne_congr AB.A ?_ hz |>.elim
              simp only [hAu, not_A_of_B hBz]
              exact false_ne_true
          subst hz
          simp only [hyz.ne, false_or] at hy
          rcases hy with hy | hy
          · refine ⟨hy ▸ hAw, hy ▸ ?_⟩
            rw [← card_singleton z]
            refine card_le_card ?_
            intro v' hv'
            simp only [mem_inter, mem_closed_neighborFinset_iff, mem_singleton,
              ← mem_neighborFinset, exists_eq_left, hNv, mem_insert] at hv' ⊢
            obtain ⟨hv'w, hv'⟩ := hv'
            simp only [mem_neighborFinset] at hv'w
            rcases hv' with hv' | hv' | hv'
            · exact hv'
            · exact hv'w.symm.ne hv' |>.elim
            · exact huw (hv' ▸ hv'w.symm) |>.elim
          · refine ⟨hy ▸ hAu, hy ▸ ?_⟩
            rw [← card_singleton z]
            refine card_le_card ?_
            intro v' hv'
            simp only [mem_inter, mem_closed_neighborFinset_iff, mem_singleton,
              ← mem_neighborFinset, exists_eq_left, hNv, mem_insert] at hv' ⊢
            obtain ⟨hv'w, hv'⟩ := hv'
            simp only [mem_neighborFinset] at hv'w
            rcases hv' with hv' | hv' | hv'
            · exact hv'
            · exact huw (hv' ▸ hv'w) |>.elim
            · exact hv'w.symm.ne hv' |>.elim
        · have hFeq : (G.closed_neighborFinset_of_Finset {v}) = {u, v, w} := by
            rw [closed_neighborFinset_of_singleton_eq, hNv]
            grind
          rw [hFeq, (by grind : {u, v, w} = ({u, w, v} : Finset _))]
          exact InducesForestOfStars_triplet_of_nonadj huw
        · have : G.closed_neighborFinset_of_Finset (G.closed_neighborFinset_of_Finset {v})
              = G.N2_of_Finset {v} ∪ G.closed_neighborFinset_of_Finset {v} :=
            Eq.symm <| sdiff_union_of_subset closed_neighborFinset_contains_Finset
          rw [this]; clear this
          have : #(G.closed_neighborFinset_of_Finset {v}) = 3 := by
            grind [closed_neighborFinset_of_singleton_eq]
          rw [this, Nat.cast_three]
          suffices 3 ≥ ∑ x ∈ G.N2_of_Finset {v}, f G AB x
              + ∑ x ∈ G.closed_neighborFinset_of_Finset {v}, f G AB x by
            exact le_of_eq_of_le (Eq.symm <| sum_disjoint_union rfl N2_inter_Nle1_empty) this
          have : ∑ x ∈ G.closed_neighborFinset_of_Finset {v}, f G AB x ≤ 4 / 3 := by
            suffices 4 / 3 = f G AB u + f G AB v + f G AB w by
              grind [closed_neighborFinset_of_singleton_eq]
            simp only [fB2 hBv hdv, fA3 hAu hdu, fA3 hAw hdw]
            linarith
          suffices ∑ x ∈ G.N2_of_Finset {v}, f G AB x ≤ 5 / 3 by
            linarith
          calc ∑ x ∈ G.N2_of_Finset {v}, f G AB x
            _ ≤ ∑ x ∈ G.N2_of_Finset {v}, 1 / 2 := by
              refine sum_le_sum fun x hx ↦ ?_
              simp only [not_exists, not_and, not_lt] at hN2
              exact hN2 x hx
            _ ≤ (3 : ℝ) * (1 / 2) := by
              simp only [sum_const']
              refine mul_le_mul ?_ (le_refl _) zero_le_one_half zero_le_three
              simp only [not_le] at hcardN2v
              rw [← Nat.cast_three, Nat.cast_le]
              exact Nat.le_of_lt_succ hcardN2v
          linarith
  else
    refine Claim1 (Or.inr hBv) hG ih <| not_lt.mp hfv |>.trans (hNv ▸ le_of_eq ?_)
    exact Eq.symm <| add_comm (γ G AB u) _ ▸ sum_pair hne.symm

lemma Claim6' {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    (∀ v ∈ AB.toFinset,
      (AB.A v ∧ G.degree v = 2) ∨ (AB.A v ∧ G.degree v = 3))
      ∨ Objective G AB := by
  cases Claim4' hG ih with
  | inr h => exact Or.inr h
  | inl h => ?_
  if H : ∃ v ∈ AB.toFinset, AB.B v then
    obtain ⟨v, hv, hBv⟩ := H
    exact Or.inr <| Claim6 hG hBv ih
  else
    simp only [not_exists, not_and] at H
    refine Or.inl <| fun v hv ↦ ?_
    rcases h v hv with ⟨hAv, hdv⟩ | ⟨hAv, hdv⟩ | ⟨hBv, hdv⟩
    · exact Or.inl ⟨hAv, hdv⟩
    · exact Or.inr ⟨hAv, hdv⟩
    · exact H v hv hBv |>.elim

end Bipartition
end AB
end CaroWeiType
