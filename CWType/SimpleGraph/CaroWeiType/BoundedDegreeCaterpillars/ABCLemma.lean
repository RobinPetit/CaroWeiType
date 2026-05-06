import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.ABC
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claims

namespace CaroWeiType
namespace ABC

open Tripartition
open Finset
open SimpleGraph

private lemma exists_argmin {α β : Type*} [LinearOrder β] {s : Finset α} (hs : s.Nonempty)
    (f : α → β) : ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y := by
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

private lemma _ok_if_no_nonneg_gain {n k : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    (hcard : ABC.card = k) (hk : ¬k = 0) (hW : ({v | v ∈ ABC ∧ 0 < γ G ABC v} : Finset _) = ∅)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  have H : ∀ v ∈ ABC, γ G ABC v = 0 := by
    intro v hv
    rcases lt_or_eq_of_le <| (γ_nonneg : 0 ≤ γ G ABC v) with hγ | hγ
    · have hvW : v ∈ ({v | v ∈ ABC ∧ 0 < γ G ABC v} : Finset _) := by
        simp only [mem_filter, mem_univ, hv, hγ, and_self]
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
      have _ : γ G ABC v = 0 := H _ (Or.inr <| Or.inr hv)
      let hobj := γ_eq_0_iff (Or.inr <| Or.inr hv) (Nat.one_le_of_lt hdv) |>.mp
        <| H _ (Or.inr <| Or.inr hv)
      simp only [hv, and_true, not_B_of_C, and_false, false_or] at hobj
      rcases hobj with hdv | hdv
      · obtain ⟨w, hvw⟩ := G.degree_pos_iff_exists_adj v |>.mp <| by lia
        if hdw : G.degree w ≤ 1 then
          refine Claim5 hG ih ⟨w, ?_, hdw⟩
          refine ABC.mem_toFinset.mpr <| hG ?_
          exact G.degree_pos_iff_mem_support _ |>.mp <| Adj.degree_pos_left hvw.symm
        else
          simp only [not_le] at hdw
          have hw : w ∈ ABC := by
            refine ABC.mem_toFinset.mpr <| hG ?_
            exact (degree_pos_iff_mem_support G w).mp <| Adj.degree_pos_left hvw.symm
          have hγw : γ G ABC w = 0 := H _ hw
          let hobj := γ_eq_0_iff hw (Nat.one_le_of_lt hdw) |>.mp hγw
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
        let := γ_eq_0_iff hx (Nat.one_le_of_lt hdx) |>.mp <| H _ hx
        grind
    rcases hW with hW | hW
    · exact hW
    · if ABC.toFinset = ∅ then
        grind only
      else
        obtain ⟨v, hv⟩ := nonempty_def.mp <| nonempty_iff_ne_empty.mpr this
        obtain ⟨hBv, hdv⟩ := hW v (ABC.mem_toFinset.mpr hv)
        obtain ⟨x, y, z, H, _⟩ := neighborFinset_eq_deg3 (G.degree ·) hdv
        have : (ABC.B x ∧ G.degree x = 3) ∧ (ABC.B y ∧ G.degree y = 3) := by
          refine ⟨?_, ?_⟩ <;> {
            refine hW _ <| ABC.mem_toFinset.mpr <| hG ?_
            refine G.mem_support.mpr ⟨v, Adj.symm <| G.mem_neighborFinset .. |>.mp ?_⟩
            simp only [H, mem_insert, mem_singleton, true_or, or_true]
          }
        obtain ⟨⟨hBx, hdx⟩, ⟨hBy, hdy⟩⟩ := this
        refine Claim10 hG hBv hdv ih ⟨x, y, by grind [degree], ?_, ?_, hBx, hBy, hdx, hdy⟩
        · refine G.mem_neighborFinset .. |>.mp
            <| by simp only [H, mem_insert, mem_singleton, true_or]
        · refine G.mem_neighborFinset .. |>.mp
            <| by simp only [H, mem_insert, mem_singleton, true_or, or_true]

theorem ABCLemma {n : ℕ} (G : SimpleGraph (Fin n)) [G.LocallyFinite] (ABC : Tripartition n)
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) :
    Objective G ABC := by
  induction hcard : ABC.card using Nat.strong_induction_on generalizing G ABC with | h k ih
  if hk : k = 0 then
    refine ⟨∅, ?_, ?_, ?_, ?_⟩ <;>
    simp [respects, card_eq_zero.mp <| hk ▸ hcard, InducesForest, IsDegenerateSet]
  else
  have ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC' :=
    fun G' _ ABC' _ hsupp' hcardABC' ↦ ih ABC'.card (hcard ▸ hcardABC') G' ABC' hsupp' rfl
  let W := ({v | v ∈ ABC ∧ 0 < γ G ABC v} : Finset _)
  if hW : W = ∅ then
    exact _ok_if_no_nonneg_gain hG hcard hk hW ih
  else
    have hW : W.Nonempty := nonempty_iff_ne_empty.mpr hW
    obtain ⟨û, hû⟩ : ∃ û, IsVstar G ABC û := by
      obtain ⟨û, hû⟩ := exists_argmin hW (key G ABC)
      use û
      simp only [IsVstar]
      let hobj := hû.1
      simp only [mem_filter, mem_univ, true_and, W] at hobj
      refine ⟨?_, ?_⟩
      · simp only [ABC.mem_toFinset.mp hobj.1, hobj, ne_eq, ne_of_lt, not_false_eq_true,
          Ne.symm, and_true]
      · refine fun v hv _ ↦ hû.2 _ ?_
        simp only [mem_filter, mem_univ, true_and, W]
        refine ⟨?_, lt_of_le_of_ne γ_nonneg (Ne.symm hv.2)⟩
        refine ABC.mem_toFinset.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp ?_
        refine Nat.zero_lt_of_ne_zero ?_
        simp only [ne_eq] at hv
        exact γ_eq_zero_of_deg_eq_zero.mt hv.2
    match Claim14 hG hû ih with
    | Or.inl h => exact h
    | Or.inr h => ?_
    obtain ⟨_, hdû, hfû, ⟨w, hûw_, hdw, hnotAw⟩⟩ := h
    have hûw : G.Adj û w := G.mem_neighborFinset .. |>.mp hûw_
    have hw := ABC.mem_toFinset.mpr <| mem_def.mpr <| hG <| G.mem_support.mpr ⟨û, hûw.symm⟩
    have : ABC.B w ∨ ABC.C w := by grind [ABC.mem_iff]
    refine Or.elim this (fun hBw ↦ Claim20 hG hû hBw hdw hûw ih) (fun hCw ↦ ?_)
    if hγNû : ∃ w', G.Adj û w' ∧ γ G ABC w' = 0 ∧ w ≠ w' then
      obtain ⟨w', hûw', hγw', hww'⟩ := hγNû
      have hdw' : 1 ≤ G.degree w' := one_le_degree_of_adj' hûw'
      have hw' := ABC.mem_toFinset.mpr <| mem_def.mpr <| hG <| G.mem_support.mpr ⟨û, hûw'.symm⟩
      rcases γ_eq_0_iff hw' hdw' |>.mp hγw' with ⟨hdw', hBw'⟩ | ⟨hdw', hCw'⟩ | ⟨hdw', hCw'⟩
      · exact Claim20 hG hû hBw' hdw' hûw' ih
      · exact Claim17 hG hû hCw hdw hCw' hdw' hww' hûw hûw' ih
      · exact Claim6 hG ih ⟨w', hdw', not_A_of_C hCw'⟩
    else
      simp only [ne_eq, not_exists, not_and, Decidable.not_not] at hγNû
      have : ∀ z ∈ G.neighborFinset û, z ≠ w → γ G ABC z ≠ 0 := by grind [mem_neighborFinset]
      obtain ⟨x, y, hNw, hfyx⟩ :=
        neighborFinset_eq_deg3' (mem_neighborFinset_symm hûw_) (f G ABC ·) hdw
      if hγx : 1 / 6 ≤ γ G ABC x then
        have hwx : G.Adj w x := G.mem_neighborFinset .. |>.mp <| by grind
        refine Corollary1 hG hwx ih ?_
        simpa only [fC3 hCw hdw]
      else if hγy : 1 / 6 ≤ γ G ABC y then
        have hwy : G.Adj w y := G.mem_neighborFinset .. |>.mp <| by grind
        refine Corollary1 hG hwy ih ?_
        simpa only [fC3 hCw hdw]
      else if hγxy : 1 / 6 ≤ γ G ABC x + γ G ABC y then
        refine Claim1 hw hG ih ?_
        rw [fC3 hCw hdw]
        have : ∑ u ∈ {x, y}, γ G ABC u ≤ ∑ u ∈ G.neighborFinset w, γ G ABC u :=
          sum_le_sum_of_subset_of_nonneg (by grind) fun _ _ _ ↦ γ_nonneg
        refine le_trans hγxy (le_of_eq_of_le ?_ this)
        grind [degree]
      else if hγy₀ : γ G ABC y = 0 then
        have hdy : 1 ≤ G.degree y := by
          have hwy : G.Adj w y := G.mem_neighborFinset .. |>.mp <| by grind
          refine one_le_degree_of_adj' hwy
        have hy : y ∈ ABC :=
          ABC.mem_toFinset.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp hdy
        rcases γ_eq_0_iff hy hdy |>.mp hγy₀ with ⟨hdy, hBy⟩ | ⟨hdy, hCy⟩ | ⟨hdy, hCy⟩
        · exact Corollary9 hG hBy hdy ih ⟨w, (G.mem_neighborFinset .. |>.mp <| by grind).symm, hCw⟩
        · exact Claim13 hG (G.mem_neighborFinset .. |>.mp <| by grind) hCw hdw hCy hdy ih
        · exact Claim6 hG ih ⟨y, hdy, not_A_of_C hCy⟩
      else
        match Corollary16 hG hû hCw hdw ih with
        | Or.inl h => exact h
        | Or.inr h => ?_
        obtain ⟨hf'û, hγû⟩ := h
        refine Claim2' (singleton_nonempty w) hG
            (singleton_subset_iff.mpr <| ABC.mem_toFinset.mp hw) respects_singleton ih
            InducesLinearForest_singleton ?_
        have hNclosedw : G.closed_neighborFinset_of_Finset {w} = {w, û, x, y} := by
          simp only [closed_neighborFinset_of_singleton_eq]
          grind
        have hZ : G.degree û - 3
            ≤ #(G.neighborFinset û \ G.closed_neighborFinset_of_Finset {w}) := by
          have h : #{w, x, y} = 3 := by grind [degree, ne_of_mem_neighborFinset]
          have h' : #(G.neighborFinset û) - #{w, x, y} ≤ #(G.neighborFinset û \ {w, x, y}) :=
            le_card_sdiff ..
          rw [← h, degree]
          refine le_trans h' ?_
          refine card_le_card ?_
          intro u hu
          simp only [mem_sdiff, mem_neighborFinset, hNclosedw] at hu ⊢
          refine ⟨hu.1, ?_⟩
          grind [Adj.ne']
        suffices 5 / 6 ≥ f G ABC x + f G ABC y + 3 * γ G ABC û by
          rw [card_singleton, Nat.cast_one]
          calc _
            _ ≥ f G ABC û + f G ABC x + f G ABC y + - f G ABC û + 3 * γ G ABC û + 1 / 6 := by
              linarith
            _ = f G ABC û + f G ABC x + f G ABC y + - f G ABC û + 3 * γ G ABC û + f G ABC w := by
              rw [fC3 hCw hdw]
            _ = ∑ u ∈ G.closed_neighborFinset_of_Finset {w}, f G ABC u
                + 3 * γ G ABC û - f G ABC û := by
              rw [hNclosedw]
              have : w ∉ ({û, x, y} : Finset _) :=
                hNw ▸ G.notMem_neighborFinset_self w
              grind [degree]
            _ = ∑ u ∈ G.closed_neighborFinset_of_Finset {w}, f G ABC u
                + 3 * γ G ABC û - G.degree û * γ G ABC û := by linarith
            _ = ∑ u ∈ G.closed_neighborFinset_of_Finset {w}, f G ABC u
                - (G.degree û - 3) * γ G ABC û := by
              linarith
          suffices (G.degree û - 3) * γ G ABC û ≤ ∑ u ∈ G.N2_of_Finset {w}, γ G ABC u by
            linarith
          rw [← Nat.cast_three, ← Nat.cast_sub hdû]
          calc _
            _ ≤ ∑ u ∈ (G.neighborFinset û \ G.closed_neighborFinset_of_Finset {w}), γ G ABC û := by
              simp only [sum_const']
              refine mul_le_mul_of_nonneg (Nat.cast_le.mpr hZ) (le_refl _) ?_ γ_nonneg
              rw [← Nat.cast_zero, Nat.cast_le]
              exact Nat.le_sub_of_add_le hdû
            _ ≤ ∑ u ∈ (G.neighborFinset û \ G.closed_neighborFinset_of_Finset {w}), γ G ABC u := by
              refine sum_le_sum ?_
              intro u hu
              have hûu : G.Adj û u := G.mem_neighborFinset .. |>.mp <| mem_sdiff.mp hu |>.1
              refine γ_vstar_le_γ hû ?_ ?_
              · exact ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨û, hûu.symm⟩
              · refine hγNû _ hûu |>.mt ?_
                refine ne_of_mem_of_not_mem ?_ (mem_sdiff.mp hu |>.2)
                exact closed_neighborFinset_contains_Finset <| mem_singleton.mpr rfl
          refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ γ_nonneg
          intro u hu
          refine mem_N2_of_Finset_iff'.mpr ?_
          refine ⟨mem_sdiff.mp hu |>.2, w, mem_singleton.mpr rfl, û, ?_, ?_, hûw⟩
          · exact notMem_singleton.mpr <| hûw.ne
          · refine Adj.symm <| G.mem_neighborFinset .. |>.mp <| mem_sdiff.mp hu |>.1
        if hfx : f G ABC x ≤ 1 / 3 then
          linarith
        else
          have hdx : 1 ≤ G.degree x := by
            have hwx : G.Adj w x := G.mem_neighborFinset .. |>.mp <| by grind
            exact one_le_degree_of_adj' hwx
          have hx : x ∈ ABC :=
            ABC.mem_toFinset.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp hdx
          obtain ⟨hAx, hdx⟩ := A4_of_13_lt_f_of_γ_lt_16 hdx hx (not_le.mp hfx) (not_le.mp hγx)
          rw [γA4 hAx hdx] at hγxy
          rw [fA4 hAx hdx]
          have hγy : γ G ABC y < 1 / 15 := by linarith
          have hfy := f_le_two_sevenths_of_γ_lt_one_fifteenth_of_γ_ne_zero hγy hγy₀
          linarith

end ABC
end CaroWeiType
