import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Operations
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim19

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

private noncomputable def f' {n : ℕ} (G : SimpleGraph (Fin n)) [G.LocallyFinite]
    (ABC : Tripartition n) (û w x y : Fin n) : Fin n → ℝ :=
  fun u ↦ (f G ABC u - f ((fromEdgeSet (G.edgeSet ∪ {s(x, y)})).deleteIncidencesOf {û})
      ((ABC \ {û}).promote w) u)

private lemma _ok_if_f'_le_zero {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {û w x y : Fin n} (hû : IsVstar G ABC û) (hBw : ABC.B w) (hdw : G.degree w = 3) (hw : G.Adj û w)
    (hf'y : f' G ABC û w x y y ≤ 0) (hf'x : f' G ABC û w x y x ≤ 0)
    (hdû : 4 ≤ G.degree û)
    {U : Finset (Fin n)} (hU : U = {u ∈ G.neighborFinset û \ {w, x, y} | γ G ABC u ≠ 0})
    (H : f G ABC û > 1 / 3 + #U * γ G ABC û - f' G ABC û w x y x - f' G ABC û w x y y)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n) [ABC'.Decidable],
      G'.support ⊆ ↑ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  have : f G ABC û > 1 / 3 := by
    suffices 0 ≤ #U * γ G ABC û by
      linarith
    exact Left.mul_nonneg (Nat.cast_nonneg' _) γ_nonneg
  have := f_le_1_over_3_of_4_le_deg_of_notA4 hdû |>.mt <| not_le.mpr this
  simp only [not_and, Classical.not_imp, Decidable.not_not] at this
  obtain ⟨hAû, hdû⟩ := this
  have : #U * γ G ABC û < (2 / 5 - 1 / 3) := by linarith [fA4 hAû hdû]
  rw [γA4 hAû hdû] at this
  have hUempty : U = ∅ := by
    have : #U  < (1 : ℝ) := by linarith
    rw [← Nat.cast_one, Nat.cast_lt] at this
    exact card_eq_zero.mp <| Nat.lt_one_iff.mp this
  have : Objective G ABC ∨ ∃ s, G.neighborFinset û = {w, x, y, s} ∧ ABC.C s ∧ G.degree s = 3 := by
    match Corollary7 hG hBw hdw ih with
    | Or.inl h => exact Or.inl h
    | Or.inr h3_le_deg => ?_
    obtain ⟨s, hs⟩ : (G.neighborFinset û \ {w, x, y}).Nonempty := by
      refine sdiff_nonempty_of_card_lt_card ?_
      rw [← degree, hdû]
      grind
    have hsU : s ∉ U := by simp only [hUempty, notMem_empty, not_false_eq_true]
    simp only [hU, mem_filter, not_and, Decidable.not_not] at hsU
    have := hsU hs
    have hds : 1 ≤ G.degree s :=
      one_le_degree_of_adj' <| G.mem_neighborFinset .. |>.mp <| mem_sdiff.mp hs |>.1
    have hsABC : s ∈ ABC :=
      ABC.mem_toFinset.mpr <| mem_def.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp hds
    have hûs : G.Adj û s := G.mem_neighborFinset .. |>.mp <| mem_sdiff.mp hs |>.1
    rcases γ_eq_0_iff hsABC hds |>.mp this with h | h | h
    · exact Or.inl <| Claim19 hG hû hBw hdw h.2 h.1 (by grind) hw hûs  ih
    · if h' : (G.neighborFinset û \ {w, x, y, s}).Nonempty then
        obtain ⟨s', hs'⟩ := h'
        have hds' : 1 ≤ G.degree s' :=
          one_le_degree_of_adj' <| G.mem_neighborFinset .. |>.mp <| mem_sdiff.mp hs' |>.1
        have hs'ABC : s' ∈ ABC :=
          ABC.mem_toFinset.mpr <| mem_def.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp hds'
        have hs'U : s' ∉ U := by simp only [hUempty, notMem_empty, not_false_eq_true]
        simp only [hU, mem_filter, not_and, Decidable.not_not] at hs'U
        have hûs' : G.Adj û s' := G.mem_neighborFinset .. |>.mp <| mem_sdiff.mp hs' |>.1
        rcases γ_eq_0_iff hs'ABC hds' |>.mp <| hs'U (by grind) with h' | h' | h'
        · exact Or.inl <| Claim19 hG hû hBw hdw h'.2 h'.1 (by grind) hw hûs'  ih
        · exact Or.inl <| Claim17 hG hû h.2 h.1 h'.2 h'.1 (by grind) hûs hûs' ih
        · exact Or.inl <| Claim6 hG ih ⟨s', h'.1, not_A_of_C h'.2⟩
      else
        simp only [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at h'
        refine Or.inr ⟨s, ?_, h.2, h.1⟩
        rcases HasSubset.Subset.eq_or_ssubset h' with h' | h'
        · exact h'
        · have := card_lt_card h'
          grind [degree]
    · exact Or.inl <| Claim6 hG ih ⟨s, h.1, not_A_of_C h.2⟩
  match this with
  | Or.inl h => exact h
  | Or.inr h => ?_
  obtain ⟨s, hs, hCs, hds⟩ := h
  match Claim16 hG hû hCs hds ih with
  | Or.inl h => exact h
  | Or.inr h => ?_
  simp only [hAû, hdû, true_and, not_true_eq_false, false_and] at h

private lemma TMP {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {û w x y : Fin n} (hû : IsVstar G ABC û) (hBw : ABC.B w) (hdw : G.degree w = 3) (hw : G.Adj û w)
    (hûw : û ∈ G.neighborFinset w)
    (hNw : G.neighborFinset w = {û, x, y})
    (hf : ∑ u ∈ G.neighborFinset û \ ({w} ∪ G.neighborFinset w), γ G ABC u <
      f G ABC û - 1 / 3
      + (f G ABC x - f ((fromEdgeSet (G.edgeSet ∪ {s(x, y)})).deleteIncidencesOf {û})
        ((ABC \ {û}).promote w) x)
      + (f G ABC y - f ((fromEdgeSet (G.edgeSet ∪ {s(x, y)})).deleteIncidencesOf {û})
        ((ABC \ {û}).promote w) y))
    (hfxy : (f G ABC y - f ((fromEdgeSet (G.edgeSet ∪ {s(x, y)})).deleteIncidencesOf {û})
        ((ABC \ {û}).promote w) y)
      ≤ (f G ABC x - f ((fromEdgeSet (G.edgeSet ∪ {s(x, y)})).deleteIncidencesOf {û})
        ((ABC \ {û}).promote w) x))
    (hdû : 4 ≤ G.degree û)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n) [ABC'.Decidable],
      G'.support ⊆ ↑ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  let U : Finset _ := {u ∈ G.neighborFinset û \ {w, x, y} | γ G ABC u ≠ 0}
  have H : f G ABC û > 1 / 3 + #U * γ G ABC û - f' G ABC û w x y x - f' G ABC û w x y y := by
    suffices #U * γ G ABC û  ≤ ∑ u ∈ G.neighborFinset û \ ({w} ∪ G.neighborFinset w), γ G ABC u by
      simp only [f']
      linarith
    calc _
      _ = ∑ u ∈ U, γ G ABC û := Eq.symm <| sum_const' U fun _ _ ↦ rfl
      _ ≤ ∑ u ∈ U, γ G ABC u := by
        refine sum_le_sum ?_
        intro u hu
        simp only [ne_eq, mem_filter, mem_sdiff, mem_neighborFinset, mem_insert, mem_singleton,
          not_or, U] at hu
        refine γ_vstar_le_γ hû ?_ hu.2
        exact ABC.mem_toFinset.mpr <| mem_def.mpr <| hG <| G.mem_support.mpr ⟨û, hu.1.1.symm⟩
    refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ γ_nonneg)
    intro u hu
    simp only [ne_eq, mem_filter, mem_sdiff, mem_neighborFinset, mem_insert, mem_singleton, not_or,
      singleton_union, U] at hu ⊢
    refine ⟨hu.1.1, hu.1.2.1, ?_⟩
    simp only [← mem_neighborFinset, hNw]
    grind [Adj.ne]
  if hf'xy : f' G ABC û w x y x ≤ 0 ∧ f' G ABC û w x y y ≤ 0 then
    exact _ok_if_f'_le_zero hG hû hBw hdw hw hf'xy.2 hf'xy.1 hdû rfl H ih
  else
    simp only [not_and, not_le] at hf'xy
    sorry

lemma Claim20 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û w : Fin n} (hû : IsVstar G ABC û)
    (hBw : ABC.B w) (hdw : G.degree w = 3) (hv : G.Adj û w)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n) [ABC'.Decidable],
      G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  have hûw : û ∈ G.neighborFinset w := G.mem_neighborFinset .. |>.mpr hv.symm
  obtain ⟨x, y, hNw, _⟩ := by
    refine neighborFinset_eq_deg3' hûw 1 hdw
  match objective_of_B3' hG hdw hBw hNw ih, Claim15 hG hû ih with
  | Or.inl h, _ => exact h
  | _, Or.inl h => exact h
  | Or.inr hf, Or.inr hdû => ?_
  sorry

end Tripartition
end ABC
end CaroWeiType
