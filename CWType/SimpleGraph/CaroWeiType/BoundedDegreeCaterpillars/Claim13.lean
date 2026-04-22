import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim1
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim2
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim3
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim5
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim9

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

private lemma _neighborhood_3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {v w : Fin n} (hvw : G.Adj v w) (hdv : G.degree v = 3)
    (f : Fin n → ℝ) :
    ∃ u₁ u₂ : Fin n, G.neighborFinset v = {w, u₁, u₂} ∧ f u₁ ≤ f u₂ := by
  obtain ⟨x, y, z, hNv, hfzy, hfyx⟩ := neighborFinset_eq_deg3' f hdv
  haveI := hNv ▸ G.mem_neighborFinset .. |>.mpr hvw
  simp only [mem_insert, mem_singleton] at this
  rcases this with hw | hw | hw
  · exact ⟨z, y, ⟨by grind, hfzy⟩⟩
  · exact ⟨z, x, ⟨by grind, hfzy.trans hfyx⟩⟩
  · exact ⟨y, x, ⟨by grind, hfyx⟩⟩

private lemma _neighborhood_3' {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} (hG : G.support.toFinset ⊆ ABC.toFinset)
    {v w : Fin n} (hCv : ABC.C v) (hCw : ABC.C w) (hvw : G.Adj v w)
    (hdv : G.degree v = 3) (hdw : G.degree w = 3)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    (Objective G ABC) ∨
      (∃ u₁ u₂ : Fin n,
        G.neighborFinset v = {w, u₁, u₂}
          ∧ ABC.A u₁ ∧ G.degree u₁ = 4 ∧ ABC.A u₂ ∧ G.degree u₂ = 6) := by
  obtain ⟨u₂, u₁, hNv, hfus⟩ := _neighborhood_3 hvw hdv (f G ABC ·)
  have _ : w ≠ u₁ ∧ w ≠ u₂ ∧ u₁ ≠ u₂ := by
    rw [degree, hNv] at hdv
    grind
  if hfs : f G ABC u₁ + f G ABC u₂ + f G ABC w ≤ 1 - f G ABC v then
    refine Or.inl <| Claim3 G ABC (ABC.mem_iff.mpr <| Or.inr <| Or.inr hCv) hG ih ?_
    rw [hNv]
    exact le_of_eq_of_le (by grind) hfs
  else
    rw [fC3 hCv hdv, fC3 hCw hdw] at hfs
    have hfu₁ : 1 / 3 < f G ABC u₁ := by
      suffices 2 / 3 < 2 * f G ABC u₁ by linarith
      simp only [not_le] at hfs
      calc 2 / (3 : ℝ)
        _ = 1 - 1 / 6  - 1 / 6 := by linarith
        _ < f G ABC u₁ + f G ABC u₂ := by lia
        _ ≤ f G ABC u₁ + f G ABC u₁ := by simp only [add_le_add_iff_left, hfus]
        _ = 2 * f G ABC u₁ := Eq.symm <| two_mul _
    have hu₁v : G.Adj u₁ v := by
      refine Adj.symm <| G.mem_neighborFinset .. |>.mp ?_
      simp only [hNv, mem_insert, mem_singleton, or_true]
    have hu₂v : G.Adj u₂ v := by
      refine Adj.symm <| G.mem_neighborFinset .. |>.mp ?_
      simp only [hNv, mem_insert, mem_singleton, or_true, true_or]
    have hNvABC : G.neighborFinset v ⊆ ABC.toFinset :=
      fun _ hu ↦ hG <| Set.mem_toFinset.mpr <|
        G.mem_support.mpr ⟨v, (G.mem_neighborFinset .. |>.mp hu).symm⟩
    if hγu₁ : 1 / 6 ≤ γ G ABC u₁ then
      refine Or.inl <| Corollary1 (ABC.mem_iff.mpr <| Or.inr <| Or.inr hCv) hNvABC hu₁v.symm ih ?_
      refine le_of_eq_of_le ?_ hγu₁
      rw [fC3 hCv hdv]
    else
      have hu₁ : u₁ ∈ ABC :=
        ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨v, hu₁v⟩
      rcases hu₁ with hAu₁ | hBu₁ | hCu₁
      · have hdu₁ : G.degree u₁ = 4 := by
          let hdegu₁ := @fA_le_13_of_5_le_deg _ G _ _ _ hAu₁ |>.mt <| not_le.mpr hfu₁
          have _ : 0 < G.degree u₁ := G.degree_pos_iff_exists_adj _ |>.mpr ⟨v, hu₁v⟩
          grind only [γA1, γA2, γA3]
        if hγu₂ : 1 / 15 ≤ γ G ABC u₂ then
          refine Or.inl <| Claim1 (by simp only [mem_iff, hCv, or_true]) hNvABC ih ?_
          rw [hNv]
          calc f G ABC v
            _ = 1 / 6 := fC3 hCv hdv
            _ = 1 / 15 + 1 / 10 + 0 := by linarith
            _ ≤ γ G ABC u₂ + γ G ABC u₁ + γ G ABC w := by
              rw [← γC3 hCw hdw, ← γA4 hAu₁ hdu₁]
              simp only [add_le_add_iff_right, hγu₂]
          exact le_of_eq <| by grind
        else
          rw [fA4 hAu₁ hdu₁] at hfs
          have hfu₂ : 4 / 15 < f G ABC u₂ := by linarith
          have hu₂ : u₂ ∈ ABC :=
            ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨v, hu₂v⟩
          rcases hu₂ with hAu₂ | hBu₂ | hCu₂
          · refine Or.inr ⟨u₁, u₂, by grind, ⟨hAu₁, hdu₁, hAu₂, ?_⟩⟩
            have _ : G.degree u₂ < 7 := by
              simp only [f, hAu₂, ↓reduceDIte] at hfu₂
              have hfA : fA 7 = 2 / 8 := by
                simp only [fA, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.cast_ofNat]
                linarith
              have hf : 2 / 8 < fA (G.degree u₂) := lt_trans (by linarith) hfu₂
              exact Nat.lt_of_succ_le <| fA_decreasing' (hfA ▸ hf)
            have _ : 4 ≤ G.degree u₂ := by
              have h : f G ABC u₂ < fA 3 := by
                refine lt_of_le_of_lt hfus ?_
                rw [fA4 hAu₁ hdu₁]
                simp only [fA, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.cast_ofNat]
                linarith
              refine fA_decreasing' ?_
              simp only [f, hAu₂, ↓reduceDIte] at h
              exact h
            have hdu₂ : G.degree u₂ = 4 ∨ G.degree u₂ = 5 ∨ G.degree u₂ = 6 := by lia
            simp only [f, hAu₂, ↓reduceDIte] at hfu₂
            rcases hdu₂ with hdu₂ | hdu₂ | hdu₂
            · simp only [one_div, γ, hAu₂, ↓reduceDIte, fA, hdu₂, Nat.add_one_sub_one,
              OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.cast_ofNat, not_le] at hγu₂
              grind
            · simp only [one_div, γ, hAu₂, ↓reduceDIte, fA, hdu₂, Nat.add_one_sub_one,
              OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.cast_ofNat, not_le] at hγu₂
              grind
            · exact hdu₂
          · simp only [f, hBu₂, not_A_of_B, ↓reduceDIte] at hfu₂
            have hdu₂ : G.degree u₂ ≤ 3 := by
              have hfB : fB 4 = 4 / 15 := by
                simp only [fB, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one,
                  Nat.reduceEqDiff, Nat.cast_ofNat]
                linarith
              exact Nat.le_of_lt_succ <| fB_decreasing' (hfB ▸ hfu₂)
            have _ : 0 < G.degree u₂ := G.degree_pos_iff_exists_adj _ |>.mpr ⟨v, hu₂v⟩
            have hdu₂ : G.degree u₂ = 1 ∨ G.degree u₂ = 2 ∨ G.degree u₂ = 3 := by lia
            rcases hdu₂ with hdu₂ | hdu₂ | hdu₂
            · refine Or.inl <| Claim5 hG ih ⟨u₂, ?_, Nat.le_of_eq hdu₂⟩
              simp only [mem_iff, hBu₂, or_true, not_A_of_B, not_C_of_B, or_false]
            · rw [γB2 hBu₂ hdu₂] at hγu₂
              grind only
            · exact Or.inl <| Corollary9 hG hBu₂ hdu₂ ih ⟨v, hu₂v, hCv⟩
          · have h : 1 / 6 < f G ABC u₂ := by linarith
            have hdu₂ : G.degree u₂ < 2 := by
              have hfC : fC 2 = 1 / 6 := by
                simp only [fC, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, or_true]
              simp only [f, hCu₂, not_A_of_C, not_B_of_C, ↓reduceDIte] at h
              rw [← hfC] at h
              exact Nat.lt_of_succ_le <| fC_decreasing' h
            refine Or.inl <| Claim5 hG ih ⟨u₂, ?_, Nat.le_of_lt_succ hdu₂⟩
            simp only [mem_iff, hCu₂, or_true, not_A_of_C, not_B_of_C]
      · let hdegu₁ := @fB_le_13_if_2_le_deg _ G _ _ _ hBu₁ |>.mt <| not_le.mpr hfu₁
        refine Or.inl <| Claim5 hG ih ⟨u₁, by simp only [mem_iff, hBu₁, or_true, true_or], ?_⟩
        exact Nat.le_of_not_lt hdegu₁
      · let hdegu₁ :=
          @fC_le_16_if_2_le_deg _ G _ _ _ hCu₁ |>.mt <| not_le.mpr <| lt_trans (by linarith) hfu₁
        refine Or.inl <| Claim5 hG ih ⟨u₁, by simp only [mem_iff, hCu₁, or_true], ?_⟩
        exact Nat.le_of_not_lt hdegu₁

lemma Claim13 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) {v w : Fin n} (hvw : G.Adj v w)
    (hCv : ABC.C v) (hdv : G.degree v = 3) (hCw : ABC.C w) (hdw : G.degree w = 3)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  cases (_neighborhood_3' hG hCv hCw hvw hdv hdw ih) with
  | inl h => exact h
  | inr h => ?_
  obtain ⟨x, y, hNv, hAx, hdx, hAy, hdy⟩ := h
  cases (_neighborhood_3' hG hCw hCv hvw.symm hdw hdv ih) with
  | inl h => exact h
  | inr h => ?_
  obtain ⟨s, t, hNw, hAs, hds, hAt, hdt⟩ := h
  let S := {x, y} ∩ G.N2_of_Finset {w}
  if hS : #S = 0 then
    have hS' : S = ∅ := card_eq_zero.mp hS
    have heq : x = s ∧ y = t := by
      refine ⟨?_, ?_⟩
      · have hxnew : x ≠ w := by grind
        have hx : x ∉ S := hS' ▸ notMem_empty x
        by_contra
        have hxw : ¬G.Adj x w :=
          fun h ↦ (not_iff_not.mpr (G.mem_neighborFinset w x) |>.mp (by grind)) h.symm
        simp only [N2_of_Finset, mem_singleton, forall_eq, exists_eq_left,
          mem_inter, mem_insert, true_or, mem_filter, mem_univ,
          not_false_eq_true, true_and, not_and, not_exists, S, hxw, hxnew] at hx
        refine (hx v hvw.ne |>.mt <| Decidable.not_not.mpr hvw) ?_
        refine Adj.symm <| G.mem_neighborFinset .. |>.mp ?_
        simp only [hNv, mem_insert, mem_singleton, true_or, or_true]
      · by_contra
        have hy : y ∉ S := hS' ▸ notMem_empty y
        have hynew : y ≠ w := by grind
        have hyw : ¬G.Adj y w :=
          fun h ↦ (not_iff_not.mpr (G.mem_neighborFinset w y) |>.mp (by grind)) h.symm
        simp only [N2_of_Finset, mem_singleton, forall_eq, exists_eq_left,
          mem_inter, mem_insert, mem_filter, mem_univ,
          not_false_eq_true, true_and, not_and, not_exists, S, hyw, hynew, or_true] at hy
        refine (hy v hvw.ne |>.mt <| Decidable.not_not.mpr hvw) ?_
        refine Adj.symm <| G.mem_neighborFinset .. |>.mp ?_
        simp only [hNv, mem_insert, mem_singleton, or_true]
    have hvwABC : {v, w} ∩ ABC.toFinset ≠ ∅ := by
      refine nonempty_iff_ne_empty.mp (nonempty_def.mpr ⟨v, mem_inter.mpr ⟨mem_insert_self .., ?_⟩⟩)
      exact ABC.coe_mem_toFinset.mp <| ABC.mem_iff.mpr <| Or.inr <| Or.inr hCv
    refine Claim0 hvwABC ?_ ih
    have hxy : {x, y} ⊆ ABC.toFinset \ {v, w} := by
      intro u hu
      simp only [mem_insert, mem_singleton] at hu
      rcases hu with hu | hu <;> {
        refine mem_sdiff.mpr ⟨?_, by grind⟩
        simp only [hu, ← ABC.coe_mem_toFinset, ABC.mem_iff, hAx, hAy, true_or]
      }
    calc eval G ABC
      _ = ∑ u ∈ ABC.toFinset \ {v, w}, f G ABC u + ∑ u ∈ {v, w}, f G ABC u := by
        refine Eq.symm <| sum_sdiff ?_
        intro u hu
        simp only [mem_insert, mem_singleton] at hu
        rcases hu with hu | hu <;> {
          --
          refine ABC.coe_mem_toFinset.mp <| ABC.mem_iff.mpr ?_
          simp only [hu, hCv, hCw, or_true]
        }
      _ = ∑ u ∈ (ABC.toFinset \ {v, w}) \ {x, y}, f G ABC u
          + ∑ u ∈ {x, y}, f G ABC u + ∑ u ∈ {v, w}, f G ABC u := by
        simp only [add_left_inj]
        refine Eq.symm <| sum_sdiff hxy
      _ = ∑ u ∈ (ABC.toFinset \ {v, w}) \ {x, y}, f G (ABC \ {v, w}) u
          + ∑ u ∈ {x, y}, f G ABC u + ∑ u ∈ {v, w}, f G ABC u := by
        simp only [add_left_inj]
        refine sum_congr rfl ?_
        exact fun _ hu ↦ f_eq_sdiff <| mem_sdiff.mp (mem_sdiff.mp hu |>.1) |>.2
      _ ≤ ∑ u ∈ (ABC.toFinset \ {v, w}) \ {x, y}, f (G.deleteIncidencesOf {v, w}) (ABC \ {v, w}) u
          + ∑ u ∈ {x, y}, f G ABC u + ∑ u ∈ {v, w}, f G ABC u := by
        refine add_le_add_left ?_ _
        refine add_le_add_left ?_ _
        exact sum_le_sum fun _ _ ↦ f_mono deleteIncidencesOf_le
      _ = ∑ u ∈ (ABC.toFinset \ {v, w}) \ {x, y}, f (G.deleteIncidencesOf {v, w}) (ABC \ {v, w}) u
          + ∑ u ∈ {x, y}, f (G.deleteIncidencesOf {v, w}) (ABC \ {v, w}) u
          - ∑ u ∈ {x, y}, f (G.deleteIncidencesOf {v, w}) (ABC \ {v, w}) u
          + ∑ u ∈ {x, y}, f G ABC u + ∑ u ∈ {v, w}, f G ABC u := by
        simp only [add_sub_cancel_right]
      _ = ∑ u ∈ (ABC.toFinset \ {v, w}), f (G.deleteIncidencesOf {v, w}) (ABC \ {v, w}) u
          - ∑ u ∈ {x, y}, f (G.deleteIncidencesOf {v, w}) (ABC \ {v, w}) u
          + ∑ u ∈ {x, y}, f G ABC u + ∑ u ∈ {v, w}, f G ABC u := by
        simp only [add_left_inj, sub_left_inj]
        refine sum_sdiff hxy
      _ = eval (G.deleteIncidencesOf {v, w}) (ABC \ {v, w})
          - ∑ u ∈ {x, y}, f (G.deleteIncidencesOf {v, w}) (ABC \ {v, w}) u
          + ∑ u ∈ {x, y}, f G ABC u + ∑ u ∈ {v, w}, f G ABC u := by
        simp only [add_left_inj, sub_left_inj, ← ABC.sdiff_toFinset]
        rfl
      _ = eval (G.deleteIncidencesOf {v, w}) (ABC \ {v, w})
          + (∑ u ∈ {x, y}, f G ABC u + ∑ u ∈ {v, w}, f G ABC u
            - ∑ u ∈ {x, y}, f (G.deleteIncidencesOf {v, w}) (ABC \ {v, w}) u) := by lia
    refine (add_le_iff_nonpos_right _).mpr ?_
    have hxy : x ≠ y := by grind
    rw [sum_pair hxy, sum_pair hvw.ne, sum_pair hxy]
    rw [fA4 hAx hdx, fA6 hAy hdy, fC3 hCv hdv, fC3 hCw hdw]
    have hAx' : (ABC \ {v, w}).A x := ⟨hAx, by grind⟩
    have hAy' : (ABC \ {v, w}).A y := ⟨hAy, by grind⟩
    have hdx' : (G.deleteIncidencesOf {v, w}).degree x = 2 := by
      have hNx : {v, w} ⊆ G.neighborFinset x := by
        intro u hu
        simp only [mem_insert, mem_singleton] at hu
        exact mem_neighborFinset_symm <| by grind
      let hobj := degree_deleteIncidencesOf_neighbor G hNx
      grind [Adj.ne]
    have hdy' : (G.deleteIncidencesOf {v, w}).degree y = 4 := by
      have hNy : {v, w} ⊆ G.neighborFinset y := by
        intro u hu
        simp only [mem_insert, mem_singleton] at hu
        exact mem_neighborFinset_symm <| by grind
      let hobj := degree_deleteIncidencesOf_neighbor G hNy
      grind [Adj.ne]
    rw [fA2 hAx' hdx', fA4 hAy' hdy']
    linarith
  else
    refine Claim2' G ABC {w}
      (singleton_nonempty _) hG
      (singleton_subset_iff.mpr <| hG <| Set.mem_toFinset.mpr (G.mem_support.mpr ⟨v, hvw.symm⟩))
      respects_singleton ih InducesLinearForest_singleton ?_
    simp only [card_singleton, Nat.cast_one, ge_iff_le, tsub_le_iff_right]
    have hNw' : G.closed_neighborFinset_of_Finset {w} = {v, w, s, t} := by
      simp only [closed_neighborFinset_of_singleton_eq]
      grind
    have hγz {z : Fin n} (hz : z ∈ S) : 1 / 21 ≤ γ G ABC z := by
      simp only [mem_inter, mem_insert, mem_singleton, S] at hz
      rcases hz.1 with hz | hz
      · subst hz
        simp only [one_div, γ, hAx, ↓reduceDIte, fA, hdx, Nat.add_one_sub_one, OfNat.ofNat_ne_zero,
          ↓reduceIte, OfNat.ofNat_ne_one, Nat.cast_ofNat]
        linarith
      · subst hz
        simp only [one_div, γ, hAy, ↓reduceDIte, fA, hdy, Nat.add_one_sub_one, OfNat.ofNat_ne_zero,
          ↓reduceIte, OfNat.ofNat_ne_one, Nat.cast_ofNat]
        linarith
    rw [hNw']
    calc ∑ u ∈ {v, w, s, t}, f G ABC u
      _ = f G ABC v + f G ABC w + f G ABC s + f G ABC t := by grind [Adj.ne]
      _ = (1 : ℝ) / 6 + 1 / 6 + 2 / 5 + 2 / 7 := by
        rw [fC3 hCv hdv, fC3 hCw hdw, fA4 hAs hds, fA6 hAt hdt]
      _ ≤ 1 + 1 / (21 : ℝ) := by linarith
    refine add_le_add_right ?_ _
    have hsumS : ∑ z ∈ S, γ G ABC z ≤ ∑ z ∈ G.N2_of_Finset {w}, γ G ABC z := by
      refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ γ_nonneg ..)
      simp only [inter_subset_right, S]
    refine le_trans ?_ hsumS
    have hsumS : #S * (1 / (21 : ℝ)) ≤ ∑ z ∈ S, γ G ABC z := by
      rw [← sum_const' S (fun _ _ ↦ rfl)]
      exact sum_le_sum (fun _ ↦ hγz)
    refine le_trans ?_ hsumS
    simp only [one_div, inv_pos, Nat.ofNat_pos, le_mul_iff_one_le_left, Nat.one_le_cast]
    exact Nat.one_le_iff_ne_zero.mpr hS

end Tripartition
end ABC
end CaroWeiType
