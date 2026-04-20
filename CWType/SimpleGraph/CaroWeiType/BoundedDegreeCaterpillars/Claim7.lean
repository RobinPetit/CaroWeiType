import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim1
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim5

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

private lemma Claim7_calc {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) {v x y z : Fin n} (hNv : G.neighborFinset v = {x, y, z})
    (hBv : ABC.B v) (hAx : ABC.A x) (hy : y ∈ ABC) (hz : z ∈ ABC)
    (hdegv : G.degree v = 3) (hdegx : G.degree x = 2)
    (hfy : f G ABC y ≤ 2 / 5) (hfz : f G ABC z ≤ 2 / 5) :
    eval G ABC ≤ eval (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z}) + 1 := by
  obtain ⟨hxney, hxnez, hynez⟩ := by
    rw [degree] at hdegv
    exact pairwise_ne_of_triplet (hNv ▸ hdegv)
  calc eval G ABC
    _ = ∑ u ∈ (ABC.toFinset \ {v, x, y, z}), f G ABC u
        + ∑ u ∈ ({v, x, y, z} : Finset _), f G ABC u := by
      refine Eq.symm <| sum_sdiff (by grind [ABC.mem_iff, ABC.coe_mem_toFinset.mp])
    _ ≤ ∑ u ∈ (ABC.toFinset \ {v, x, y, z}),
        f (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z}) u
        + ∑ u ∈ ({v, x, y, z} : Finset _), f G ABC u := by
      refine add_le_add_left (sum_le_sum ?_) _
      intro u hu
      simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hu
      simp only [f, dite_eq_ite, mem_insert, mem_singleton, not_or, sdiff.eq_1]
      have : (G.deleteIncidencesOf {v, y, z}).degree u ≤ G.degree u :=
        deleteIncidencesOf_degree_le
      rcases ABC.coe_mem_toFinset.mpr hu.1 with hAu | hBu | hCu
      · simp only [hAu, ↓reduceIte, mem_insert, hu.2, mem_singleton, or_self,
          not_false_eq_true, and_self, fA_decreasing this]
      · simp only [hBu, not_A_of_B, ↓reduceIte, mem_insert, hu.2, mem_singleton,
          or_self, not_false_eq_true, and_true, and_self, fB_decreasing this]
      · simp only [hCu, not_A_of_C, ↓reduceIte, not_B_of_C, mem_insert, hu.2, or_self,
          mem_singleton, not_false_eq_true, and_true, and_self, fC_decreasing this]
    _ = ∑ u ∈ (ABC.toFinset \ {v, x, y, z}),
        f (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z}) u
        + f (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z}) x
        - f (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z}) x
        + ∑ u ∈ ({v, x, y, z} : Finset _), f G ABC u := by
      grind
    _ = ∑ u ∈ (ABC.toFinset \ {v, y, z}), f (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z}) u
        - f (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z}) x
        + ∑ u ∈ ({v, x, y, z} : Finset _), f G ABC u := by
      simp only [add_left_inj, sub_left_inj]
      rw [← sum_singleton (f _ _ ·) _]
      have : ((ABC.toFinset \ {v, y, z}) \ ({x} : Finset _)) = (ABC.toFinset \ {v, x, y, z}) := by
        grind
      rw [← this]
      refine sum_sdiff ?_
      intro a
      simp only [mem_singleton, mem_sdiff, mem_insert, not_or]
      intro ha; subst ha
      refine ⟨?_, ?_, hxney, hxnez⟩
      · exact ABC.coe_mem_toFinset.mp <| by simp only [mem_iff, hAx, true_or]
      · exact (G.mem_neighborFinset .. |>.mp <| hNv ▸ mem_insert_self ..).ne'
    _ = eval (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z})
        - f (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z}) x
        + ∑ u ∈ ({v, x, y, z} : Finset _), f G ABC u := by
      simp only [add_left_inj, sub_left_inj, ← sdiff_toFinset]
      rfl
    _ = eval (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z})
        + (∑ u ∈ ({v, x, y, z} : Finset _), f G ABC u
        - f (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z}) x) := by
      lia
  refine add_le_add_right ?_ _
  haveI : v ≠ x ∧ v ≠ y ∧ v ≠ z := by
    refine ⟨?_, ?_, ?_⟩ <;> {
      intro heq; subst heq
      exact @SimpleGraph.irrefl _ G v <| (G.mem_neighborFinset ..).mp
        <| hNv ▸ (by simp only [mem_insert, mem_singleton, true_or, or_true])
    }
  obtain ⟨hvnex, hvney, hvnez⟩ := this
  have : ∑ u ∈ {v, x, y, z}, f G ABC u = f G ABC v + f G ABC x + f G ABC y + f G ABC z := by
    calc _
      _ = f G ABC v + ∑ u ∈ {v, x, y, z} \ {v}, f G ABC u := by
        rw [add_comm (f G ABC v) _, ← sum_singleton (f _ _ ·) v]
        exact Eq.symm <| sum_sdiff <| by simp
      _ = f G ABC v + ∑ u ∈ {x, y, z}, f G ABC u := by
        simp only [add_right_inj]
        refine sum_congr (by grind) (fun x hx ↦ rfl)
    grind
  rw [this, fB3 hBv hdegv, fA2 hAx hdegx]
  suffices f G ABC y + f G ABC z ≤ f (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z}) x by
    grind
  calc _
    _ ≤ 2 / (5 : ℝ) + f G ABC z := add_le_add_left hfy (f G ABC z)
    _ ≤ 2 / (5 : ℝ) + 2 / (5 : ℝ) := add_le_add_right hfz _
    _ ≤ 5 / (6 : ℝ) := by linarith
  suffices (G.deleteIncidencesOf {v, y, z}).degree x ≤ 1 by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h0 | h1
    · rw [@fA0 _ (G.deleteIncidencesOf {v, y, z}) _ (ABC \ {v, y, z}) _ ⟨hAx, by grind⟩ h0]
      grind
    · rw [@fA1 _ (G.deleteIncidencesOf {v, y, z}) _ (ABC \ {v, y, z}) _ ⟨hAx, by grind⟩ h1]
  suffices (G.deleteIncidencesOf {v, y, z}).neighborFinset x ⊆ G.neighborFinset x \ {v} by
    rw [degree]
    refine le_trans (card_le_card this) ?_
    rw [card_setminus_singleton' (mem_neighborFinset_symm (hNv ▸ mem_insert_self ..)) hdegx]
  intro u
  simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_neighborFinset, mem_insert,
    mem_singleton, inf_adj, iInf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet,
    Sym2.mem_iff, not_and, not_or, ne_eq, mem_sdiff, and_imp]
  intro hxu
  simp only [hxu, forall_const, true_and, hxu.ne, not_false_eq_true, and_true, forall_eq_or_imp,
    forall_eq, and_imp]
  exact fun _ h _ _ _ _ ↦ Ne.symm h

private lemma _Claim7_resp {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v w y z : Fin n} (hBv : ABC.B v) (hAw : ABC.A w)
    (hNv : G.neighborFinset v = {w, y, z}) (hdegw : G.degree w = 2)
    {s : Finset (Fin n)} (hs : s ⊆ (ABC \ {v, y, z}).toFinset)
    (hsresp : respects s (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z})) :
    respects (s ∪ {v}) G ABC := by
  intro u hu
  simp only [union_singleton, mem_insert] at hu
  rcases hu with hu | hu
  · subst hu
    simp only [hBv, not_A_of_B, degree_in, union_singleton, mem_neighborFinset,
      SimpleGraph.irrefl, not_false_eq_true, inter_insert_of_notMem, IsEmpty.forall_iff,
      forall_const, not_C_of_B, card_eq_zero, and_true, true_and]
    refine le_trans ?_ (le_of_eq <| card_singleton w)
    refine card_le_card ?_
    intro a
    simp only [mem_inter, mem_neighborFinset, mem_singleton, and_imp]
    intro hua has
    have H : a ∈ ({w, y, z} : Finset _) := hNv ▸ G.mem_neighborFinset .. |>.mpr hua
    let H' := mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs has) |>.2
    simp only [mem_insert, mem_singleton, not_or] at H'
    simp only [mem_insert, mem_singleton] at H
    rcases H with h | h | h
    · exact h
    · exact H'.2.1 h |>.elim
    · exact H'.2.2 h |>.elim
  · let hu' := mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs hu) |>.2
    if hvu : v ∈ G.neighborFinset u then
      have : u = w := by
        have hin := hNv ▸ G.mem_neighborFinset .. |>.mpr
          <| G.mem_neighborFinset .. |>.mp hvu |>.symm
        have heq : ({v, y, z} : Finset _) = ({y, z, v} : Finset _) := by grind
        exact eq_of_mem_of_notMem hin (heq ▸ hu')
      subst this
      simp only [hAw, degree_in, union_singleton, forall_const, not_B_of_A, IsEmpty.forall_iff,
        not_C_of_A, card_eq_zero, and_self, and_true, ge_iff_le]
      exact le_trans degree_in_le_degree (le_of_eq hdegw)
    else
      have heq : G.degree_in (s ∪ {v}) u = (G.deleteIncidencesOf {v, y, z}).degree_in s u := by
        refine congrArg Finset.card ?_
        ext a
        simp only [union_singleton, mem_inter, mem_neighborFinset, mem_insert,
          deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_singleton, inf_adj,
          iInf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and,
          not_or, ne_eq]
        constructor
        · intro ⟨hua, ha⟩
          rcases ha with ha | ha
          · subst ha
            simp only [hua, forall_const, true_and, hua.ne, not_false_eq_true, and_true,
              forall_eq_or_imp, hua.ne', not_true_eq_false, and_false, forall_eq, false_and]
            exact hvu <| (G.mem_neighborFinset ..).mpr hua
          · simp only [hua, forall_const, true_and, hua.ne, not_false_eq_true, and_true,
              forall_eq_or_imp, forall_eq, ha]
            let hobj := mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs hu) |>.2
            let hobj' := mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs ha) |>.2
            grind
        · intro ⟨⟨hua, h⟩, ha⟩
          simp only [hua, ha, or_true, and_self]
      rw [heq]
      obtain ⟨h₁, h₂, h₃⟩ := hsresp u hu
      refine ⟨?_, ?_, ?_⟩
      · exact fun h ↦ h₁ ⟨h, hu'⟩
      · exact fun h ↦ h₂ ⟨h, hu'⟩
      · exact fun h ↦ h₃ ⟨h, hu'⟩

lemma Claim7 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} (hG : G.support.toFinset ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    (∃ v w, (G.degree v = 3 ∧ ABC.B v ∧ G.degree w = 2 ∧ ABC.A w ∧ G.Adj v w))
      → Objective G ABC := by
  intro h
  obtain ⟨v, w, hdegv, hBv, hdegw, hAw, hvw⟩ := h
  obtain ⟨x, y, z, hNv, hzy, hyx⟩ := neighborFinset_eq_deg3' (f G ABC ·) hdegv
  have hinABC {v₁ v₂} (h' : G.Adj v₁ v₂) : v₁ ∈ ABC :=
    ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨v₂, h'⟩
  have hv : v ∈ ABC := hinABC hvw
  have hinABC_Nv {v'} (h' : v' ∈ G.neighborFinset v) : v' ∈ ABC :=
    hinABC <| Adj.symm <| G.mem_neighborFinset _ _ |>.mp h'
  have hx : x ∈ ABC := hinABC_Nv (by simp [hNv])
  have hy : y ∈ ABC := hinABC_Nv (by simp [hNv])
  have hz : z ∈ ABC := hinABC_Nv (by simp [hNv])
  if h' : 1 / 3 ≤ γ G ABC x + γ G ABC y + γ G ABC z then
    refine Claim1 G ABC v ?_ ?_ ih ?_
    · refine ABC.coe_mem_toFinset.mpr <| hG ?_
      exact Set.mem_toFinset.mpr <| (mem_support G).mpr ⟨w, hvw⟩
    · intro u hu
      refine hG <| Set.mem_toFinset.mpr <| (mem_support G).mpr ⟨v, ?_⟩
      exact Adj.symm <| G.mem_neighborFinset .. |>.mp hu
    · calc f G ABC v
        _ = 1 / 3 := fB3 hBv hdegv
        _ ≤ γ G ABC x + γ G ABC y + γ G ABC z := h'
        _ = ∑ u ∈ G.neighborFinset v, γ G ABC u := by
          rw [hNv]
          suffices x ≠ y ∧ x ≠ z ∧ y ≠ z by grind
          rw [degree] at hdegv
          refine ⟨?_, ?_, ?_⟩ <;> { intro heq; subst heq; grind [hNv ▸ hdegv] }
  else if hδ : ∃ u ∈ ABC, G.degree u ≤ 1 then
    exact Claim5 hG ih hδ
  else
    simp only [not_exists, not_and, not_le] at hδ
    have hfw : f G ABC w = 2 / 3 := fA2 hAw hdegw
    have hfy : f G ABC y ≤ 2 / 5 := by
      by_contra
      simp only [not_le] at this
      obtain ⟨hAy, hdegy⟩ := A2_or_A3_of_f_lt_25_of_2_le_deg (hδ y hy) hy this
      have hγy : γ G ABC y = 1 / 6 := by
        rcases hdegy with h | h <;> { simp only [γA3, γA2, h, hAy] }
      obtain ⟨hAx, hdegx⟩ :=
        A2_or_A3_of_f_lt_25_of_2_le_deg (hδ x hx) hx <| lt_of_lt_of_le this hyx
      have hγx : γ G ABC x = 1 / 6 := by
        rcases hdegx with h | h <;> { simp only [γA3, γA2, h, hAx] }
      rw [hγx, hγy] at h'
      grind
    have heq : w = x := by
      have hw : w ∈ ({x, y, z} : Finset _) := hNv ▸ (mem_neighborFinset G v w).mpr hvw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with hx | hy | hz <;> grind
    subst heq
    obtain ⟨s, hs, hsf, hsresp, hscard⟩ := by
      refine ih (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z}) (ABC.sdiff_card ?_)
      exact nonempty_iff_ne_empty.mp ⟨y, by simp [ABC.coe_mem_toFinset.mp hy]⟩
    have h₁ : s ∪ {v} ⊆ ABC.toFinset := by
      intro u
      simp only [union_singleton, mem_insert, ← coe_mem_toFinset]
      intro h
      rcases h with h | h
      · exact h ▸ hv
      · exact ABC.coe_mem_toFinset.mpr <| mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs h) |>.1
    have hresp : respects (s ∪ {v}) G ABC := _Claim7_resp hBv hAw hNv hdegw hs hsresp
    refine ⟨s ∪ {v}, h₁, ?_, hresp, ?_⟩
    · intro t ht htne
      if hvt : v ∈ t then
        refine ⟨v, hvt, ?_⟩
        refine le_trans ?_ (le_of_eq <| card_singleton w)
        refine card_le_card ?_
        intro u hu
        simp only [mem_inter, mem_neighborFinset, mem_singleton] at hu ⊢
        let hin := hNv ▸ G.mem_neighborFinset .. |>.mpr hu.1
        by_contra
        simp only [mem_insert, this, mem_singleton, false_or] at hin
        rcases hin with hu' | hu' <;> {
          subst hu'
          rcases mem_union.mp (ht hu.2) with h' | h'
          · grind [mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs h') |>.2]
          · grind [G.irrefl]
        }
      else
        have hts : t ⊆ s := by
          intro a ha
          rcases mem_union.mp (ht ha) with ha' | ha'
          · exact ha'
          · simp only [mem_singleton] at ha'
            exact hvt (ha' ▸ ha) |>.elim
        obtain ⟨x', hx't, hx'⟩ := hsf t hts htne
        refine ⟨x', hx't, ?_⟩
        refine le_trans ?_ hx'
        refine card_le_card ?_
        intro u hu
        simp only [mem_inter, mem_neighborFinset] at hu
        simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_inter,
          mem_neighborFinset, mem_insert, mem_singleton, inf_adj, hu.1, iInf_adj, deleteEdges_adj,
          Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, true_and, not_or, ne_eq, hu.1.ne,
          not_false_eq_true, and_true, forall_eq_or_imp, forall_eq, hu.2]
        let h'x' := mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs (hts hx't)) |>.2
        let h'u := mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs (hts hu.2)) |>.2
        grind
    · calc eval G ABC
        _ ≤ eval (G.deleteIncidencesOf {v, y, z}) (ABC \ {v, y, z}) + 1 :=
          Claim7_calc G ABC hNv hBv hAw hy hz hdegv hdegw hfy (hzy.trans hfy)
        _ ≤ #s + (1 : ℝ) :=
          add_le_add_left hscard _
        _ = #(s ∪ {v}) := by
          rw [← Nat.cast_one, ← card_singleton v, ← Nat.cast_add]
          refine Nat.cast_inj.mpr ?_
          refine Eq.symm (card_union_of_disjoint <| disjoint_singleton_right.mpr <| fun h ↦ ?_)
          let hobj := mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs h) |>.2
          simp at hobj

end Tripartition
end ABC
end CaroWeiType
