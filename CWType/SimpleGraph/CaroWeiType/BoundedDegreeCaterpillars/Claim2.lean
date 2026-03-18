import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

lemma Claim2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (F : Finset (Fin n)) (hFne : F.Nonempty)
    (hF : F ⊆ ABC.toFinset) (hF' : respects F G ABC)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    G.InducesLinearForest F →
      #F ≥ eval G ABC - eval (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
                             (ABC \ G.closed_neighborFinset_of_Finset F) →
        Objective G ABC := by
  intro h h'
  have hcap : G.closed_neighborFinset_of_Finset F ∩ ABC.toFinset ≠ ∅ := by
    refine Nonempty.ne_empty <| nonempty_def.mpr ?_
    obtain ⟨x, hx⟩ := nonempty_def.mp hFne
    refine ⟨x, mem_inter.mpr ⟨closed_neighborFinset_contains_Finset G F <| hx, hF hx⟩⟩
  obtain ⟨s', hs', hlf', hresp, hcard'⟩ :=
    ih (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
      (ABC \ (G.closed_neighborFinset_of_Finset F)) (Tripartition.sdiff_card ABC hcap)
  have hresp : respects (s' ∪ F) G ABC := by
    refine respects_union G ABC (respects_mono G ABC hs' hresp) hF' ?_
    intro y hy z hz this
    have _ : y ∈ G.closed_neighborFinset_of_Finset F := by
      simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
      refine Or.inr ⟨z, hz, this⟩
    let hobj := hs' hy
    simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff,
      mem_filter, mem_univ, true_and] at hobj
    have _ : y ∉ G.closed_neighborFinset_of_Finset F := by grind
    contradiction
  refine ⟨s' ∪ F, fun _ _ ↦ by grind [Tripartition.toFinset_mono], ?_, hresp, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro t ht htne
      have _ : (t ∩ s') ⊆ s' := inter_subset_right
      if hcap : t ∩ s' = ∅ then exact h.1 t (by grind) htne
      else ?_
      obtain ⟨x, hx, hx'⟩ := hlf'.1 (t ∩ s') (inter_subset_right) hcap
      refine ⟨x, mem_of_mem_filter x hx, ?_⟩
      refine le_trans ?_ hx'
      refine Finset.card_le_card ?_
      intro y
      simp only [mem_filter, mem_inter, and_imp, deleteIncidencesOf, deleteIncidenceSet]
      intro hy hxy
      simp only [hy, true_and, closed_neighborFinset_of_Finset, mem_filter, mem_univ,
        incidenceSet, inf_adj, hxy, iInf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet,
        Sym2.mem_iff, not_or, ne_eq, hxy.ne, not_false_eq_true, and_true]
      have hnotinF {z} (hz : z ∈ s') : z ∉ G.closed_neighborFinset_of_Finset F := by
        let hobj := hs' hz
        simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff,
          mem_filter, mem_univ, true_and] at hobj
        grind
      refine ⟨?_, ?_⟩
      · rcases mem_union.mp <| ht hy with hy | hy
        · exact hy
        · refine (hnotinF <| (mem_inter.mp hx).2) ?_ |>.elim
          simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
          exact Or.inr ⟨y, hy, hxy⟩
      · intro w h
        have hw : w ∈ G.closed_neighborFinset_of_Finset F := by
          simp [h, closed_neighborFinset_of_Finset]
        constructor
        · exact fun heq ↦ (hnotinF (mem_inter.mp hx).2) (heq ▸ hw)
        · suffices y ∉ G.closed_neighborFinset_of_Finset F by
            exact fun heq ↦ this (heq ▸ hw)
          rcases mem_union.mp <| ht hy with hy | hy
          · exact hnotinF hy
          · refine (hnotinF (mem_inter.mp hx).2) ?_ |>.elim
            simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
            exact Or.inr ⟨y, hy, hxy⟩
    · intro x hx
      simp only [respects, degree_in] at hresp
      have hxABC : x ∈ ABC := by
        rcases mem_union.mp hx with hx | hx
        · let hobj := hs' hx
          simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff,
            mem_filter, mem_univ, true_and] at hobj
          grind [Tripartition.mem_iff]
        · exact ABC.coe_mem_toFinset.mpr <| hF hx
      simp only [Tripartition.mem_iff] at hxABC
      grind
  · simp only [ge_iff_le, tsub_le_iff_right] at h'
    calc eval G ABC
      _ = eval G ABC - eval (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
                             (ABC \ G.closed_neighborFinset_of_Finset F)
                     + eval (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
                             (ABC \ G.closed_neighborFinset_of_Finset F) := by
        simp only [sub_add_cancel]
      _ ≤ #F + eval (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
                             (ABC \ G.closed_neighborFinset_of_Finset F) := by
        simp only [sub_add_cancel, h']
      _ ≤ #F + #s' := by
        simp only [add_le_add_iff_left, hcard']
      _ = #s' + #F := add_comm ..
      _ = #(s' ∪ F) + #(s' ∩ F) := by
        simp only [← Nat.cast_add]
        refine Nat.cast_inj.mpr ?_
        exact Eq.symm <| card_union_add_card_inter ..
      _ = #(s' ∪ F) := by
        simp only [add_eq_left, Nat.cast_eq_zero, card_eq_zero]
        ext x
        simp only [mem_inter, notMem_empty, iff_false, not_and]
        intro hx
        let hobj := hs' hx
        simp [Tripartition.sdiff, Tripartition.toFinset] at hobj
        have hfinal : x ∉ G.closed_neighborFinset_of_Finset F := by grind
        exact fun hx ↦ hfinal <| closed_neighborFinset_contains_Finset G F hx

private lemma _γ_on_N2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (F : Finset (Fin n)) :
    ∑ w ∈ G.N2_of_Finset F, γ G ABC w ≤ ∑ w ∈ G.N2_of_Finset F,
        (f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
          (ABC \ G.closed_neighborFinset_of_Finset F) w - f G ABC w) := by
  refine sum_le_sum ?_
  intro w hw
  have hwNF : w ∉ G.closed_neighborFinset_of_Finset F := by
    exact fun _ ↦ by grind [closed_neighborFinset_of_Finset, N2_of_Finset]
  have hdeg : (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F).degree w + 1
      ≤ G.degree w := by
    refine Order.add_one_le_iff.mpr ?_
    repeat rw [degree]
    refine Finset.card_lt_card ⟨?_, ?_⟩
    · intro x hx
      simp only [closed_neighborFinset_of_Finset, deleteIncidencesOf, deleteIncidenceSet,
        incidenceSet, mem_neighborFinset, mem_filter, mem_univ, true_and, inf_adj, iInf_adj,
        deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq,
        N2_of_Finset] at hx hw
      exact (G.mem_neighborFinset ..).mpr hx.1
    · refine sdiff_nonempty.mp ?_
      simp only [N2_of_Finset, mem_filter, mem_univ, true_and] at hw
      obtain ⟨x, hx, y, hy, hwy, hyx⟩ := hw.2.2
      refine ⟨y, ?_⟩
      refine mem_sdiff.mpr ⟨(G.mem_neighborFinset w y).mpr hwy, ?_⟩
      have hy' : y ∈ G.closed_neighborFinset_of_Finset F := by
        simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
        exact Or.inr ⟨x, hx, hyx⟩
      simp only [mem_neighborFinset]
      exact Adj.symm.mt <| deleteIncidencesOf_notadj G hy'
  have hdegw : 1 ≤ G.degree w := Nat.one_le_of_lt hdeg
  have h1 : ((((G.degree w- 1) : ℕ) : ℝ) + 1) = (G.degree w : ℝ) := by
    simp only [Nat.cast_one, sub_add_cancel, Nat.cast_sub hdegw]
  rw [γ, f]
  have hAiff : ABC.A w ↔ (ABC \ G.closed_neighborFinset_of_Finset F).A w := by
    exact ⟨fun h ↦ by simp [Tripartition.sdiff, h, hwNF], fun h ↦ h.1⟩
  have hBiff : ABC.B w ↔ (ABC \ G.closed_neighborFinset_of_Finset F).B w := by
    exact ⟨fun h ↦ by simp [Tripartition.sdiff, h, hwNF], fun h ↦ h.1⟩
  have hCiff : ABC.C w ↔ (ABC \ G.closed_neighborFinset_of_Finset F).C w := by
    exact ⟨fun h ↦ by simp [Tripartition.sdiff, h, hwNF], fun h ↦ h.1⟩
  if hA : ABC.A w then
    simp only [hA, ↓reduceDIte, f, tsub_le_iff_right, sub_add_cancel,
      ge_iff_le, hAiff.mp hA, fA, Nat.pred_eq_succ_iff, zero_add]
    split_ifs
    any_goals grind [f_le_56]
    · rw [h1]
      exact mul_le_one (Nat.cast_pos'.mpr hdegw) (Nat.ofNat_le_cast.mpr (by grind))
    · rw [h1]
      ring_nf
      calc ((G.degree w) : ℝ)⁻¹ * 2
        _ ≤ (3 : ℝ)⁻¹ * 2 := by
          simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
          exact inv_anti₀ three_pos (Nat.cast_le.mpr (by grind))
      grind
    · ring_nf
      simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
      refine inv_anti₀ (by grind) ?_
      simp only [add_le_add_iff_left, Nat.cast_le]
      grind
  else if hB : ABC.B w then
    simp only [hA, ↓reduceDIte, hB, fB, Nat.pred_eq_succ_iff, zero_add, Nat.reduceAdd, one_div,
      Tripartition.sdiff, false_and, true_and, fC, dite_eq_ite, ite_not, f, tsub_le_iff_right,
      sub_add_cancel, ge_iff_le, h1]
    split_ifs
    any_goals grind
    · ring_nf
      calc (G.degree w : ℝ)⁻¹ * (4 / (3 : ℝ))
        _ ≤ (2 : ℝ)⁻¹ * (4 / (3 : ℝ)) := by
          simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀]
          exact inv_anti₀ two_pos (Nat.cast_le.mpr (by grind))
        _ ≤ 1 := by grind
    · ring_nf
      calc (G.degree w : ℝ)⁻¹ * (4 / (3 : ℝ))
        _ ≤ (2 : ℝ)⁻¹ * (4 / (3 : ℝ)) := by
          simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀]
          exact inv_anti₀ two_pos (Nat.cast_le.mpr (by grind))
        _ ≤ 5 / (6 : ℝ) := by grind
    · ring_nf
      suffices (4 : ℝ) ≤ G.degree w by
        calc (G.degree w : ℝ)⁻¹ * (4 / (3 : ℝ))
          _ ≤ (4 : ℝ)⁻¹ * (4 / (3 : ℝ)) := by
            simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀]
            exact inv_anti₀ four_pos this
          _ ≤ 1 / (3 : ℝ) := by grind
      exact Nat.cast_le.mpr <| by grind
    · refine div_le_div_iff_of_pos_left (by grind) (by grind) (by grind) |>.mpr ?_
      rw [← Nat.cast_one, ← Nat.cast_add _ 1]
      exact Nat.cast_le.mpr hdeg
 else if hC : ABC.C w then
    simp only [hA, ↓reduceDIte, hB, hC, fC, Nat.pred_eq_succ_iff, zero_add, Nat.reduceAdd, one_div,
      h1, Tripartition.sdiff, false_and, true_and, dite_eq_ite, ite_not, f, tsub_le_iff_right,
      sub_add_cancel, ge_iff_le]
    split_ifs
    any_goals grind
    · ring_nf
      calc (G.degree w : ℝ)⁻¹ * (2 / (3 : ℝ))
        _ ≤ 1⁻¹ * (2 / (3 : ℝ)) := by
          simp only [inv_one, one_mul, Nat.ofNat_pos, div_pos_iff_of_pos_left,
            mul_le_iff_le_one_left]
          rw [← inv_one]
          refine inv_anti₀ one_pos ?_
          exact @Nat.cast_one ℝ _ ▸ Nat.cast_le.mpr hdegw
        _ ≤ 1 := by grind
    · ring_nf
      calc (G.degree w : ℝ)⁻¹ * (2 / (3 : ℝ))
        _ ≤ (4 : ℝ)⁻¹ * (2 / (3 : ℝ)) := by
          simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀]
          refine inv_anti₀ four_pos ?_
          exact @Nat.cast_four ℝ _ ▸ Nat.cast_le.mpr (by grind)
        _ ≤ (1 / (6 : ℝ)) := by grind
    · refine div_le_div_iff_of_pos_left (by grind) (by grind) (by grind) |>.mpr ?_
      rw [← Nat.cast_one, ← Nat.cast_add]
      exact Nat.cast_le.mpr hdeg
  else
    simp [hA, hB, hC]

lemma Claim2' {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (F : Finset (Fin n)) (hFne : F.Nonempty)
    (hG : G.support.toFinset ⊆ ABC.toFinset)
    (hF : F ⊆ ABC.toFinset)
    (hF' : respects F G ABC)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    G.InducesLinearForest F →
      #F ≥ ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G ABC v
        - ∑ w ∈ G.N2_of_Finset F, γ G ABC w →
        Objective G ABC := by
  intro h h'
  refine Claim2 G ABC F hFne hF hF' ih h ?_
  simp_all only [ge_iff_le]
  simp only [eval]
  calc ∑ v ∈ ABC.toFinset, f G ABC v
       - ∑ v ∈ (ABC \ G.closed_neighborFinset_of_Finset F).toFinset,
          f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
            (ABC \ G.closed_neighborFinset_of_Finset F) v
    _ = ∑ v ∈ ABC.toFinset \ (G.closed_neighborFinset_of_Finset F), f G ABC v
        + ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G ABC v
        - ∑ v ∈ (ABC \ G.closed_neighborFinset_of_Finset F).toFinset,
            f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
              (ABC \ G.closed_neighborFinset_of_Finset F) v := by
      simp only [sub_left_inj]
      refine Eq.symm <| sum_sdiff ?_
      intro w
      simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
      intro hw
      rcases hw with hw | hw
      · exact hF hw
      · refine hG <| Set.mem_toFinset.mpr <| G.degree_pos_iff_mem_support w |>.mp ?_
        obtain ⟨x, _, hx⟩ := hw
        exact (degree_pos_iff_exists_adj G w).mpr ⟨x, hx⟩
    _ = (∑ v ∈ ABC.toFinset \ (G.closed_neighborFinset_of_Finset F), f G ABC v
        - ∑ v ∈ (ABC \ G.closed_neighborFinset_of_Finset F).toFinset,
          f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
            (ABC \ G.closed_neighborFinset_of_Finset F) v)
        + ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G ABC v := by
      grind
    _ = (∑ v ∈ ABC.toFinset \ (G.closed_neighborFinset_of_Finset F), f G ABC v
        - ∑ v ∈ ABC.toFinset \ (G.closed_neighborFinset_of_Finset F),
          f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
            (ABC \ G.closed_neighborFinset_of_Finset F) v)
        + ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G ABC v := by
      simp only [Tripartition.toFinset_eq]
    _ = ∑ v ∈ ABC.toFinset \ (G.closed_neighborFinset_of_Finset F), (f G ABC v
          - f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
            (ABC \ G.closed_neighborFinset_of_Finset F) v)
        + ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G ABC v := by
      simp only [sum_sub_distrib]
  refine le_trans ?_ h'
  rw [add_comm ..]
  refine add_le_add_iff_left _ |>.mpr ?_
  refine neg_le_neg_iff.mp ?_
  simp only [neg_neg]
  rw [← sum_neg_distrib]
  calc ∑ w ∈ G.N2_of_Finset F, γ G ABC w
    _ ≤ ∑ w ∈ G.N2_of_Finset F,
        (f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
          (ABC \ G.closed_neighborFinset_of_Finset F) w - f G ABC w) := by
      exact _γ_on_N2 G ABC F
    _ = 0 + ∑ w ∈ G.N2_of_Finset F,
        (f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
          (ABC \ G.closed_neighborFinset_of_Finset F) w - f G ABC w) := by
      simp only [zero_add]
    _ = ∑ w ∈ (ABC.toFinset \ G.closed_neighborFinset_of_Finset F) \ G.N2_of_Finset F,
          (f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
            (ABC \ G.closed_neighborFinset_of_Finset F) w - f G ABC w)
        + ∑ w ∈ G.N2_of_Finset F,
        (f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
          (ABC \ G.closed_neighborFinset_of_Finset F) w - f G ABC w) := by
      simp only [add_left_inj]
      refine Eq.symm <| sum_eq_zero ?_
      intro z hz
      have hz' : z ∉ G.closed_neighborFinset_of_Finset F :=
        mem_sdiff.mp (mem_sdiff.mp hz |>.1) |>.2
      rw [f_eq_in_sdiff _ ABC hz']
      rw [sub_eq_zero]
      refine f_mono_degree _ _ ABC ?_
      repeat rw [degree]
      refine congrArg _ ?_
      ext y
      simp only [closed_neighborFinset_of_Finset, deleteIncidencesOf, deleteIncidenceSet,
        incidenceSet, mem_neighborFinset, mem_filter, mem_univ, true_and, inf_adj, iInf_adj,
        deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq,
        and_iff_left_iff_imp]
      refine fun h ↦ ⟨fun x ↦ ⟨fun h' ↦ ⟨h, fun _ ↦ ?_⟩, h.ne⟩, h.ne⟩
      rcases h' with hx | hx
      · constructor
        · exact fun heq ↦ hz' <| closed_neighborFinset_contains_Finset G F <| heq ▸ hx
        · refine fun heq ↦ hz' ?_
          simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
          exact Or.inr ⟨x, hx, heq ▸ h⟩
      · constructor
        · have hx : x ∈ G.closed_neighborFinset_of_Finset F := by
            simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
            exact Or.inr hx
          exact fun heq ↦ hz' <| heq ▸ hx
        · intro heq
          subst heq
          refine mem_sdiff.mp hz |>.2 ?_
          simp only [N2_of_Finset, mem_filter, mem_univ, true_and]
          simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and, not_or,
            not_exists, not_and] at hz'
          refine ⟨hz'.1, hz'.2, ?_⟩
          · obtain ⟨y, hy, hxy⟩ := hx
            exact ⟨y, hy, x, by grind, h, hxy⟩
    _ = ∑ w ∈ ABC.toFinset \ G.closed_neighborFinset_of_Finset F,
          (f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
            (ABC \ G.closed_neighborFinset_of_Finset F) w - f G ABC w) := by
      refine Finset.sum_sdiff ?_
      intro w
      simp only [N2_of_Finset, mem_filter, mem_univ, true_and, closed_neighborFinset_of_Finset,
        mem_sdiff, not_or, not_exists, not_and, and_imp, forall_exists_index]
      intro hw H x hx y hy hwy hyx
      refine ⟨hG ?_, ⟨hw, H⟩⟩
      simp only [Set.mem_toFinset]
      exact G.degree_pos_iff_mem_support w |>.mp hwy.degree_pos_left
    _ = ∑ w ∈ ABC.toFinset \ G.closed_neighborFinset_of_Finset F,
        -(f G ABC w - f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
              (ABC \ G.closed_neighborFinset_of_Finset F) w) := by
      refine sum_congr rfl ?_
      intro w hw
      exact Eq.symm <| neg_sub ..

lemma Corollary2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (F : Finset (Fin n)) (hFne : F.Nonempty)
    (hG : G.support.toFinset ⊆ ABC.toFinset)
    (hF : F ⊆ ABC.toFinset)
    (hF' : respects F G ABC)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    G.InducesLinearForest F →
      #F ≥ ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G ABC v →
        Objective G ABC := by
  intro h h'
  refine Claim2' G ABC F hFne hG hF hF' ih h ?_
  simp only [ge_iff_le, tsub_le_iff_right] at h' ⊢
  refine le_trans h' ?_
  simp only [le_add_iff_nonneg_right]
  refine sum_nonneg <| fun _ _ ↦ γ_nonneg G ABC

end Tripartition
end ABC
end CaroWeiType
