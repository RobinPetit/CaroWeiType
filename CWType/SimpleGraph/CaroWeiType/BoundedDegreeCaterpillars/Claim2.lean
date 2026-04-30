import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

private lemma hAiff {n : ℕ} {w : Fin n} {F : Finset (Fin n)} {ABC : Tripartition n}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hw : w ∉ G.closed_neighborFinset_of_Finset F) :
    ABC.A w ↔ (ABC \ G.closed_neighborFinset_of_Finset F).A w := by
  exact ⟨fun h ↦ by simp [Tripartition.sdiff, h, hw], fun h ↦ h.1⟩

lemma Claim2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {F : Finset (Fin n)} (hFne : F.Nonempty)
    (hF : F ⊆ ABC.toFinset) (hF' : respects F G ABC)
    (hG : G.support.toFinset ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    G.InducesLinearForest F →
      #F ≥ eval G ABC - eval (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
                             (ABC \ G.closed_neighborFinset_of_Finset F) →
        Objective G ABC := by
  intro h h'
  have hcap : G.closed_neighborFinset_of_Finset F ∩ ABC.toFinset ≠ ∅ := by
    refine Nonempty.ne_empty <| nonempty_def.mpr ?_
    obtain ⟨x, hx⟩ := nonempty_def.mp hFne
    refine ⟨x, mem_inter.mpr ⟨closed_neighborFinset_contains_Finset hx, hF hx⟩⟩
  obtain ⟨s', hs', hlf, hresp, hcard'⟩ :=
    ih (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
      (ABC \ (G.closed_neighborFinset_of_Finset F)) (hsupp_mono hG) (ABC.sdiff_card hcap)
  have hresp : respects (s' ∪ F) G ABC := by
    refine respects_union (respects_mono G ABC hs' hresp) hF' ?_
    intro y hy z hz this
    have _ : y ∈ G.closed_neighborFinset_of_Finset F := by
      simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
      refine Or.inr ⟨z, hz, this⟩
    let hobj := hs' hy
    simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff,
      mem_filter, mem_univ, true_and] at hobj
    have _ : y ∉ G.closed_neighborFinset_of_Finset F := and_or_3.mp hobj |>.2
    contradiction
  refine ⟨s' ∪ F, fun _ _ ↦ by grind [Tripartition.toFinset_mono], ?_, hresp, ?_⟩
  · refine InducesForest_union_disjoint_neighborhoods ?_ h.1 ?_
    · exact InducesForest_mono' (by grind [sdiff_toFinset]) hlf
    · intro x hx y hy
      let hobj := mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs' hx) |>.2
      simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and, not_or,
        not_exists, not_and] at hobj
      exact hobj.2 _ hy
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
        exact fun hx ↦ hfinal <| closed_neighborFinset_contains_Finset hx

private lemma hdeg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {w : Fin n}
    {F : Finset (Fin n)} (hw : w ∈ G.N2_of_Finset F) :
    (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F)).degree w + 1 ≤ G.degree w := by
  refine Order.add_one_le_iff.mpr ?_
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

private lemma d_minues_one_plus_one {d : ℕ} (hd : 1 ≤ d) : (((d - 1) : ℕ) : ℝ) + 1 = d := by
  simp only [Nat.cast_one, sub_add_cancel, Nat.cast_sub hd]

private lemma cast_add_one {m n : ℕ} (h : m + 1 ≤ n) : (m : ℝ) + 1 ≤ (n : ℝ) := by
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
  exact h

private lemma _ok_A {n : ℕ} {w : Fin n} {F : Finset (Fin n)} {ABC : Tripartition n}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hA : ABC.A w) (hdw : 1 ≤ G.degree w)
    (hw : w ∈ G.N2_of_Finset F) (hwNF : w ∉ G.closed_neighborFinset_of_Finset F) :
    γ G ABC w ≤
      f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
        (ABC \ G.closed_neighborFinset_of_Finset F) w -
      f G ABC w := by
  rw [γ, f]
  simp only [hA, ↓reduceDIte, f, tsub_le_iff_right, sub_add_cancel, (hAiff hwNF).mp hA, fA,
    Nat.pred_eq_succ_iff, zero_add, d_minues_one_plus_one hdw]
  split_ifs
  any_goals grind [hdeg hw]
  · refine mul_le_one (Nat.cast_pos'.mpr hdw) (Nat.ofNat_le_cast.mpr <| by lia)
  · refine le_trans ?_ two_thirds_le_five_sixths
    refine div_le_div_of_nonneg_left zero_le_two three_pos ?_
    exact Nat.ofNat_le_cast.mpr <| by lia
  · exact div_le_div_of_nonneg_left zero_le_two add_one_pos <| cast_add_one <| hdeg hw

private lemma _ok_B {n : ℕ} {w : Fin n} {F : Finset (Fin n)} {ABC : Tripartition n}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hB : ABC.B w) (hdw : 1 ≤ G.degree w)
    (hw : w ∈ G.N2_of_Finset F) (hwNF : w ∉ G.closed_neighborFinset_of_Finset F) :
    γ G ABC w ≤
      f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
        (ABC \ G.closed_neighborFinset_of_Finset F) w -
      f G ABC w := by
  rw [γ, f]
  simp only [hB, not_A_of_B, ↓reduceDIte, fB, Nat.pred_eq_succ_iff, zero_add, Nat.reduceAdd,
    d_minues_one_plus_one hdw, sdiff, false_and, true_and, not_C_of_B, dite_eq_ite, ite_not, f,
    tsub_le_iff_right, sub_add_cancel]
  have hdeg_pos : (0 : ℝ) < G.degree w := Nat.cast_pos'.mpr hdw
  split_ifs
  any_goals grind [hdeg hw]
  · refine div_le_comm₀ one_pos hdeg_pos |>.mp ?_
    simp_rw [div_one]
    refine le_trans four_thirds_le_two <| Nat.cast_le.mpr <| by lia
  · refine div_le_comm₀ ?_ hdeg_pos |>.mp ?_
    · refine div_pos ?_ ?_ <;> exact Nat.ofNat_pos'
    · exact @le_trans _ _ _ 2 _ (by linarith) (Nat.cast_le.mpr <| by lia)
  · refine div_le_comm₀ one_third_pos hdeg_pos |>.mp ?_
    rw [div_div_div_eq]
    simp only [mul_one, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      IsUnit.mul_div_cancel_right, Nat.ofNat_le_cast]
    lia
  · exact div_le_div_of_nonneg_left zero_le_four_thirds add_one_pos <| cast_add_one <| hdeg hw

private lemma _ok_C {n : ℕ} {w : Fin n} {F : Finset (Fin n)} {ABC : Tripartition n}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hC : ABC.C w) (hdw : 1 ≤ G.degree w)
    (hw : w ∈ G.N2_of_Finset F) (hwNF : w ∉ G.closed_neighborFinset_of_Finset F) :
    γ G ABC w ≤
      f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
        (ABC \ G.closed_neighborFinset_of_Finset F) w -
      f G ABC w := by
  rw [γ, f]
  simp only [hC, not_A_of_C, ↓reduceDIte, fC, Nat.pred_eq_succ_iff, zero_add, Nat.reduceAdd,
    d_minues_one_plus_one hdw, sdiff, false_and, true_and, not_B_of_C, dite_eq_ite, ite_not, f,
    tsub_le_iff_right, sub_add_cancel]
  have hdeg_pos : (0 : ℝ) < G.degree w := Nat.cast_pos'.mpr hdw
  split_ifs
  any_goals grind [hdeg hw]
  · refine div_le_comm₀ one_pos hdeg_pos |>.mp ?_
    simp_rw [div_one]
    refine le_trans ?_ (Nat.cast_le.mpr hdw)
    rw [Nat.cast_one]
    exact two_thirds_le_one
  · exact div_le_comm₀ one_sixth_pos hdeg_pos |>.mp
      <| @le_trans _ _ _ 4 _ (by linarith) (Nat.cast_le.mpr <| by lia)
  · exact div_le_div_of_nonneg_left zero_le_two_thirds add_one_pos <| cast_add_one <| hdeg hw

private lemma _γ_on_N2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {ABC : Tripartition n} (F : Finset (Fin n)) :
    ∑ w ∈ G.N2_of_Finset F, γ G ABC w ≤ ∑ w ∈ G.N2_of_Finset F,
        (f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
          (ABC \ G.closed_neighborFinset_of_Finset F) w - f G ABC w) := by
  refine sum_le_sum ?_
  intro w hw
  have hwNF : w ∉ G.closed_neighborFinset_of_Finset F :=
    fun _ ↦ by grind [closed_neighborFinset_of_Finset, N2_of_Finset]
  have hdegw : 1 ≤ G.degree w := Nat.one_le_of_lt <| hdeg hw
  have h1 : ((((G.degree w - 1) : ℕ) : ℝ) + 1) = (G.degree w : ℝ) := by
    simp only [Nat.cast_one, sub_add_cancel, Nat.cast_sub hdegw]
  if hA : ABC.A w then
    exact _ok_A hA hdegw hw hwNF
  else if hB : ABC.B w then
    exact _ok_B hB hdegw hw hwNF
 else if hC : ABC.C w then
    exact _ok_C hC hdegw hw hwNF
  else
    simp [hA, hB, hC]

lemma Claim2' {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {F : Finset (Fin n)} (hFne : F.Nonempty)
    (hG : G.support.toFinset ⊆ ABC.toFinset)
    (hF : F ⊆ ABC.toFinset)
    (hF' : respects F G ABC)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    G.InducesLinearForest F →
      #F ≥ ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G ABC v
        - ∑ w ∈ G.N2_of_Finset F, γ G ABC w →
        Objective G ABC := by
  intro h h'
  refine Claim2 hFne hF hF' hG ih h ?_
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
      exact _γ_on_N2 G F
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
        · exact fun heq ↦ hz' <| closed_neighborFinset_contains_Finset <| heq ▸ hx
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

lemma Corollary2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {F : Finset (Fin n)} (hFne : F.Nonempty)
    (hG : G.support.toFinset ⊆ ABC.toFinset)
    (hF : F ⊆ ABC.toFinset)
    (hF' : respects F G ABC)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    G.InducesLinearForest F →
      #F ≥ ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G ABC v →
        Objective G ABC := by
  intro h h'
  refine Claim2' hFne hG hF hF' ih h ?_
  simp only [ge_iff_le, tsub_le_iff_right] at h' ⊢
  refine le_trans h' ?_
  simp only [le_add_iff_nonneg_right]
  refine sum_nonneg <| fun _ _ ↦ γ_nonneg

end Tripartition
end ABC
end CaroWeiType
