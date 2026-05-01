import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim1
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim4

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

lemma Claim5_0 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    (∃ x ∈ ABC, G.degree x = 0) → Objective G ABC := by
  intro ⟨x, hx, hdegx0⟩
  have hcard' : (ABC \ {x}).card < ABC.card := by
    refine ABC.sdiff_card ?_
    refine nonempty_iff_ne_empty.mp ⟨x, ?_⟩
    exact mem_inter.mpr ⟨mem_singleton.mpr rfl, ABC.mem_toFinset.mp hx⟩
  obtain ⟨s', hs'1, hs'2, hs'3, hs'4⟩ :=
    ih (G.deleteIncidencesOf {x}) (ABC \ {x}) (hsupp_mono hG) hcard'
  refine ⟨s' ∪ {x}, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rcases mem_union.mp hw with hw | hw
    · exact mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs'1 hw) |>.1
    · exact (mem_singleton.mp hw) ▸ ABC.mem_toFinset.mp hx
  · refine G.IsDegenerateSet_union s' {x} ?_ (by simp [hdegx0])
    refine IsDegenerateSet_mono' G _ s' {x} ?_ hs'2
    ext y
    simp only [mem_inter, mem_singleton, notMem_empty, iff_false, not_and]
    intro hy
    exact (not_iff_not.mpr mem_singleton).mp
      <| mem_sdiff.mp (ABC.sdiff_toFinset ▸ (hs'1 hy)) |>.2
  · refine respects_union (respects_mono G ABC hs'1 hs'3) respects_singleton ?_
    simp only [mem_singleton, forall_eq]
    exact fun _ _ h ↦ (Ne.symm <| ne_of_lt h.symm.degree_pos_left) hdegx0
  · calc eval G ABC
      _ = ∑ v ∈ ABC.toFinset, f G ABC v := rfl
      _ = ∑ v ∈ ABC.toFinset \ {x}, f G ABC v + f G ABC x := by
        have hxABC : {x} ⊆ ABC.toFinset := by simp [ABC.mem_toFinset.mp hx]
        rw [← sum_sdiff hxABC]
        rw [sum_singleton (f G ABC ·) x]
      _ = ∑ v ∈ ABC.toFinset \ {x}, f (G.deleteIncidencesOf {x}) (ABC \ {x}) v + f G ABC x := by
        simp only [add_left_inj]
        refine sum_congr rfl ?_
        refine fun w hw ↦ Eq.symm <| f_deleteIncidencesOf_isolated ABC G hdegx0 ?_
        exact (not_iff_not.mpr mem_singleton).mp (mem_sdiff.mp hw).2
      _ = eval (G.deleteIncidencesOf {x}) (ABC \ {x}) + f G ABC x := by
        simp only [add_left_inj]
        rw [← ABC.sdiff_toFinset]
        rfl
      _ ≤ #s' + f G ABC x := by
        simp only [add_le_add_iff_right]
        exact hs'4
      _ = #s' + 1 := by
        simp only [add_right_inj]
        exact f0 hx hdegx0
      _ = (#(s' ∪ {x}) : ℝ) := by
        rw [← Nat.cast_one, ← Nat.cast_add]
        refine Nat.cast_inj.mpr ?_
        simp only [union_singleton]
        refine Eq.symm <| card_insert_of_notMem ?_
        intro hmem
        let hobj := mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs'1 hmem) |>.2
        simp only [mem_singleton, not_true_eq_false] at hobj

private lemma _Claim5_1_respect {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} [ABC.Decidable] {x u : Fin n} (hu' : ∀ y, G.Adj x y → y = u)
    (hABx : ABC.A x ∨ ABC.B x) (hCu : ¬ABC.C u) (hxu : G.Adj x u)
    (hdx : G.degree x = 1) {s : Finset (Fin n)} (hs : s ⊆ ((ABC \ {x}).demote u).toFinset)
    (hsresp : respects s (G.deleteIncidenceSet x) ((ABC \ {x}).demote u)) :
    respects (s ∪ {x}) G ABC  := by
  have hxnotins : x ∉ s := by
    intro this
    let hobj := hs this
    simp only [← demote_toFinset_eq, ← Tripartition.mem_toFinset] at hobj
    exact ABC.sdiff_notMem {x} x (mem_singleton.mpr rfl) hobj |>.elim
  intro z hz
  simp only [union_singleton, mem_insert] at hz
  rcases hz with hz | hz
  · subst hz
    if hA : ABC.A z then
      refine ⟨?_, ?_, ?_⟩
      · exact fun _ ↦ le_trans degree_in_le_degree (by simp only [hdx, Nat.one_le_ofNat])
      · simp only [hA, not_B_of_A, degree_in, union_singleton, mem_neighborFinset,
          SimpleGraph.irrefl, not_false_eq_true, inter_insert_of_notMem, IsEmpty.forall_iff]
      · simp only [hA, not_C_of_A, degree_in, union_singleton, mem_neighborFinset,
          SimpleGraph.irrefl, not_false_eq_true, inter_insert_of_notMem, card_eq_zero,
          IsEmpty.forall_iff]
    else
      have hB : ABC.B z := Or.resolve_left hABx hA
      refine ⟨?_, ?_, ?_⟩
      · exact fun hA' ↦ hA hA' |>.elim
      · exact fun _ ↦ le_trans degree_in_le_degree <| le_of_eq hdx
      · exact fun hC ↦ not_C_of_B hB hC |>.elim
  · if heq : z = u then
    subst heq
    simp only [IsEmpty.forall_iff, and_true, hCu]
    refine ⟨?_, ?_⟩
    · intro hAz
      have hB'z : ((ABC \ {x}).demote z).B z := by
        refine demote_from_A (ABC \ {x}) ?_
        simp [Tripartition.sdiff, hAz, hxu.ne']
      exact le_trans (degree_in_deleteIncidenceSet' s hxnotins hxu)
        <| add_le_add_left (hsresp z hz |>.2.1 hB'z) 1
    · intro hBz
      have hC'z : ((ABC \ {x}).demote z).C z := by
        refine demote_from_B (ABC \ {x}) ?_
        simp [Tripartition.sdiff, hBz, hxu.ne']
      exact le_trans (degree_in_deleteIncidenceSet' s hxnotins hxu)
        <| add_le_add_left (le_of_eq <| hsresp z hz |>.2.2 hC'z) 1
    else
      have h1 : G.degree_in (s ∪ {x}) z = G.degree_in s z := by
        refine congrArg Finset.card ?_
        ext y
        simp only [union_singleton, mem_inter, mem_neighborFinset, mem_insert,
          and_congr_right_iff, or_iff_right_iff_imp]
        intro hzy heq
        let hobj := hu' z (heq ▸ hzy.symm)
        contradiction
      have h2 : G.degree_in s z = (G.deleteIncidenceSet x).degree_in s z := by
        refine congrArg Finset.card ?_
        ext y
        simp only [mem_inter, mem_neighborFinset, deleteIncidenceSet, incidenceSet,
          deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or,
          and_congr_left_iff, iff_self_and, forall_self_imp]
        intro hy hzy
        constructor
        · intro h; subst h
          exact hxnotins hz
        · intro h; subst h
          exact heq (hu' z (hzy.symm)) |>.elim
      simp_rw [h1, h2]
      have hznotinx : z ∉ ({x} : Finset _) := by
        simp only [mem_singleton]
        exact fun heq ↦ hxnotins (heq ▸ hz)
      obtain ⟨h₁, h₂, h₃⟩ := hsresp z hz
      refine ⟨?_, ?_, ?_⟩
      · exact fun hA ↦ h₁ <| A_of_demote_ne _ heq ⟨hA, hznotinx⟩
      · exact fun hB ↦ h₂ <| B_of_demote_ne _ heq ⟨hB, hznotinx⟩
      · exact fun hC ↦ h₃ <| C_of_demote_ne _ ⟨hC, hznotinx⟩

lemma Claim5_1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    (∃ x ∈ ABC, G.degree x = 1) → Objective G ABC := by
  intro ⟨x, hx, hdegx⟩
  obtain ⟨u, hu, hu'⟩ := degree_eq_one_iff_existsUnique_adj.mp hdegx
  have Nx : G.neighborFinset x = {u} := by
    ext y
    simp only [mem_neighborFinset, mem_singleton]
    exact ⟨hu' y, fun heq ↦ heq ▸ hu⟩
  have huABC : u ∈ ABC := ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨x, hu.symm⟩
  simp only at hu hu'
  have hx' : (ABC.A x ∨ ABC.B x) ∨ ABC.C x := by grind [ABC.mem_iff.mp hx]
  cases hx' with
  | inl hABx => ?_
  | inr hCx =>
      refine Corollary1 hG hu.symm ih ?_
      refine le_trans (f_le_56 G ABC hu.symm.degree_pos_left) (le_of_eq ?_)
      simp only [γ, not_A_of_C, ↓reduceDIte, not_B_of_C, hCx, fC, hdegx, tsub_self, ↓reduceIte,
        one_ne_zero, OfNat.one_ne_ofNat, or_false, one_div]
      linarith
  -- x ∈ A ∪ B
  if hCu : ABC.C u then
    refine Corollary1 hG hu.symm ih ?_
    have hγ : γ G ABC x = 1 / 6 := by
      simp only [γ, fA, hdegx, tsub_self, ↓reduceIte, one_ne_zero, fB, dite_eq_ite]
      split_ifs <;> grind
    have hdegupos : G.degree u ≠ 0 := ne_of_gt hu.symm.degree_pos_left
    simp only [hγ, f, not_A_of_C, ↓reduceDIte, not_B_of_C, hCu, fC, hdegupos, ↓reduceIte, ge_iff_le]
    split_ifs
    · exact le_refl _
    · refine div_le_comm₀ one_sixth_pos add_one_pos |>.mp ?_
      simp only [one_div, div_inv_eq_mul]
      calc (2 : ℝ) / 3 * 6
        _ = 3 + 1 := by linarith
        _ ≤ G.degree u + 1 := by
          rw [← Nat.cast_three, ← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add]
          refine Nat.cast_le.mpr <| by lia
  else
    -- {u, x} ⊆ A ∪ B as well
    obtain ⟨s, hs, hsf, hsresp, hscard⟩ := by
      refine ih (G.deleteIncidenceSet x) ((ABC \ {x}).demote u) ?_ ?_
      · simp_rw [← deleteIncidencesOf_singleton_eq_deleteIncidenceSet x, ← demote_toFinset_eq _]
        exact hsupp_mono hG
      · simp only [← Tripartition.card_demote_eq_card]
        refine Tripartition.sdiff_card ABC ?_
        refine nonempty_iff_ne_empty.mp ?_
        exact ⟨x, by simp only [ABC.mem_toFinset.mp hx, singleton_inter_of_mem, mem_singleton]⟩
    have hs'ABC : s ∪ {x} ⊆ ABC.toFinset := by
      intro y
      simp only [union_singleton, mem_insert]
      intro hy
      rcases hy with hy | hy
      · exact ABC.mem_toFinset.mp (hy ▸ hx)
      · let hobj := hs hy
        simp only [← Tripartition.demote_toFinset_eq, Tripartition.sdiff_toFinset] at hobj
        exact mem_sdiff.mp hobj |>.1
    have hxnotins : x ∉ s := by
      intro this
      let hobj := hs this
      simp only [← demote_toFinset_eq, ← Tripartition.mem_toFinset] at hobj
      have : x ∉ ABC \ {x} := ABC.sdiff_notMem {x} x <| mem_singleton.mpr rfl
      contradiction
    let hs'resp := _Claim5_1_respect hu' hABx hCu hu hdegx hs hsresp
    refine ⟨s ∪ {x}, hs'ABC, ?_, hs'resp, ?_⟩
    · intro t ht htne
      if hxt :x ∈ t then
        refine ⟨x, hxt, ?_⟩
        refine le_trans ?_ (le_of_eq hdegx)
        refine card_le_card inter_subset_left
      else
        obtain ⟨z, hzt, hzdeg⟩ := by
          refine hsf t ?_ htne
          intro u hu
          rcases mem_union.mp <| ht hu with h | h
          · exact h
          · exact hxt (mem_singleton.mp h ▸ hu) |>.elim
        refine ⟨z, hzt, ?_⟩
        refine le_trans ?_ hzdeg
        refine card_le_card ?_
        intro y
        simp only [mem_inter, mem_neighborFinset, deleteIncidenceSet, incidenceSet, deleteEdges_adj,
          Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, and_imp]
        refine fun hzy hy ↦ ⟨⟨hzy, fun _ ↦ by grind [Adj.ne]⟩, hy⟩
    · have : ((ABC \ {x}).demote u).toFinset = ABC.toFinset \ {x} := by
        simp_rw [← demote_toFinset_eq, sdiff_toFinset]
      calc ∑ v ∈ ABC.toFinset, f G ABC v
        _ = ∑ v ∈ ABC.toFinset \ {x}, f G ABC v + f G ABC x := by
          rw [← sum_singleton (f G ABC ·) x]
          refine Eq.symm <| sum_sdiff <| union_subset_right hs'ABC
        _ = ∑ v ∈ ABC.toFinset \ {x}, f G ABC v + 5 / 6 := by
          simp only [add_right_inj]
          rcases hABx with hA | hB
          · simp only [f, hA, ↓reduceDIte, fA, hdegx, one_ne_zero, ↓reduceIte]
          · simp only [f, hB, not_A_of_B, ↓reduceDIte, fB, hdegx, one_ne_zero, ↓reduceIte]
        _ = ∑ v ∈ (ABC.toFinset \ {x}) \ {u}, f G ABC v + f G ABC u + 5 / 6 := by
          simp only [add_left_inj]
          rw [← sum_singleton (f G ABC ·) u]
          refine Eq.symm <| sum_sdiff ?_
          simp [hu.ne', ABC.mem_toFinset.mp huABC]
        _ = ∑ v ∈ (ABC.toFinset \ {x}) \ {u}, f (G.deleteIncidenceSet x) ((ABC \ {x}).demote u) v
            + f G ABC u + 5 / 6 := by
          simp only [add_left_inj]
          refine sum_congr rfl ?_
          intro v hv
          simp only [mem_sdiff, mem_singleton] at hv
          have hdegeq : G.degree v = (G.deleteIncidenceSet x).degree v := by
            refine congrArg Finset.card ?_
            ext w
            simp only [mem_neighborFinset, deleteIncidenceSet, incidenceSet, deleteEdges_adj,
              Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, Ne.symm hv.1.2, false_or, not_and,
              iff_self_and, forall_self_imp]
            refine fun hvw heq ↦ hv.2 <| hu' v (heq ▸ hvw.symm)
          if hA : ABC.A v then
            have hA' : (ABC \ {x}).demote u |>.A v := by
              refine A_of_demote_ne _ hv.2 ⟨hA, ?_⟩
              simp only [mem_singleton, hv.1, not_false_eq_true]
            simp only [f, hA, hA', ↓reduceDIte, fA, hdegeq]
          else if hB : ABC.B v then
            have hB' : (ABC \ {x}).demote u |>.B v := by
              refine B_of_demote_ne _ hv.2 ⟨hB, ?_⟩
              simp only [mem_singleton, hv.1, not_false_eq_true]
            have hA' : ¬((ABC \ {x}).demote u).A v :=
              fun h ↦ Tripartition.sound _ v |>.1 ⟨h, hB'⟩
            simp only [f, hA, hA', ↓reduceDIte, hB, hB', fB, hdegeq]
          else
            have hC : ABC.C v := by
              rcases ABC.mem_toFinset.mpr hv.1.1 with h | h | h
              · exact hA h |>.elim
              · exact hB h |>.elim
              · exact h
            have hC' : (ABC \ {x}).demote u |>.C v := by
              refine C_of_demote_ne _ ⟨hC, ?_⟩
              simp only [mem_singleton, hv.1, not_false_eq_true]
            simp only [f, not_A_of_C, ↓reduceDIte, not_B_of_C, hC, hC', fC, hdegeq]
        _ = ∑ v ∈ ((ABC \ {x}).demote u).toFinset \ {u},
              f (G.deleteIncidenceSet x) ((ABC \ {x}).demote u) v
            + f G ABC u + 5 / 6 := by
          simp only [add_left_inj]
          refine sum_congr ?_ (fun _ _ ↦ rfl)
          refine congrArg (fun (s : Finset _) ↦ s \ _) ?_
          exact this.symm
        _ = ∑ v ∈ ((ABC \ {x}).demote u).toFinset \ {u},
              f (G.deleteIncidenceSet x) ((ABC \ {x}).demote u) v
            + f (G.deleteIncidenceSet x) ((ABC \ {x}).demote u) u
            - f (G.deleteIncidenceSet x) ((ABC \ {x}).demote u) u
            + f G ABC u + 5 / 6 := by
          lia
        _ = ∑ v ∈ ((ABC \ {x}).demote u).toFinset,
              f (G.deleteIncidenceSet x) ((ABC \ {x}).demote u) v
            - f (G.deleteIncidenceSet x) ((ABC \ {x}).demote u) u + f G ABC u + 5 / 6 := by
          simp only [add_left_inj, sub_left_inj]
          rw [← sum_singleton (f _ _ ·) u]
          refine sum_sdiff ?_
          simp only [singleton_subset_iff, this, ABC.mem_toFinset.mp huABC, mem_sdiff, hu.ne',
            mem_singleton, not_false_eq_true, and_true]
        _ = eval (G.deleteIncidenceSet x) ((ABC \ {x}).demote u)
            - f (G.deleteIncidenceSet x) ((ABC \ {x}).demote u) u + f G ABC u + 5 / 6 := by
          simp only [add_left_inj]
          rfl
        _ ≤ #s - f (G.deleteIncidenceSet x) ((ABC \ {x}).demote u) u + f G ABC u + 5 / 6 := by
          refine add_le_add_left ?_ _
          refine add_le_add_left ?_ _
          exact add_le_add_left hscard _
        _ ≤ #s + 1 + (- f (G.deleteIncidenceSet x) ((ABC \ {x}).demote u) u
            + f G ABC u - 1 / 6) := by
          linarith
      have hcardunion : (#(s ∪ {x}) : ℝ) = #s + (1 : ℝ) := by
        rw [← Nat.cast_one, ← Nat.cast_add, ← card_singleton x]
        refine Nat.cast_inj.mpr <| card_union_of_disjoint <| disjoint_singleton_right.mpr hxnotins
      rw [hcardunion]
      refine add_le_iff_nonpos_right _ |>.mpr ?_
      calc -f (G.deleteIncidenceSet x) ((ABC \ {x}).demote u) u + f G ABC u - 1 / 6
        _ = f G ABC u - f (G.deleteIncidenceSet x) ((ABC \ {x}).demote u) u - 1 / 6 := by
          lia
        _ = f G ABC u - f (G.deleteIncidenceSet x) (ABC.demote u) u - 1 / 6 := by
          ring_nf
          simp only [add_right_inj, sub_right_inj]
          have hABu : ABC.A u ∨ ABC.B u := by
            rcases huABC with hA | hB | hC
            · exact Or.inl hA
            · exact Or.inr hB
            · exact hCu hC |>.elim
          have hunotinx : u ∉ ({x} : Finset _) := by
            simp only [mem_singleton]
            exact hu.ne'
          rcases hABu with hA | hB
          · have hB : (ABC.demote u).B u := demote_from_A _ hA
            have hB' : ((ABC \ {x}).demote u).B u := demote_from_A _ ⟨hA, hunotinx⟩
            have hA' : ¬((ABC \ {x}).demote u).A u := demote_from_A' _ ⟨hA, hunotinx⟩
            simp only [f, demote_from_A, demote_from_A', hA, hA', hB', ↓reduceDIte]
          · have hC : (ABC.demote u).C u := demote_from_B _ hB
            have hC' : ((ABC \ {x}).demote u).C u := demote_from_B _ ⟨hB, hunotinx⟩
            have hB' : ¬((ABC \ {x}).demote u).B u := demote_from_B' _ ⟨hB, hunotinx⟩
            have hA : ¬(ABC.demote u).A u := fun h ↦ Tripartition.sound _ u |>.2.1 ⟨h, hC⟩
            have hA' : ¬((ABC \ {x}).demote u).A u := fun h ↦ Tripartition.sound _ u |>.2.1 ⟨h, hC'⟩
            simp only [f, demote_from_B, demote_from_B', hB, hB', hC', hA, hA', ↓reduceDIte]
        _ ≤ 1 / 6 - 1 / (6 : ℝ) := by
          refine add_le_add_left ?_ _
          refine Claim4' ?_
          calc G.degree u
            _ = #((G.neighborFinset u \ {x}) ∪ {x}) := by
              refine congrArg Finset.card ?_
              refine Eq.symm <| sdiff_union_of_subset ?_
              simp only [singleton_subset_iff, mem_neighborFinset, hu.symm]
            _ = #(G.neighborFinset u \ {x}) + 1 := by
              rw [← card_singleton x]
              exact card_union_of_disjoint sdiff_disjoint
            _ = #((G.deleteIncidenceSet x).neighborFinset u) + 1 := by
              simp only [add_left_inj]
              refine congrArg _ ?_
              ext w
              simp only [neighborFinset, neighborSet, Set.toFinset_setOf, mem_sdiff, mem_filter,
                mem_univ, true_and, mem_singleton, deleteIncidenceSet, incidenceSet,
                deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or,
                and_congr_right_iff]
              grind
          exact le_refl _
        _ = 0 := sub_self _

lemma Claim5 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    (∃ x ∈ ABC, G.degree x ≤ 1) → Objective G ABC := by
  intro ⟨x, hx, hdegx⟩
  if hdegx0 : G.degree x = 0 then
    exact Claim5_0 hG ih ⟨x, hx, hdegx0⟩
  else
    refine Claim5_1 hG ih ⟨x, hx, ?_⟩
    exact Nat.le_antisymm hdegx (Nat.one_le_iff_ne_zero.mpr hdegx0)

end Tripartition
end ABC
end CaroWeiType
