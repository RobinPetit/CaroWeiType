import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim1
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim4

open SimpleGraph
open Finset

namespace CaroWeiType
namespace ABC
namespace Tripartition

variable {V : Type} [Fintype V] [DecidableEq V]

lemma Claim5_0 {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
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
  · refine G.IsDegenerateSet_union' s' {x} ?_ (by simp [hdegx0])
    refine IsDegenerateSet_graph_mono' G _ s' {x} ?_ hs'2
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

private lemma _Claim5_1_respect {G : SimpleGraph V} [DecidableRel G.Adj]
    {ABC : Tripartition V} [ABC.Decidable] {x u : V} (hu' : ∀ y, G.Adj x y → y = u)
    (hABx : ABC.A x ∨ ABC.B x) (hCu : ¬ABC.C u) (hxu : G.Adj x u)
    (hdx : G.degree x = 1) {s : Finset V} (hs : s ⊆ ((ABC \ {x}).demote u).toFinset)
    (hsresp : respects s (G.deleteIncidencesOf {x}) ((ABC \ {x}).demote u)) :
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
    have hdeg : G.degree_in (s ∪ {x}) z ≤ (G.deleteIncidencesOf {x}).degree_in s z + #{x} := by
      refine degree_in_deleteIncidencesOf' _ _ ?_ ?_
      · exact singleton_inter_eq_empty_iff.mpr hxnotins
      · simp only [mem_singleton]
        refine ne_of_mem_of_not_mem hz ?_
        intro hxs
        have := hs hxs
        simp only [← demote_toFinset_eq, toFinset_eq, mem_sdiff, mem_singleton, not_true_eq_false,
          and_false] at this
    refine ⟨?_, ?_⟩
    · intro hAz
      have hB'z : ((ABC \ {x}).demote z).B z := by
        refine demote_from_A (ABC \ {x}) ?_
        simp [Tripartition.sdiff, hAz, hxu.ne']
      exact le_trans hdeg (add_le_add_left (hsresp z hz |>.2.1 hB'z) 1)
    · intro hBz
      have hC'z : ((ABC \ {x}).demote z).C z := by
        refine demote_from_B (ABC \ {x}) ?_
        simp [Tripartition.sdiff, hBz, hxu.ne']
      exact le_trans hdeg (add_le_add_left (le_of_eq <| hsresp z hz |>.2.2 hC'z) 1)
    else
      have h1 : G.degree_in (s ∪ {x}) z = G.degree_in s z := by
        refine degree_in_union_eq <| singleton_inter_of_notMem ?_
        exact not_iff_not.mpr (mem_neighborFinset ..) |>.mpr <| not_adj_symm <| hu' _ |>.mt heq
      have h2 : G.degree_in s z = (G.deleteIncidencesOf {x}).degree_in s z := by
        refine Eq.symm <| degree_in_deleteIncidencesOf _ _ ?_ ?_
        · exact singleton_inter_of_notMem hxnotins
        · exact notMem_singleton.mpr <| ne_of_mem_of_not_mem hz hxnotins
      simp_rw [h1, h2]
      have hznotinx : z ∉ ({x} : Finset _) := by
        simp only [mem_singleton]
        exact fun heq ↦ hxnotins (heq ▸ hz)
      obtain ⟨h₁, h₂, h₃⟩ := hsresp z hz
      refine ⟨?_, ?_, ?_⟩
      · exact fun hA ↦ h₁ <| A_of_demote_ne _ heq ⟨hA, hznotinx⟩
      · exact fun hB ↦ h₂ <| B_of_demote_ne _ heq ⟨hB, hznotinx⟩
      · exact fun hC ↦ h₃ <| C_of_demote_ne _ ⟨hC, hznotinx⟩

lemma Claim5_1 {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
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
      exact Eq.symm <| γC1 hCx hdegx
  -- x ∈ A ∪ B
  if hCu : ABC.C u then
    refine Corollary1 hG hu.symm ih ?_
    have hγ : γ G ABC x = 1 / 6 := by
      simp only [γ, fA, hdegx, tsub_self, ↓reduceIte, one_ne_zero, fB, dite_eq_ite]
      rcases hABx with h | h <;> { simp only [h, not_A_of_B, ↓reduceIte]; linarith }
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
      refine ih (G.deleteIncidencesOf {x}) ((ABC \ {x}).demote u) ?_ ?_
      · simp_rw [← demote_toFinset_eq _]
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
      · have hobj := hs hy
        simp only [← Tripartition.demote_toFinset_eq, Tripartition.sdiff_toFinset] at hobj
        exact mem_sdiff.mp hobj |>.1
    have hxnotins : x ∉ s := by
      refine notMem_mono hs ?_
      simp only [← demote_toFinset_eq, sdiff_toFinset, mem_sdiff, mem_singleton, not_true_eq_false,
        and_false, not_false_eq_true]
    let hs'resp := _Claim5_1_respect hu' hABx hCu hu hdegx hs hsresp
    refine ⟨s ∪ {x}, hs'ABC, ?_, hs'resp, ?_⟩
    · refine InducesForest_union_leaf G s ?_ ?_
      · exact InducesForest_graph_mono' (inter_singleton_of_notMem hxnotins) hsf
      · exact le_of_le_of_eq degree_in_le_degree hdegx
    · have : ((ABC \ {x}).demote u).toFinset = ABC.toFinset \ {x} := by
        simp_rw [← demote_toFinset_eq, sdiff_toFinset]
      simp only [eval]
      refine le_of_eq_of_le (sum_sdiff_singleton_eval (ABC.mem_toFinset.mp hx) ?_) ?_
      · exact coe_subset.mp <| (Set.subset_toFinset.mp neighborFinset_subset_support).trans hG
      · have hfx : f G ABC x = 5 / 6 := by
          rcases hABx with hA | hB
          · exact fA1 hA hdegx
          · exact fB1 hB hdegx
        have : {u} ⊆ ABC.toFinset \ {x} := singleton_subset_iff.mpr
            <| mem_sdiff.mpr ⟨ABC.mem_toFinset.mp huABC, notMem_singleton.mpr hu.ne'⟩
        rw [hfx, sum_eq_sum_demote_finset this, Nx, sum_singleton, sum_singleton]
        calc _
          _ = ∑ x_1 ∈ ABC.toFinset \ {x},
                f (G.deleteIncidencesOf {x}) ((ABC \ {x}).demote_finset {u}) x_1
              + (f G ABC u - f (G.deleteIncidencesOf {x}) ((ABC \ {x}).demote_finset {u}) u)
              + 5 / 6 := by
            linarith
          _ ≤ #s + (f G ABC u - f (G.deleteIncidencesOf {x}) ((ABC \ {x}).demote_finset {u}) u)
              + 5 / 6 := by
            simp only [add_le_add_iff_right]
            simp only [eval, ← demote_toFinset_eq, sdiff_toFinset] at hscard
            exact hscard
        suffices (f G ABC u - f (G.deleteIncidencesOf {x}) ((ABC \ {x}).demote_finset {u}) u)
            ≤ 1 / 6 by
          rw [card_union, inter_singleton_of_notMem hxnotins, card_empty, card_singleton]
          refine @le_trans _ _ _ (#s + (1 : ℝ)) _ (by linarith) ?_
          simp only [tsub_zero, Nat.cast_add, Nat.cast_one, le_refl]
        rw [f_eq_sdiff <| notMem_singleton.mpr hu.ne']
        refine Claim4 (mem_singleton.mpr rfl) ?_
        refine ge_of_eq <| degree_deleteIncidencesOf_neighbor_singleton G hu

lemma Claim5 {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
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
