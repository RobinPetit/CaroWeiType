import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim5
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim8

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

@[simp, reducible]
private def _op {n : ℕ} (G : SimpleGraph (Fin n)) (x y z : Fin n) : SimpleGraph (Fin n) :=
  (fromEdgeSet <| G.edgeSet ∪ {s(x, y)}).deleteIncidencesOf {z}

private lemma _adj_v_op {n : ℕ} {G : SimpleGraph (Fin n)} (v x y z : Fin n)
    (hz : G.Adj v z) {w : Fin n} (hw : G.Adj v w)
    (hwz : w ≠ z) :
    _op G x y z |>.Adj v w := by
  simp only [_op, deleteIncidencesOf, Set.union_singleton, mem_singleton, deleteIncidenceSet,
    incidenceSet, Set.mem_insert_iff, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, iInf_iInf_eq_left,
    sdiff_le_iff, le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj, mem_edgeSet, hw,
    or_true, ne_eq, hw.ne, not_false_eq_true, and_self, Set.mem_setOf_eq, Sym2.mem_iff, hz.ne',
    hwz.symm, or_self, and_false, and_true]

private lemma _adj_xy {n : ℕ} {G : SimpleGraph (Fin n)} (x y z : Fin n)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    _op G x y z |>.Adj x y := by
  simp only [_op, deleteIncidencesOf, Set.union_singleton, mem_singleton, deleteIncidenceSet,
    incidenceSet, Set.mem_insert_iff, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, iInf_iInf_eq_left,
    sdiff_le_iff, le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj, true_or, ne_eq, hxy,
    not_false_eq_true, Set.mem_setOf_eq, Sym2.mem_iff, hxz.symm,
    hyz.symm, or_self, and_false, and_true]

private lemma degree_G_le_degree_op_outside {n : ℕ} (G : SimpleGraph (Fin n)) [G.LocallyFinite]
    {v x y z w : Fin n} (hw : w ∉ ({v, x, y, z} : Finset _)) :
    (_op G x y z).degree w ≤ G.degree w := by
    refine card_le_card ?_
    intro u
    simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_neighborFinset,
      Set.union_singleton, mem_singleton, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff,
      Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, iInf_iInf_eq_left, sdiff_le_iff,
      le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, ne_eq, Set.mem_setOf_eq,
      Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and, Decidable.not_not, and_imp]
    intro hu
    rcases hu with hu | hu
    · exact fun _ _ ↦ by grind only [= mem_insert]
    · exact fun _ _ ↦ hu

private lemma f_G_le_f_op_outside {n : ℕ} (G : SimpleGraph (Fin n)) [G.LocallyFinite]
    {ABC : Tripartition n} {v x y z w : Fin n} (hw : w ∉ ({v, x, y, z} : Finset _)) :
    f G ABC w ≤ f (_op G x y z) ((ABC \ {z}).promote v) w := by
  if hAw : ABC.A w then
    have hA'w : ((ABC \ {z}).promote v).A w :=
      A_of_promote_ne _ (by grind) ⟨hAw, by grind⟩
    simp only [f, hAw, ↓reduceDIte, hA'w]
    exact fA_decreasing (degree_G_le_degree_op_outside G hw)
  else if hBw : ABC.B w then
    have hB'w : ((ABC \ {z}).promote v).B w :=
      B_of_promote_ne _ (by grind) ⟨hBw, by grind⟩
    simp only [f, hBw, ↓reduceDIte, hB'w, not_A_of_B]
    exact fB_decreasing (degree_G_le_degree_op_outside G hw)
  else if hCw : ABC.C w then
    have hC'w : ((ABC \ {z}).promote v).C w :=
      C_of_promote_ne _ (by grind) ⟨hCw, by grind⟩
    simp only [f, hCw, ↓reduceDIte, hC'w, not_A_of_C, not_B_of_C]
    exact fC_decreasing (degree_G_le_degree_op_outside G hw)
  else
    simp only [f, hAw, ↓reduceDIte, hBw, hCw, dite_eq_ite]
    split_ifs
    · exact zero_le_fA
    · exact zero_le_fB
    · exact zero_le_fC
    · exact le_refl _

lemma Claim9 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {v : Fin n} (hBv : ABC.B v) (hdv : G.degree v = 3)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    (∃ w, G.Adj v w ∧ f G ABC w ≤ 1 / 6) → Objective G ABC := by
  intro ⟨w, hvw, hfw⟩
  obtain ⟨x, y, z, hNv, hzy, hyx⟩ := neighborFinset_eq_deg3 (f G ABC ·) hdv
  have h₁' : G.Adj v x :=
    G.mem_neighborFinset .. |>.mp <| by simp only [hNv, mem_insert, mem_singleton, true_or]
  have h₂' : G.Adj v y :=
    G.mem_neighborFinset .. |>.mp <| by simp only [hNv, mem_insert, mem_singleton, true_or, or_true]
  have h₃' : G.Adj v z :=
    G.mem_neighborFinset .. |>.mp <| by simp only [hNv, mem_insert, mem_singleton, or_true]
  have hneNv : x ≠ y ∧ x ≠ z ∧ y ≠ z := by
    rw [degree] at hdv
    exact pairwise_ne_of_triplet (hNv ▸ hdv)
  obtain ⟨H₁, H₂, H₃⟩ := hneNv
  if hℓ : ℓ G ABC x + ℓ G ABC y > 1 / 6 then
    exact Claim8 G ABC hG ih hBv hdv h₁'.symm h₂'.symm H₁ hyx hℓ
  else
    have hcard : (ABC \ {z} |>.promote v).card < ABC.card := by
      simp only [← card_promote_eq_card]
      refine ABC.sdiff_card ?_
      suffices z ∈ ABC.toFinset by
        simp only [this, singleton_inter_of_mem, ne_eq, singleton_ne_empty, not_false_eq_true]
      refine hG <| G.mem_support.mpr ⟨v, Adj.symm <| (G.mem_neighborFinset ..).mp ?_⟩
      simp only [hNv, mem_insert, mem_singleton, or_true]
    obtain ⟨s, hs, hsf, hsresp, hscard⟩ := by
      refine ih (_op G x y z) (ABC \ {z} |>.promote v) ?_ hcard
      rw [← promote_toFinset_eq]
      intro u hu
      simp only [_op] at hu
      simp only [toFinset, toSet, mem_sdiff_iff, Set.coe_toFinset, Set.mem_setOf_eq]
      refine ⟨ABC.mem_toFinset.mpr <| hG ?_, notMem_of_mem_support_deleteIncidencesOf hu⟩
      obtain ⟨u', hu'⟩ := mem_support _ |>.mp hu
      rcases adj_fromEdgeSet_union_iff.mp <| deleteIncidencesOf_le hu' with hu' | hu'
      · exact G.mem_support.mpr ⟨u', hu'⟩
      · exact G.mem_support.mpr ⟨v, Adj.symm <| by grind⟩
    have hznotins : z ∉ s := by
      simp only [← promote_toFinset_eq, sdiff_toFinset] at hs
      intro this
      let bla := mem_sdiff.mp (hs this) |>.2
      simp only [mem_singleton, not_true_eq_false] at bla
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · exact subset_trans hs <| by simp only [← promote_toFinset_eq, toFinset_mono]
    · have hG_le : G ≤ (fromEdgeSet (G.edgeSet ∪ {s(x, y)})) := by
        intro _ _ h
        simp only [Set.union_singleton, fromEdgeSet_adj, Set.mem_insert_iff, mem_edgeSet, h,
          or_true, ne_eq, h.ne, not_false_eq_true, and_self]
      refine InducesForest_mono hG_le ?_
      exact InducesForest_mono'
        (by simp only [hznotins, not_false_eq_true, inter_singleton_of_notMem]) hsf
    · intro u hu
      if heq : v = u then
        subst heq
        simp only [hBv, not_A_of_B, IsEmpty.forall_iff, forall_const, not_C_of_B,
          and_true, true_and]
        have hA'v : ((ABC \ {z}).promote v).A v := by
          refine promote_from_B (ABC \ {z}) v ⟨hBv, ?_⟩
          simp only [mem_singleton]
          exact fun h ↦ (h ▸ hznotins) hu
        let hobj := hsresp v hu |>.1 hA'v
        have H : (_op G x y z).Adj v x ∧ (_op G x y z).Adj v y ∧ (_op G x y z).Adj x y :=
          ⟨_adj_v_op v x y z h₃' h₁' H₂, _adj_v_op v x y z h₃' h₂' H₃, _adj_xy x y z H₁ H₂ H₃⟩
        have : ¬{v, x, y} ⊆ s := by
          refine no_induced_K3_of_InducesForest _ _ H.1 H.2.2 (Adj.symm ?_) hsf
          exact _adj_v_op v x y z h₃' h₂' H₃
        grind
      else
        have h_card_le : G.degree_in s u ≤ (_op G x y z).degree_in s u := by
          refine card_le_card ?_
          intro w hw
          simp only [mem_inter, mem_neighborFinset] at hw
          simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_inter,
            mem_neighborFinset, Set.union_singleton, mem_singleton, edgeSet_fromEdgeSet,
            Set.mem_diff, Set.mem_insert_iff, Sym2.mem_diagSet, deleteEdges_fromEdgeSet,
            fromEdgeSet_sdiff, iInf_iInf_eq_left, sdiff_le_iff, le_sup_right, inf_of_le_right,
            sdiff_adj, fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
            mem_edgeSet, hw.1, or_true, ne_eq, hw.1.ne, not_false_eq_true, and_self,
            Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, true_and, and_true, not_or,
            hw.2]
          exact ⟨fun h ↦ hznotins (h ▸ hu), fun h ↦ hznotins (h ▸ hw.2)⟩
        refine ⟨?_, ?_, ?_⟩
        · refine fun hAu ↦ le_trans h_card_le (hsresp u hu |>.1 ?_)
          refine A_of_promote_ne _ (Ne.symm heq) ⟨hAu, ?_⟩
          simp only [mem_singleton]
          exact fun heq ↦ (heq ▸ hznotins) hu
        · refine fun hBu ↦ le_trans h_card_le (hsresp u hu |>.2.1 ?_)
          refine B_of_promote_ne _ (Ne.symm heq) ⟨hBu, ?_⟩
          simp only [mem_singleton]
          exact fun heq ↦ (heq ▸ hznotins) hu
        · refine fun hCu ↦ le_antisymm ?_ (zero_le _)
          refine le_trans h_card_le (le_of_eq <| hsresp u hu |>.2.2 ?_)
          refine C_of_promote_ne _ (Ne.symm heq) ⟨hCu, ?_⟩
          simp only [mem_singleton]
          exact fun heq ↦ (heq ▸ hznotins) hu
    · have hinABC {u} (hu : G.Adj v u) : u ∈ ABC.toFinset := hG <| G.mem_support.mpr ⟨v, hu.symm⟩
      calc eval G ABC
        _ = ∑ w ∈ ABC.toFinset \ {v, x, y, z}, f G ABC w + ∑ w ∈ {v, x, y, z}, f G ABC w := by
          refine Eq.symm <| sum_sdiff ?_
          intro u hu
          simp only [mem_insert, mem_singleton] at hu
          rcases hu with h | h | h | h
          · subst h
            simp [← ABC.mem_toFinset, hBv]
          · subst h; exact hinABC h₁'
          · subst h; exact hinABC h₂'
          · subst h; exact hinABC h₃'
        _ ≤ ∑ w ∈ ABC.toFinset \ {v, x, y, z}, f (_op G x y z) ((ABC \ {z}).promote v) w
            + ∑ w ∈ {v, x, y, z}, f G ABC w := by
          refine add_le_add_left ?_ _
          refine sum_le_sum ?_
          intro w hw
          exact f_G_le_f_op_outside G (mem_sdiff.mp hw |>.2)
        _ = ∑ w ∈ ((ABC \ {z}).promote v).toFinset \ {v, x, y},
              f (_op G x y z) ((ABC \ {z}).promote v) w
            + ∑ w ∈ {v, x, y, z}, f G ABC w := by
          simp only [add_left_inj]
          refine sum_congr ?_ (fun _ _ ↦ rfl)
          rw [← promote_toFinset_eq, sdiff_toFinset]
          grind
        _ = ∑ w ∈ ((ABC \ {z}).promote v).toFinset \ {v, x, y},
              f (_op G x y z) ((ABC \ {z}).promote v) w
            + ∑ w ∈ {v, x, y}, f (_op G x y z) ((ABC \ {z}).promote v) w
            - ∑ w ∈ {v, x, y}, f (_op G x y z) ((ABC \ {z}).promote v) w
            + ∑ w ∈ {v, x, y, z}, f G ABC w := by
          ring
        _ = ∑ w ∈ ((ABC \ {z}).promote v).toFinset, f (_op G x y z) ((ABC \ {z}).promote v) w
            - ∑ w ∈ {v, x, y}, f (_op G x y z) ((ABC \ {z}).promote v) w
            + ∑ w ∈ {v, x, y, z}, f G ABC w := by
          simp only [add_left_inj, sub_left_inj]
          refine sum_sdiff ?_
          rw [← promote_toFinset_eq, sdiff_toFinset]
          intro u hu
          simp only [mem_insert, mem_singleton] at hu
          refine mem_sdiff.mpr ⟨?_, by grind [h₃'.ne]⟩
          rcases hu with h | h | h
          · subst h
            refine ABC.mem_toFinset.mp ?_
            simp only [mem_iff, hBv, or_true, not_A_of_B, not_C_of_B, or_false]
          · subst h
            exact hinABC h₁'
          · subst h
            exact hinABC h₂'
        _ ≤ #s
            - ∑ w ∈ {v, x, y}, f (_op G x y z) ((ABC \ {z}).promote v) w
            + ∑ w ∈ {v, x, y, z}, f G ABC w := by
          refine add_le_add_left ?_ _
          refine sub_le_sub_right ?_ _
          exact hscard
      suffices ∑ w ∈ {v, x, y, z}, f G ABC w
          ≤ ∑ w ∈ {v, x, y}, f (_op G x y z) ((ABC \ {z}).promote v) w by
        grind
      have : ∑ w ∈ {v, x, y, z}, f G ABC w = f G ABC v + f G ABC x + f G ABC y + f G ABC z := by
        grind [Adj.ne]
      rw [this]
      have : ∑ w ∈ {v, x, y}, f (_op G x y z) ((ABC \ {z}).promote v) w
          = f (_op G x y z) ((ABC \ {z}).promote v) v + f (_op G x y z) ((ABC \ {z}).promote v) x
          + f (_op G x y z) ((ABC \ {z}).promote v) y := by
        grind [Adj.ne]
      rw [this]
      have hfz : f G ABC z ≤ 1 / 6 := by
        have : w ∈ ({x, y, z} : Finset _) := hNv ▸ G.mem_neighborFinset .. |>.mpr hvw
        grind
      have hwfℓ {w} (hw : w = x ∨ w = y) :
          f G ABC w ≤ f (_op G x y z) ((ABC \ {z}).promote v) w + ℓ G ABC w := by
        rw [ℓ]
        have hdegrees : (_op G x y z).degree w ≤ G.degree w + 1 := by
          suffices (_op G x y z).neighborFinset w ⊆ G.neighborFinset w ∪ ({x, y} \ {w}) by
            rw [degree, degree]
            have hcard : #({x, y} \ {w} : Finset _) = 1 := by grind
            rw [← hcard]
            exact le_trans (card_le_card this) (card_union_le ..)
          intro u
          simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_neighborFinset,
            Set.union_singleton, mem_singleton, edgeSet_fromEdgeSet, Set.mem_diff,
            Set.mem_insert_iff, Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff,
            iInf_iInf_eq_left, sdiff_le_iff, le_sup_right, inf_of_le_right, sdiff_adj,
            fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet,
            ne_eq, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and,
            Decidable.not_not, and_imp, mem_union, mem_sdiff, mem_insert]
          grind
        rcases hw with hw | hw <;> {
          split_ifs with hA hB hC
          · have hA' : ((ABC \ {z}).promote v).A w :=
              A_of_promote_ne _ (by simp [h₁'.ne', h₂'.ne', hw]) ⟨hA, by simp [H₂, H₃, hw]⟩
            simp only [f, hA, ↓reduceDIte, hA']
            suffices fA (G.degree w + 1) ≤ fA ((_op G x y z).degree w) by grind
            exact fA_decreasing hdegrees
          · have hB' : ((ABC \ {z}).promote v).B w :=
              B_of_promote_ne _ (by simp [h₁'.ne', h₂'.ne', hw]) ⟨hB, by simp [H₂, H₃, hw]⟩
            simp only [f, hB, ↓reduceDIte, hB', not_A_of_B]
            suffices fB (G.degree w + 1) ≤ fB ((_op G x y z).degree w) by grind
            exact fB_decreasing hdegrees
          · have hC' : ((ABC \ {z}).promote v).C w :=
              C_of_promote_ne _ (by simp [h₁'.ne', h₂'.ne', hw]) ⟨hC, by simp [H₂, H₃, hw]⟩
            simp only [f, hB, ↓reduceDIte, hC', not_A_of_C, not_B_of_C]
            suffices fC (G.degree w + 1) ≤ fC ((_op G x y z).degree w) by grind
            exact fC_decreasing hdegrees
          · simp only [f, ↓reduceDIte, hA, hB, hC]
            split_ifs
            · simp only [add_zero, zero_le_fA]
            · simp only [add_zero, zero_le_fB]
            · simp only [add_zero, zero_le_fC]
            · simp only [add_zero, le_refl]
        }
      calc f G ABC v + f G ABC x + f G ABC y + f G ABC z
        _ ≤ 1 / 3 + (f (_op G x y z) ((ABC \ {z}).promote v) x + ℓ G ABC x)
            + (f (_op G x y z) ((ABC \ {z}).promote v) y + ℓ G ABC y)
            + 1 / 6 := by
          refine add_le_add ?_ hfz
          refine add_le_add ?_ (hwfℓ <| Or.inr rfl)
          refine add_le_add ?_ (hwfℓ <| Or.inl rfl)
          exact le_of_eq <| fB3 hBv hdv
        _ = 1 / 2 + ℓ G ABC x + ℓ G ABC y
            + f (_op G x y z) ((ABC \ {z}).promote v) x
            + f (_op G x y z) ((ABC \ {z}).promote v) y := by ring
        _ ≤ 2 / 3
            + f (_op G x y z) ((ABC \ {z}).promote v) x
            + f (_op G x y z) ((ABC \ {z}).promote v) y := by
          refine add_le_add_left ?_ _
          refine add_le_add_left ?_ _
          grind
        _ = f (_op G x y z) ((ABC \ {z}).promote v) v
            + f (_op G x y z) ((ABC \ {z}).promote v) x
            + f (_op G x y z) ((ABC \ {z}).promote v) y := by
          have hA'v : ((ABC \ {z}).promote v).A v := by
            refine promote_from_B (ABC \ {z}) v ⟨hBv, ?_⟩
            simp [h₃'.ne]
          have hdv' : (_op G x y z).degree v = 2 := by
            suffices (_op G x y z).neighborFinset v = {x, y} by grind [degree]
            ext u
            simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_neighborFinset,
              Set.union_singleton, mem_singleton, edgeSet_fromEdgeSet, Set.mem_diff,
              Set.mem_insert_iff, Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff,
              iInf_iInf_eq_left, sdiff_le_iff, le_sup_right, inf_of_le_right, sdiff_adj,
              fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, h₁'.ne, false_and,
              Prod.swap_prod_mk, h₂'.ne, or_self, mem_edgeSet, false_or, ne_eq, Set.mem_setOf_eq,
              Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, h₃'.ne', not_and, Decidable.not_not, and_imp,
              mem_insert]
            refine ⟨?_, by grind [Adj.ne]⟩
            intro ⟨h1, _⟩
            have _ : u ∈ ({x, y, z} : Finset _) := by
              simp only [← hNv, mem_neighborFinset, h1.1]
            grind
          rw [← fA2 hA'v hdv']

lemma Corollary9 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {v : Fin n} (hBv : ABC.B v) (hdv : G.degree v = 3)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    (∃ w, G.Adj v w ∧ ABC.C w) → Objective G ABC := by
  intro ⟨w, hvw, hCw⟩
  if hdw : G.degree w ≤ 1 then
    refine Claim5 hG ih ⟨w, ?_, hdw⟩
    exact ABC.mem_toFinset.mpr <| hG <| G.mem_support |>.mpr ⟨v, hvw.symm⟩
  else
    refine Claim9 hG hBv hdv ih ⟨w, hvw, ?_⟩
    refine fC_le_16_if_2_le_deg hCw ?_
    simp only [not_le] at hdw
    exact Nat.succ_le_of_lt hdw

end Tripartition
end ABC
end CaroWeiType
