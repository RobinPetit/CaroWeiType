import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim18

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

private lemma neighbors_vw {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} (hG : G.support.toFinset ⊆ ABC.toFinset) {û v w : Fin n}
    (hBv : ABC.B v) (hdv : G.degree v = 3) (hBw : ABC.B w) (hdw : G.degree w = 3)
    (hvnew : v ≠ w) (hv : G.Adj û v) (hw : G.Adj û w) (hvw : G.Adj v w)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨
      ∃ x y, G.neighborFinset v = {û, w, x} ∧ G.neighborFinset w = {û, v, y} ∧ x ≠ y:= by
  obtain ⟨x, hNv⟩ := neighborFinset_of_adj_of_adj_of_ne hdv hw.ne hv.symm hvw
  obtain ⟨y, hNw⟩ := neighborFinset_of_adj_of_adj_of_ne hdw hv.ne hw.symm hvw.symm
  if heq : x = y then
    have hne : û ≠ x := by grind [degree]
    exact Or.inl <| Claim12 hG hvw.ne hBv hdv hBw hdw hne (by grind) ih
  else
    exact Or.inr ⟨x, y, hNv, hNw, heq⟩

private lemma Claim19_vw {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} (hG : G.support.toFinset ⊆ ABC.toFinset) {û v w : Fin n}
    (hBv : ABC.B v) (hdv : G.degree v = 3) (hBw : ABC.B w) (hdw : G.degree w = 3)
    (hû : IsVstar G ABC û) (hvnew : v ≠ w) (hv : G.Adj û v) (hw : G.Adj û w) (hvw : G.Adj v w)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  match neighbors_vw hG hBv hdv hBw hdw hvnew hv hw hvw ih with
  | Or.inl h => exact h
  | Or.inr h => ?_
  obtain ⟨x, y, hNv, hNw, hxy⟩ := h
  if hdle1 : ∃ u ∈ ABC, G.degree u ≤ 1 then
    exact Claim5 hG ih hdle1
  else if hA4û : ABC.A û ∧ G.degree û = 4 then
    exact Claim18 hG hû hA4û.1 hA4û.2 hBv hdv hBw hdw hvnew hv hw hvw ih
  else
    match Claim15 hG hû ih with
    | Or.inl h => exact h
    | Or.inr hdû => ?_
    have hfû : f G ABC û ≤ 1 / 3 := f_le_1_over_3_of_4_le_deg_of_notA4 hdû hA4û
    have hxv : G.Adj x v := Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNv]
    have hyw : G.Adj y w := Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]
    have hxABC :=
      ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨_, hxv⟩
    have hyABC :=
      ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨_, hyw⟩
    if hdx : G.degree x = 2 then
      cases hxABC with
      | inl hA =>  exact Claim7 hG ih ⟨_, _, hdv, hBv, hdx, hA, hxv.symm⟩
      | inr hBC => exact Claim6 hG ih ⟨_, hdx, by grind [not_A_of_B, not_A_of_C]⟩
    else if hdy : G.degree y = 2 then
      cases hyABC with
      | inl hA =>  exact Claim7 hG ih ⟨_, _, hdw, hBw, hdy, hA, hyw.symm⟩
      | inr hBC => exact Claim6 hG ih ⟨_, hdy, by grind [not_A_of_B, not_A_of_C]⟩
    else
      have hfx : f G ABC x ≤ 1 / 2 := f_le_1_over_2_of_3_le_deg (by grind)
      have hfy : f G ABC y ≤ 1 / 2 := f_le_1_over_2_of_3_le_deg (by grind)
      refine Corollary2' hG hBv hBw hxv hyw hvnew ?_ ih
      rw [hNvw hNv hNw, sum_hNvw hxy hdv hdw hvnew hNv hNw]
      linarith [fB3 hBv hdv, fB3 hBw hdw]

private lemma neighbors_not_vw {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {û v w : Fin n}
    (hvw : ¬G.Adj v w) (hvnew : v ≠ w) (hv : G.Adj û v) (hw : G.Adj û w)
    (hdv : G.degree v = 3) (hdw : G.degree w = 3) (hBv : ABC.B v) (hBw : ABC.B w) :
    ∃ v w x y s t,
      ABC.B v ∧ ABC.B w ∧ G.degree v = 3 ∧ G.degree w = 3 ∧ ¬G.Adj v w ∧ v ≠ w ∧
      G.Adj û v ∧ G.Adj û w ∧ G.neighborFinset v = {û, x, y} ∧ G.neighborFinset w = {û, s, t} ∧
      f G ABC y ≤ f G ABC x ∧ f G ABC t ≤ f G ABC s ∧
      ℓ G ABC s + ℓ G ABC t ≤ ℓ G ABC x + ℓ G ABC y := by
  obtain ⟨x, y, hNv, hfyx⟩ :=
    neighborFinset_eq_deg3' (G.mem_neighborFinset .. |>.mpr hv.symm) (f G ABC ·) hdv
  obtain ⟨s, t, hNw, hfts⟩ :=
    neighborFinset_eq_deg3' (G.mem_neighborFinset .. |>.mpr hw.symm) (f G ABC ·) hdw
  if hℓxy : ℓ G ABC s + ℓ G ABC t ≤ ℓ G ABC x + ℓ G ABC y then
    exact ⟨v, w, x, y, s, t, hBv, hBw, hdv, hdw, hvw, hvnew, hv, hw, hNv, hNw, hfyx, hfts, hℓxy⟩
  else
    exact ⟨w, v, s, t, x, y, hBw, hBv, hdw, hdv, not_adj_symm hvw, Ne.symm hvnew, hw, hv, hNw, hNv,
      hfts, hfyx, le_of_lt <| not_le.mp hℓxy⟩

private lemma A3_or_1_over_15 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} (hG : G.support.toFinset ⊆ ABC.toFinset)
    {x : Fin n} (hdx : 3 ≤ G.degree x) :
    (ABC.A x ∧ G.degree x = 3) ∨ ℓ G ABC x ≤ 1 / 15 := by
  have hγ : γ G ABC x ≤ 1 / 6 := γ_le_1_over_6_of_3_le_degree hdx
  have hx : x ∈ ABC :=
    ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr
      <| G.degree_pos_iff_mem_support _ |>.mp (by linarith)
  match lt_or_eq_of_le hdx with
  | Or.inl h => exact Or.inr <| ℓ_le_1_over_15_of_4_le_degree h
  | Or.inr h => ?_
  rcases hx with hx | hx | hx
  · simp only [hx, h, true_and, true_or]
  · simp only [ℓB3 hx h.symm, le_refl, or_true]
  · simp only [ℓC3 hx h.symm]
    grind

private lemma _losses {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) {v x y : Fin n} (hBv : ABC.B v) (hdv : G.degree v = 3)
    (hxy : x ≠ y) (hdx : 3 ≤ G.degree x) (hdy : 3 ≤ G.degree y)
    (hx : x ∈ G.neighborFinset v) (hy : y ∈ G.neighborFinset v)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨ ℓ G ABC x + ℓ G ABC y ≤ 1 / 6 := by
  match A3_or_1_over_15 hG hdx, A3_or_1_over_15 hG hdy with
  | _, Or.inr h =>
      suffices ℓ G ABC x ≤ 1 / 10 by grind
      exact ℓ_le_1_over_10_of_3_le_degree hdx
  | Or.inr h, _ =>
      suffices ℓ G ABC y ≤ 1 / 10 by grind
      exact ℓ_le_1_over_10_of_3_le_degree hdy
  | Or.inl h, Or.inl h' => ?_
  have hv : v ∈ ABC :=
    ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr
      <| (G.degree_pos_iff_mem_support _).mp <| by linarith
  refine Or.inl <| Claim1 hv hG ih ?_
  calc f G ABC v
    _ = 1 / 3 := by rw [fB3 hBv hdv]
    _ = γ G ABC x + γ G ABC y := by
      linarith [γA3 h.1 h.2, γA3 h'.1 h'.2]
    _ = ∑ u ∈ {x, y}, γ G ABC u := by grind
  refine sum_le_sum_of_subset_of_nonneg (by grind) fun _ _ _ ↦ γ_nonneg

@[reducible]
private def _op_g {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (û x y s t : Fin n) :
    SimpleGraph (Fin n) :=
  (fromEdgeSet <| G.edgeSet ∪ {s(x, y), s(s, t)}).deleteIncidencesOf {û}

private lemma adj_vx {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {û v x y s t : Fin n} (hdv : G.degree v = 3) (hNv : G.neighborFinset v = {û, x, y}) :
    (_op_g G û x y s t).Adj v x := by
  have hvx : G.Adj v x := G.mem_neighborFinset .. |>.mp <| by simp [hNv]
  have hvnex : v ≠ x := hvx.ne
  simp only [_op_g, deleteIncidencesOf, Set.union_insert, Set.union_singleton, mem_singleton,
    deleteIncidenceSet, incidenceSet, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff,
    Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, iInf_iInf_eq_left, sdiff_le_iff,
    le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff',
    Prod.mk.injEq, hvnex, false_and, Prod.swap_prod_mk, and_true, false_or, mem_edgeSet, hvx,
    or_true, ne_eq, not_false_eq_true, and_self, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq,
    Sym2.mem_iff, true_and, not_or]
  refine ⟨?_, ?_⟩
  · refine Adj.ne' <| G.mem_neighborFinset .. |>.mp <| by simp [hNv]
  · grind [degree]

private lemma adj_vy {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {û v x y s t : Fin n} (hdv : G.degree v = 3) (hNv : G.neighborFinset v = {û, x, y}) :
    (_op_g G û x y s t).Adj v y := by
  have hvy : G.Adj v y := G.mem_neighborFinset .. |>.mp <| by simp [hNv]
  have hvney : v ≠ y := hvy.ne
  simp only [_op_g, deleteIncidencesOf, Set.union_insert, Set.union_singleton, mem_singleton,
    deleteIncidenceSet, incidenceSet, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff,
    Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, iInf_iInf_eq_left, sdiff_le_iff,
    le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff',
    Prod.mk.injEq, hvney, false_and, Prod.swap_prod_mk, and_true, mem_edgeSet, hvy,
    or_true, ne_eq, not_false_eq_true, and_self, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq,
    Sym2.mem_iff, true_and, not_or]
  refine ⟨?_, ?_⟩
  · refine Adj.ne' <| G.mem_neighborFinset .. |>.mp <| by simp [hNv]
  · grind [degree]

private lemma adj_xy {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {û v x y s t : Fin n} (hdv : G.degree v = 3) (hNv : G.neighborFinset v = {û, x, y}) :
    (_op_g G û x y s t).Adj x y := by
  simp only [_op_g, deleteIncidencesOf, Set.union_insert, Set.union_singleton, mem_singleton,
    deleteIncidenceSet, incidenceSet, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff,
    Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, iInf_iInf_eq_left, sdiff_le_iff,
    le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff',
    Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, true_or, ne_eq, true_and, Set.mem_setOf_eq,
    Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and, Decidable.not_not, and_imp]
  grind [degree]

private lemma adj_ws {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {û w x y s t : Fin n} (hdw : G.degree w = 3) (hNw : G.neighborFinset w = {û, s, t}) :
    (_op_g G û x y s t).Adj w s := by
  have hws : G.Adj w s := G.mem_neighborFinset .. |>.mp <| by simp [hNw]
  have hwnes : w ≠ s := hws.ne
  simp only [_op_g, deleteIncidencesOf, Set.union_insert, Set.union_singleton, mem_singleton,
    deleteIncidenceSet, incidenceSet, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff,
    Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, iInf_iInf_eq_left, sdiff_le_iff,
    le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff',
    Prod.mk.injEq, hwnes, false_and, Prod.swap_prod_mk, and_true, false_or, mem_edgeSet, hws,
    or_true, ne_eq, not_false_eq_true, and_self, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq,
    Sym2.mem_iff, true_and, not_or]
  refine ⟨?_, ?_⟩
  · refine Adj.ne' <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]
  · grind [degree]

private lemma adj_wt {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {û w x y s t : Fin n} (hdw : G.degree w = 3) (hNw : G.neighborFinset w = {û, s, t}) :
    (_op_g G û x y s t).Adj w t := by
  have hwt : G.Adj w t := G.mem_neighborFinset .. |>.mp <| by simp [hNw]
  have hwnet : w ≠ t := hwt.ne
  simp only [_op_g, deleteIncidencesOf, Set.union_insert, Set.union_singleton, mem_singleton,
    deleteIncidenceSet, incidenceSet, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff,
    Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, iInf_iInf_eq_left, sdiff_le_iff,
    le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff',
    Prod.mk.injEq, hwnet, false_and, Prod.swap_prod_mk, and_true, mem_edgeSet, hwt,
    or_true, ne_eq, not_false_eq_true, and_self, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq,
    Sym2.mem_iff, true_and, not_or]
  refine ⟨?_, ?_⟩
  · refine Adj.ne' <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]
  · grind [degree]

private lemma adj_st {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {û w x y s t : Fin n} (hdw : G.degree w = 3) (hNw : G.neighborFinset w = {û, s, t}) :
    (_op_g G û x y s t).Adj s t := by
  simp only [_op_g, deleteIncidencesOf, Set.union_insert, Set.union_singleton, mem_singleton,
    deleteIncidenceSet, incidenceSet, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff,
    Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, iInf_iInf_eq_left, sdiff_le_iff,
    le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff',
    Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, true_or, or_true, ne_eq, true_and,
    Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and, Decidable.not_not, and_imp]
  grind [degree]

private lemma neighborFinset_subset {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {F : Finset (Fin n)} {û u x y s t : Fin n} (hû : û ∉ F) (huneû : u ≠ û) :
    G.neighborFinset u ∩ F ⊆ (_op_g G û x y s t).neighborFinset u ∩ F := by
  intro u'
  simp only [mem_inter, mem_neighborFinset, deleteIncidencesOf, deleteIncidenceSet, incidenceSet,
    Set.union_insert, Set.union_singleton, mem_singleton, edgeSet_fromEdgeSet, Set.mem_diff,
    Set.mem_insert_iff, Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff,
    iInf_iInf_eq_left, sdiff_le_iff, le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj,
    Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, ne_eq, Set.mem_setOf_eq,
    Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and, Decidable.not_not, and_imp]
  grind [Adj.ne]

@[reducible]
private def _op_t {n : ℕ} (ABC : Tripartition n) (û v w : Fin n) : Tripartition n := by
  exact ABC \ {û} |>.promote_finset {v, w}

private lemma _hGop {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) {û v w x y s t : Fin n}
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t}) :
    (_op_g G û x y s t).support.toFinset ⊆ (_op_t ABC û v w).toFinset := by
  intro u
  simp only [_op_g, deleteIncidencesOf, Set.union_insert, Set.union_singleton, mem_singleton,
    deleteIncidenceSet, incidenceSet, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff,
    Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, iInf_iInf_eq_left, sdiff_le_iff,
    le_sup_right, inf_of_le_right, Set.mem_toFinset, mem_support, sdiff_adj, fromEdgeSet_adj,
    Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, ne_eq, Set.mem_setOf_eq,
    Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and, Decidable.not_not, and_imp, _op_t,
    ← promote_finset_toFinset_eq, toFinset_eq, mem_sdiff, forall_exists_index]
  intro u' hu huneu' hu'
  simp only [huneu', not_false_eq_true, imp_false, not_or, forall_const] at hu'
  rcases hu with hu | hu | hu
  · simp only [hu, true_or, forall_const] at hu'
    refine ⟨?_, Ne.symm hu'.1⟩
    suffices u ∈ ({x, y} : Finset _) by
      refine hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨v, ?_⟩
      exact Adj.symm <| G.mem_neighborFinset .. |>.mp (by grind)
    grind
  · simp only [hu, true_or, or_true, forall_const] at hu'
    refine ⟨?_, Ne.symm hu'.1⟩
    suffices u ∈ ({s, t} : Finset _) by
      refine hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨w, ?_⟩
      exact Adj.symm <| G.mem_neighborFinset .. |>.mp (by grind)
    grind
  · exact ⟨hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨u', hu⟩, by grind⟩

private lemma _respects {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {û v w x y s t : Fin n} {F : Finset (Fin n)}
    (hdv : G.degree v = 3) (hdw : G.degree w = 3) (hBv : ABC.B v) (hBw : ABC.B w)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t})
    (hF : F ⊆ (ABC._op_t û v w).toFinset) (hFf : (_op_g G û x y s t).InducesForest F)
    (hFresp : respects F (_op_g G û x y s t) (ABC._op_t û v w)) :
    respects F G ABC := by
  intro u huF
  have hûF : û ∉ F := by
    intro this
    have hobj := hF this
    simp only [_op_t, ← promote_finset_toFinset_eq, toFinset_eq, mem_sdiff, mem_singleton,
      not_true_eq_false, and_false] at hobj
  have huneû : u ≠ û := fun heq ↦ hûF (heq ▸ huF)
  have huû : u ∉ ({û} : Finset _) := by simp only [mem_singleton, huneû, not_false_eq_true]
  refine ⟨?_, ?_, ?_⟩
  · intro hAu
    refine le_trans (card_le_card ?_) (hFresp u huF |>.1 <| Or.inl ⟨hAu, huû⟩)
    exact neighborFinset_subset hûF fun heq ↦ hûF (heq ▸ huF)
  · intro hBu
    if hu : u ∈ ({v, w} : Finset _) then
      have hB'u : (_op_t ABC û v w).A u := Or.inr ⟨⟨hBu, huû⟩, hu⟩
      have hvxy := by
        refine @no_induced_K3_of_InducesForest _ _ _ F v x y ?_ ?_ ?_ hFf
        · exact adj_vx hdv hNv
        · exact adj_xy hdv hNv
        · exact (adj_vy hdv hNv).symm
      have hvxy := by
        refine @no_induced_K3_of_InducesForest _ _ _ F w s t ?_ ?_ ?_ hFf
        · exact adj_ws hdw hNw
        · exact adj_st hdw hNw
        · exact (adj_wt hdw hNw).symm
      simp only [mem_insert, mem_singleton] at hu
      rcases hu with hu | hu
      · if hx : x ∈ F then refine (card_singleton x) ▸ card_le_card (by grind)
        else               refine (card_singleton y) ▸ card_le_card (by grind)
      · if hx : s ∈ F then refine (card_singleton s) ▸ card_le_card (by grind)
        else               refine (card_singleton t) ▸ card_le_card (by grind)
    else
      refine le_trans (card_le_card ?_) (hFresp u huF |>.2.1 <| Or.inl ⟨⟨hBu, huû⟩, hu⟩)
      exact neighborFinset_subset hûF fun heq ↦ hûF (heq ▸ huF)
  · intro hCu
    have hu : u ∉ ({v, w} : Finset _) := by
      grind only [= mem_insert, = Sym2.eq, not_C_of_B, = mem_singleton]
    refine le_antisymm ?_ (Nat.zero_le _)
    refine le_of_le_of_eq (card_le_card ?_) (hFresp u huF |>.2.2 <| ⟨⟨hCu, huû⟩, hu⟩)
    exact neighborFinset_subset hûF fun heq ↦ hûF (heq ▸ huF)

private lemma f_le_op {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    {û v w x y s t u : Fin n} (hu : u ∈ ABC.toFinset \ ({û, v, w, x, y, s, t} : Finset _)) :
    f G ABC u ≤ f (_op_g G û x y s t) (_op_t ABC û v w) u := by
  simp only [mem_sdiff] at hu
  have hNu : (_op_g G û x y s t).neighborFinset u ⊆ G.neighborFinset u := by
    intro u'
    simp only [mem_neighborFinset, deleteIncidencesOf, deleteIncidenceSet, incidenceSet,
      Set.union_insert, Set.union_singleton, mem_singleton, edgeSet_fromEdgeSet, Set.mem_diff,
      Set.mem_insert_iff, Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff,
      iInf_iInf_eq_left, sdiff_le_iff, le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj,
      Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, ne_eq,
      Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and, Decidable.not_not, and_imp]
    grind
  rcases ABC.coe_mem_toFinset.mpr hu.1 with hA | hB | hC
  · have hA' : (_op_t ABC û v w).A u := Or.inl ⟨hA, by grind⟩
    simp only [f, hA, hA', ↓reduceDIte]
    exact fA_decreasing (card_le_card hNu)
  · have hB' : (_op_t ABC û v w).B u := Or.inl ⟨⟨hB, by grind⟩, by grind⟩
    simp only [f, hB, hB', not_A_of_B, ↓reduceDIte]
    exact fB_decreasing (card_le_card hNu)
  · have hC' : (_op_t ABC û v w).C u := ⟨⟨hC, by grind⟩, by grind⟩
    simp only [f, hC, hC', not_A_of_C, not_B_of_C, ↓reduceDIte]
    exact fC_decreasing (card_le_card hNu)

private lemma hin_toFinset {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {û v w x y s t : Fin n} {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) (hv : G.Adj û v) (hw : G.Adj û w)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t}) :
    {û, v, w, x, y, s, t} ⊆ ABC.toFinset := by
  have : {û, x, y} ⊆ ABC.toFinset := by
    intro u hu
    refine hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨v, ?_⟩
    refine Adj.symm <| G.mem_neighborFinset .. |>.mp (by grind)
  have : {û, s, t} ⊆ ABC.toFinset := by
    intro u hu
    refine hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨w, ?_⟩
    refine Adj.symm <| G.mem_neighborFinset .. |>.mp (by grind)
  suffices {v, w} ⊆ ABC.toFinset by
    grind
  exact fun _ _ ↦ hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr (by grind [Adj.symm])

private lemma A2_vw {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    {u û v w x y s t : Fin n} (hu : u ∈ ({v, w} : Finset _))
    (hBv : ABC.B v) (hBw : ABC.B w) (hdv : G.degree v = 3) (hdw : G.degree w = 3)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t})
    (hNxy : ({v, w} : Finset _) ∩ {x, y, s, t} = ∅) :
    (_op_t ABC û v w).A u ∧ (_op_g G û x y s t).degree u = 2 := by
  refine ⟨?_, ?_⟩
  · refine Or.inr ⟨⟨by grind, ?_⟩, hu⟩
    simp only [mem_singleton]
    refine (G.mem_neighborFinset .. |>.mp (by grind)).ne
  · suffices (G.neighborFinset u \ {û}) = (_op_g G û x y s t).neighborFinset u by
      refine Eq.symm ?_
      calc _
        _ = 3 - 1 := Eq.symm (Nat.add_one_sub_one _)
        _ = #(G.neighborFinset u) - 1 := by
          grind [degree]
        _ = #(G.neighborFinset u \ {û}) := by
          rw [← card_singleton û]
          refine Eq.symm <| card_sdiff_of_subset (by grind)
        _ = #((_op_g G û x y s t).neighborFinset u \ {û}) := by
          rw [congrArg Finset.card this]
          refine congrArg _ ?_
          refine eq_sdiff_of_empty_inter ?_
          grind
      suffices û ∉ (_op_g G û x y s t).neighborFinset u by
        grind [degree]
      simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_neighborFinset,
        Set.union_insert, Set.union_singleton, mem_singleton, edgeSet_fromEdgeSet, Set.mem_diff,
        Set.mem_insert_iff, Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff,
        iInf_iInf_eq_left, sdiff_le_iff, le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj,
        Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, ne_eq,
        Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, or_true, and_true, and_self_right,
        not_and, Decidable.not_not, Classical.not_imp, imp_self]
    ext z
    simp only [mem_sdiff, mem_neighborFinset, mem_singleton, deleteIncidencesOf, deleteIncidenceSet,
      incidenceSet, Set.union_insert, Set.union_singleton, edgeSet_fromEdgeSet, Set.mem_diff,
      Set.mem_insert_iff, Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff,
      iInf_iInf_eq_left, sdiff_le_iff, le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj,
      Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, ne_eq,
      Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and, Decidable.not_not, and_imp]
    constructor
    · intro ⟨huz, hne⟩
      suffices u ≠ û by grind [Adj.ne]
      refine (G.mem_neighborFinset .. |>.mp (by grind)).ne
    · intro ⟨⟨h, hunez⟩, h'⟩
      rcases h with h | h <;> grind

private lemma u_notin_singleton_û {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u û v w x y s t : Fin n} (hdv : G.degree v = 3) (hdw : G.degree w = 3)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t})
    (hu : u ∈ ({x, y, s, t} : Finset _)) : u ∉ ({û} : Finset _) := by
  if u ∈ ({x, y} : Finset _) then
    grind [degree]
  else
    grind [degree]

private lemma Δf_le_ℓ {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {u û v w x y s t : Fin n} (hdv : G.degree v = 3) (hdw : G.degree w = 3)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t})
    (hu : u ∈ ({x, y, s, t} : Finset _))
    (hNvw : ({x, y} : Finset _) ∩ {s, t} = ∅)
    (Hcap : ({v, w} : Finset _) ∩ {x, y, s, t} = ∅) :
    f G ABC u - f (_op_g G û x y s t) (ABC._op_t û v w) u ≤ ℓ G ABC u := by
  if huABC : u ∈ ABC then
    have huû : u ∉ ({û} : Finset _) := u_notin_singleton_û hdv hdw hNv hNw hu
    have hdu : (_op_g G û x y s t).degree u ≤ G.degree u + 1 := by
      simp only [mem_insert, mem_singleton] at hu
      rcases hu with hu | hu | hu | hu
      · rw [← card_singleton y, degree, degree]
        refine le_trans (card_le_card ?_) (card_union_le ..)
        intro z
        simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_neighborFinset,
          Set.union_insert, Set.union_singleton, mem_singleton, edgeSet_fromEdgeSet, Set.mem_diff,
          Set.mem_insert_iff, Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff,
          iInf_iInf_eq_left, sdiff_le_iff, le_sup_right, inf_of_le_right, hu, sdiff_adj,
          fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk,
          mem_edgeSet, ne_eq, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and,
          Decidable.not_not, and_imp, union_singleton, mem_insert]
        grind
      · rw [← card_singleton x, degree, degree]
        refine le_trans (card_le_card ?_) (card_union_le ..)
        intro z
        simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_neighborFinset,
          Set.union_insert, Set.union_singleton, mem_singleton, edgeSet_fromEdgeSet, Set.mem_diff,
          Set.mem_insert_iff, Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff,
          iInf_iInf_eq_left, sdiff_le_iff, le_sup_right, inf_of_le_right, hu, sdiff_adj,
          fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk,
          mem_edgeSet, ne_eq, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and,
          Decidable.not_not, and_imp, union_singleton, mem_insert]
        grind
      · rw [← card_singleton t, degree, degree]
        refine le_trans (card_le_card ?_) (card_union_le ..)
        intro z
        simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_neighborFinset,
          Set.union_insert, Set.union_singleton, mem_singleton, edgeSet_fromEdgeSet, Set.mem_diff,
          Set.mem_insert_iff, Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff,
          iInf_iInf_eq_left, sdiff_le_iff, le_sup_right, inf_of_le_right, hu, sdiff_adj,
          fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk,
          mem_edgeSet, ne_eq, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and,
          Decidable.not_not, and_imp, union_singleton, mem_insert]
        grind
      · rw [← card_singleton s, degree, degree]
        refine le_trans (card_le_card ?_) (card_union_le ..)
        intro z
        simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_neighborFinset,
          Set.union_insert, Set.union_singleton, mem_singleton, edgeSet_fromEdgeSet, Set.mem_diff,
          Set.mem_insert_iff, Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff,
          iInf_iInf_eq_left, sdiff_le_iff, le_sup_right, inf_of_le_right, hu, sdiff_adj,
          fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk,
          mem_edgeSet, ne_eq, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and,
          Decidable.not_not, and_imp, union_singleton, mem_insert]
        grind
    rcases huABC with hA | hB | hC
    · have hA' : (_op_t ABC û v w).A u := Or.inl ⟨hA, huû⟩
      simp only [f, hA, hA', ↓reduceDIte, ℓ]
      suffices fA (G.degree u + 1) ≤ fA ((_op_g G û x y s t).degree u) by
        linarith
      exact fA_decreasing hdu
    · have hB' : (_op_t ABC û v w).B u := Or.inl ⟨⟨hB, huû⟩, notMem_of_empty_inter_of_mem Hcap hu⟩
      simp only [f, hB, hB', not_A_of_B, ↓reduceDIte, ℓ]
      suffices fB (G.degree u + 1) ≤ fB ((_op_g G û x y s t).degree u) by
        linarith
      exact fB_decreasing hdu
    · have hC' : (_op_t ABC û v w).C u := ⟨⟨hC, huû⟩, notMem_of_empty_inter_of_mem Hcap hu⟩
      simp only [f, hC, hC', not_A_of_C, not_B_of_C, ↓reduceDIte, ℓ]
      suffices fC (G.degree u + 1) ≤ fC ((_op_g G û x y s t).degree u) by
        linarith
      exact fC_decreasing hdu
  else
    have hu'ABC : u ∉ (_op_t ABC û v w) := by
      refine (mem_of_mem_promote_finset _).mt ?_
      exact not_iff_not.mpr (ABC.mem_sdiff_iff _) |>.mpr <| by simp [huABC]
    simp only [← f_eq_zero_of_notMem G huABC, ← f_eq_zero_of_notMem (_op_g G û x y s t) hu'ABC,
      ← ℓ_eq_zero_of_notMem G huABC, sub_self, le_refl]

private lemma eval_ok_not_A4 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {F : Finset (Fin n)} {û v w x y s t : Fin n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) (hdû : 4 ≤ G.degree û)
    (hA4û : ¬(ABC.A û ∧ G.degree û = 4))
    (hvw : ¬G.Adj v w) (hxy : x ≠ y) (hvnew : v ≠ w) (hv : G.Adj û v) (hw : G.Adj û w)
    (hBv : ABC.B v) (hdv : G.degree v = 3) (hBw : ABC.B w) (hdw : G.degree w = 3)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t})
    (hNvw : ({x, y} : Finset _) ∩ {s, t} = ∅)
    (hFcard : eval (_op_g G û x y s t) (ABC._op_t û v w) ≤ #F)
    (hℓxy : ℓ G ABC x + ℓ G ABC y ≤ 1 / 6)
    (hℓ : ℓ G ABC s + ℓ G ABC t ≤ ℓ G ABC x + ℓ G ABC y) :
    eval G ABC ≤ ↑(#F) := by
  calc eval G ABC
    _ = ∑ u ∈ ABC.toFinset, f G ABC u := by rfl
    _ = ∑ u ∈ ABC.toFinset \ {û, v, w, x, y, s, t}, f G ABC u
        + ∑ u ∈ {û, v, w, x, y, s, t}, f G ABC u := by
      refine Eq.symm <| sum_sdiff <| hin_toFinset hG hv hw hNv hNw
    _ ≤ ∑ u ∈ ABC.toFinset \ {û, v, w, x, y, s, t}, f (_op_g G û x y s t) (_op_t ABC û v w) u
        + ∑ u ∈ {û, v, w, x, y, s, t}, f G ABC u := by
      simp only [add_le_add_iff_right]
      exact sum_le_sum fun _ hu ↦ f_le_op hu
    _ = ∑ u ∈ ABC.toFinset \ {û, v, w, x, y, s, t}, f (_op_g G û x y s t) (_op_t ABC û v w) u
        + ∑ u ∈ {v, w, x, y, s, t}, f (_op_g G û x y s t) (_op_t ABC û v w) u
        - ∑ u ∈ {v, w, x, y, s, t}, f (_op_g G û x y s t) (_op_t ABC û v w) u
        + ∑ u ∈ {û, v, w, x, y, s, t}, f G ABC u := by linarith
    _ = ∑ u ∈ ((ABC.toFinset \ {û, v, w, x, y, s, t}) ∪ {v, w, x, y, s, t}),
          f (_op_g G û x y s t) (_op_t ABC û v w) u
        - ∑ u ∈ {v, w, x, y, s, t}, f (_op_g G û x y s t) (_op_t ABC û v w) u
        + ∑ u ∈ {û, v, w, x, y, s, t}, f G ABC u := by
      simp only [add_left_inj, sub_left_inj]
      refine Eq.symm <| sum_union ?_
      refine disjoint_iff_inter_eq_empty.mpr ?_
      ext
      simp only [mem_sdiff, mem_insert, mem_singleton, true_or, or_true, not_true_eq_false,
        and_false, not_false_eq_true, inter_insert_of_notMem, inter_singleton_of_notMem,
        notMem_empty]
    _ = eval (_op_g G û x y s t) (_op_t ABC û v w)
        - ∑ u ∈ {v, w, x, y, s, t}, f (_op_g G û x y s t) (_op_t ABC û v w) u
        + ∑ u ∈ {û, v, w, x, y, s, t}, f G ABC u := by
      simp only [add_left_inj, sub_left_inj]
      suffices (ABC.toFinset \ {û, v, w, x, y, s, t}) ∪ {v, w, x, y, s, t}
          = (_op_t ABC û v w).toFinset by
        rw [this]
        rfl
      simp only [_op_t, ← promote_finset_toFinset_eq, sdiff_toFinset]
      ext u
      simp only [mem_union, mem_sdiff]
      refine ⟨?_, by grind only [= mem_insert, = mem_singleton]⟩
      have : {û, v, w, x, y, s, t} ⊆ ABC.toFinset := by exact hin_toFinset hG hv hw hNv hNw
      intro h
      rcases h with h | h
      · exact ⟨h.1, by grind only [= mem_insert, = mem_singleton]⟩
      · grind [degree, Adj.ne]
  suffices ∑ u ∈ {û, v, w, x, y, s, t}, f G ABC u
      ≤ ∑ u ∈ {v, w, x, y, s, t}, f (_op_g G û x y s t) (ABC._op_t û v w) u by
    linarith
  have : û ∉ ({v, w, x, y, s, t} : Finset _) := by grind [degree, Adj.ne]
  suffices f G ABC û
      + ∑ u ∈ {v, w, x, y, s, t}, (f G ABC u - f (_op_g G û x y s t) (_op_t ABC û v w) u) ≤ 0 by
    calc _
      _ = f G ABC û + ∑ u ∈ {v, w, x, y, s, t}, f G ABC u := by
        grind
    rw [sum_sub_distrib] at this
    linarith
  have Hcap : ({v, w} : Finset _) ∩ {x, y, s, t} = ∅ := by
    ext u
    simp only [mem_inter, notMem_empty, iff_false, not_and]
    intro hu
    simp only [mem_insert, mem_singleton] at hu
    suffices u ∉ ({x, y} : Finset _) ∧ u ∉ ({s, t} : Finset _) by
      grind
    rcases hu with hu | hu
    · refine ⟨?_, ?_⟩
      · simp only [mem_insert, mem_singleton, not_or]
        refine ⟨?_, ?_⟩ <;> exact (G.mem_neighborFinset .. |>.mp (by simp [hu ▸ hNv])).ne
      · suffices u ∉ G.neighborFinset w by grind
        exact not_iff_not.mpr (G.mem_neighborFinset ..) |>.mpr fun h ↦ hvw (hu ▸ h.symm)
    · refine ⟨?_, ?_⟩
      · suffices u ∉ G.neighborFinset v by grind
        exact not_iff_not.mpr (G.mem_neighborFinset ..) |>.mpr fun h ↦ hvw (hu ▸ h)
      · simp only [mem_insert, mem_singleton, not_or]
        refine ⟨?_, ?_⟩ <;> exact (G.mem_neighborFinset .. |>.mp (by simp [hu ▸ hNw])).ne
  suffices f G ABC û
      + (f G ABC v - f (_op_g G û x y s t) (_op_t ABC û v w) v)
      + (f G ABC w - f (_op_g G û x y s t) (_op_t ABC û v w) w)
      + ∑ u ∈ {x, y, s, t}, (f G ABC u - f (_op_g G û x y s t) (_op_t ABC û v w) u)
      ≤ 0 by
    grind
  obtain ⟨hA'v, hdv'⟩ : (_op_t ABC û v w).A v ∧ (_op_g G û x y s t).degree v = 2 :=
    A2_vw (by simp only [mem_insert, mem_singleton, true_or]) hBv hBw hdv hdw hNv hNw Hcap
  obtain ⟨hA'w, hdw'⟩ : (_op_t ABC û v w).A w ∧ (_op_g G û x y s t).degree w = 2 :=
    A2_vw (by simp only [mem_insert, mem_singleton, or_true]) hBv hBw hdv hdw hNv hNw Hcap
  rw [fB3 hBv hdv, fB3 hBw hdw, fA2 hA'v hdv', fA2 hA'w hdw']
  suffices ∑ u ∈ {x, y, s, t}, (f G ABC u - f (_op_g G û x y s t) (ABC._op_t û v w) u) ≤ 1 / 3 by
    have : f G ABC û ≤ 1 / 3 := f_le_1_over_3_of_4_le_deg_of_notA4 hdû hA4û
    linarith
  suffices ∑ u ∈ {x, y, s, t}, ℓ G ABC u ≤ 1 / 3 by
    refine le_trans ?_ this
    refine sum_le_sum ?_
    intro u hu
    exact Δf_le_ℓ hdv hdw hNv hNw hu hNvw Hcap
  grind [degree]

private lemma _ok_not_A4 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) {û v w x y s t : Fin n}
    (hA4û : ¬(ABC.A û ∧ G.degree û = 4)) (hdû : 4 ≤ G.degree û)
    (hvw : ¬G.Adj v w) (hBv : ABC.B v) (hdv : G.degree v = 3) (hBw : ABC.B w) (hdw : G.degree w = 3)
    (hNv : G.neighborFinset v = {û, x, y})
    (hNw : G.neighborFinset w = {û, s, t})
    (hxy : x ≠ y) (hvnew : v ≠ w) (hv : G.Adj û v) (hw : G.Adj û w)
    (hdx : 3 ≤ G.degree x) (hdy : 3 ≤ G.degree y)
    (hNvw : ({x, y} : Finset _) ∩ {s, t} = ∅)
    (hℓxy : ℓ G ABC x + ℓ G ABC y ≤ 1 / 6)
    (hℓ : ℓ G ABC s + ℓ G ABC t ≤ ℓ G ABC x + ℓ G ABC y)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  match _losses hG hBv hdv hxy hdx hdy (by simp [hNv]) (by simp [hNv]) ih with
  | Or.inl h => exact h
  | Or.inr h => ?_
  have H : (_op_t ABC û v w).card < ABC.card := by
    simp only [_op_t, ← card_promote_finset_eq_card]
    refine ABC.sdiff_card <| nonempty_iff_ne_empty.mp ⟨û, ?_⟩
    simp only [mem_inter, mem_singleton, true_and]
    exact hG <| Set.mem_toFinset.mpr <| (G.degree_pos_iff_mem_support û).mp <| by linarith
  obtain ⟨F, hF, hFf, hFresp, hFcard⟩ := by
    refine ih (_op_g G û x y s t) (_op_t ABC û v w) (_hGop hG hNv hNw) ?_
    simp only [_op_t, ← card_promote_finset_eq_card]
    refine sdiff_card ABC <| nonempty_iff_ne_empty.mp ⟨û, ?_⟩
    simp only [mem_inter, mem_singleton, true_and]
    exact hG <| Set.mem_toFinset.mpr <| (G.degree_pos_iff_mem_support û).mp (by linarith)
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · refine subset_trans hF ?_
    simp only [_op_t, ← promote_finset_toFinset_eq]
    exact toFinset_mono
  · intro t ht htne
    obtain ⟨u, hut, hdu⟩ := hFf t ht htne
    refine ⟨u, hut, le_trans (card_le_card ?_) hdu⟩
    intro u'
    simp only [mem_inter, mem_neighborFinset, deleteIncidencesOf, deleteIncidenceSet,
      incidenceSet, Set.union_insert, Set.union_singleton, mem_singleton, edgeSet_fromEdgeSet,
      Set.mem_diff, Set.mem_insert_iff, Sym2.mem_diagSet, deleteEdges_fromEdgeSet,
      fromEdgeSet_sdiff, iInf_iInf_eq_left, sdiff_le_iff, le_sup_right, inf_of_le_right, sdiff_adj,
      fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, ne_eq,
      Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and, Decidable.not_not, and_imp]
    intro huu' hu't
    simp only [huu', or_true, huu'.ne, not_false_eq_true, and_self, imp_false, not_or, forall_const,
      true_and, hu't, and_true]
    have hobj := And.intro (hF (ht hu't)) (hF (ht hut))
    simp only [_op_t, ← promote_finset_toFinset_eq, toFinset_eq, mem_sdiff, mem_singleton] at hobj
    grind
  · exact _respects hdv hdw hBv hBw hNv hNw hF hFf hFresp
  · exact eval_ok_not_A4 hG hdû hA4û hvw hxy hvnew hv hw hBv hdv hBw hdw hNv hNw hNvw hFcard hℓxy hℓ

lemma ok_of_one_sixth_lt_ℓxy {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} (hG : G.support.toFinset ⊆ ABC.toFinset)
    {û v x y : Fin n} (hBv : ABC.B v) (hdv : G.degree v = 3)
    (hdx : 3 ≤ G.degree x) (hdy : 3 ≤ G.degree y) (hNv : G.neighborFinset v = {û, x, y})
    (hℓxy : 1 / 6 < ℓ G ABC x + ℓ G ABC y)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  rcases Nat.eq_or_lt_of_le hdx with hdx | hdx
  · have hℓy : 1 / 15 < ℓ G ABC y := by
      suffices ℓ G ABC x ≤ 1 / 10 by linarith
      exact ℓ_le_1_over_10_of_3_le_degree (le_of_eq hdx)
    have hdy : G.degree y = 3 := by
      suffices ¬4 ≤ G.degree y by linarith
      exact ℓ_le_1_over_15_of_4_le_degree.mt <| not_le.mpr hℓy
    have hy : ABC.A y := by
      have hy : y ∈ ABC :=
        ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr
          <| (G.degree_pos_iff_mem_support _).mp <| by linarith
      by_contra
      simp only [mem_iff, this, false_or] at hy
      rcases hy with hy | hy
      · rw [ℓB3 hy hdy] at hℓy
        linarith
      · rw [ℓC3 hy hdy] at hℓy
        linarith
    rw [ℓA3 hy hdy] at hℓxy
    have hx : ABC.A x := by
      have hx : x ∈ ABC :=
        ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr
          <| (G.degree_pos_iff_mem_support _).mp <| by linarith
      by_contra
      simp only [mem_iff, this, false_or] at hx
      rcases hx with hx | hx
      · rw [ℓB3 hx hdx.symm] at hℓxy
        linarith
      · rw [ℓC3 hx hdx.symm] at hℓxy
        linarith
    have hv : v ∈ ABC := by simp only [mem_iff, hBv, not_A_of_B, not_C_of_B, or_false, or_true]
    refine Claim1 hv hG ih ?_
    calc f G ABC v
      _ = 1 / 3 := by rw [fB3 hBv hdv]
      _ = 1 / 6 + 1 / 6 := by linarith
      _ = γ G ABC x + γ G ABC y := by rw [γA3 hx hdx.symm, γA3 hy hdy]
      _ = ∑ u ∈ {x, y}, γ G ABC u := by grind [degree]
    refine sum_le_sum_of_subset_of_nonneg (by grind) fun _ _ _ ↦ γ_nonneg
  · suffices (1 : ℝ) / 6 < 1 / 6 by linarith
    calc (1 : ℝ) / 6
      _ < ℓ G ABC x + ℓ G ABC y := hℓxy
      _ ≤ 1 / 15 + 1 / 10 :=
        add_le_add (ℓ_le_1_over_15_of_4_le_degree hdx) (ℓ_le_1_over_10_of_3_le_degree hdy)
      _ = 1 / 6 := by linarith

lemma Claim19 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) {û v w : Fin n} (hû : IsVstar G ABC û)
    (hBv : ABC.B v) (hdv : G.degree v = 3) (hBw : ABC.B w) (hdw : G.degree w = 3)
    (hvnew : v ≠ w) (hv : G.Adj û v) (hw : G.Adj û w)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  match Claim15 hG hû ih with
  | Or.inl h => exact h
  | Or.inr hdû => ?_
  if hvw : G.Adj v w then
    exact Claim19_vw hG hBv hdv hBw hdw hû hvnew hv hw hvw ih
  else
    obtain ⟨v, w, x, y, s, t, hBv, hBw, hdv, hdw, hvw, hvnew, hv, hw, hNv, hNw, hfyx, hfts, hℓ⟩ :=
      neighbors_not_vw hvw hvnew hv hw hdv hdw hBv hBw
    if hxyst_deg_gt_2 : ∃ u ∈ ({x, y, s, t} : Finset _), G.degree u ≤ 2 then
      obtain ⟨u, hu, hdu⟩ := hxyst_deg_gt_2
      have huABC : u ∈ ABC := by
        refine ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ?_
        suffices u ∈ G.neighborFinset v ∪ G.neighborFinset w by
          simp only [mem_union, mem_neighborFinset] at this
          grind [Adj.symm]
        grind
      rcases Nat.eq_or_lt_of_le hdu with hdu | hdu
      · rcases huABC with hA | hBC
        · if hu : u ∈ ({x, y} : Finset _) then
            exact Claim7 hG ih ⟨v, u, hdv, hBv, hdu, hA, G.mem_neighborFinset .. |>.mp (by grind)⟩
          else
            exact Claim7 hG ih ⟨w, u, hdw, hBw, hdu, hA, G.mem_neighborFinset .. |>.mp (by grind)⟩
        · exact Claim6 hG ih ⟨u, hdu, by grind [not_A_of_B, not_A_of_C]⟩
      · exact Claim5 hG ih ⟨u, huABC, Nat.le_of_lt_succ hdu⟩
    else if hNvw : ({x, y} : Finset _) ∩ {s, t} ≠ ∅ then
      obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.mpr hNvw
      have hûneu : û ≠ u := by grind [degree]
      exact Claim12 hG hvnew hBv hdv hBw hdw hûneu (by grind) ih
    else
    simp only [not_exists, not_and, not_le] at hxyst_deg_gt_2
    have hxyst_3_le_deg : ∀ u ∈ ({x, y, s, t} : Finset _), 3 ≤ G.degree u :=
      fun _ hu ↦ hxyst_deg_gt_2 _ hu
    if hℓxy : 1 / 6 < ℓ G ABC x + ℓ G ABC y then
      refine ok_of_one_sixth_lt_ℓxy hG hBv hdv ?_ ?_ hNv hℓxy ih <;> grind
    else if hA4û : ABC.A û ∧ G.degree û = 4 then
      sorry
    else
      simp only [not_lt] at hℓxy
      simp only [ne_eq, Decidable.not_not] at hNvw
      refine _ok_not_A4 hG hA4û hdû hvw hBv hdv hBw hdw hNv hNw ?_ hvnew hv hw ?_ ?_ hNvw hℓxy hℓ ih
      <;> grind [degree]

end Tripartition
end ABC
end CaroWeiType
