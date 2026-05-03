import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim18

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

private lemma neighbors_vw {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w : Fin n}
    (hBv : ABC.B v) (hdv : G.degree v = 3) (hBw : ABC.B w) (hdw : G.degree w = 3)
    (hvnew : v ≠ w) (hv : G.Adj û v) (hw : G.Adj û w) (hvw : G.Adj v w)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨
      ∃ x y, G.neighborFinset v = {û, w, x} ∧ G.neighborFinset w = {û, v, y} ∧ x ≠ y:= by
  obtain ⟨x, hNv⟩ := neighborFinset_of_adj_of_adj_of_ne hdv hw.ne hv.symm hvw
  obtain ⟨y, hNw⟩ := neighborFinset_of_adj_of_adj_of_ne hdw hv.ne hw.symm hvw.symm
  if heq : x = y then
    have hne : û ≠ x := by grind [degree]
    exact Or.inl <| Claim12 hG hvw.ne hBv hdv hBw hdw hne (by simp [hNv, hNw, heq]) ih
  else
    exact Or.inr ⟨x, y, hNv, hNw, heq⟩

private lemma Claim19_vw {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w : Fin n}
    (hBv : ABC.B v) (hdv : G.degree v = 3) (hBw : ABC.B w) (hdw : G.degree w = 3)
    (hû : IsVstar G ABC û) (hvnew : v ≠ w) (hv : G.Adj û v) (hw : G.Adj û w) (hvw : G.Adj v w)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  match neighbors_vw hG hBv hdv hBw hdw hvnew hv hw hvw ih with
  | Or.inl h => exact h
  | Or.inr h => ?_
  obtain ⟨x, y, hNv, hNw, hxy⟩ := h
  if hdle1 : ∃ u ∈ ABC, G.degree u ≤ 1 then
    exact Claim5 hG ih hdle1
  else if hA4û : ABC.A û ∧ G.degree û = 4 then
    exact Claim18 hG hû hA4û.1 hA4û.2 hBv hdv hBw hdw hv hw hvw ih
  else
    match Claim15 hG hû ih with
    | Or.inl h => exact h
    | Or.inr hdû => ?_
    have hfû : f G ABC û ≤ 1 / 3 := f_le_1_over_3_of_4_le_deg_of_notA4 hdû hA4û
    have hxv : G.Adj x v := Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNv]
    have hyw : G.Adj y w := Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]
    have hxABC := ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨_, hxv⟩
    have hyABC := ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨_, hyw⟩
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

private lemma neighbors_not_vw {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
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

private lemma A3_or_1_over_15 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {x : Fin n} (hdx : 3 ≤ G.degree x) :
    (ABC.A x ∧ G.degree x = 3) ∨ ℓ G ABC x ≤ 1 / 15 := by
  have hγ : γ G ABC x ≤ 1 / 6 := γ_le_1_over_6_of_3_le_degree hdx
  have hx : x ∈ ABC :=
    ABC.mem_toFinset.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp (Nat.zero_lt_of_lt hdx)
  match lt_or_eq_of_le hdx with
  | Or.inl h => exact Or.inr <| ℓ_le_1_over_15_of_4_le_degree h
  | Or.inr h => ?_
  rcases hx with hx | hx | hx
  · simp only [hx, h, true_and, true_or]
  · simp only [ℓB3 hx h.symm, le_refl, or_true]
  · simp only [ℓC3 hx h.symm]
    grind

private lemma _losses {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {v x y : Fin n} (hBv : ABC.B v) (hdv : G.degree v = 3)
    (hxy : x ≠ y) (hdx : 3 ≤ G.degree x) (hdy : 3 ≤ G.degree y)
    (hx : x ∈ G.neighborFinset v) (hy : y ∈ G.neighborFinset v)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨ ℓ G ABC x + ℓ G ABC y ≤ 1 / 6 := by
  match A3_or_1_over_15 hG hdx, A3_or_1_over_15 hG hdy with
  | _, Or.inr h =>
      suffices ℓ G ABC x ≤ 1 / 10 by exact Or.inr <| by linarith
      exact ℓ_le_1_over_10_of_3_le_degree hdx
  | Or.inr h, _ =>
      suffices ℓ G ABC y ≤ 1 / 10 by exact Or.inr <| by linarith
      exact ℓ_le_1_over_10_of_3_le_degree hdy
  | Or.inl h, Or.inl h' => ?_
  have hv : v ∈ ABC :=
    ABC.mem_toFinset.mpr <| hG <| (G.degree_pos_iff_mem_support _).mp <| by linarith
  refine Or.inl <| Claim1 hv hG ih ?_
  calc f G ABC v
    _ = 1 / 3 := by rw [fB3 hBv hdv]
    _ = γ G ABC x + γ G ABC y := by
      linarith [γA3 h.1 h.2, γA3 h'.1 h'.2]
    _ = ∑ u ∈ {x, y}, γ G ABC u := by grind
  refine sum_le_sum_of_subset_of_nonneg (by grind) fun _ _ _ ↦ γ_nonneg

private abbrev _op_g {n : ℕ} (G : SimpleGraph (Fin n)) (û x y s t : Fin n) :
    SimpleGraph (Fin n) :=
  (fromEdgeSet <| G.edgeSet ∪ {s(x, y), s(s, t)}).deleteIncidencesOf {û}

section _op

variable {n : ℕ} {G : SimpleGraph (Fin n)} {û x y s t : Fin n}

private lemma _op_g_eq_xy {u u' : Fin n} :
    (_op_g G û x y s t).Adj u u' ↔ (_op_g G û y x s t).Adj u u' := by
  simp only [_op_g, Sym2.eq_swap]

private lemma _op_g_adj_of_G_adj {u u' : Fin n} (hu : u ≠ û) (hu' : u' ≠ û) (huu' : G.Adj u u') :
    (_op_g G û x y s t).Adj u u' := by
  have huû : u ∉ ({û} : Finset _) := not_iff_not.mpr mem_singleton |>.mpr hu
  have hu'û : u' ∉ ({û} : Finset _) := not_iff_not.mpr mem_singleton |>.mpr hu'
  refine deleteIncidencesOf_adj_iff_of_notMem huû hu'û |>.mp ?_
  refine (fromEdgeSet_adj _).mpr ?_
  exact ⟨Set.mem_union_left _ huu', huu'.ne⟩

variable {v w : Fin n}

private lemma adj_vx [Fintype (G.neighborSet v)] (hdv : G.degree v = 3)
    (hNv : G.neighborFinset v = {û, x, y}) :
    (_op_g G û x y s t).Adj v x := by
  have hvû : v ≠ û := Adj.ne <| G.mem_neighborFinset .. |>.mp <| by simp [hNv]
  have hxû : x ≠ û := by grind [degree]
  exact _op_g_adj_of_G_adj hvû hxû <| G.mem_neighborFinset .. |>.mp <| by simp [hNv]

private lemma adj_vy [Fintype (G.neighborSet v)] (hdv : G.degree v = 3)
    (hNv : G.neighborFinset v = {û, x, y}) :
    (_op_g G û x y s t).Adj v y := by
  have hvû : v ≠ û := Adj.ne <| G.mem_neighborFinset .. |>.mp <| by simp [hNv]
  have hyû : y ≠ û := by grind [degree]
  exact _op_g_adj_of_G_adj hvû hyû <| G.mem_neighborFinset .. |>.mp <| by simp [hNv]

private lemma adj_xy [Fintype (G.neighborSet v)] (hdv : G.degree v = 3)
    (hNv : G.neighborFinset v = {û, x, y}) :
    (_op_g G û x y s t).Adj x y := by
  have hxû : x ∉ ({û} : Finset _) := by grind [degree]
  have hyû : y ∉ ({û} : Finset _) := by grind [degree]
  refine deleteIncidencesOf_adj_iff_of_notMem hxû hyû |>.mp ?_
  exact (fromEdgeSet_adj _).mpr ⟨Set.mem_union_right _ (Set.mem_insert ..), by grind [degree]⟩

private lemma adj_ws [Fintype (G.neighborSet w)] (hdw : G.degree w = 3)
    (hNw : G.neighborFinset w = {û, s, t}) :
    (_op_g G û x y s t).Adj w s := by
  have hwû : w ≠ û := Adj.ne <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]
  have hsû : s ≠ û := by grind [degree]
  exact _op_g_adj_of_G_adj hwû hsû <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]

private lemma adj_wt [Fintype (G.neighborSet w)] (hdw : G.degree w = 3)
    (hNw : G.neighborFinset w = {û, s, t}) :
    (_op_g G û x y s t).Adj w t := by
  have hwû : w ≠ û := Adj.ne <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]
  have htû : t ≠ û := by grind [degree]
  exact _op_g_adj_of_G_adj hwû htû <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]

private lemma adj_st [Fintype (G.neighborSet w)] (hdw : G.degree w = 3)
    (hNw : G.neighborFinset w = {û, s, t}) :
    (_op_g G û x y s t).Adj s t := by
  have hsû : s ∉ ({û} : Finset _) := by grind [degree]
  have htû : t ∉ ({û} : Finset _) := by grind [degree]
  refine deleteIncidencesOf_adj_iff_of_notMem hsû htû |>.mp ?_
  refine (fromEdgeSet_adj _).mpr ⟨Set.mem_union_right _ ?_, by grind [degree]⟩
  exact Set.mem_insert_of_mem _ rfl

end _op

private lemma neighborFinset_subset {n : ℕ} (G : SimpleGraph (Fin n)) [G.LocallyFinite]
    {F : Finset (Fin n)} {û u x y s t : Fin n}
    (hû : û ∉ F) (huneû : u ≠ û) :
    G.neighborFinset u ∩ F ⊆ (_op_g G û x y s t).neighborFinset u ∩ F := by
  intro u'
  simp only [mem_inter]
  intro ⟨hu', hu'F⟩
  simp only [mem_neighborFinset] at hu'
  refine ⟨?_, hu'F⟩
  have huû : u ∉ ({û} : Finset _) := notMem_singleton.mpr huneû
  have hu'û : u' ∉ ({û} : Finset _) := notMem_singleton.mpr <| ne_of_mem_of_not_mem hu'F hû
  refine mem_neighborFinset .. |>.mpr ?_
  refine deleteIncidencesOf_adj_iff_of_notMem huû hu'û |>.mp ?_
  exact fromEdgeSet_adj _ |>.mpr ⟨Set.mem_union_left _ (G.mem_edgeSet.mpr hu'), hu'.ne⟩

@[reducible]
private def _op_t {n : ℕ} (ABC : Tripartition n) (û v w : Fin n) : Tripartition n := by
  exact ABC \ {û} |>.promote_finset {v, w}

private lemma _hGop {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w x y s t : Fin n}
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t}) :
    (_op_g G û x y s t).support ⊆ (_op_t ABC û v w).toFinset := by
  intro u hu
  simp only [_op_t, ← promote_finset_toFinset_eq, mem_coe, sdiff_toFinset, mem_sdiff, mem_singleton]
  simp only [_op_g] at hu
  refine ⟨hG ?_, ?_⟩
  · obtain ⟨u', hu'⟩ := mem_support _ |>.mp
      <| (Set.mem_diff _ |>.mp <| deleteIncidencesOf_support_subset hu).1
    rcases adj_fromEdgeSet_union_iff.mp hu' with hu' | hu'
    · exact G.mem_support.mpr ⟨u', hu'⟩
    · simp only [Set.mem_insert_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
      Set.mem_singleton_iff, ne_eq] at hu'
      have hu : (u = x ∨ u = y) ∨ (u = s ∨ u = t) := by grind only
      rcases hu with hu | hu
      · refine G.mem_support.mpr ⟨v, Adj.symm <| G.mem_neighborFinset .. |>.mp <| hNv ▸ ?_⟩
        grind only [= mem_insert, = mem_singleton]
      · refine G.mem_support.mpr ⟨w, Adj.symm <| G.mem_neighborFinset .. |>.mp <| hNw ▸ ?_⟩
        grind only [= mem_insert, = mem_singleton]
  · intro heq
    have := (Set.mem_diff _ |>.mp <| deleteIncidencesOf_support_subset hu).2
    simp only [coe_singleton, Set.mem_singleton_iff] at this
    contradiction

private lemma _respects {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] {û v w x y s t : Fin n} {F : Finset (Fin n)}
    (hdv : G.degree v = 3) (hdw : G.degree w = 3) (hBv : ABC.B v) (hBw : ABC.B w)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t})
    (hF : F ⊆ (ABC._op_t û v w).toFinset)
    (hFf : (_op_g G û x y s t).InducesForest F)
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
    exact neighborFinset_subset G hûF fun heq ↦ hûF (heq ▸ huF)
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
      · if hx : x ∈ F then
          refine (card_singleton x) ▸ card_le_card (by grind)
        else
          refine (card_singleton y) ▸ card_le_card (by grind)
      · if hx : s ∈ F then
          refine (card_singleton s) ▸ card_le_card (by grind)
        else
          refine (card_singleton t) ▸ card_le_card (by grind)
    else
      refine le_trans (card_le_card ?_) (hFresp u huF |>.2.1 <| Or.inl ⟨⟨hBu, huû⟩, hu⟩)
      exact neighborFinset_subset G hûF fun heq ↦ hûF (heq ▸ huF)
  · intro hCu
    have hu : u ∉ ({v, w} : Finset _) := by
      grind only [= mem_insert, = Sym2.eq, not_C_of_B, = mem_singleton]
    refine le_antisymm ?_ (Nat.zero_le _)
    refine le_of_le_of_eq (card_le_card ?_) (hFresp u huF |>.2.2 <| ⟨⟨hCu, huû⟩, hu⟩)
    exact neighborFinset_subset G hûF fun heq ↦ hûF (heq ▸ huF)

private lemma f_le_op {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] {û v w x y s t u : Fin n}
    (hu : u ∈ ABC.toFinset \ ({û, v, w, x, y, s, t} : Finset _)) :
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
  rcases ABC.mem_toFinset.mpr hu.1 with hA | hB | hC
  · have hA' : (_op_t ABC û v w).A u := Or.inl ⟨hA, by grind⟩
    simp only [f, hA, hA', ↓reduceDIte]
    exact fA_decreasing (card_le_card hNu)
  · have hB' : (_op_t ABC û v w).B u := Or.inl ⟨⟨hB, by grind⟩, by grind⟩
    simp only [f, hB, hB', not_A_of_B, ↓reduceDIte]
    exact fB_decreasing (card_le_card hNu)
  · have hC' : (_op_t ABC û v w).C u := ⟨⟨hC, by grind⟩, by grind⟩
    simp only [f, hC, hC', not_A_of_C, not_B_of_C, ↓reduceDIte]
    exact fC_decreasing (card_le_card hNu)

private lemma hin_toFinset {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {û v w x y s t : Fin n} {ABC : Tripartition n} [ABC.Decidable]
    (hG : G.support ⊆ ABC.toFinset) (hv : G.Adj û v) (hw : G.Adj û w)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t}) :
    {û, v, w, x, y, s, t} ⊆ ABC.toFinset := by
  have : {û, x, y} ⊆ ABC.toFinset := by
    intro u hu
    refine hG <| G.mem_support.mpr ⟨v, ?_⟩
    refine Adj.symm <| G.mem_neighborFinset .. |>.mp (by grind)
  have : {û, s, t} ⊆ ABC.toFinset := by
    intro u hu
    refine hG <| G.mem_support.mpr ⟨w, ?_⟩
    refine Adj.symm <| G.mem_neighborFinset .. |>.mp (by grind)
  suffices {v, w} ⊆ ABC.toFinset by
    grind
  exact fun _ _ ↦ hG <| G.mem_support.mpr (by grind [Adj.symm])

private lemma A2_vw {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    {u û v w x y s t : Fin n} (hu : u ∈ ({v, w} : Finset _))
    (hBv : ABC.B v) (hBw : ABC.B w) (hdv : G.degree v = 3) (hdw : G.degree w = 3)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t})
    (hNxy : ({v, w} : Finset _) ∩ {x, y, s, t} = ∅) :
    (_op_t ABC û v w).A u ∧ (_op_g G û x y s t).degree u = 2 := by
  have hûu : û ∉ (_op_g G û x y s t).neighborFinset u := by
    refine not_iff_not.mpr (mem_neighborFinset ..) |>.mpr <| not_adj_symm ?_
    exact deleteIncidencesOf_notadj (mem_singleton_self _)
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
          exact congrArg _ <| eq_sdiff_of_empty_inter <| singleton_inter_of_notMem hûu
      rw [card_sdiff, card_eq_zero.mpr <| singleton_inter_of_notMem hûu]
      exact Nat.sub_zero _
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

private lemma u_notin_singleton_û {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {u û v w x y s t : Fin n} (hdv : G.degree v = 3) (hdw : G.degree w = 3)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t})
    (hu : u ∈ ({x, y, s, t} : Finset _)) : u ∉ ({û} : Finset _) := by
  grind [degree]

private lemma _op_degree_le' {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {û x y s t v : Fin n} (hdv : G.degree v = 3) (hNv : G.neighborFinset v = {û, x, y})
    (hNvw : ({x, y} : Finset _) ∩ {s, t} = ∅) :
    (_op_g G û x y s t).degree x ≤ G.degree x + 1 := by
  have hxy : x ≠ y := by
    rw [degree] at hdv
    exact pairwise_ne_of_triplet (hNv ▸ hdv) |>.2.2
  rw [← card_singleton y, degree, degree]
  refine le_trans (card_le_card ?_) (card_union_le ..)
  intro u hu
  have := mem_neighborFinset_of_deleteIncidencesOf_mem_neighborFinset hu
  rcases mem_fromEdgeSet_union_neighborFinset_iff.mp this with hu | hu
  · exact mem_union_left _ hu
  · simp only [Set.mem_insert_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and,
      Prod.swap_prod_mk, Set.mem_singleton_iff, ne_eq] at hu
    refine mem_union_right _ ?_
    refine mem_singleton.mpr ?_
    by_contra
    have H := notMem_of_mem_of_empty_inter (mem_insert_self ..) hNvw
    simp only [mem_insert, mem_singleton, not_or] at H
    simp only [this, false_or, hxy, false_and, H] at hu

private lemma _op_degree_le {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {u û x y s t v : Fin n} (hdv : G.degree v = 3) (hNv : G.neighborFinset v = {û, x, y})
    (hu : u ∈ ({x, y} : Finset _)) (hNvw : ({x, y} : Finset _) ∩ {s, t} = ∅) :
    (_op_g G û x y s t).degree u ≤ G.degree u + 1 := by
  simp only [mem_insert, mem_singleton] at hu
  rcases hu with hu | hu
  · subst hu
    exact _op_degree_le' hdv hNv hNvw
  · subst hu
    have bla := @_op_g_eq_xy _ G û x u s t
    rename_i inst
    refine le_of_eq_of_le ?_ (_op_degree_le' hdv (hNv ▸ (triplet_eq ..)) ((pair_comm x _) ▸ hNvw))
    refine congrArg Finset.card ?_
    ext
    simp only [mem_neighborFinset, _op_g_eq_xy]

private lemma Δf_le_ℓ {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {u û v w x y s t : Fin n}
    (hdv : G.degree v = 3) (hdw : G.degree w = 3)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t})
    (hu : u ∈ ({x, y, s, t} : Finset _))
    (hNvw : ({x, y} : Finset _) ∩ {s, t} = ∅)
    (Hcap : ({v, w} : Finset _) ∩ {x, y, s, t} = ∅) :
    f G ABC u - f (_op_g G û x y s t) (ABC._op_t û v w) u ≤ ℓ G ABC u := by
  have hu' : u ∉ ({v, w} : Finset _) := notMem_of_empty_inter_of_mem Hcap hu
  have hu : u ∈ ({x, y} : Finset _) ∨ u ∈ ({s, t} : Finset _) := by grind
  have hu'' : u ∉ ({û} : Finset _) := by grind [degree]
  refine Δf_le_ℓ_of_Δdeg_le_1 ?_ ?_
  · simp only [_op_g]
    refine le_trans deleteIncidencesOf_degree_le ?_
    refine le_trans fromEdgeSet_union_degree_le' ?_
    simp only [add_le_add_iff_left]
    rcases hu with hu | hu
    · have : fromEdgeSet {s(x, y), s(s, t)} = fromEdgeSet (insert s(s, t) {s(x, y)}) := by
        refine congrArg _ ?_
        grind
      rw [degree_eq_of_eq this]
      have : (fromEdgeSet {s(x, y)}).degree u ≤ 1 := fromEdgeSet_singleton_degree_le_1
      refine le_of_eq_of_le ?_ this
      have : u ∉ ({s, t} : Finset _) := notMem_of_empty_inter_of_mem' hNvw hu
      simp only [mem_insert, mem_singleton, not_or] at this
      refine @fromEdgeSet_insert_degree_eq _ _ _ _ {s(x, y)} ?_ _ this.1 this.2
    · have : (fromEdgeSet {s(s, t)}).degree u ≤ 1 := fromEdgeSet_singleton_degree_le_1
      refine le_of_eq_of_le ?_ this
      have : u ∉ ({x, y} : Finset _) := notMem_of_empty_inter_of_mem hNvw hu
      simp only [mem_insert, mem_singleton, not_or] at this
      refine @fromEdgeSet_insert_degree_eq _ _ _ _ {s(s, t)} ?_ _ this.1 this.2
  · simp only [_op_t, promote_finset, hu', and_false, or_false, not_false_eq_true, sdiff, hu'',
      and_true, and_self, ← mem_iff]
    rcases hu with hu | hu
    · refine ABC.mem_toFinset.mpr <| mem_def.mpr <| hG <| G.mem_support.mpr ⟨v, ?_⟩
      refine Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
    · refine ABC.mem_toFinset.mpr <| mem_def.mpr <| hG <| G.mem_support.mpr ⟨w, ?_⟩
      refine Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind

private lemma eval_ok_of_hsumℓ {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] {F : Finset (Fin n)} {û v w x y s t : Fin n}
    (hG : G.support ⊆ ABC.toFinset)
    (hvw : ¬G.Adj v w) (hxy : x ≠ y) (hvnew : v ≠ w) (hv : G.Adj û v) (hw : G.Adj û w)
    (hBv : ABC.B v) (hdv : G.degree v = 3) (hBw : ABC.B w) (hdw : G.degree w = 3)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t})
    (hNvw : ({x, y} : Finset _) ∩ {s, t} = ∅)
    (hFcard : eval (_op_g G û x y s t) (ABC._op_t û v w) ≤ #F)
    (hsumℓ : ℓ G ABC x + ℓ G ABC y + ℓ G ABC s + ℓ G ABC t ≤ 2 / 3 - f G ABC û) :
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
      have : {û, v, w, x, y, s, t} ⊆ ABC.toFinset := hin_toFinset hG hv hw hNv hNw
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
  suffices ∑ u ∈ {x, y, s, t}, (f G ABC u - f (_op_g G û x y s t) (ABC._op_t û v w) u)
      ≤ 2 / 3 - f G ABC û by
    linarith
  suffices ∑ u ∈ {x, y, s, t}, ℓ G ABC u ≤ 2 / 3 - f G ABC û by
    refine le_trans ?_ this
    refine sum_le_sum ?_
    intro u hu
    exact Δf_le_ℓ hG hdv hdw hNv hNw hu hNvw Hcap
  refine le_of_eq_of_le ?_ hsumℓ
  clear hFcard hsumℓ hdv' hdw' hA'v hA'w
  calc ∑ u ∈ {x, y, s, t}, ℓ G ABC u
    _ = ∑ u ∈ {x, y}, ℓ G ABC u + ∑ u ∈ {s, t}, ℓ G ABC u := by grind
  grind [degree]

lemma ok_of_hsumℓ {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w x y s t : Fin n}
    (hvw : ¬G.Adj v w) (hBv : ABC.B v) (hdv : G.degree v = 3) (hBw : ABC.B w) (hdw : G.degree w = 3)
    (hNv : G.neighborFinset v = {û, x, y})
    (hNw : G.neighborFinset w = {û, s, t})
    (hxy : x ≠ y) (hvnew : v ≠ w) (hv : G.Adj û v) (hw : G.Adj û w)
    (hNvw : ({x, y} : Finset _) ∩ {s, t} = ∅)
    (hsumℓ : ℓ G ABC x + ℓ G ABC y + ℓ G ABC s + ℓ G ABC t ≤ 2 / 3 - f G ABC û)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n) [ABC'.Decidable],
      G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  obtain ⟨F, hF, hFf, hFresp, hFcard⟩ := by
    refine ih (_op_g G û x y s t) (_op_t ABC û v w) (_hGop hG hNv hNw) ?_
    simp only [_op_t, ← card_promote_finset_eq_card]
    refine ABC.sdiff_card <| nonempty_iff_ne_empty.mp ⟨û, ?_⟩
    simp only [mem_inter, mem_singleton, true_and]
    refine hG <| G.mem_support.mpr ⟨v, ?_⟩
    refine Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNv]
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
  · exact eval_ok_of_hsumℓ hG hvw hxy hvnew hv hw hBv hdv hBw hdw hNv hNw hNvw hFcard hsumℓ

lemma ok_of_one_sixth_lt_ℓxy {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {û v x y : Fin n} (hBv : ABC.B v) (hdv : G.degree v = 3)
    (hdx : 3 ≤ G.degree x) (hdy : 3 ≤ G.degree y) (hNv : G.neighborFinset v = {û, x, y})
    (hℓxy : 1 / 6 < ℓ G ABC x + ℓ G ABC y)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n) [ABC'.Decidable],
      G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
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
        ABC.mem_toFinset.mpr <| hG <| (G.degree_pos_iff_mem_support _).mp <| by linarith
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
        ABC.mem_toFinset.mpr <| hG <| (G.degree_pos_iff_mem_support _).mp <| by linarith
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

lemma A3x_of_2_over_15_lt_ℓx_plus_ℓy {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {x y : Fin n} {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    (hdx : 3 ≤ G.degree x) (hdy : 3 ≤ G.degree y)
    (hfyx : f G ABC y ≤ f G ABC x)
    (hℓxy : 2 / 15 < ℓ G ABC x + ℓ G ABC y) :
    ABC.A x ∧ G.degree x = 3 := by
  by_contra
  have hℓx := ℓ_le_1_over_15_of_3_le_degree_of_notA3 hdx this
  have hℓy : 1 / 15 < ℓ G ABC y := by linarith
  have hA3y := ℓ_le_1_over_15_of_3_le_degree_of_notA3 hdy |>.mt <| not_le.mpr hℓy
  simp only [not_and, Classical.not_imp, not_not] at hA3y
  obtain ⟨hAy, hdy⟩ := hA3y
  rw [fA3 hAy hdy] at hfyx
  have : ¬4 ≤ G.degree x := by
    have hfx : ¬f G ABC x ≤ 2 / 5 := by linarith
    refine f_le_2_over_5_of_4_le_deg.mt hfx
  have hdx : G.degree x = 3 := by linarith
  have hxABC : x ∈ ABC :=
    ABC.mem_toFinset.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith
  have hBC : ABC.B x ∨ ABC.C x := by grind [ABC.mem_iff]
  rcases hBC with hB | hC
  · linarith [fB3 hB hdx]
  · linarith [fC3 hC hdx]

lemma ok_of_A4_step1 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v y q r : Fin n}
    (hû : IsVstar G ABC û) (hBv : ABC.B v) (hdv : G.degree v = 3)
    (hBy : ABC.B y) (hdy : G.degree y = 3) (hAû : ABC.A û) (hdû : G.degree û = 4)
    (hNy : G.neighborFinset y = {v, q, r}) (hdNy : ∀ w ∈ G.neighborFinset y, 3 ≤ G.degree w)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n) [ABC'.Decidable],
      G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨ ¬∃ q' ∈ ({q, r} : Finset _), γ G ABC q' < 1 / 10 := by
  if hγNy : ¬∃ q' ∈ ({q, r} : Finset _), γ G ABC q' < 1 / 10 then
    exact Or.inr hγNy
  else
    simp only [not_not] at hγNy
    obtain ⟨q', hq', hγq'⟩ := hγNy
    have hq'ABC : q' ∈ ABC := by
      refine ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨y, ?_⟩
      exact Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
    have hγ0 : γ G ABC q' = 0 :=
      Decidable.not_not.mp <| γ_vstar_le_γ hû hq'ABC |>.mt <| by linarith [γA4 hAû hdû]
    have _ := by
      refine γ_eq_0_iff ?_ ?_ |>.mp hγ0
      · exact ABC.mem_toFinset.mpr <| hG
          <| G.mem_support.mpr ⟨y, Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind⟩
      · exact le_trans NeZero.one_le (hdNy q' (by grind))
    obtain ⟨hBCq', hdq'⟩ : (ABC.B q' ∨ ABC.C q') ∧ G.degree q' = 3 := by grind
    rcases hBCq' with hBq' | hCq'
    · refine Or.inl <|
        Claim10 hG hBy hdy ih ⟨v, q', by grind [degree], ?_, ?_, hBv, hBq', hdv, hdq'⟩
        <;> refine G.mem_neighborFinset .. |>.mp <| by grind
    · exact Or.inl <| Corollary9 hG hBy hdy ih ⟨q', G.mem_neighborFinset .. |>.mp (by grind), hCq'⟩

lemma ok_of_A4_step2 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {v y q r : Fin n}
    (hNy : G.neighborFinset y = {v, q, r}) (hdNy : ∀ w ∈ G.neighborFinset y, 3 ≤ G.degree w)
    (hγNy : ∀ x ∈ ({q, r} : Finset _), 1 / 10 ≤ γ G ABC x) :
    Objective G ABC
      ∨ ∀ q' ∈ ({q, r} : Finset _), (ABC.A q' ∧ (G.degree q' = 3 ∨ G.degree q' = 4)) := by
  if h : ∀ q' ∈ ({q, r} : Finset _), (ABC.A q' ∧ (G.degree q' = 3 ∨ G.degree q' = 4)) then
    exact Or.inr h
  else
    simp only [not_forall, not_and'] at h
    obtain ⟨q', hq', Hq'⟩ := h
    if hAq' : ABC.A q' then
      simp only [hAq', not_true_eq_false, false_or, not_or] at Hq'
      have := hdNy q' (hNy ▸ mem_insert_of_mem hq')
      have H : 1 / 10 ≤ γ G ABC q' := by grind
      simp only [γ, hAq', ↓reduceDIte] at H
      have hdq' : 5 ≤ G.degree q' := by grind
      have := H.trans <| γA_decreasing_of_three_le_degree hdq' (by linarith)
      grind
    else
      have hq'ABC : q' ∈ ABC := ABC.mem_toFinset.mpr <| hG
          <| G.mem_support.mpr ⟨y, Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind⟩
      have hdq' := (hdNy q' (hNy ▸ mem_insert_of_mem hq'))
      have := γ_le_γB_of_three_le_deg_of_notA hdq' hAq'
      have H : 1 / 10 ≤ γ G ABC q' := by grind
      have := le_trans H this
      rcases Nat.eq_or_lt_of_le hdq' with hdq' | hdq'
      · rw [← hdq'] at this
        grind
      · have := γB_decreasing_of_four_le_degree hdq' (le_refl _)
        grind

private lemma _respects_of_A4 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] {v y q r : Fin n} (hBy : ABC.B y) (hdy : G.degree y = 3)
    (hNy : G.neighborFinset y = {v, q, r}) {s : Finset (Fin n)}
    (hs : s ⊆ ((ABC \ {v}).promote y).toFinset)
    (hsf : ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v}).InducesForest s)
    (hsresp : respects s ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v})
      ((ABC \ {v}).promote y)) :
    respects s G ABC := by
  intro u hu
  have huv : u ∉ ({v} : Finset _) := by
    have := hs hu
    simp only [← promote_toFinset_eq, toFinset_eq, mem_sdiff] at this
    exact this.2
  have hvs : v ∉ s := by
    intro hvs
    have := hs hvs
    simp only [← promote_toFinset_eq, toFinset_eq, mem_sdiff, inter_self, ne_eq, singleton_ne_empty,
      not_false_eq_true, mem_of_singleton_inter_ne_emty, not_true_eq_false, and_false] at this
  have hvs' : {v} ∩ s = ∅ := singleton_inter_of_notMem hvs
  have hdeg : G.degree_in s u
      ≤ ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v}).degree_in s u := by
    exact degree_in_deleteIncidencesOf_of_le hvs' huv le_fromEdgeSet_union
  refine ⟨?_, ?_, ?_⟩
  · intro hA
    refine le_trans hdeg (hsresp u hu |>.1 (Or.inl ⟨hA, huv⟩))
  · if huy : u = y then
      subst huy
      have : G.neighborFinset u ∩ s ⊆ G.neighborFinset u := by exact inter_subset_left
      simp only [hBy, forall_const, degree_in, hNy]
      suffices #({q, r} ∩ s) ≤ 1 by
        refine le_of_eq_of_le ?_ this
        grind only [= inter_insert]
      have : ¬{u, q, r} ⊆ s := by
        refine no_induced_K3_of_InducesForest
          ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v}) s ?_ ?_ ?_ hsf
        · refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj huv ?_ ?_
          · grind [degree]
          · suffices G.Adj u q by
              exact le_fromEdgeSet_union this
            refine G.mem_neighborFinset .. |>.mp <| by simp [hNy]
        · refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ ?_
          · grind [degree]
          · grind [degree]
          · refine le_fromEdgeSet_right <| fromEdgeSet_adj _ |>.mpr ?_
            simp only [Set.mem_singleton_iff, ne_eq, true_and]
            grind [degree]
        · refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ huv  ?_
          · grind [degree]
          · suffices G.Adj u r by
              exact Adj.symm <| le_fromEdgeSet_union this
            refine G.mem_neighborFinset .. |>.mp <| by simp [hNy]
      grind
    else
      intro hB
      exact le_trans hdeg (hsresp u hu |>.2.1 (Or.inl ⟨⟨hB, huv⟩, notMem_singleton.mpr huy⟩))
  · intro hC
    refine le_antisymm (le_of_le_of_eq hdeg <| hsresp u hu |>.2.2 ⟨⟨hC, huv⟩, ?_⟩) (zero_le _)
    refine notMem_singleton.mpr <| ne_of_ne_congr (ABC.C ·) ?_
    simp only [hC, not_C_of_B hBy, ne_eq, true_ne_false, not_false_eq_true]

private lemma _split_sum {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {û v x y q r : Fin n}
    (hdv : G.degree v = 3) (hNv : G.neighborFinset v = {û, x, y}) (hxy : ¬G.Adj x y)
    (hyû : ¬G.Adj y û) (hdy : G.degree y = 3) (hNy : G.neighborFinset y = {v, q, r})
    {f : Fin n → ℝ} :
    ∑ u ∈ {û, x, y, q, r}, f u = f û + f x + f y + f q + f r := by
  have H : Disjoint ({û, x, y} : Finset _) ({q, r} : Finset _) := by
    refine disjoint_iff_inter_eq_empty.mpr ?_
    rw [inter_comm]
    ext u
    simp only [mem_inter, notMem_empty, iff_false, not_and]
    intro hu
    simp only [mem_insert, mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩
    · refine ne_of_ne_congr (G.Adj · y) ?_
      simp only [not_adj_symm hyû, ne_eq, eq_iff_iff, iff_false, not_not]
      refine Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
    · refine ne_of_ne_congr (G.Adj · y) ?_
      simp only [hxy, ne_eq, eq_iff_iff, iff_false, not_not]
      refine Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
    · refine ne_of_mem_of_not_mem (by grind) (G.notMem_neighborFinset_self y)
  have H' : ({û, x, y} : Finset _) ∪ {q, r} = {û, x, y, q, r} := by
    grind
  rw [← H', sum_union H]
  grind [degree]

private lemma _split_sum' {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {û v x y q r : Fin n}
    (hdv : G.degree v = 3) (hNv : G.neighborFinset v = {û, x, y}) (hxy : ¬G.Adj x y)
    (hyû : ¬G.Adj y û) (hdy : G.degree y = 3) (hNy : G.neighborFinset y = {v, q, r})
    {f : Fin n → ℝ} :
    ∑ u ∈ {v, û, x, y, q, r}, f u = f v + f û + f x + f y + f q + f r := by
  have H : Disjoint ({v} : Finset _) ({û, x, y, q, r} : Finset _) := by
    refine disjoint_iff_inter_eq_empty.mpr ?_
    ext u
    simp only [mem_inter, notMem_empty, iff_false, not_and]
    intro hu
    simp only [mem_singleton] at hu
    subst hu
    suffices u ∉ ({û, x, y} : Finset _) ∧ u ∉ ({q, r} : Finset _) by
      grind
    refine ⟨?_, ?_⟩
    · exact hNv ▸ G.notMem_neighborFinset_self u
    · grind [degree]
  have H' : ({v} : Finset _) ∪ {û, x, y, q, r} = {v, û, x, y, q, r} := by
    grind
  rw [← H', sum_union H]
  simp only [sum_singleton, _split_sum hdv hNv hxy hyû hdy hNy]
  grind

private lemma _hdeg {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {u û v x y q r : Fin n} (hu : u ∈ G.neighborFinset v)
    (hxy : ¬G.Adj x y) (hyû : ¬G.Adj y û)
    (hNv : G.neighborFinset v = {û, x, y})
    (hNy : G.neighborFinset y = {v, q, r}) :
    ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v}).degree u = G.degree u - 1 := by
  have Hvy : G.neighborFinset v ∩ G.neighborFinset y = ∅ := by
    rw [hNv]
    ext u'
    simp only [mem_inter, mem_insert, mem_singleton, mem_neighborFinset, notMem_empty, iff_false,
      not_and]
    intro h
    rcases h with hu' | hu' | hu'
    · exact hu' ▸ hyû
    · exact not_adj_symm <| hu' ▸ hxy
    · exact fun h ↦ h.ne' hu'
  rw [← card_singleton v]
  suffices ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v}).neighborFinset u
      = G.neighborFinset u \ {v} by
    rw [degree, this, card_sdiff]
    simp only [card_neighborFinset_eq_degree]
    refine congrArg (G.degree u - Finset.card ·) ?_
    exact singleton_inter_of_mem <| mem_neighborFinset_symm hu
  ext u'
  constructor
  · intro hu'
    refine mem_sdiff.mpr ⟨?_, ?_⟩
    · have := mem_neighborFinset_of_deleteIncidencesOf_mem_neighborFinset hu'
      rcases mem_fromEdgeSet_union_neighborFinset_iff.mp this with hu' | hu'
      · exact hu'
      · simp only [Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
          Prod.swap_prod_mk, ne_eq] at hu'
        rcases hu'.1 with hu' | hu'
        <;> exact (notMem_of_empty_inter_of_mem Hvy (by grind)) hu |>.elim
    · exact notMem_of_mem_neighborFinset_deleteIncidencesOf hu'
  · intro hu'
    refine (mem_neighborFinset_deleteIncidencesOf_iff_of_notMem ?_ ?_).mp ?_
    · exact mem_sdiff.mp hu' |>.2
    · exact notMem_singleton.mpr <| ne_of_mem_neighborFinset hu
    · exact le_fromEdgeSet_union' <| mem_sdiff.mp hu' |>.1

lemma _eval_ok_of_A4 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ↑ABC.toFinset)
    {û v x y q r : Fin n} (hBv : ABC.B v) (hdv : G.degree v = 3) (hAû : ABC.A û)
    (hdû : G.degree û = 4) (hNv : G.neighborFinset v = {û, x, y}) (hxy : ¬G.Adj x y)
    (hyû : ¬G.Adj y û) (hAx : ABC.A x) (hdx : G.degree x = 3) (hBy : ABC.B y)
    (hdy : G.degree y = 3) (hNy : G.neighborFinset y = {v, q, r})
    (hA34q' : ∀ q' ∈ ({q, r} : Finset _), ABC.A q' ∧ (G.degree q' = 3 ∨ G.degree q' = 4))
    {s : Finset (Fin n)}
    (hscard : eval ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v})
      ((ABC \ {v}).promote y) ≤ #s) :
    eval G ABC ≤ #s := by
  refine le_trans ?_ hscard
  simp only [eval, ← promote_toFinset_eq]
  calc _
    _ = ∑ w ∈ ABC.toFinset \ {v, û, x, y, q, r}, f G ABC w
        + ∑ w ∈ {v, û, x, y, q, r}, f G ABC w := by
      refine Eq.symm <| sum_sdiff ?_
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      have hw : (w = v) ∨ (w = q ∨ w = r) ∨ (w = û ∨ w = x ∨ w = y) := by grind
      rcases hw with hw | hw | hw
      · exact mem_def.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp (hw ▸ by linarith)
      · rcases hw with hw | hw <;> {
          refine mem_def.mpr <| hG <| G.mem_support.mpr ⟨y, ?_⟩
          refine Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hw, hNy]
        }
      · rcases hw with hw | hw <;> {
          refine mem_def.mpr <| hG <| G.mem_support.mpr ⟨v, ?_⟩
          refine Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hw, hNv]
        }
    _ = ∑ w ∈ ABC.toFinset \ {v, û, x, y, q, r},
        f ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v})
          ((ABC \ {v}).promote y) w + ∑ w ∈ {v, û, x, y, q, r}, f G ABC w := by
      simp only [add_left_inj]
      refine sum_congr rfl ?_
      intro w hw
      have hNw : G.neighborFinset w
          = ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v}).neighborFinset w := by
        ext u
        if huv : u ∈ ({v} : Finset _) then
          simp only [mem_singleton] at huv
          subst huv
          simp only [deleteIncidencesOf_notAdj' (mem_singleton.mpr (rfl : u = u)),
            mem_neighborFinset, iff_false]
          refine not_iff_not.mpr (G.mem_neighborFinset ..) |>.mp <| not_mem_neighborFinset_symm ?_
          grind
        else
          have hwv : w ∉ ({v} : Finset _) := by grind
          refine Iff.trans ?_ (mem_neighborFinset_deleteIncidencesOf_iff_of_notMem huv hwv)
          refine Iff.trans ⟨Or.inl, by grind⟩ mem_fromEdgeSet_union_neighborFinset_iff.symm
      rcases ABC.mem_toFinset.mpr <| mem_sdiff.mp hw |>.1 with hA | hB | hC
      · have hA' : (ABC \ {v}).promote y |>.A w := Or.inl <| ⟨hA, by grind⟩
        simp only [f, hA, hA', ↓reduceDIte]
        exact congrArg (fA ∘ Finset.card) hNw
      · have hB' : (ABC \ {v}).promote y |>.B w := Or.inl <| ⟨⟨hB, by grind⟩, by grind⟩
        simp only [f, hB, hB', not_A_of_B, ↓reduceDIte]
        exact congrArg (fB ∘ Finset.card) hNw
      · have hC' : (ABC \ {v}).promote y |>.C w := ⟨⟨hC, by grind⟩, by grind⟩
        simp only [f, hC, hC', not_A_of_C, not_B_of_C, ↓reduceDIte]
        exact congrArg (fC ∘ Finset.card) hNw
    _ = ∑ w ∈ ABC.toFinset \ {v, û, x, y, q, r},
          f ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v}) ((ABC \ {v}).promote y) w
        + ∑ w ∈ {û, x, y, q, r},
          f ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v}) ((ABC \ {v}).promote y) w
        - ∑ w ∈ {û, x, y, q, r},
          f ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v}) ((ABC \ {v}).promote y) w
        + ∑ w ∈ {v, û, x, y, q, r}, f G ABC w := by
      simp only [add_sub_cancel_right]
    _ = ∑ w ∈ ABC.toFinset \ {v},
          f ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v}) ((ABC \ {v}).promote y) w
        - ∑ w ∈ {û, x, y, q, r},
          f ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v}) ((ABC \ {v}).promote y) w
        + ∑ w ∈ {v, û, x, y, q, r}, f G ABC w := by
      simp only [add_left_inj, sub_left_inj]
      suffices (ABC.toFinset \ {v, û, x, y, q, r}) ∪ {û, x, y, q, r} = ABC.toFinset \ {v} by
        rw [← this]
        suffices Disjoint (ABC.toFinset \ {v, û, x, y, q, r}) {û, x, y, q, r} by
          rw [sum_union this]
        simp only [disjoint_insert_right, mem_sdiff, mem_insert, mem_singleton, true_or, or_true,
          singleton_inter_of_mem, ne_eq, singleton_ne_empty, not_false_eq_true,
          mem_of_singleton_inter_ne_emty, not_true_eq_false, and_false, disjoint_singleton_right,
          and_self]
      suffices {û, x, y} ⊆ ABC.toFinset ∧ {q, r} ⊆ ABC.toFinset
          ∧ v ∉ ({û, x, y} : Finset _) ∧ v ∉ ({q, r} : Finset _) by
        grind
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro u hu
        refine mem_def.mpr <| hG <| G.mem_support.mpr ⟨v, ?_⟩
        refine Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
      · intro u hu
        refine mem_def.mpr <| hG <| G.mem_support.mpr ⟨y, ?_⟩
        refine Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
      · exact hNv ▸ G.notMem_neighborFinset_self _
      · grind [degree]
  simp only [sdiff_toFinset]
  refine le_sub_iff_add_le.mp <| tsub_le_tsub_left ?_ _
  rw [_split_sum hdv hNv hxy hyû hdy hNy, _split_sum' hdv hNv hxy hyû hdy hNy]
  rw [fB3 hBv hdv, fA4 hAû hdû, fA3 hAx hdx, fB3 hBy hdy]
  have hûv : û ∈ G.neighborFinset v := by grind
  have hAû' : (ABC \ {v}).promote y |>.A û :=
    Or.inl ⟨hAû, notMem_singleton.mpr <| ne_of_mem_neighborFinset hûv⟩
  have hdû' := hdû ▸ _hdeg hûv hxy hyû hNv hNy
  have hxv : x ∈ G.neighborFinset v := by grind
  have hAx' : (ABC \ {v}).promote y |>.A x :=
    Or.inl ⟨hAx, notMem_singleton.mpr <| ne_of_mem_neighborFinset hxv⟩
  have hdx' := hdx ▸ _hdeg hxv hxy hyû hNv hNy
  have hyv : y ∈ G.neighborFinset v := by grind
  have hAy' : (ABC \ {v}).promote y |>.A y := by
    refine Or.inr ⟨⟨hBy, notMem_singleton.mpr <| Ne.symm ?_⟩, mem_singleton.mpr rfl⟩
    exact ne_of_mem_of_not_mem (mem_neighborFinset_symm hyv) (G.notMem_neighborFinset_self _)
  have hdy' := hdy ▸ _hdeg hyv hxy hyû hNv hNy
  rw [fA3 hAû' hdû', fA2 hAx' hdx', fA2 hAy' hdy']
  suffices (f G ABC q
      - f ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v}) ((ABC \ {v}).promote y) q)
      + (f G ABC r
      - f ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v}) ((ABC \ {v}).promote y) r)
      ≤ 2 * (1 / 10) by
    linarith
  calc _
    _ ≤ ℓ G ABC q + ℓ G ABC r := by
      refine add_le_add ?_ ?_
      · refine Δf_le_ℓ_of_Δdeg_le_1 ?_ ?_
        · refine le_trans deleteIncidencesOf_degree_le ?_
          refine le_trans fromEdgeSet_union_degree_le' ?_
          simp only [add_le_add_iff_left, fromEdgeSet_singleton_degree_le_1]
        · have := hA34q' q (by grind)
          simp only [this.1, not_B_of_A, not_C_of_A, and_true, or_false, and_false]
          refine Or.inl ⟨this.1, ?_⟩
          grind [degree]
      · refine Δf_le_ℓ_of_Δdeg_le_1 ?_ ?_
        · refine le_trans deleteIncidencesOf_degree_le ?_
          refine le_trans fromEdgeSet_union_degree_le' ?_
          simp only [add_le_add_iff_left, fromEdgeSet_singleton_degree_le_1]
        · have := hA34q' r (by grind)
          simp only [this.1, not_B_of_A, not_C_of_A, and_true, or_false, and_false]
          refine Or.inl ⟨this.1, ?_⟩
          grind [degree]
    _ ≤ 1 / 10 + 1 / 10 := by
      refine add_le_add ?_ ?_
      · obtain ⟨hAq, hdq⟩ := hA34q' q (by grind)
        rcases hdq with hdq | hdq
        · linarith only [ℓA3 hAq hdq]
        · linarith only [ℓA4 hAq hdq]
      · obtain ⟨hAr, hdr⟩ := hA34q' r (by grind)
        rcases hdr with hdr | hdr
        · linarith only [ℓA3 hAr hdr]
        · linarith only [ℓA4 hAr hdr]
  linarith

lemma ok_of_A4 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w x y s t : Fin n}
    (hû : IsVstar G ABC û) (hBv : ABC.B v) (hdv : G.degree v = 3) (hdw : G.degree w = 3)
    (hdx : 3 ≤ G.degree x) (hdy : 3 ≤ G.degree y) (hAû : ABC.A û) (hdû : G.degree û = 4)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t}) (hxy : x ≠ y)
    (hv : G.Adj û v) (hfyx : f G ABC y ≤ f G ABC x)
    (hsumℓ : 2 / 3 - f G ABC û < ℓ G ABC x + ℓ G ABC y + ℓ G ABC s + ℓ G ABC t)
    (hℓ : ℓ G ABC s + ℓ G ABC t ≤ ℓ G ABC x + ℓ G ABC y)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n) [ABC'.Decidable],
      G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  rw [fA4 hAû hdû] at hsumℓ
  obtain ⟨hAx, hdx⟩ := A3x_of_2_over_15_lt_ℓx_plus_ℓy hG hdx hdy hfyx (by linarith)
  if hγy : γ G ABC y ≠ 0 then
    have hy : y ∈ ABC :=
      ABC.mem_toFinset.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith
    have : γ G ABC û ≤ γ G ABC y := γ_vstar_le_γ hû hy hγy
    have hvABC : v ∈ ABC :=
      ABC.mem_toFinset.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith
    refine Claim1 hvABC hG ih (hNv ▸ ?_)
    calc f G ABC v
      _ = 1 / 3 := by rw [fB3 hBv hdv]
      _ ≤ 1 /10 + 1 / 6 + 1 / 10 := by linarith
      _ = γ G ABC û + γ G ABC x + γ G ABC û := by
        rw [γA4 hAû hdû, γA3 hAx hdx]
      _ ≤ γ G ABC û + γ G ABC x + γ G ABC y := by
        simp only [add_le_add_iff_left, γ_vstar_le_γ hû hy hγy]
      _ = ∑ u ∈ {û, x, y}, γ G ABC u := by grind [degree]
  else
    have hy : y ∈ ABC :=
        ABC.mem_toFinset.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith
    if hCy : ABC.C y then
      refine Corollary9 hG hBv hdv ih ⟨y, ?_, hCy⟩
      exact G.mem_neighborFinset .. |>.mp <| by simp only [hNv, mem_insert, mem_singleton, or_true]
    else
      have hB3y : ABC.B y ∧ G.degree y = 3 := by
        have := γ_eq_0_iff hy (by linarith) |>.mp <| Decidable.not_not.mp hγy
        grind
      obtain ⟨hBy, hdy⟩ := hB3y
      if hxy : G.Adj x y then
        have hNx : ∃ u, G.neighborFinset x = {v, y, u} := by
          refine neighborFinset_eq_deg3'' ?_ ?_ ?_ hdx
          · exact mem_neighborFinset_symm <| by simp [hNv]
          · exact G.mem_neighborFinset .. |>.mpr hxy
          · refine Adj.ne <| G.mem_neighborFinset .. |>.mp <| by simp [hNv]
        obtain ⟨_, hNx⟩ := hNx
        exact Claim11 hG hAx hdx hNx hBv hBy hdv hdy ih
      else if hyû : G.Adj y û then
        refine Claim18 hG hû hAû hdû hBy hdy hBv hdv hyû.symm ?_ ?_ ih
        <;> exact Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNv]
      else
        have : ∃ q r, G.neighborFinset y = {v, q, r} ∧ f G ABC r ≤ f G ABC q :=
          neighborFinset_eq_deg3' (mem_neighborFinset_symm <| by simp [hNv]) (f G ABC ·) hdy
        obtain ⟨q, r, hNy, hfrq⟩ := this
        match Corollary7 hG hBy hdy ih with
        | Or.inl h => exact h
        | Or.inr hdNy => ?_
        match ok_of_A4_step1 hG hû hBv hdv hBy hdy hAû hdû hNy hdNy ih with
        | Or.inl h => exact h
        | Or.inr hγNy => ?_
        simp only [not_exists, not_and, not_lt] at hγNy
        match ok_of_A4_step2 hG hNy hdNy hγNy with
        | Or.inl h => exact h
        | Or.inr hA34q' => ?_
        obtain ⟨s, hs, hsf, hsresp, hscard⟩ := by
          refine ih ((fromEdgeSet (G.edgeSet ∪ {s(q, r)})).deleteIncidencesOf {v})
            ((ABC \ {v}).promote y) ?_ ?_
          · intro u
            simp only [← promote_toFinset_eq, toFinset_eq, coe_sdiff,
              coe_singleton, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
            intro hu
            obtain ⟨u', huu'⟩ := mem_support _ |>.mp hu
            refine ⟨?_, notMem_singleton.mp <| notMem_of_adj_deleteIncidencesOf' huu'.symm⟩
            rcases adj_fromEdgeSet_union_iff.mp <| adj_of_deleteIncidencesOf_adj huu' with hu | hu
            · exact mem_def.mpr <| hG <| G.mem_support.mpr ⟨u', hu⟩
            · have : u = q ∨ u = r := by grind
              refine mem_def.mpr <| hG <| G.mem_support.mpr ⟨y, ?_⟩
              exact Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
          · simp only [← card_promote_eq_card]
            refine ABC.sdiff_card ?_
            suffices v ∈ ABC.toFinset by
              simp only [ne_eq, singleton_inter_eq_empty_iff, Decidable.not_not, this]
            refine mem_def.mpr <| hG <| (G.degree_pos_iff_mem_support _).mp hv.degree_pos_right
        have hvs : v ∉ s := by
          intro hvs
          have := hs hvs
          simp only [← promote_toFinset_eq, toFinset_eq, mem_sdiff, inter_self, ne_eq, and_false,
            singleton_ne_empty, not_false_eq_true, mem_of_singleton_inter_ne_emty,
            not_true_eq_false] at this
        refine ⟨s, ?_, ?_, ?_, ?_⟩
        · intro u hu
          have hobj := hs hu
          simp only [← promote_toFinset_eq, sdiff_toFinset, mem_sdiff] at hobj
          exact hobj.1
        · exact InducesForest_mono le_fromEdgeSet_union
            (InducesForest_mono' (inter_singleton_of_notMem hvs) hsf)
        · exact _respects_of_A4 hBy hdy hNy hs hsf hsresp
        · exact _eval_ok_of_A4 hG hBv hdv hAû hdû hNv hxy hyû hAx hdx hBy hdy hNy hA34q' hscard

lemma Claim19 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w : Fin n} (hû : IsVstar G ABC û)
    (hBv : ABC.B v) (hdv : G.degree v = 3) (hBw : ABC.B w) (hdw : G.degree w = 3)
    (hvnew : v ≠ w) (hv : G.Adj û v) (hw : G.Adj û w)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n) [ABC'.Decidable],
      G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
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
        refine ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ?_
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
    if hsumℓ : ℓ G ABC x + ℓ G ABC y + ℓ G ABC s + ℓ G ABC t ≤ 2 / 3 - f G ABC û then
      refine ok_of_hsumℓ hG hvw hBv hdv hBw hdw hNv hNw ?_ hvnew hv hw ?_ hsumℓ ih
      <;> grind [degree]
    else if hA4û : ABC.A û ∧ G.degree û = 4 then
      simp only [not_le] at hsumℓ
      refine ok_of_A4 hG hû hBv hdv hdw ?_ ?_ hA4û.1 hA4û.2 hNv hNw
        ?_ hv hfyx hsumℓ hℓ ih <;> grind [degree]
    else
      have hℓxy : 1 / 6 < ℓ G ABC x + ℓ G ABC y := by
        suffices f G ABC û ≤ 1 / 3 by linarith
        exact f_le_1_over_3_of_4_le_deg_of_not_A4 hdû hA4û
      refine ok_of_one_sixth_lt_ℓxy hG hBv hdv ?_ ?_ hNv hℓxy ih <;> grind

end Tripartition
end ABC
end CaroWeiType
