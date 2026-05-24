import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Operations
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim19

open SimpleGraph
open Finset

namespace CaroWeiType
namespace ABC
namespace Tripartition

variable {V : Type} [Fintype V]

private lemma _ABC_iff {ABC : Tripartition V} {x : V} {s s' : Finset V}
    (hs : x ∉ s) (hs' : x ∉ s') (hx : x ∈ ABC) :
      ((ABC \ s).promote_finset s').A x ∧ ABC.A x ∨
      ((ABC \ s).promote_finset s').B x ∧ ABC.B x ∨
      ((ABC \ s).promote_finset s').C x ∧ ABC.C x := by
  rcases hx with hA | hB | hC
  · have hA' : ((ABC \ s).promote_finset s').A x := Or.inl ⟨hA, hs⟩
    simp only [hA, hA', true_and, true_or]
  · have hB' : ((ABC \ s).promote_finset s').B x := Or.inl ⟨⟨hB, hs⟩, hs'⟩
    simp only [hB, hB', true_and, true_or, or_true]
  · have hC' : ((ABC \ s).promote_finset s').C x := ⟨⟨hC, hs⟩, hs'⟩
    simp only [hC, hC', true_and, or_true]

variable [DecidableEq V]

private noncomputable def f' (G : SimpleGraph V) [DecidableRel G.Adj]
    (ABC : Tripartition V) (û w x y : V) : V → ℝ :=
  fun u ↦ (f G ABC u - f ((fromEdgeSet (G.edgeSet ∪ {s(x, y)})).deleteIncidencesOf {û})
      ((ABC \ {û}).promote w) u)

private lemma f'_eq {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V}
    {û w x y : V} : f' G ABC û w x y = f' G ABC û w y x := by
  ext; rw [f', f', Sym2.eq_swap]

private lemma _C3_of_γ_eq_0 {G : SimpleGraph V} [DecidableRel G.Adj]
    {ABC : Tripartition V} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {û w z : V} (hû : IsVstar G ABC û) (hBw : ABC.B w) (hdw : G.degree w = 3) (hw : G.Adj û w)
    (hz : G.Adj û z) (hγz : γ G ABC z = 0) (hzw : z ≠ w)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ↑ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨ (ABC.C z ∧ G.degree z = 3) := by
  have hdz : 1 ≤ G.degree z := one_le_degree_of_adj' hz
  have hzABC : z ∈ ABC :=
      ABC.mem_toFinset.mpr <| mem_def.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp hdz
  rcases (γ_eq_0_iff hzABC hdz).mp hγz with ⟨hdz, hBz⟩ | ⟨hdz, hCz⟩ | ⟨hdz, hCz⟩
  · exact Or.inl <| Claim19 hG hû hBw hdw hBz hdz hzw.symm hw hz ih
  · exact Or.inr ⟨hCz, hdz⟩
  · exact Or.inl <| Claim6 hG ih ⟨z, hdz, not_A_of_C hCz⟩

private lemma _unique_C3_of_γ_eq_0 {G : SimpleGraph V} [DecidableRel G.Adj]
    {ABC : Tripartition V} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {û w z s : V} (hû : IsVstar G ABC û) (hBw : ABC.B w) (hdw : G.degree w = 3) (hw : G.Adj û w)
    (hz : G.Adj û z) (hγz : γ G ABC z = 0) (hzw : z ≠ w) (hγs : γ G ABC s = 0) (hs : G.Adj û s)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ↑ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨ s = w ∨ s = z := by
  if hsw : s = w then
    exact Or.inr <| Or.inl hsw
  else if hsz : s = z then
    exact Or.inr <| Or.inr hsz
  else
    match _C3_of_γ_eq_0 hG hû hBw hdw hw hs hγs hsw ih,
        _C3_of_γ_eq_0 hG hû hBw hdw hw hz hγz hzw ih with
    | Or.inl h, _ => exact Or.inl h
    | _, Or.inl h => exact Or.inl h
    | Or.inr hs, Or.inr hz => ?_
    obtain ⟨hCs, hds⟩ := hs
    obtain ⟨hCz, hdz⟩ := hz
    exact Or.inl <| Claim17 hG hû hCs hds hCz hdz hsz hs hz ih

private lemma _step_1 {G : SimpleGraph V} [DecidableRel G.Adj]
    {ABC : Tripartition V} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {û w x y : V} (hû : IsVstar G ABC û) (hBw : ABC.B w) (hdw : G.degree w = 3) (hw : G.Adj û w)
    (hNw : G.neighborFinset w = {û, x, y})
    (hf'y : f' G ABC û w x y y ≤ 0) (hf'x : f' G ABC û w x y x ≤ f' G ABC û w x y y)
    (hdû : 4 ≤ G.degree û)
    {U : Finset V} (hU : U = {u ∈ G.neighborFinset û \ {w, x, y} | γ G ABC u ≠ 0})
    (H : f G ABC û > 1 / 3 + #U * γ G ABC û - f' G ABC û w x y x - f' G ABC û w x y y)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ↑ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
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
    have hγs := hsU hs
    have hûs : G.Adj û s := G.mem_neighborFinset .. |>.mp <| mem_sdiff.mp hs |>.1
    match _C3_of_γ_eq_0 hG hû hBw hdw hw hûs hγs (by grind) ih with
    | Or.inl h => exact Or.inl h
    | Or.inr h => ?_
    obtain ⟨hCs, hds⟩ := h
    if h' : (G.neighborFinset û \ {w, x, y, s}).Nonempty then
      obtain ⟨s', hs'⟩ := h'
      have hûs' : G.Adj û s' := G.mem_neighborFinset .. |>.mp <| mem_sdiff.mp hs' |>.1
      have hγs' : γ G ABC s' = 0 := by
        have hs'U : s' ∉ U := by simp only [hUempty, notMem_empty, not_false_eq_true]
        grind
      match _unique_C3_of_γ_eq_0 hG hû hBw hdw hw hûs hγs (by grind) hγs' hûs' ih with
      | Or.inl h => exact Or.inl h
      | Or.inr h => grind
    else
      refine Or.inr ⟨s, ?_, hCs, hds⟩
      simp only [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at h'
      refine eq_of_subset_and_eq_card h' ?_
      rw [← degree, hdû]
      grind [degree, ne_of_mem_neighborFinset]
  match this with
  | Or.inl h => exact h
  | Or.inr h => ?_
  obtain ⟨s, hs, hCs, hds⟩ := h
  match Claim16 hG hû hCs hds ih with
  | Or.inl h => exact h
  | Or.inr h => ?_
  simp only [hAû, hdû, true_and, not_true_eq_false, false_and] at h

private lemma _step2 {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {û w x y : V} (hdw : G.degree w = 3) (hNw : G.neighborFinset w = {û, x, y})
    (hf'y : 0 < f' G ABC û w x y y) :
    ((fromEdgeSet <| G.edgeSet ∪ {s(x, y)}).deleteIncidencesOf {û}).degree y = G.degree y + 1
      ∧ ¬G.Adj û y ∧ ¬G.Adj x y := by
  have hyABC : y ∈ ABC := by
    refine ABC.mem_toFinset.mpr <| mem_def.mpr <| hG <| G.mem_support.mpr ⟨w, ?_⟩
    exact Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
  have H : G.degree y
      < ((fromEdgeSet <| G.edgeSet ∪ {s(x, y)}).deleteIncidencesOf {û}).degree y := by
    have hyû : y ∉ ({û} : Finset _) := by grind [degree]
    have hyw : y ∉ ({w} : Finset _) := by
      refine notMem_singleton.mpr ?_
      exact ne_of_mem_neighborFinset <| (by grind : y ∈ G.neighborFinset w)
    rcases hyABC with hA | hB | hC
    · have hA' : ((ABC \ {û}).promote w).A y := Or.inl ⟨hA, hyû⟩
      simp only [f', f, hA, hA', ↓reduceDIte, sub_pos] at hf'y
      exact fA_decreasing' hf'y
    · have hB' : ((ABC \ {û}).promote w).B y := Or.inl ⟨⟨hB, hyû⟩, hyw⟩
      simp only [f', f, hB, hB', not_A_of_B, ↓reduceDIte, sub_pos] at hf'y
      exact fB_decreasing' hf'y
    · have hC' : ((ABC \ {û}).promote w).C y := ⟨⟨hC, hyû⟩, hyw⟩
      simp only [f', f, hC, hC', not_A_of_C, not_B_of_C, ↓reduceDIte, sub_pos] at hf'y
      exact fC_decreasing' hf'y
  have hdegy := by
    refine le_antisymm ?_ (Order.add_one_le_iff.mpr H)
    refine le_trans deleteIncidencesOf_degree_le (le_trans fromEdgeSet_union_degree_le' ?_)
    exact add_le_add_iff_left _ |>.mpr <| fromEdgeSet_singleton_degree_le_1
  have hûy : ¬G.Adj û y := by
    intro hûy
    suffices ((fromEdgeSet <| G.edgeSet ∪ {s(x, y)}).deleteIncidencesOf {û}).degree y
        < G.degree y + 1 by
      linarith
    calc _
      _ < (fromEdgeSet (G.edgeSet ∪ {s(x, y)})).degree y := by
        refine deleteIncidencesOf_degree_lt (le_fromEdgeSet_union hûy).symm (by grind)
      _ ≤ G.degree y + 1 := by
        refine le_trans fromEdgeSet_union_degree_le' ?_
        exact add_le_add_iff_left _ |>.mpr <| fromEdgeSet_singleton_degree_le_1
  have hxy : ¬G.Adj x y := by
    have : ((fromEdgeSet <| G.edgeSet ∪ {s(x, y)}).deleteIncidencesOf {û}).degree y
        = (fromEdgeSet <| G.edgeSet ∪ {s(x, y)}).degree y := by
      refine congrArg Finset.card ?_
      refine neighborFinset_eq_delelteIncidencesOf_of_empty_inter_neighborFinset ?_ ?_
      · refine inter_singleton_of_notMem ?_
        refine not_iff_not.mpr mem_fromEdgeSet_union_neighborFinset_iff |>.mpr ?_
        simp only [not_or, not_and, mem_neighborFinset, not_adj_symm hûy, not_false_eq_true,
          true_and, Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
          Prod.swap_prod_mk, true_and, ne_eq, Decidable.not_not]
        grind [degree]
      · grind [degree]
    rw [hdegy] at this
    intro hxy
    have : (fromEdgeSet (G.edgeSet ∪ {s(x, y)})).degree y = G.degree y := by
      refine congrArg Finset.card ?_
      refine Set.toFinset_inj.mpr ?_
      suffices (fromEdgeSet (G.edgeSet ∪ {s(x, y)})) = G by
        rw [this]
      refine eq_fromEdgeSet_of_union_le_right ?_
      intro u u' huu'
      simp only [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk, ne_eq] at huu'
      grind [Adj.symm]
    linarith
  exact ⟨hdegy, hûy, hxy⟩

private lemma _step_3 {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {û w x y : V} (hû : IsVstar G ABC û) (hBw : ABC.B w) (hdw : G.degree w = 3) (hw : G.Adj û w)
    (hNw : G.neighborFinset w = {û, x, y})
    {U : Finset V}
    (hU : U = {u ∈ G.neighborFinset û \ {w, x, y} | γ G ABC u ≠ 0})
    (H : f G ABC û > 1 / 3 + ↑(#U) * γ G ABC û - f' G ABC û w x y x - f' G ABC û w x y y)
    (hûy : ¬G.Adj û y)
    (hf'x : f' G ABC û w x y x ≤ ℓ G ABC x)
    (hf'y : f' G ABC û w x y y ≤ ℓ G ABC y)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ↑ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨ (G.neighborFinset û \ U) ⊆ {w, x} := by
  if hNûUwx : (G.neighborFinset û \ U) ⊆ {w, x} then
    exact Or.inr hNûUwx
  else
    obtain ⟨s, hsNû, hsw, hsx⟩: ∃ s, s ∈ (G.neighborFinset û \ U) ∧ s ≠ w ∧ s ≠ x := by grind
    have hγs : γ G ABC s = 0 := by
      have := mem_sdiff.mp hsNû |>.2
      have hsy : s ≠ y := by
        refine ne_of_mem_of_not_mem (mem_sdiff.mp hsNû |>.1) ?_
        simp only [mem_neighborFinset, hûy, not_false_eq_true]
      simp only [hU, ne_eq, mem_filter, mem_sdiff, mem_sdiff.mp hsNû |>.1, mem_insert, hsw, hsx,
        mem_singleton, false_or, true_and, Decidable.not_not, hsy, not_false_eq_true] at this
      exact this
    have hûs : G.Adj û s := G.mem_neighborFinset .. |>.mp <| mem_sdiff.mp hsNû |>.1
    match _C3_of_γ_eq_0 hG hû hBw hdw hw hûs hγs (by grind) ih with
    | Or.inl h => exact Or.inl h
    | Or.inr h => ?_
    obtain ⟨hCs, hds⟩ := h
    have : Objective G ABC ∨ (G.neighborFinset û \ U) ⊆ {w, x, s} := by
      if hobj : Objective G ABC then exact Or.inl hobj
      else
        refine Or.inr ?_
        intro u' hu'
        if hu'wx : u' = w ∨ u' = x then grind
        else
          simp only [not_or] at hu'wx
          simp only [hU, ne_eq, mem_sdiff, mem_neighborFinset, mem_filter, mem_insert, hu'wx,
            mem_singleton, false_or, not_and, Decidable.not_not, and_imp] at hu'
          have hu'y : u' ≠ y := by grind
          have := _unique_C3_of_γ_eq_0 hG hû hBw hdw hw hûs hγs hsw (hu'.2 hu'.1 hu'y) hu'.1 ih
          grind
    refine Or.elim this Or.inl (fun hNûU ↦ ?_)
    have : G.degree û - #U ≤ 3 := by
      have : #{w, x, s} = 3 := by
        have : w ≠ x := Ne.symm <| ne_of_mem_neighborFinset (by grind : x ∈ G.neighborFinset w)
        grind
      refine le_of_le_of_eq (le_of_eq_of_le ?_ (card_le_card hNûU)) this
      rw [degree]
      refine Eq.symm (card_sdiff_of_subset ?_)
      intro u' hu'
      simp only [hU, mem_filter] at hu'
      exact mem_sdiff.mp hu'.1 |>.1
    have hx : G.Adj x w := Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]
    have hy : G.Adj y w := Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]
    refine Or.elim (Corollary8 hG ih hBw hdw hx hy (by grind [degree])) Or.inl (fun hℓ ↦ ?_)
    refine Or.elim (Corollary16 hG hû hCs hds ih) Or.inl (fun _ ↦ ?_)
    refine Or.elim (Claim14 hG hû ih) Or.inl (fun ⟨hnotA2, hdû, hfû, hγ0⟩ ↦ ?_)
    suffices 1 / 7 > 1 / (6 : ℝ) by linarith
    calc _
      _ ≥ 3 * γ G ABC û := by linarith
      _ ≥ (G.degree û - #U) * γ G ABC û := by
        refine mul_le_mul_of_nonneg ?_ (le_refl _) ?_ γ_nonneg
        · rw [← Nat.cast_sub, ← Nat.cast_three, Nat.cast_le]
          · exact this
          · exact card_le_card (by grind)
        · simp only [sub_nonneg, Nat.cast_le]
          exact card_le_card (by grind)
      _ = (G.degree û) * γ G ABC û - #U * γ G ABC û := by
        exact sub_mul ..
      _ = f G ABC û - #U * γ G ABC û := by
        simp only [sub_left_inj]
        exact hfû.symm
    linarith

private lemma _degree_ok {G : SimpleGraph V} [DecidableRel G.Adj] {û w x y : V}
    (hdw : G.degree w = 3) (hNw : G.neighborFinset w = {û, x, y}) (hûx : G.Adj x û)
    (hxy : ¬G.Adj x y) :
    G.degree x = ((fromEdgeSet <| G.edgeSet ∪ {s(x, y)}).deleteIncidencesOf {û}).degree x := by
  have : (fromEdgeSet <| G.edgeSet ∪ {s(x, y)}).degree x
      = ((fromEdgeSet <| G.edgeSet ∪ {s(x, y)}).deleteIncidencesOf {û}).degree x + 1 := by
    rw [← card_singleton û]
    refine degree_deleteIncidencesOf_neighbor (fromEdgeSet (G.edgeSet ∪ {s(x, y)})) ?_
    simp only [singleton_subset_iff, mem_neighborFinset]
    exact le_fromEdgeSet_union hûx
  have : (fromEdgeSet (G.edgeSet ∪ {s(x, y)})).degree x = G.degree x + 1 := by
    refine le_antisymm ?_ ?_
    · refine le_trans fromEdgeSet_union_degree_le' ?_
      simp only [add_le_add_iff_left, fromEdgeSet_singleton_degree_le_1]
    · rw [← card_singleton y]
      have : G.degree x + #{y} = #(G.neighborFinset x ∪ {y}) := by
        refine Eq.symm <| (card_union_eq_card_add_card).mpr ?_
        refine disjoint_singleton_right.mpr ?_
        simp only [mem_neighborFinset, hxy, not_false_eq_true]
      rw [this]
      refine card_le_card ?_
      intro u hu
      simp only [mem_neighborFinset]
      refine adj_fromEdgeSet_union_iff.mpr ?_
      simp only [union_singleton, mem_insert, mem_neighborFinset] at hu
      rcases hu with hu | hu
      · grind [degree]
      · exact Or.inl hu
  linarith

private lemma _Claim20 {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {û w x y : V} (hû : IsVstar G ABC û) (hBw : ABC.B w) (hdw : G.degree w = 3) (hw : G.Adj û w)
    (hNw : G.neighborFinset w = {û, x, y})
    (hf : ∑ u ∈ G.neighborFinset û \ ({w} ∪ G.neighborFinset w), γ G ABC u <
      f G ABC û - 1 / 3 + f' G ABC û w x y x + f' G ABC û w x y y)
    (hf'xy : f' G ABC û w x y x ≤ f' G ABC û w x y y)
    (hdû : 4 ≤ G.degree û)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ↑ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  let U : Finset _ := {u ∈ G.neighborFinset û \ {w, x, y} | γ G ABC u ≠ 0}
  have H : f G ABC û > 1 / 3 + #U * γ G ABC û - f' G ABC û w x y x - f' G ABC û w x y y := by
    suffices #U * γ G ABC û  ≤ ∑ u ∈ G.neighborFinset û \ ({w} ∪ G.neighborFinset w), γ G ABC u by
      linarith
    calc _
      _ = ∑ u ∈ U, γ G ABC û := Eq.symm <| sum_const' fun _ _ ↦ rfl
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
  if hf'y : f' G ABC û w x y y ≤ 0 then
    exact _step_1 hG hû hBw hdw hw hNw hf'y hf'xy hdû rfl H ih
  else
    simp only [not_le] at hf'y
    obtain ⟨hdegy, hûy, hxy⟩ := _step2 hG hdw hNw hf'y
    have hfx : f' G ABC û w x y x ≤ ℓ G ABC x := by
      rw [f']
      refine Δf_le_ℓ_of_Δdeg_le_1 ?_ ?_
      · refine le_trans deleteIncidencesOf_degree_le (le_trans fromEdgeSet_union_degree_le' ?_)
        exact add_le_add (le_refl _) fromEdgeSet_singleton_degree_le_1
      · refine _ABC_iff (by grind [degree]) (by grind [ne_of_mem_neighborFinset]) ?_
        refine ABC.mem_toFinset.mpr <| mem_def.mpr <| hG <| G.mem_support.mpr ⟨w, ?_⟩
        exact Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
    have hfy : f' G ABC û w x y y ≤ ℓ G ABC y := by
      rw [f']
      refine Δf_le_ℓ_of_Δdeg_le_1 ?_ ?_
      · exact le_of_eq hdegy
      · refine _ABC_iff (by grind [degree]) (by grind [ne_of_mem_neighborFinset]) ?_
        refine ABC.mem_toFinset.mpr <| mem_def.mpr <| hG <| G.mem_support.mpr ⟨w, ?_⟩
        exact Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
    refine Or.elim (_step_3 hG hû hBw hdw hw hNw rfl H hûy hfx hfy ih) (·) (fun h ↦ ?_)
    refine Or.elim (Claim14 hG hû ih) (·) (fun ⟨hnotA2, _, hfû, hγ0⟩ ↦ ?_)
    have hobj : ((G.degree û - #U) : ℕ) * γ G ABC û > 1 / 3 - ℓ G ABC x - f' G ABC û w x y y := by
      calc _
        _ = G.degree û * γ G ABC û - #U * γ G ABC û := by
          rw [Nat.cast_sub]
          · exact sub_mul ..
          · exact card_le_card (by grind)
        _ = f G ABC û - #U * γ G ABC û := by linarith
      linarith
    if hûx : x ∈ G.neighborFinset û then
      have : G.degree û - #U ≤ 2 := by
        refine le_trans (le_of_eq_of_le ?_ (card_le_card h)) (@card_le_two _ _ w x)
        simp only [U, degree]
        refine Eq.symm (card_sdiff_of_subset <| by grind)
      have hyw : G.Adj y w := Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
      refine Or.elim (Corollary8' hG ih hBw hdw hyw) (·) (fun hℓy ↦ ?_)
      suffices 2 * (1 / (10 : ℝ)) > 1 / 5 by linarith
      calc _
        _ ≥ 2 * γ G ABC û := by
          simp only [ge_iff_le, two_pos, mul_le_mul_iff_right₀]
          exact γ_le_1_10_of_4_le_degree hdû
        _ ≥ (G.degree û - #U) * γ G ABC û := by
          refine mul_le_mul_of_nonneg ?_ (le_refl _) ?_ γ_nonneg
          · rw [← Nat.cast_sub, ← Nat.cast_two, Nat.cast_le]
            · exact this
            · exact card_le_card (by grind)
          · simp only [sub_nonneg, Nat.cast_le]
            exact card_le_card (by grind)
        _ > 1 / 3 - ℓ G ABC y := by
          suffices f' G ABC û w x y x = 0 by linarith
          simp only [f']
          refine sub_eq_zero_of_eq ?_
          refine f_congr ?_ ?_
          · exact _degree_ok hdw hNw (G.mem_neighborFinset .. |>.mp hûx).symm hxy
          · have hxû : x ∉ ({û} : Finset _) := by grind [degree]
            have hxw : x ∉ ({w} : Finset _) := by grind [ne_of_mem_neighborFinset]
            refine ⟨fun hA ↦ ?_, fun hB ↦ ?_, fun hC ↦ ?_, mt <| fun h ↦ ?_⟩
            · exact Or.inl ⟨hA, hxû⟩
            · exact Or.inl ⟨⟨hB, hxû⟩, hxw⟩
            · exact ⟨⟨hC, hxû⟩, hxw⟩
            · exact ABC.mem_toFinset.mpr
                <| mem_of_subset_of_adj hG (G.mem_neighborFinset w x |>.mp <| by simp [hNw])
      linarith
    else
      have : G.degree û - #U = 1 := by
        rw [← card_singleton w]
        have : G.degree û - #U = #(G.neighborFinset û \ U) :=
          Eq.symm <| card_sdiff_of_subset <| by grind
        refine this.trans ?_
        refine congrArg Finset.card ?_
        ext u'
        constructor
        · intro hu'
          have := h hu'
          suffices u' ≠ x by grind
          exact ne_of_mem_of_not_mem (mem_sdiff.mp hu' |>.1) hûx
        · intro hu'
          simp only [ne_eq, mem_singleton.mp hu', mem_sdiff, mem_neighborFinset, mem_filter,
            mem_singleton, inter_insert_of_mem, insert_ne_empty, not_false_eq_true,
            mem_of_singleton_inter_ne_emty, not_true_eq_false, and_false, false_and, and_true, U]
          refine Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]
      have hx : G.Adj x w := Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]
      have hy : G.Adj y w := Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]
      refine Or.elim (Corollary8 hG ih hBw hdw hx hy (by grind [degree])) (·) (fun hℓ ↦ ?_)
      rw [this, Nat.cast_one, one_mul] at hobj
      suffices 1 / 10 > 1 / (6 : ℝ) by linarith
      calc _
        _ ≥ γ G ABC û := by
          exact γ_le_1_10_of_4_le_degree hdû
      linarith

private lemma _exists {G : SimpleGraph V} [DecidableRel G.Adj] (ABC : Tripartition V)
    {û w : V} (hdw : G.degree w = 3) (hw : G.Adj û w) :
    ∃ x y, G.neighborFinset w = {û, x, y} ∧ f' G ABC û w x y x ≤ f' G ABC û w x y y := by
  have hûw : û ∈ G.neighborFinset w := G.mem_neighborFinset .. |>.mpr hw.symm
  obtain ⟨x, y, hNw, _⟩ := neighborFinset_eq_deg3' hûw 1 hdw
  if h : f' G ABC û w x y x ≤ f' G ABC û w x y y then
    exact ⟨x, y, hNw, h⟩
  else
    refine ⟨y, x, by grind, ?_⟩
    nth_rw 1 [f'_eq]
    nth_rw 2 [f'_eq]
    exact le_of_lt <| not_le.mp h

lemma Claim20 {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û w : V} (hû : IsVstar G ABC û)
    (hBw : ABC.B w) (hdw : G.degree w = 3) (hw : G.Adj û w)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  obtain ⟨x, y, hNw, hf'xy⟩ := _exists ABC hdw hw
  match objective_of_B3' hG hdw hBw hNw ih, Claim15 hG hû ih with
  | Or.inl h, _ => exact h
  | _, Or.inl h => exact h
  | Or.inr hf, Or.inr hdû => ?_
  refine _Claim20 hG hû hBw hdw hw hNw ?_ hf'xy hdû ih
  grind [f', degree]

end Tripartition
end ABC
end CaroWeiType
