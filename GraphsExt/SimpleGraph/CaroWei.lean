import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

open Finset Fintype

namespace SimpleGraph


/-
Inspired by a solution from Mitchell Horner (see
https://leanprover.zulipchat.com/#narrow/channel/252551-graph-theory/topic/induction.20on.20number.20of.20vertices/near/574097168)
-/

private lemma sum_const' {ι : Type*} {f : ι → ℝ} {c : ℝ} (X : Finset ι) (h : ∀ x ∈ X, f x = c) :
    ∑ x ∈ X, f x = #X * c := by
  let tmp := Finset.sum_congr rfl h
  rw [tmp]
  let tmp2 := @sum_const ι ℝ X _ c
  grind

private lemma _gains {x y : ℝ} {hpos : 0 < x} (h : x ≤ y) :
    (x * (x + 1))⁻¹ ≥ (y * (y + 1))⁻¹ := by
  have h' : y⁻¹ ≤ x⁻¹ := by exact inv_anti₀ hpos h
  have hp1' : (y + 1)⁻¹ ≤ (x + 1)⁻¹ := by
    refine inv_anti₀ ?_ ?_
    · exact lt_trans hpos (lt_add_one x)
    · simp only [add_le_add_iff_right, h]
  simp only [mul_inv_rev, ge_iff_le]
  calc (y + 1)⁻¹ * y⁻¹
    _ ≤ (y + 1)⁻¹ * x⁻¹ := by
      refine (mul_le_mul_iff_of_pos_left <| inv_pos.mpr ?_).mpr h'
      have hy : 0 < y := Std.lt_of_lt_of_le hpos h
      exact lt_trans hy (lt_add_one y)
    _ ≤ (x + 1)⁻¹ * x⁻¹ := by
      refine (mul_le_mul_iff_of_pos_right ?_).mpr hp1'
      simp only [inv_pos, hpos]

variable {V : Type*}

open Classical in
private lemma card_setminus_singleton {X : Finset V} {v : V} (h : v ∈ X) :
    #(X \ {v}) = #X - 1 := by grind

variable [Fintype V]

open Classical in
lemma v_notin_neighbors {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    G.neighborFinset v ∩ {v} = ∅ := by
  ext w
  constructor
  · intro hw
    simp only [mem_inter, mem_singleton] at hw
    simp only [notMem_empty]
    exact G.irrefl <| (mem_neighborFinset G v v).mp (hw.2 ▸ hw.1)
  · intro hw
    simp_all only [notMem_empty]

open Classical in
lemma deleteIncidenceSet_degree_nonneighbor_eq (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    {x : V} (hx : ¬G.Adj x v) (hne : x ≠ v) : G.degree x = (G.deleteIncidenceSet v).degree x := by
  simp_rw [degree]
  refine congrArg card ?_
  ext w
  simp_all only [ne_eq, mem_neighborFinset, deleteIncidenceSet, incidenceSet, deleteEdges_adj,
    Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, hne.symm, false_or]
  refine ⟨?_, fun hw ↦ hw.left⟩
  intro hw
  simp only [not_and]
  exact ⟨hw, fun _ heq ↦ hx <| (heq ▸ hw)⟩

open Classical in
lemma deleteIncidenceSet_degree_neighbor_eq (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    {x : V} (hx : G.Adj x v) : G.degree x = (G.deleteIncidenceSet v).degree x + 1 := by
  simp_rw [degree]
  suffices G.neighborFinset x = (G.deleteIncidenceSet v).neighborFinset x ∪ {v} by
    rw [congrArg card this]
    have _ : v ∉ (G.deleteIncidenceSet v).neighborFinset x := by
      intro hv
      simp only [deleteIncidenceSet, mem_neighborFinset, deleteEdges_adj] at hv
      exact hv.right <| (mk'_mem_incidenceSet_right_iff G).mpr hv.left
    simp_all
  ext w
  constructor
  · intro hw
    simp_all only [mem_neighborFinset, deleteIncidenceSet, union_singleton, mem_insert,
      deleteEdges_adj, true_and]
    cases Classical.em <| w = v with
    | inl h => exact Or.intro_left _ h
    | inr h =>
        refine Or.intro_right _ ?_
        simp only [incidenceSet, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or]
        exact fun _ ↦ ⟨Adj.ne' hx, by grind⟩
  · intro hw
    simp only [union_singleton, mem_insert, mem_neighborFinset] at hw
    cases hw with
    | inl h => simp_all [adj_symm]
    | inr h => exact (G.mem_neighborFinset _ _).mpr <| deleteEdges_adj.mp h |>.left

lemma _cw_bound_mono (x : ℝ) (h : 1 ≤ x) :
    (x)⁻¹ = (x + 1)⁻¹ + (x * (x + 1))⁻¹ := by
  have h : x * (1 + x) * (x + x^2) ≠ 0 := by
    suffices x * (1 + x) * (x + x^2) ≥ 4 by grind
    ring_nf
    calc (x ^ 2 + x ^ 3 * 2 + x ^ 4)
      _ ≥ 1 + x ^3 * 2 + x ^ 4 := by simp only [ge_iff_le, add_le_add_iff_right, one_le_pow₀ h]
      _ ≥ 1 + 1 * 2 + x ^ 4 := by
          simp only [one_mul, ge_iff_le, add_le_add_iff_right,
          add_le_add_iff_left, Nat.ofNat_pos, le_mul_iff_one_le_left, one_le_pow₀ h]
      _ ≥ 1 + 1 * 2 + 1 := by
          simp only [one_mul, ge_iff_le, add_le_add_iff_left, one_le_pow₀ h]
      _ ≥ 4 := by grind
  exact (mul_left_inj' h).mp (by grind)

open Classical in
theorem cw_bound_mono (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (hdegv : G.maxDegree = @SimpleGraph.degree V G v (G.neighborSetFintype v))
    (hΔ : 0 < G.maxDegree) {X : Finset V} (hout : ∀ x ∈ univ \ X, G.degree x = 0) :
    ∑ x ∈ (X \ {v}), ((G.deleteIncidenceSet v).degree x + 1 : ℝ)⁻¹
      ≥ ∑ x ∈ X, (G.degree x + 1 : ℝ)⁻¹ := by
  let Nv := G.neighborFinset v
  have _ : #Nv = G.maxDegree := hdegv.symm
  have hNv : Nv ⊆ X := by
    intro w hwNv
    by_contra
    have hw : w ∈ univ \ X := mem_sdiff.mpr ⟨mem_univ w, this⟩
    have hdegw : G.degree w > 0 :=
      Adj.degree_pos_left <| adj_symm G <| (G.mem_neighborFinset v w).mp hwNv
    suffices 0 < 0 by exact Nat.not_succ_le_zero 0 this
    exact (hout w hw) ▸ hdegw
  have hdegNv : ∀ x ∈ Nv, G.degree x = (G.deleteIncidenceSet v).degree x + 1 := by
    intro x hx
    refine deleteIncidenceSet_degree_neighbor_eq G v ?_
    simp [Nv] at hx
    exact hx.symm
  have hsumNv : ∑ x ∈ Nv, ((G.deleteIncidenceSet v).degree x + 1 : ℝ)⁻¹
      ≥ ∑ x ∈ Nv, (G.degree x + 1 : ℝ)⁻¹ + (G.degree v + 1 : ℝ)⁻¹ := by
    have h : ∑ x ∈ Nv, ((G.deleteIncidenceSet v).degree x + 1 : ℝ)⁻¹
        = ∑ x ∈ Nv, (G.degree x : ℝ)⁻¹ := by
      refine sum_congr rfl ?_
      intro x hx
      let h := (@Nat.cast_inj ℝ _ _ _ _).mpr <| Eq.symm <|
        deleteIncidenceSet_degree_neighbor_eq G v <| (mem_neighborFinset G v x).mp hx |>.symm
      refine inv_inj.mpr <| (@Nat.cast_add_one ℝ _ _) ▸ h
    simp only [h]
    calc (∑ x ∈ Nv, ((G.degree x) : ℝ)⁻¹)
      _ = ∑ x ∈ Nv, ((((G.degree x) : ℝ) + 1)⁻¹
          + (((G.degree x) : ℝ) * (((G.degree x) : ℝ) + 1))⁻¹) := by
          refine sum_congr rfl ?_
          intro x hx
          exact _cw_bound_mono _ <| Nat.one_le_cast.mpr <| Nat.lt_of_sub_eq_succ (hdegNv x hx)
      _ = ∑ x ∈ Nv, (((G.degree x) : ℝ) + 1)⁻¹
          + ∑ x ∈ Nv, (((G.degree x) : ℝ) * (((G.degree x) : ℝ) + 1))⁻¹ := by
          exact sum_add_distrib
    simp only [add_le_add_iff_left]
    apply ge_iff_le.mp
    calc ∑ x ∈ Nv, ((((G.degree x) : ℝ)) * (((G.degree x) : ℝ) + 1))⁻¹
      _ ≥ ∑ x ∈ Nv, ((((G.maxDegree) : ℝ)) * (((G.maxDegree) : ℝ) + 1))⁻¹ := by
          refine sum_le_sum ?_
          intro x hx
          have hpos : 0 < G.degree x := by exact Nat.lt_of_sub_eq_succ (hdegNv x hx)
          have hpos' : 0 < ((G.degree x) : ℝ) := by exact Nat.cast_pos'.mpr hpos
          have h : G.degree x ≤ G.maxDegree := by exact degree_le_maxDegree G x
          have h' : ((G.degree x) : ℝ) ≤ (G.maxDegree : ℝ) := by exact Nat.cast_le.mpr h
          exact @_gains _ _ hpos' h'
      _ = #Nv * ((((G.maxDegree) : ℝ)) * (((G.maxDegree) : ℝ) + 1))⁻¹ := by
          exact sum_const' Nv fun x ↦ congrFun rfl
      _ = (G.maxDegree) * ((((G.maxDegree) : ℝ)) * (((G.maxDegree) : ℝ) + 1))⁻¹ := by
          simp_all only []
      _ = (((G.maxDegree) : ℝ) + 1)⁻¹ := by
          simp only [mul_inv_rev]
          rw [← mul_comm _ _]
          exact inv_mul_cancel_right₀ (Nat.cast_ne_zero.mpr <| Nat.ne_zero_of_lt hΔ) _
      _ = (G.degree v + 1 : ℝ)⁻¹ := by
          simp [hdegv]
  calc (∑ x ∈ (X \ {v}), ((G.deleteIncidenceSet v).degree x + 1 : ℝ)⁻¹)
    _ = ∑ x ∈ (X \ {v}) \ Nv, ((G.deleteIncidenceSet v).degree x + 1 : ℝ)⁻¹
      + ∑ x ∈ Nv, ((G.deleteIncidenceSet v).degree x + 1 : ℝ)⁻¹ := by
        refine Eq.symm (sum_sdiff ?_)
        intro x hx
        simp only [mem_sdiff, mem_singleton]
        refine ⟨?_, ne_of_mem_of_not_mem hx <| notMem_neighborFinset_self G v⟩
        · by_contra
          let hdegx0 := hout x <| mem_sdiff.mpr ⟨mem_univ x, this⟩
          exact Nat.not_succ_le_zero 0
            <| hdegx0 ▸ (Adj.degree_pos_left ((mem_neighborFinset G v x).mp hx).symm)
    _ = ∑ x ∈ ((X \ {v}) \ Nv), (G.degree x + 1 : ℝ)⁻¹
      + ∑ x ∈ Nv, ((G.deleteIncidenceSet v).degree x + 1 : ℝ)⁻¹ := by
        simp only [add_left_inj]
        refine sum_congr rfl ?_
        intro x hx
        simp only [inv_inj, add_left_inj, Nat.cast_inj]
        suffices (G.deleteIncidenceSet v).neighborFinset x = G.neighborFinset x by
          rw [degree, degree]
          exact congrArg card this
        ext w
        simp only [deleteIncidenceSet, mem_neighborFinset, deleteEdges_adj, incidenceSet]
        constructor
        · exact fun hw ↦ hw.left
        · intro hw
          refine ⟨hw, ?_⟩
          have _ : v ≠ x ∧ v ≠ w := by
            refine ⟨by grind, ?_⟩
            exact fun h ↦ (mem_sdiff.mp hx).right <| (mem_neighborFinset G v x).mpr (h ▸ hw).symm
          simp_all
    _ = ∑ x ∈ X \ ({v} ∪ Nv), (G.degree x + 1 : ℝ)⁻¹
      + ∑ x ∈ Nv, ((G.deleteIncidenceSet v).degree x + 1 : ℝ)⁻¹ := by
        suffices X \ ({v} ∪ Nv) = (X \ {v}) \ Nv by
          simp only [add_left_inj]
          rw [← this]
        ext _
        simp_all only [singleton_union, mem_sdiff, mem_singleton, mem_insert, not_or]
        apply Iff.intro
        all_goals exact fun _ ↦ by simp_all
    _ ≥ ∑ x ∈ X \ ({v} ∪ Nv), (G.degree x + 1 : ℝ)⁻¹
      + (∑ x ∈ Nv, (G.degree x + 1 : ℝ)⁻¹ + (G.degree v + 1 : ℝ)⁻¹) := by
        simp only [singleton_union, ge_iff_le, add_le_add_iff_left, hsumNv]
    _ = ∑ x ∈ X \ ({v} ∪ Nv), (G.degree x + 1 : ℝ)⁻¹
      + ∑ x ∈ (Nv ∪ {v}), (G.degree x + 1 : ℝ)⁻¹ := by
        have hdisjoint : Nv ∩ {v} = ∅ := v_notin_neighbors
        simp only [singleton_union, add_right_inj]
        apply Eq.symm
        let bla := @sum_union_inter V ℝ Nv {v} _ (fun x ↦ ((G.degree x + 1) : ℝ)⁻¹) _
        simp only [hdisjoint, Finset.sum_empty, add_zero, sum_singleton] at bla
        exact bla
    _ = ∑ x ∈ X \ ({v} ∪ Nv), (G.degree x + 1 : ℝ)⁻¹
      + ∑ x ∈ ({v} ∪ Nv), (G.degree x + 1 : ℝ)⁻¹ := by
        simp_all only [mem_sdiff, mem_univ, true_and, Nat.cast_add, Nat.cast_one, ge_iff_le,
          singleton_union, union_singleton]
    _ = ∑ x ∈ X, (G.degree x + 1 : ℝ)⁻¹ := by
        refine @sum_sdiff V ℝ ({v} ∪ Nv) X _ (fun x ↦ ((G.degree x + 1) : ℝ)⁻¹) _ ?_
        intro x hx
        simp only [singleton_union, mem_insert] at hx
        cases hx with
        | inl h =>
            by_contra
            exact Nat.not_succ_le_zero 0
              <| Nat.lt_of_lt_of_eq hΔ <| hdegv ▸ (h ▸ (hout x (by simp [this])))
        | inr h => exact hNv h

open Classical in
private theorem _CaroWei (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    (hout : ∀ w ∈ (Finset.univ \ X), G.degree w = 0) :
    ∃ s : Finset V, s ⊆ X ∧ G.IsIndepSet s ∧ ∑ v ∈ X, (G.degree v + 1 : ℝ)⁻¹ ≤ #s := by
  rcases eq_zero_or_pos #X with h0 | hcard_ge_1
  · have hXempty : X = ∅ := by exact Finset.card_eq_zero.mp h0
    exact ⟨∅, by simp, by simp, by simp [hXempty]⟩
  · cases Classical.em <| 0 = G.maxDegree with
    | inl hΔ =>
        refine ⟨X, by simp, ?_, ?_⟩
        · intro x _ _ _ _ hxy
          exact Nat.not_succ_le_zero _
            <| Nat.lt_of_lt_of_le (Adj.degree_pos_left hxy) (hΔ ▸ (G.degree_le_maxDegree x))
        · have h {x} : (G.degree x : ℝ) = 0 := by
            rw [← AddMonoidWithOne.natCast_zero]
            exact (@Nat.cast_inj ℝ _ _ (G.degree x) (0 : ℕ)).mpr
              <| Nat.eq_zero_of_le_zero <| le_of_le_of_eq (G.degree_le_maxDegree x) hΔ.symm
          have hfeq1 : ∀ x ∈ X, (G.degree x + 1 : ℝ)⁻¹ = 1 := fun _ _ ↦ by simp_all
          simp [sum_const' X hfeq1]
    | inr hΔ => ?_
    have _ : Nonempty X := Nonempty.to_subtype <| Finset.card_pos.mp hcard_ge_1
    have _ : Nonempty V := Nonempty.intro <| Classical.arbitrary X
    obtain ⟨v, hdegv_is_max⟩ := G.exists_maximal_degree_vertex
    have hvX : v ∈ X := by grind
    let G' := G.deleteIncidenceSet v
    have hout' : ∀ w ∈ (Finset.univ \ (X \ {v})), G'.degree w = 0 := by
      intro w hw
      simp_all only [mem_sdiff, mem_univ, true_and, Finset.card_pos, nonempty_subtype,
        mem_singleton, not_and, Decidable.not_not]
      cases Classical.em <| w ∈ X with
      | inl hwX =>
          rw [hw hwX]
          by_contra
          obtain ⟨x, hadjx⟩ := (degree_pos_iff_exists_adj G' v).mp <| Nat.zero_lt_of_ne_zero this
          simp [G', deleteIncidenceSet] at hadjx
      | inr hnotwX =>
          simp only [G']
          have hdegw0 : G.degree w = 0 := hout w hnotwX
          calc ((G.deleteIncidenceSet v).degree w)
            _ = G.degree w := by
                apply Eq.symm
                refine deleteIncidenceSet_degree_nonneighbor_eq G v ?_ ?_
                · exact fun hadj ↦ Nat.ne_zero_of_lt (Adj.degree_pos_left hadj) <| hdegw0
                · exact fun heq ↦ hnotwX <| (heq ▸ hvX)
            _ = 0 := hdegw0
    let ⟨s', ⟨hs', hs'_ind, hs'_card⟩⟩ := _CaroWei G' (X \ {v}) hout'
    use s'
    have hG'_adj {u w : V} : G'.Adj u w ↔ G.Adj u w ∧ u ≠ v ∧ w ≠ v :=
      @deleteIncidenceSet_adj V G v u w
    refine ⟨?_, ?_, ?_⟩
    · exact hs'.trans sdiff_subset  -- s ⊆ X
    · intro x hx y hy hne  -- s is independent set
      have _ : ¬G'.Adj x y := Not.intro (hs'_ind hx hy hne)
      have _ : x ≠ v ∧ y ≠ v := by grind
      simp_all
    · let Nv := G.neighborFinset v  -- #s ≥ f(G)
      have hΔ : 0 < G.maxDegree := by exact Nat.zero_lt_of_ne_zero fun a ↦ hΔ (Eq.symm a)
      exact le_trans (cw_bound_mono G hdegv_is_max hΔ hout) hs'_card
    termination_by #X decreasing_by
    exact (card_setminus_singleton hvX) ▸ (Nat.sub_one_lt_of_lt hcard_ge_1)

open Classical in
theorem CaroWei (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ s : Finset V,
      G.IsIndepSet s ∧ ∑ v, (G.degree v + 1 : ℝ)⁻¹ ≤ #s := by
  obtain ⟨s, hs, hind, hcard⟩ := _CaroWei G univ (by simp)
  exact ⟨s, hind, hcard⟩

end SimpleGraph
