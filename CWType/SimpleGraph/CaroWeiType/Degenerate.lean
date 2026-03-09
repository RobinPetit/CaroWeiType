-- import Mathlib

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Nat.Cast.Order.Field

import CWType.SimpleGraph.CaroWeiType.Basic
import CWType.SimpleGraph.CaroWeiType.Lemmas

noncomputable def aks_bound (k : ℕ) (d : ℕ) : ℝ :=
  min 1 ((k + 1) * (d + 1 : ℝ)⁻¹)

lemma one_le_mul' {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : 1 ≤ y * x⁻¹ := by
  calc 1
    _ = x * x⁻¹ := by exact Eq.symm <| mul_inv_cancel₀ (ne_of_gt hx)
    _ ≤ y * x⁻¹ := by
      simp only [Right.inv_pos.mpr hx, mul_le_mul_iff_left₀]
      exact hxy

lemma mul_le_one {x y : ℝ} (hx : 0 < x) (hxy : y ≤ x) : y * x⁻¹ ≤ 1 := by
  calc y * x⁻¹
    _ ≤ x * x⁻¹ := by
      simp only [Right.inv_pos.mpr hx, mul_le_mul_iff_left₀]
      exact hxy
    _ = 1 := by exact mul_inv_cancel₀ (ne_of_gt hx)

lemma aks_bound_eq (k : ℕ) (d : ℕ) (hd : d ≤ k) : aks_bound k d = 1 := by
  refine inf_eq_left.mpr ?_
  suffices (d + 1 : ℝ) ≤ (k + 1 : ℝ) by exact one_le_mul' d.cast_add_one_pos this
  simp only [add_le_add_iff_right, Nat.cast_le, hd]

lemma aks_bound_eq' (k : ℕ) (d : ℕ) (hd : k ≤ d) : aks_bound k d = (k + 1 : ℝ) * (d + 1 : ℝ)⁻¹ := by
  refine inf_eq_right.mpr ?_
  suffices (k + 1 : ℝ) ≤ (d + 1: ℝ) by exact mul_le_one d.cast_add_one_pos this
  simp only [add_le_add_iff_right, Nat.cast_le, hd]

theorem aks_bound_decreasing (k : ℕ) (d : ℕ) :
    aks_bound k (d + 1) ≤ aks_bound k d := by
  if hdk : d ≤ k then
    simp only [aks_bound_eq k d hdk]
    exact min_le_left ..
  else
    simp only [not_le] at hdk
    simp only [aks_bound_eq' k d (le_of_lt hdk)]
    calc aks_bound k (d + 1)
      _ ≤ (k + 1 : ℝ) * ((d + 1 : ℕ) + 1 : ℝ)⁻¹ := min_le_right 1 _
      _ ≤ (k + 1 : ℝ) * (d + 1 : ℝ)⁻¹ := by
        simp only [Nat.cast_add, Nat.cast_one]
        simp only [k.cast_add_one_pos, mul_le_mul_iff_right₀]
        refine (inv_le_inv₀ (by grind) d.cast_add_one_pos).mpr ?_
        simp only [le_add_iff_nonneg_right, zero_le_one]

theorem aks_bound_decreasing' (k : ℕ) :
    ∀ d d', d ≤ d' → aks_bound k d' ≤ aks_bound k d := by
  intro d d' hdd'
  induction h : (d' - d) generalizing d with
  | zero =>
      have heq : d' = d := Nat.le_antisymm (Nat.le_of_sub_eq_zero h) hdd'
      subst heq
      exact le_refl _
  | succ n ih =>
      refine le_trans ?_ (aks_bound_decreasing k _)
      have h' : d + 1 ≤ d' := by
        simp only [Order.add_one_le_iff]
        exact Nat.lt_of_sub_eq_succ h
      exact ih (d + 1) h' (by grind)

theorem aks_gain_decreasing (k : ℕ) (d : ℕ) (hd : k < d) :
    aks_bound k d - aks_bound k (d + 1) ≤ aks_bound k (d - 1) - aks_bound k d := by
  have _ : k ≤ d-1 := Nat.le_sub_one_of_lt hd
  simp only [aks_bound_eq' k (d - 1) (Nat.le_sub_one_of_lt hd)]
  simp only [aks_bound_eq' k d (le_of_lt hd)]
  simp only [aks_bound_eq' k (d + 1) (by grind)]
  suffices (d + 1 : ℝ)⁻¹ - ((d + 1 : ℕ) + 1 : ℝ)⁻¹ ≤ ((d - 1 : ℕ) + 1 : ℝ)⁻¹ - (d + 1 : ℝ)⁻¹ by
    calc (k + 1 : ℝ) * (d + 1 : ℝ)⁻¹ - (k + 1 : ℝ) * ((d + 1 : ℕ) + 1 : ℝ)⁻¹
      _ = (k + 1 : ℝ) * ((d + 1 : ℝ)⁻¹ - ((d + 1 : ℕ) + 1 : ℝ)⁻¹) :=
        Eq.symm <| mul_sub_left_distrib ..
      _ ≤ (k + 1 : ℝ) * (((d - 1 : ℕ) + 1 : ℝ)⁻¹ - (d + 1 : ℝ)⁻¹) :=
        mul_le_mul_iff_of_pos_left k.cast_add_one_pos |>.mpr this
      _ = (k + 1 : ℝ) * ((d - 1 : ℕ) + 1 : ℝ)⁻¹ - (k + 1 : ℝ) * (d + 1 : ℝ)⁻¹ := by
        exact mul_sub_left_distrib ..
  rw [discrete_derivative_inv_eq d (Nat.zero_lt_of_lt hd)]
  let bla := Nat.add_sub_self_right d 1 ▸ discrete_derivative_inv_eq (d + 1) d.zero_lt_succ
  rw [bla]
  simp only [mul_inv_rev, Nat.cast_add, Nat.cast_one, ge_iff_le]
  calc (d + 1 + 1 : ℝ)⁻¹ * (d + 1 : ℝ)⁻¹
    _ ≤ (d + 1 + 1 : ℝ)⁻¹ * (d : ℝ)⁻¹ := by
      refine (mul_le_mul_iff_of_pos_left ?_).mpr ?_
      · refine Right.inv_pos.mpr (by grind)
      · refine inv_anti₀ ?_ ?_
        · simp only [Nat.cast_pos]
          exact Nat.zero_lt_of_lt hd
        · simp only [le_add_iff_nonneg_right, zero_le_one]
    _ ≤ (d + 1 : ℝ)⁻¹ * (d : ℝ)⁻¹ := by
      refine (mul_le_mul_iff_of_pos_right ?_).mpr ?_
      · simp only [inv_pos, Nat.cast_pos]
        exact Nat.zero_lt_of_lt hd
      · refine inv_anti₀ ?_ ?_
        · exact Nat.cast_add_one_pos d
        · simp only [le_add_iff_nonneg_right, zero_le_one]

theorem aks_gain_decreasing' (k : ℕ) (d d' : ℕ) (hd : k < d) (hd' : d ≤ d') :
    aks_bound k (d' - 1) - aks_bound k d' ≤ aks_bound k (d - 1) - aks_bound k d := by
  induction h : (d' - d) generalizing d with
  | zero =>
      have heq : d' = d := Nat.le_antisymm (Nat.le_of_sub_eq_zero h) hd'
      subst heq
      exact le_refl _
  | succ n ih =>
      refine le_trans ?_ (aks_gain_decreasing k _ hd)
      have h' : d + 1 ≤ d' := by
        simp only [Order.add_one_le_iff]
        exact Nat.lt_of_sub_eq_succ h
      exact ih (d + 1) (Nat.lt_add_right 1 hd) h' (by grind)

open Finset

namespace SimpleGraph

abbrev IsDegenerateSet {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (s : Finset V) :=
  ∀ t ⊆ s, t ≠ ∅ → ∃ x ∈ t, {y ∈ t | G.Adj x y}.card ≤ k

lemma isDegenerate_mono {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (s : Finset V) : G.IsDegenerateSet k s → ∀ s' ⊆ s, G.IsDegenerateSet k s' := by
  intro h s' hs' t ht htnonempty
  exact h t (subset_trans ht hs') htnonempty

@[simp]
lemma emptyset_IsDegenerate {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ k : ℕ, G.IsDegenerateSet k ∅ := by
  intro k
  simp [IsDegenerateSet]

theorem Is1DegenerateSet_iff_IsIndepSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) :
    G.IsDegenerateSet 0 s ↔ G.IsIndepSet s := by
  constructor
  · intro h x hx y hy hne hxy
    obtain ⟨z, ⟨hz, h⟩⟩ := h {x, y} (by grind) (by simp)
    simp only [mem_insert, mem_singleton] at hz
    simp only [nonpos_iff_eq_zero, card_eq_zero, filter_eq_empty_iff, mem_insert, mem_singleton,
      forall_eq_or_imp, forall_eq] at h
    cases hz with
    | inl hz => exact h.2 (hz ▸ hxy)
    | inr hz => exact h.1 <| (hz ▸ hxy.symm)
  · intro h s' hs' hs'ne
    obtain x := @Classical.choice s' <| Nonempty.to_subtype (by grind)
    refine ⟨x.1, x.2, ?_⟩
    simp only [nonpos_iff_eq_zero, card_eq_zero, filter_eq_empty_iff]
    intro y hy
    if hxy : x = y then
      exact hxy.symm ▸ G.irrefl
    else
      exact h (hs' x.2) (hs' hy) hxy

namespace CaroWeiType

theorem kDegenerateSetClique_iff_le_k_plus_one (k : ℕ) {n : ℕ} (s : Finset (Fin n))
    [DecidableRel (completeGraph (Fin n)).Adj] :
    (completeGraph (Fin n)).IsDegenerateSet k s ↔ s.card ≤ k + 1 := by
  constructor
  · intro h
    let K' := FiniteCompleteGraph (n + 1)
    let _ := K'.decAdj
    if hs : s = ∅ then
      simp only [hs, card_empty, le_add_iff_nonneg_left, zero_le]
    else
    obtain ⟨x, ⟨hx, hcard⟩⟩ := h s (subset_refl s) hs
    simp at hcard
    suffices s = {y ∈ s | ¬x = y} ∪ {x} by grind
    grind
  · intro h s' hs' hne
    obtain x := @Classical.choice s' <| Nonempty.to_subtype (by grind)
    refine ⟨x.1, x.2, ?_⟩
    simp only [completeGraph_eq_top, top_adj, ne_eq]
    calc {y ∈ s' | ¬x.1 = y}.card
      _ = (s' \ {x.1}).card := by
        refine congrArg _ ?_
        grind
      _ = s'.card - ({x.1} : Finset (Fin n)).card := by
        exact card_sdiff_of_subset (by simp)
      _ ≤ s.card - 1 := by
        exact Nat.sub_le_sub_right (card_le_card hs') _
      _ ≤ k := by grind

lemma neighbourFinset_cap_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (v : V) :
    {x ∈ s | G.Adj v x} = G.neighborFinset v ∩ s := by
  ext x
  constructor <;>
    { simp only [mem_filter, mem_inter, mem_neighborFinset, and_imp, p_and_p_implies];
      exact fun a _ ↦ a }

theorem DegenerateSet_mono_bounded_degree_not_in {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (s : Finset V) {v : V}
    (hs : (G.deleteIncidenceSet v).IsDegenerateSet k s)
    (hvs : v ∉ s) :
    G.IsDegenerateSet k s := by
  intro t ht htne
  have hvt : v ∉ t := fun this ↦ hvs <| ht this
  obtain ⟨x, ⟨hxt, hcard⟩⟩ := hs t ht htne
  refine ⟨x, hxt, ?_⟩
  refine le_trans ?_ hcard
  refine Finset.card_le_card ?_
  intro y hy
  simp_all only [deleteIncidenceSet, incidenceSet, ne_eq, deleteEdges_adj, Set.mem_setOf_eq,
    mem_edgeSet, Sym2.mem_iff, not_and, not_or, mem_filter, forall_const, true_and]
  constructor
  · exact fun hveqx ↦ hvt (hveqx ▸ hxt)
  · exact fun hveqx ↦ hvt (hveqx ▸ hy.1)

theorem DegenerateSet_mono_bounded_degree_in {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (s : Finset V) {v : V}
    (hs : (G.deleteIncidenceSet v).IsDegenerateSet k s)
    (hv : (G.neighborFinset v ∩ s).card ≤ k) :
    G.IsDegenerateSet k s := by
  intro t ht htne
  if hvt : v ∈ t then
    refine ⟨v, hvt, ?_⟩
    let bla := hs t ht htne
    calc #({y ∈ t | G.Adj v y})
      _ = (G.neighborFinset v ∩ t).card := congrArg _ <| neighbourFinset_cap_eq G t v
      _ ≤ (G.neighborFinset v ∩ s).card :=
        Finset.card_le_card <| Finset.inter_subset_inter (subset_refl _) ht
      _ ≤ k := hv
  else
    obtain ⟨x, ⟨hxt, hcard⟩⟩ := hs t ht htne
    refine ⟨x, hxt, ?_⟩
    refine le_trans ?_ hcard
    refine Finset.card_le_card ?_
    intro y hy
    simp_all only [deleteIncidenceSet, incidenceSet, ne_eq, deleteEdges_adj, Set.mem_setOf_eq,
      mem_edgeSet, Sym2.mem_iff, not_and, not_or, mem_filter, forall_const, true_and]
    constructor
    · exact fun hveqx ↦ hvt (hveqx ▸ hxt)
    · exact fun hveqx ↦ hvt (hveqx ▸ hy.1)


theorem DegenerateSet_union_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (s : Finset V)
    (hs : G.IsDegenerateSet k s) {v : V} (hv : (G.neighborFinset v ∩ s).card ≤ k) :
    G.IsDegenerateSet k (s ∪ {v}) := by
  intro t ht htne
  if hvt : v ∈ t then
    refine ⟨v, ⟨hvt, ?_⟩⟩
    calc #({y ∈ t | G.Adj v y})
      _  ≤ #({y ∈ s | G.Adj v y}) := by
        refine Finset.card_le_card ?_
        intro y hy
        simp only [mem_filter] at hy ⊢
        refine ⟨?_, hy.2⟩
        let hys : y ∈ s ∪ {v} := ht hy.1
        simp only [union_singleton, mem_insert] at hys
        cases hys with
        | inl hys => exact hy.2.ne' hys |>.elim
        | inr hys => exact hys
      _ = #(G.neighborFinset v ∩ s) := by
        refine congrArg _ ?_
        ext y
        constructor <;>
          { intro hy
            simp only [mem_filter, mem_inter, mem_neighborFinset] at hy ⊢
            exact And.comm.mp hy }
      _ ≤ k := hv
  else
    have hts' : t ⊆ s := by
      intro x hx
      let hxs := ht hx
      simp only [union_singleton, mem_insert] at hxs
      cases hxs with
      | inl hxs => exact hvt (hxs ▸ hx) |>.elim
      | inr hxs => exact hxs
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := hs t hts' htne
    refine ⟨x, hx1, ?_⟩
    suffices ({y ∈ t | (G.deleteIncidenceSet v).Adj x y}) = ({y ∈ t | G.Adj x y}) by
      exact this ▸ hx2
    simp only [deleteIncidenceSet, incidenceSet, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet,
      Sym2.mem_iff, not_and, not_or]
    ext y
    constructor
    · intro hy
      simp only [mem_filter] at hy ⊢
      exact ⟨hy.1, hy.2.1⟩
    · intro hy
      simp only [mem_filter] at hy ⊢
      refine ⟨hy.1, hy.2, ?_⟩
      intro _
      constructor <;> refine fun heq ↦ hvt ?_
      · exact heq ▸ hx1
      · exact heq ▸ hy.1

-- Alon, Noga, Jeff Kahn, and Paul D. Seymour.
-- "Large induced degenerate subgraphs."
-- Graphs and Combinatorics 3, no. 1 (1987): 203-211.
theorem AlonKahnSeymour {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (X : Finset (Fin n)) (hX : G.support ⊆ X) :
    ∃ s : Finset (Fin n),
      s ⊆ X ∧ G.IsDegenerateSet k s ∧ ∑ v ∈ X, aks_bound k (G.degree v) ≤ s.card := by
  induction hcard : #X generalizing G X with
  | zero => refine ⟨∅, by simp, by simp [IsDegenerateSet], by simp_all⟩
  | succ m ih => ?_
  have hX' : X.Nonempty := card_pos.mp <| Nat.lt_of_sub_eq_succ hcard
  have _ : Nonempty X := by exact Nonempty.to_subtype hX'
  have _ : Nonempty (Fin n) := Exists.nonempty hX'
  obtain ⟨v, ⟨hvX, hdegv⟩⟩ := G.exists_minimal_degree_vertex_in X
  if hδ : (G.neighborFinset v ∩ X).card ≤ k then
    obtain ⟨s', ⟨hs', hdeg', hcard'⟩⟩ :=
      ih (G.deleteIncidenceSet v) (X \ {v}) (deleteIncidenceSet_support G X hX)
        (card_setminus_singleton' hvX hcard)
    refine ⟨s' ∪ {v}, ?_, ?_, ?_⟩
    · intro x hx
      simp only [union_singleton, mem_insert] at hx
      cases hx with
      | inl hx => exact hx ▸ hvX
      | inr hx => exact mem_sdiff.mp (hs' hx) |>.1
    · have hcard_le_k : #(G.neighborFinset v ∩ s') ≤ k := by
        refine le_trans (Finset.card_le_card <| Finset.inter_subset_inter (subset_refl _) ?_) hδ
        exact fun w hw ↦ mem_sdiff.mp (hs' hw) |>.1
      refine DegenerateSet_union_singleton G k s'  ?_ hcard_le_k
      exact DegenerateSet_mono_bounded_degree_in G k _ hdeg' (hcard_le_k)
    · have hvs' : v ∉ s' := by
        intro this
        let hobj := mem_sdiff.mp (hs' this) |>.2
        simp at hobj
      simp only [union_singleton, hvs', not_false_eq_true, card_insert_of_notMem, Nat.cast_add,
        Nat.cast_one, ge_iff_le]
      refine le_trans (cw_bound_deleteIncidenceSet_le (aks_bound k) G _ hvX ?_) ?_
      · intro d d' hdd'
        exact aks_bound_decreasing' k d d' hdd'
      · calc ∑ x ∈ X \ {v}, aks_bound k ((G.deleteIncidenceSet v).degree x)
            + aks_bound k (G.degree v)
          _ ≤ ↑(#s') + aks_bound k (G.degree v) := by
            simp only [add_le_add_iff_right]
            exact hcard'
          _ ≤ ↑(#s') + 1 := by
            simp only [add_le_add_iff_left]
            exact min_le_left ..
  else ?_
  simp only [not_le] at hδ
  obtain ⟨v', ⟨hv'X, hdegv'⟩⟩ := G.exists_maximal_degree_vertex_in X
  obtain ⟨s', ⟨hs', ⟨hdeg', hcard'⟩⟩⟩ :=
    ih (G.deleteIncidenceSet v') (X \ {v'}) (deleteIncidenceSet_support G X hX)
     (card_setminus_singleton' hv'X hcard)
  refine ⟨s', subset_eq_inter hs', ?_, ?_⟩
  · refine DegenerateSet_mono_bounded_degree_not_in G k s' hdeg' ?_
    exact fun this ↦ Finset.mem_sdiff.mp (hs' this) |>.2 <| mem_singleton.mpr rfl
  · refine le_trans ?_ hcard'
    have hvΔ : G.degree v' = G.maxDegree := by
      refine G.maxDegree_iff.mpr ?_
      intro w
      if hw : w ∈ G.support then
        simp only [G.degree_eq X hX]
        exact hdegv' w (hX hw)
      else
        rw [degree_eq_zero_iff_notMem_support G w |>.mpr hw]
        exact Nat.zero_le _
    have hΔk : G.maxDegree > k := by
      rw [← hvΔ]
      refine lt_of_le_of_lt' ?_ hδ
      rw [G.degree_eq _ hX]
      exact hdegv' _ hvX
    refine cw_bound_mono (aks_bound k) G hvΔ hΔk X hX ?_ ?_ ?_
    · intro d₁ d₂ hd₁ hd₂
      exact aks_gain_decreasing' k d₁ d₂ hd₁ hd₂
    · intro x hx
      simp_all only [gt_iff_lt]
      calc k
        _ < #(G.neighborFinset v ∩ X) := hδ
        _ ≤ #(G.neighborFinset x ∩ X) := by
          refine hdegv x (hX ?_)
          refine G.degree_pos_iff_mem_support x |>.mp ?_
          exact Adj.degree_pos_left <| (G.mem_neighborFinset v' x).mp hx |>.symm
        _ ≤ G.degree x := by
          rw [G.degree_eq X hX x]
    · intro d hd
      simp only [aks_bound_eq' k (d-1) (Nat.le_sub_one_of_lt hd)]
      simp only [aks_bound_eq' k d (le_of_lt hd)]
      suffices (d + 1 : ℝ)⁻¹ ≤ (d : ℝ) * (((d - 1 : ℕ) + 1 : ℝ)⁻¹ - (d + 1 : ℝ)⁻¹) by
        calc (k + 1 : ℝ) * (d + 1 : ℝ)⁻¹
          _ ≤ (k + 1 : ℝ) * ((d : ℝ) * (((d - 1 : ℕ) + 1 : ℝ)⁻¹ - (d + 1 : ℝ)⁻¹)) := by
            simp only [Nat.cast_add_one_pos k, mul_le_mul_iff_right₀, this]
          _ ≤ (d : ℝ) * ((k + 1 : ℝ) * ((d - 1 : ℕ) + 1 : ℝ)⁻¹ - (k + 1 : ℝ) * (d + 1 : ℝ)⁻¹) := by
            grind
      refine le_of_eq ?_
      exact Eq.symm <| avg_gain d (by exact Nat.zero_lt_of_lt hd)

theorem IndepSet_LowerBound_iff_1DegenerateSet_LowerBound (f : ℕ → ℝ) :
    IsCaroWeiTypeLowerBound f (fun G s ↦ G.graph.IsIndepSet s)
      ↔ IsCaroWeiTypeLowerBound f (fun G s ↦ G.graph.IsDegenerateSet 0 s) := by
  constructor <;> refine fun h n G ↦ ⟨h G |>.choose, ?_⟩
  · obtain ⟨hsprop, hscard⟩ := h G |>.choose_spec
    refine ⟨?_, hscard⟩
    exact Is1DegenerateSet_iff_IsIndepSet G.graph _ |>.mpr hsprop
  · obtain ⟨hsprop, hscard⟩ := h G |>.choose_spec
    refine ⟨?_, hscard⟩
    exact Is1DegenerateSet_iff_IsIndepSet G.graph _ |>.mp hsprop

theorem DegenerateSet_LowerBound (k : ℕ) :
    IsCaroWeiTypeLowerBound (aks_bound k) (fun G s ↦ G.graph.IsDegenerateSet k s) := by
  intro n G
  obtain ⟨s, ⟨_, ⟨hdeg, hcard⟩⟩⟩ := AlonKahnSeymour G.graph k univ (by simp)
  exact ⟨s, hdeg, hcard⟩

theorem kDegenerateSet_LowerBound_iff (f : ℕ → ℝ) :
    ∀ k : ℕ,
      IsCaroWeiTypeLowerBound f (fun G s ↦ G.graph.IsDegenerateSet k s)
        ↔ f ≤ aks_bound k := by
  intro k
  refine ⟨?_, fun hf ↦ CaroWeiTypeLowerBound_mono hf <| DegenerateSet_LowerBound k⟩
  intro hf d
  unfold IsCaroWeiTypeLowerBound at hf
  simp only [aks_bound]
  refine le_min ?_ ?_
  · exact (CaroWeiTypeLB_le_1 f hf d)
  · suffices (d + 1) * f d ≤ k + 1 by
      if hfd : 0 = f d then
        refine le_of_lt ?_
        exact (hfd) ▸ (Left.mul_pos (Nat.cast_add_one_pos _) Nat.inv_pos_of_nat)
      else ?_
      calc f d
        _ = 1 * f d := by simp only [one_mul]
        _ = (d + 1 : ℝ)⁻¹ * (d + 1 : ℝ) * f d := by
          have _ : 0 ≠ (d + 1 : ℝ) := Ne.symm (Nat.cast_add_one_ne_zero d)
          have hfd : 0 ≠ f d := by grind
          refine mul_left_inj' (Ne.symm hfd) |>.mpr ?_
          exact Eq.symm <| inv_mul_cancel₀ <| Nat.cast_add_one_ne_zero d
        _ = (d + 1 : ℝ)⁻¹ * ((d + 1 : ℝ) * f d) := by grind
        _ ≤ (d + 1 : ℝ)⁻¹ * (k + 1) := by
          have h' : 0 < (d + 1 : ℝ)⁻¹ := Nat.inv_pos_of_nat
          simp only [h', mul_le_mul_iff_right₀, ge_iff_le]
          exact this
        _≤ (k + 1) * (d + 1 : ℝ)⁻¹ := by grind
    let K' := FiniteCompleteGraph (d + 1)
    let _ := K'.decAdj
    obtain ⟨s, ⟨hdeg, hcard⟩⟩ := hf K'
    let bla := kDegenerateSetClique_iff_le_k_plus_one k s |>.mp hdeg
    let bla' := (@bound_of_completeGraph f d _) ▸ hcard
    calc (d + 1 : ℝ) * f d
      _ ≤ (s.card : ℝ) := (@bound_of_completeGraph f d _) ▸ hcard
      _ ≤ (((k + 1) : ℕ) : ℝ) := by
        refine Nat.cast_le.mpr ?_
        exact kDegenerateSetClique_iff_le_k_plus_one k s |>.mp hdeg
      _ ≤ (k + 1 : ℝ) := by grind

end CaroWeiType
end SimpleGraph

#min_imports
