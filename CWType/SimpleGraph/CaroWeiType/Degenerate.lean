import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Nat.Cast.Order.Field

import CWType.SimpleGraph.CaroWeiType.Basic
import CWType.SimpleGraph.CaroWeiType.Lemmas

open CaroWeiType

noncomputable def aks_bound (k : ℕ) (d : ℕ) : ℝ :=
  min 1 ((k + 1) * (d + 1 : ℝ)⁻¹)

lemma one_le_mul' {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : 1 ≤ y * x⁻¹ := by
  calc 1
    _ = x * x⁻¹ := Eq.symm <| mul_inv_cancel₀ (ne_of_gt hx)
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
        refine (inv_le_inv₀ add_one_add_one_pos add_one_pos).mpr ?_
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
      exact ih (d + 1) h' (by grind only)

theorem aks_gain_decreasing (k : ℕ) (d : ℕ) (hd : k < d) :
    aks_bound k d - aks_bound k (d + 1) ≤ aks_bound k (d - 1) - aks_bound k d := by
  have _ : k ≤ d-1 := Nat.le_sub_one_of_lt hd
  simp only [aks_bound_eq' k (d - 1) (Nat.le_sub_one_of_lt hd)]
  simp only [aks_bound_eq' k d (le_of_lt hd)]
  simp only [aks_bound_eq' k (d + 1) (by linarith)]
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
      · refine Right.inv_pos.mpr add_one_add_one_pos
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
      exact ih (d + 1) (Nat.lt_add_right 1 hd) h' (by grind only)

open Finset

namespace SimpleGraph

abbrev IsDegenerateSet {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (s : Finset V) :=
  ∀ t ⊆ s, t ≠ ∅ → ∃ x ∈ t, G.degree_in t x ≤ k

end SimpleGraph

open SimpleGraph
namespace GraphParameter

universe u u' in
lemma IsDegenerateSet_of_graph_iso {k : ℕ} {V : Type u} {V' : Type v}
    [DecidableEq V] [DecidableEq V'] [Fintype V] [Fintype V']
    {G : SimpleGraph V} {G' : SimpleGraph V'} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (φ : G ≃g G') (s : Finset V) (hs : G.IsDegenerateSet k s) :
    G'.IsDegenerateSet k (s.image φ.toFun) := by
  intro t' ht' ht'ne
  obtain ⟨x, hx, hdx⟩ := by
    refine hs (t'.image φ.invFun) ?_ (not_iff_not.mpr image_eq_empty |>.mpr ht'ne)
    intro x hx
    suffices φ.toFun x ∈ image φ.toFun s by
      simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, mem_image,
        EmbeddingLike.apply_eq_iff_eq, exists_eq_right] at this
      exact this
    refine ht' ?_
    suffices φ.invFun (φ.toFun x) ∈ image φ.invFun t' by
      simp only [Equiv.invFun_as_coe, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, mem_image,
        EmbeddingLike.apply_eq_iff_eq, exists_eq_right] at this
      exact this
    obtain ⟨x', hx't', hx'⟩ := mem_image.mp hx
    simp [← hx', hx't']
  refine ⟨φ.toFun x, ?_, ?_⟩
  · simp only [mem_image] at hx
    obtain ⟨x', hx't', hxx'⟩ := hx
    rw [← hxx']
    simp only [Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.apply_symm_apply, hx't']
  · refine le_of_eq_of_le ?_ hdx
    simp only [degree_in, neighborFinset]
    refine Eq.symm (Set.BijOn.finsetCard_eq φ.toFun ⟨?_, ?_, ?_⟩)
    · intro y hy
      simp only [Equiv.invFun_as_coe, coe_inter, Set.coe_toFinset, coe_image, Set.mem_inter_iff,
        mem_neighborSet, Set.mem_image_equiv, Equiv.symm_symm, RelIso.coe_fn_toEquiv,
        SetLike.mem_coe, Equiv.toFun_as_coe] at hy ⊢
      exact ⟨φ.map_rel_iff'.mpr hy.1, hy.2⟩
    · suffices Function.Injective φ.toFun by
        exact Function.Injective.injOn this
      obtain ⟨hinj, hsurj⟩ : Function.Bijective φ.toFun :=
        Function.bijective_iff_has_inverse.mpr ⟨φ.invFun, φ.left_inv, φ.right_inv⟩
      exact hinj
    · intro u hu
      simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, coe_inter, Set.coe_toFinset,
        Set.mem_inter_iff, mem_neighborSet, SetLike.mem_coe, Equiv.invFun_as_coe, coe_image,
        Set.mem_image, ↓existsAndEq, and_true] at hu ⊢
      refine ⟨u, ⟨?_, hu.2⟩, (RelIso.eq_symm_apply φ).mp rfl⟩
      refine φ.map_rel_iff'.mp ?_
      simp only [RelIso.coe_fn_toEquiv, Equiv.apply_symm_apply, hu.1]

def DegenerateSet (k : ℕ) : GraphParameter where
  toFun := fun G s ↦ G.graph.IsDegenerateSet k s
  invariant := by
    intro V V' _ _ _ _ G G' φ s
    constructor
    · exact fun hs ↦ IsDegenerateSet_of_graph_iso φ s hs
    · intro hs'
      suffices s = ((s.image φ).image φ.symm.toFun) by
        exact this ▸ IsDegenerateSet_of_graph_iso φ.symm (s.image φ) hs'
      ext x
      simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, mem_image, exists_exists_and_eq_and,
        RelIso.symm_apply_apply, exists_eq_right]

end GraphParameter

namespace SimpleGraph

lemma IsDegenerateSet_union {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {k : ℕ}
    (s₁ s₂ : Finset (Fin n)) (hs₁ : G.IsDegenerateSet k s₁) (hs₂ : ∀ x ∈ s₂, G.degree x ≤ k) :
    G.IsDegenerateSet k (s₁ ∪ s₂) := by
  intro t ht htne
  if hcap : t ∩ s₂ ≠ ∅ then
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hcap
    refine ⟨x, mem_inter.mp hx |>.1, ?_⟩
    refine le_trans ?_ <| hs₂ x <| mem_inter.mp hx |>.2
    exact card_le_card <| fun _ ↦ by simpa using p_imp_q_imp_p
  else
    have ht' : t ⊆ s₁ := by
      intro y hy
      rcases mem_union.mp <| ht hy with hy' | hy'
      · exact hy'
      · suffices y ∈ (∅ : Finset _) by exact notMem_empty y this |>.elim
        simp only [ne_eq, Decidable.not_not] at hcap
        rw [← hcap]
        refine mem_inter.mpr ⟨hy, hy'⟩
    exact hs₁ t ht' htne

lemma IsDegenerateSet_union_singleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {k : ℕ}
    (s : Finset (Fin n)) (hs : G.IsDegenerateSet k s) {v : Fin n} (hv : G.degree_in s v ≤ k) :
    G.IsDegenerateSet k (s ∪ {v}) := by
  intro t ht htne
  if hvt : v ∈ t then
    refine ⟨v, hvt, ?_⟩
    refine le_trans ?_ hv
    rw [degree_in_union_self _ s]
    exact degree_in_mono ht
  else
    refine hs t ?_ htne
    intro x hx
    rcases mem_union.mp (ht hx) with hx | hx'
    · exact hx
    · exact hvt ((mem_singleton.mp hx') ▸ hx) |>.elim

lemma IsDegenerateSet_mono {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n))
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hle : G₁ ≤ G₂) (k : ℕ)
    (s : Finset (Fin n)) (h : G₂.IsDegenerateSet k s) : G₁.IsDegenerateSet k s := by
  intro t ht htne
  obtain ⟨x, hx, hxdeg⟩ := h t ht htne
  refine ⟨x, hx, le_trans ?_ hxdeg⟩
  refine Finset.card_le_card ?_
  refine inter_subset_inter ?_ (subset_refl _)
  intro y hy
  simp only [mem_neighborFinset] at hy ⊢
  exact hle hy

lemma IsDegenerateSet_mono' {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (s₁ s₂ : Finset (Fin n)) (hs : s₁ ∩ s₂ = ∅) [DecidableRel (G.deleteIncidencesOf s₂).Adj]
    (h : (G.deleteIncidencesOf s₂).IsDegenerateSet k s₁) :
    G.IsDegenerateSet k s₁ := by
  intro t ht htne
  obtain ⟨x, hx, hxdeg⟩ := h t ht htne
  refine ⟨x, hx, ?_⟩
  suffices (G.deleteIncidencesOf s₂).degree_in t x = G.degree_in t x by
    exact this ▸ hxdeg
  refine congrArg card ?_
  ext y
  simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_inter, mem_neighborFinset,
    inf_adj, iInf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and,
    not_or, ne_eq, and_congr_left_iff, and_iff_left_iff_imp]
  intro hy hxy
  refine ⟨fun w ↦ ⟨fun hw ↦ ⟨hxy, ?_⟩, hxy.ne⟩, hxy.ne⟩
  intro _
  constructor
  · exact ne_of_mem_of_not_mem hw <| notMem_of_mem_of_empty_inter (ht hx) hs
  · exact ne_of_mem_of_not_mem hw <| notMem_of_mem_of_empty_inter (ht hy) hs

lemma IsDegenerate_iff_induce {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (s : Finset (Fin n)) :
    G.IsDegenerateSet k s ↔
      ∀ t ⊆ s, t ≠ ∅ → (G.induce t).minDegree ≤ k := by
  constructor
  · intro h t ht htne
    obtain ⟨x, hx, hxdeg⟩ := h t ht htne
    refine le_trans ((G.induce t).minDegree_le_degree ⟨x, hx⟩) ?_
    rw [induced_degree_eq]
    simp only [degree_in] at hxdeg
    suffices (G.neighborFinset x ∩ t) = {w ∈ t | G.Adj x w} by exact this ▸ hxdeg
    ext w
    simp [and_comm]
  · intro h t ht htne
    have _ : Nonempty t := Nonempty.to_subtype <| nonempty_iff_ne_empty.mpr htne
    obtain ⟨⟨x, hx⟩, hxdeg⟩ := (G.induce t).exists_minimal_degree_vertex
    refine ⟨x, hx, ?_⟩
    simp only [degree_in]
    rw [← induced_degree_eq G t x hx]
    refine le_trans (le_of_eq ?_) (h t ht htne)
    exact hxdeg.symm

theorem minDegree_le_degeneracy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (s : Finset (Fin n)) (hs : G.IsDegenerateSet k s) :
    (G.induce s).minDegree ≤ k := by
  if hsempty : s = ∅ then
    suffices (G.induce s).minDegree = 0 by simp [this]
    suffices G.induce s = ⊥ by simp [this]
    refine edgeFinset_eq_empty.mp ?_
    rw [hsempty]
    ext _
    simp
  else
    exact IsDegenerate_iff_induce G k s |>.mp hs s (subset_refl _) hsempty

lemma isDegenerate_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (s : Finset (Fin n)) : G.IsDegenerateSet k s → ∀ s' ⊆ s, G.IsDegenerateSet k s' := by
  intro h s' hs' t ht htnonempty
  exact h t (subset_trans ht hs') htnonempty

@[simp]
lemma emptyset_IsDegenerate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∀ k : ℕ, G.IsDegenerateSet k ∅ := by
  intro k
  simp only [IsDegenerateSet, subset_empty, ne_eq, degree_in, forall_eq, not_true_eq_false,
    notMem_empty, inter_empty, card_empty, zero_le, and_true, exists_false, imp_self]

end SimpleGraph

namespace CaroWeiType

theorem DegenerateSet_mono_bounded_degree_not_in {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (s : Finset V) {v : V}
    (hs : (G.deleteIncidencesOf {v}).IsDegenerateSet k s)
    (hvs : v ∉ s) :
    G.IsDegenerateSet k s := by
  intro t ht htne
  have hvt : v ∉ t := fun this ↦ hvs <| ht this
  obtain ⟨x, ⟨hxt, hcard⟩⟩ := hs t ht htne
  refine ⟨x, hxt, ?_⟩
  refine le_trans ?_ hcard
  refine Finset.card_le_card ?_
  intro y hy
  simp only [mem_inter, mem_neighborFinset] at hy
  simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_inter, mem_neighborFinset,
    mem_singleton, iInf_iInf_eq_left, inf_adj, hy.1, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet,
    Sym2.mem_iff, true_and, not_or, hy.2, and_true]
  constructor
  · exact fun hveqx ↦ hvt (hveqx ▸ hxt)
  · exact fun hveqx ↦ hvt (hveqx ▸ hy.2)

theorem DegenerateSet_mono_bounded_degree_in {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (s : Finset V) {v : V}
    [DecidableRel (G.deleteIncidencesOf {v}).Adj]
    (hs : (G.deleteIncidencesOf {v}).IsDegenerateSet k s)
    (hv : (G.neighborFinset v ∩ s).card ≤ k) :
    G.IsDegenerateSet k s := by
  intro t ht htne
  if hvt : v ∈ t then
    refine ⟨v, hvt, ?_⟩
    let bla := hs t ht htne
    calc G.degree_in t v
      _ ≤ (G.neighborFinset v ∩ s).card :=
        Finset.card_le_card <| Finset.inter_subset_inter (subset_refl _) ht
      _ ≤ k := hv
  else
    obtain ⟨x, ⟨hxt, hcard⟩⟩ := hs t ht htne
    refine ⟨x, hxt, ?_⟩
    refine le_trans ?_ hcard
    refine Finset.card_le_card ?_
    intro y hy
    simp only [mem_inter, mem_neighborFinset] at hy
    simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_inter, mem_neighborFinset,
      mem_singleton, iInf_iInf_eq_left, inf_adj, hy.1, deleteEdges_adj, Set.mem_setOf_eq,
      mem_edgeSet, Sym2.mem_iff, true_and, not_or, hy.2, and_true]
    constructor
    · exact fun hveqx ↦ hvt (hveqx ▸ hxt)
    · exact fun hveqx ↦ hvt (hveqx ▸ hy.2)

theorem kDegenerateSetClique_iff_le_k_plus_one {n : ℕ}
    (k : ℕ) (s : Finset (Fin n)) [DecidableRel (completeGraph (Fin n)).Adj] :
    (completeGraph (Fin n)).IsDegenerateSet k s ↔ s.card ≤ k + 1 := by
  constructor
  · intro h
    if hs : s = ∅ then
      simp only [hs, card_empty, le_add_iff_nonneg_left, zero_le]
    else
    obtain ⟨x, ⟨hx, hcard⟩⟩ := h s (subset_refl s) hs
    simp only [degree_in] at hcard
    suffices (completeGraph (Fin n)).neighborFinset x ∩ s = s \ {x} by
      grind
    ext v
    simp only [completeGraph_eq_top, mem_inter, mem_neighborFinset, top_adj, ne_eq, mem_sdiff,
      mem_singleton, ne_comm, and_comm]
  · intro h s' hs' hne
    obtain ⟨x, hx⟩ := nonempty_def.mp <| nonempty_iff_ne_empty.mpr hne
    refine ⟨x, hx, ?_⟩
    simp only [degree_in]
    suffices (completeGraph (Fin n)).neighborFinset x ∩ s' = (s' \ {x}) by
      calc #((completeGraph (Fin n)).neighborFinset x ∩ s')
        _ = #(s' \ {x}) := by rw [this]
        _ = #s' - 1 := card_setminus_singleton hx
        _ ≤ (k + 1) - 1 := by
          simp only [add_tsub_cancel_right, tsub_le_iff_right]
          exact le_trans (card_le_card hs') h
    ext v
    simp only [completeGraph_eq_top, mem_inter, mem_neighborFinset, top_adj, ne_eq, mem_sdiff,
      mem_singleton, ne_comm, and_comm]

theorem DegenerateSet_union_singleton {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (s : Finset V) (hs : G.IsDegenerateSet k s) {v : V}
    (hv : (G.neighborFinset v ∩ s).card ≤ k) :
    G.IsDegenerateSet k (s ∪ {v}) := by
  intro t ht htne
  if hvt : v ∈ t then
    refine ⟨v, ⟨hvt, ?_⟩⟩
    simp only [degree_in]
    refine le_trans ?_ hv
    refine card_le_card ?_
    intro w
    simp only [mem_inter, mem_neighborFinset, and_imp]
    refine fun hvw hwt ↦ ⟨hvw, ?_⟩
    rcases mem_union.mp <| ht hwt with hw | hw
    · exact hw
    · simp only [mem_singleton, hvw.ne'] at hw
  else
    have hts' : t ⊆ s := by
      intro x hx
      let hxs := ht hx
      simp only [union_singleton, mem_insert] at hxs
      cases hxs with
      | inl hxs => exact hvt (hxs ▸ hx) |>.elim
      | inr hxs => exact hxs
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := hs t hts' htne
    refine ⟨x, hx1, hx2⟩

-- Alon, Noga, Jeff Kahn, and Paul D. Seymour.
-- "Large induced degenerate subgraphs."
-- Graphs and Combinatorics 3, no. 1 (1987): 203-211.
theorem AlonKahnSeymour {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (X : Finset V) (hX : G.support ⊆ X) :
    ∃ s : Finset V,
      s ⊆ X ∧ G.IsDegenerateSet k s ∧ ∑ v ∈ X, aks_bound k (G.degree v) ≤ s.card := by
  induction hcard : #X generalizing G X with
  | zero => refine ⟨∅, by simp, by simp [IsDegenerateSet], by simp_all⟩
  | succ m ih => ?_
  have hX' : X.Nonempty := card_pos.mp <| Nat.lt_of_sub_eq_succ hcard
  have _ : Nonempty X := by exact Nonempty.to_subtype hX'
  have _ : Nonempty V := Exists.nonempty hX'
  obtain ⟨v, ⟨hvX, hdegv⟩⟩ := G.exists_minimal_degree_vertex_in X
  if hδ : (G.neighborFinset v ∩ X).card ≤ k then
    obtain ⟨s', ⟨hs', hdeg', hcard'⟩⟩ := by
      refine ih (G.deleteIncidencesOf {v}) (X \ {v}) ?_ (card_setminus_singleton' hvX hcard)
      intro u hu
      refine mem_coe.mpr <| mem_sdiff.mpr ⟨?_, notMem_of_mem_support_deleteIncidencesOf hu⟩
      exact mem_def.mpr <| hX <| Set.mem_of_mem_inter_left <| deleteIncidencesOf_support hu
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
      · calc ∑ x ∈ X \ {v}, aks_bound k ((G.deleteIncidencesOf {v}).degree x)
            + aks_bound k (G.degree v)
          _ ≤ ↑(#s') + aks_bound k (G.degree v) := by
            simp only [add_le_add_iff_right]
            exact hcard'
          _ ≤ ↑(#s') + 1 := by
            simp only [add_le_add_iff_left]
            exact min_le_left ..
  else
    simp only [not_le] at hδ
    obtain ⟨v', ⟨hv'X, hdegv'⟩⟩ := G.exists_maximal_degree_vertex_in X
    obtain ⟨s', ⟨hs', ⟨hdeg', hcard'⟩⟩⟩ := by
      refine ih (G.deleteIncidencesOf {v'}) (X \ {v'}) ?_ (card_setminus_singleton' hv'X hcard)
      intro u hu
      refine mem_coe.mpr <| mem_sdiff.mpr ⟨?_, notMem_of_mem_support_deleteIncidencesOf hu⟩
      exact mem_def.mpr <| hX <| Set.mem_of_mem_inter_left <| deleteIncidencesOf_support hu
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
            _ ≤ (d : ℝ) * ((k + 1 : ℝ) *
                ((d - 1 : ℕ) + 1 : ℝ)⁻¹ - (k + 1 : ℝ) * (d + 1 : ℝ)⁻¹) := by
              linarith
        refine le_of_eq ?_
        exact Eq.symm <| avg_gain d (by exact Nat.zero_lt_of_lt hd)

theorem DegenerateSet_LowerBound (k : ℕ) :
    IsCaroWeiTypeLowerBound (aks_bound k) (GraphParameter.DegenerateSet k) := by
  intro n _ _ G
  obtain ⟨s, hd, hdeg, hcard⟩ :=
    AlonKahnSeymour G.graph k univ (by simp only [coe_univ, Set.subset_univ])
  exact ⟨s, hdeg, hcard⟩

theorem kDegenerateSet_LowerBound_iff (f : ℕ → ℝ) :
    ∀ k : ℕ, IsCaroWeiTypeLowerBound f (GraphParameter.DegenerateSet k) ↔ f ≤ aks_bound k := by
  intro k
  refine ⟨?_, fun hf ↦ CaroWeiTypeLowerBound_mono hf <| DegenerateSet_LowerBound k⟩
  intro hf d
  refine le_min ?_ ?_
  · exact f_le_1_of_IsCaroWeiTypeLowerBound hf d
  · suffices f d ≤ (k + 1 : ℕ) / (d + 1 : ℝ) by
      exact le_of_le_of_eq this <| by lia
    refine f_on_complete_graph' hf ?_
    intro s hs
    refine (kDegenerateSetClique_iff_le_k_plus_one ..).mp hs

end CaroWeiType
