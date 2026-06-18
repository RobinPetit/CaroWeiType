import CWType.SimpleGraph.CaroWeiType.Forests.Basic
import CWType.SimpleGraph.CaroWeiType.Degenerate
import CWType.SimpleGraph.CaroWeiType.IndepSet

namespace SimpleGraph
open Finset

lemma InducesForest_of_IndepSet {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V} (hs : G.IsIndepSet s) :
    G.InducesForest s := by
  refine IsDegenerateSet_mono G zero_le_one s ?_
  exact CaroWeiType.Is0DegenerateSet_iff_IsIndepSet G s |>.mpr hs

lemma InducesForest_of_InducesCaterpillar {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V} (hs : G.InducesCaterpillar s) :
    G.InducesForest s := by
  intro t ht htne
  simp only [InducesCaterpillar, InducesLinearForest] at hs
  if h : ∃ x ∈ t, G.degree_in s x = 1 then
    obtain ⟨x, hxt, hxd⟩ := h
    refine ⟨x, hxt, le_of_le_of_eq (degree_in_mono ht) hxd⟩
  else
    simp only [not_exists, not_and] at h
    refine hs.1 t ?_ htne
    intro y hy
    refine mem_sdiff.mpr ⟨ht hy, ?_⟩
    simp only [mem_filter, not_and, ht hy, forall_const, h y hy, not_false_eq_true]

lemma InducesForest_of_InducesForestOfStars {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V} (hs : G.InducesForestOfStars s) :
    G.InducesForest s := by
  simp only [InducesForestOfStars] at hs
  if h : {x ∈ s | G.degree_in s x = 1} = ∅ then
    simp only [degree_in, h, sdiff_empty] at hs
    exact InducesForest_of_IndepSet G hs
  else
    have : s = (s \ {x ∈ s | G.degree_in s x = 1}) ∪ {x ∈ s | G.degree_in s x = 1} := by
      grind
    rw [this]
    refine IsDegenerateSet_union G (s \ {x ∈ s | G.degree_in s x = 1}) {x ∈ s | G.degree_in s x = 1}
      (InducesForest_of_IndepSet G hs) ?_
    intro x hx
    simp only [mem_filter] at hx
    exact le_of_eq (this ▸ hx.2)

lemma InducesForestIsUnionStable {V : Type*} [DecidableEq V] [Fintype V] :
    IsNonAdjacentUnionStableProp (fun G _ s ↦ @SimpleGraph.InducesForest V _ _ G _ s) :=
  IsDegenerateSetIsUnionStable _

lemma InducesForest_pair {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {v w : V} : G.InducesForest {v, w} := by
  refine IsDegenerateSet_of_degree_in_le _ _ _ ?_
  intro x hx
  refine le_trans (degree_in_le_card_minus_one_of_mem hx) (by grind)

lemma InducesForest_singleton {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    G.InducesForest {v} :=
  pair_eq_singleton v ▸ InducesForest_pair

lemma InducesForest_triplet_of_nonadj {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {u v w : V} (huv : ¬G.Adj u v) :
    G.InducesForest {u, v, w} := by
  intro t ht htne
  if hu : u ∈ t then
    refine ⟨u, hu, ?_⟩
    rw [← card_singleton w]
    refine card_le_card ?_
    intro x hx
    simp only [mem_inter, mem_neighborFinset] at hx
    obtain ⟨hux, hxt⟩ := hx
    have hx' := ht hxt
    simp only [mem_insert, mem_singleton] at hx' ⊢
    rcases hx' with hx' | hx' | hx'
    · exact hux.ne' hx' |>.elim
    · exact huv (hx' ▸ hux) |>.elim
    · exact hx'
  else
    have ht' : t ⊆ {v, w} := by grind
    obtain ⟨x, hx⟩ := by exact nonempty_iff_ne_empty.mpr htne
    refine ⟨x, hx, (degree_in_mono ht').trans ?_⟩
    refine le_trans (degree_in_le_card_minus_one_of_mem <| ht' hx) ?_
    simp only [tsub_le_iff_right, Nat.reduceAdd, card_le_two]

lemma InducesLinearForestIsUnionStable {V : Type*} [DecidableEq V] [Fintype V] :
    IsNonAdjacentUnionStableProp (fun G _ s ↦ @SimpleGraph.InducesLinearForest V _ _ G _ s) := by
  intro G _ s s' hss' h ⟨hsf, hs⟩ ⟨hs'f, hs'⟩
  refine ⟨InducesForestIsUnionStable G _ _ hss' h hsf hs'f, ?_⟩
  intro x hx
  rcases mem_union.mp hx with hx | hx
  · refine le_of_eq_of_le ?_ (hs _ hx)
    refine congrArg Finset.card ?_
    ext y
    simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff, or_iff_left_iff_imp]
    exact fun hxy hy ↦ h x hx y hy hxy |>.elim
  · refine le_of_eq_of_le ?_ (hs' _ hx)
    refine congrArg Finset.card ?_
    ext y
    simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff, or_iff_right_iff_imp]
    exact fun hxy hy ↦ h y hy x hx hxy.symm |>.elim

lemma InducesLinearForest_singleton {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    G.InducesLinearForest {v} := by
  simp [InducesLinearForest, InducesForest_singleton]

lemma InducesLinearForest_pair {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v w : V} :
    G.InducesLinearForest {v, w} := by
  simp only [InducesLinearForest, InducesForest_pair, mem_insert, mem_singleton, degree_in,
    forall_eq_or_imp, mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true,
    inter_insert_of_notMem, forall_eq, true_and]
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ <| one_le_two
    rw [← card_singleton w]
    exact card_le_card inter_subset_right
  · refine le_trans ?_ <| @card_le_two _ _ v w
    exact card_le_card inter_subset_right

lemma InducesForest_mono {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s t : Finset V} (hle : s ⊆ t) (h : G.InducesForest t) :
    G.InducesForest s :=
  fun _ hs' hs'ne ↦ h _ (hs'.trans hle) hs'ne

lemma InducesForest_graph_mono {V : Type*} [DecidableEq V] [Fintype V] {G₁ G₂ : SimpleGraph V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    {s : Finset V} (hle : G₁ ≤ G₂) (h : G₂.InducesForest s) : G₁.InducesForest s := by
  simp only [InducesForest] at h ⊢
  exact IsDegenerateSet_graph_mono G₁ G₂ hle 1 s h

lemma InducesForest_graph_mono' {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s₁ s₂ : Finset V} (hs : s₁ ∩ s₂ = ∅)
    (h : (G.deleteIncidencesOf s₂).InducesForest s₁) :
    G.InducesForest s₁ := by
  exact IsDegenerateSet_graph_mono' G 1 s₁ s₂ hs h

lemma InducesForest_union_leaf {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (hs : G.InducesForest s)
    {v : V} (hv : G.degree_in s v ≤ 1) :
    G.InducesForest (s ∪ {v}) := by
  simp only [InducesForest] at hs ⊢
  exact G.IsDegenerateSet_union_singleton s hs hv

lemma InducesForest_union_disjoint_neighborhoods {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s₁ s₂ : Finset V} (hs₁ : G.InducesForest s₁)
    (hs₂ : G.InducesForest s₂) (h : ∀ x ∈ s₁, ∀ y ∈ s₂, ¬G.Adj x y) :
    G.InducesForest (s₁ ∪ s₂) := by
  intro t ht htne
  if ht' : t ∩ s₁ ≠ ∅ then
    obtain ⟨x, hx, hdeg⟩ := hs₁ (t ∩ s₁) inter_subset_right ht'
    refine ⟨x, (mem_inter.mp hx).1, ?_⟩
    simp only [degree_in] at hdeg ⊢
    refine le_trans (le_of_eq ?_) hdeg
    refine congrArg card ?_
    ext y
    simp only [mem_inter, mem_neighborFinset, and_congr_right_iff, iff_self_and]
    grind
  else
    have ht' : t ∩ s₂ ≠ ∅ := by grind
    obtain ⟨x, hx, hdeg⟩ := hs₂ (t ∩ s₂) inter_subset_right ht'
    refine ⟨x, (mem_inter.mp hx).1, ?_⟩
    simp only [degree_in] at hdeg ⊢
    refine le_trans (le_of_eq ?_) hdeg
    refine congrArg card ?_
    ext y
    simp only [mem_inter, mem_neighborFinset, and_congr_right_iff, iff_self_and]
    grind [Adj.symm]

lemma InducesForestOfStars_iff {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset V} :
    G.InducesForestOfStars s
      ↔ (G.InducesForest s ∧
        ∀ u₁ u₂ u₃ u₄, u₁ ∈ s → u₂ ∈ s → u₃ ∈ s → u₄ ∈ s → u₁ ≠ u₃ → u₂ ≠ u₄ →
          G.Adj u₁ u₂ → G.Adj u₂ u₃ → ¬G.Adj u₃ u₄) := by
  constructor
  · intro hsf
    refine ⟨InducesForest_of_InducesForestOfStars G hsf, ?_⟩
    intro u₁ u₂ u₃ u₄ hu₁ hu₂ hu₃ hu₄ hne₁₃ hne₂₄ hu₁u₂ hu₂u₃
    suffices G.degree_in s u₃ = 1 by
      have := by
        refine eq_of_mem_of_mem_of_singleton this ?_ |>.mt hne₂₄
        exact mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr hu₂u₃.symm, hu₂⟩
      simp only [mem_inter, mem_neighborFinset, hu₄, and_true] at this
      exact this
    have := by
      refine (@hsf u₂ ?_ u₃ ·).mt ?_
      · simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe, Set.mem_setOf_eq,
          hu₂, true_and]
        suffices 2 ≤ G.degree_in s u₂ by
          exact Nat.ne_of_lt' this
        rw [← card_pair hne₁₃]
        refine card_le_card ?_
        intro u hu
        simp only [mem_insert, mem_singleton, mem_inter, mem_neighborFinset] at hu ⊢
        rcases hu with hu | hu
        · exact ⟨hu ▸ hu₁u₂.symm, hu ▸ hu₁⟩
        · exact ⟨hu ▸ hu₂u₃, hu ▸ hu₃⟩
      · simp only [ne_eq, hu₂u₃.ne, not_false_eq_true, hu₂u₃, not_true_eq_false, imp_false]
    simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe, hu₃,
      Set.mem_setOf_eq, true_and, Decidable.not_not] at this
    exact this
  · intro ⟨hsf, h⟩ x hx y hy hne
    simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe, Set.mem_setOf_eq,
      not_and, cancel_imp_of_and] at hx hy
    intro hxy
    have : 2 ≤ G.degree_in s x := by
      refine (Nat.two_le_iff _).mpr ⟨?_, hx.2⟩
      exact card_ne_zero.mpr ⟨y, mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr hxy, hy.1⟩⟩
    obtain ⟨u₁, hu₁, hne₁⟩ := Finset_get_other this y
    have : 2 ≤ G.degree_in s y := by
      refine (Nat.two_le_iff _).mpr ⟨?_, hy.2⟩
      exact card_ne_zero.mpr ⟨x, mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr hxy.symm, hx.1⟩⟩
    obtain ⟨u₄, hu₄, hne₄⟩ := Finset_get_other this x
    refine h u₁ x y u₄ (mem_inter.mp hu₁ |>.2) hx.1 hy.1 (mem_inter.mp hu₄ |>.2)
        hne₁.symm hne₄ ?_ hxy ?_
    · exact Adj.symm <| mem_neighborFinset .. |>.mp <| mem_inter.mp hu₁ |>.1
    · exact mem_neighborFinset .. |>.mp <| mem_inter.mp hu₄ |>.1

lemma InducesForestOfStars_graph_mono {V : Type*} [DecidableEq V] [Fintype V]
    {G₁ G₂ : SimpleGraph V} [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    {s : Finset V} (hle : G₁ ≤ G₂) (h : G₂.InducesForestOfStars s) :
    G₁.InducesForestOfStars s := by
  refine InducesForestOfStars_iff.mpr ⟨?_, ?_⟩
  · exact InducesForest_graph_mono hle <| G₂.InducesForest_of_InducesForestOfStars h
  · intro u₁ u₂ u₃ u₄ hu₁ hu₂ hu₃ hu₄ hne₁₃ hne₂₄ hu₁u₂ hu₂u₃
    suffices ¬G₂.Adj u₃ u₄ by exact (this <| hle ·)
    exact InducesForestOfStars_iff.mp h |>.2
      u₁ u₂ u₃ u₄ hu₁ hu₂ hu₃ hu₄ hne₁₃ hne₂₄ (hle hu₁u₂) (hle hu₂u₃)

lemma InducesForestOfStars_graph_mono' {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s₁ s₂ : Finset V} (hs : s₁ ∩ s₂ = ∅)
    (h : (G.deleteIncidencesOf s₂).InducesForestOfStars s₁) :
    G.InducesForestOfStars s₁ := by
  refine InducesForestOfStars_iff.mpr ⟨?_, ?_⟩
  · exact InducesForest_graph_mono' hs <| InducesForestOfStars_iff.mp h |>.1
  · intro u₁ u₂ u₃ u₄ hu₁ hu₂ hu₃ hu₄ hne₁₃ hne₂₄ hu₁u₂ hu₂u₃
    suffices ¬(G.deleteIncidencesOf s₂).Adj u₃ u₄ by
      refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ |>.mt this
      · exact notMem_of_mem_of_empty_inter hu₃ hs
      · exact notMem_of_mem_of_empty_inter hu₄ hs
    refine InducesForestOfStars_iff.mp h |>.2 u₁ u₂ u₃ u₄ hu₁ hu₂ hu₃ hu₄ hne₁₃ hne₂₄ ?_ ?_
    · refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ hu₁u₂
      · exact notMem_of_mem_of_empty_inter hu₁ hs
      · exact notMem_of_mem_of_empty_inter hu₂ hs
    · refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ hu₂u₃
      · exact notMem_of_mem_of_empty_inter hu₂ hs
      · exact notMem_of_mem_of_empty_inter hu₃ hs

lemma InducesForestOfStars_empty {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    G.InducesForestOfStars ∅ := by
  refine InducesForestOfStars_iff.mpr ⟨?_, ?_⟩
  · exact fun t ht htne ↦ htne (subset_empty.mp ht) |>.elim
  · simp only [notMem_empty, IsEmpty.forall_iff, implies_true]

lemma InducesForestOfStars_singleton {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    G.InducesForestOfStars {v} := by
  intro x hx y hy hne
  refine hne ?_ |>.elim
  simp only [degree_in, coe_sdiff, coe_singleton, coe_filter, mem_singleton, Set.mem_diff,
    Set.mem_singleton_iff, Set.mem_setOf_eq, not_and] at hx hy
  rw [hx.1, hy.1]

lemma InducesForestOfStars_pair {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v w : V} :
    G.InducesForestOfStars {v, w} := by
  intro x hx y hy hne
  simp only [coe_sdiff, coe_insert, coe_singleton, coe_filter, mem_insert, mem_singleton, not_and,
    cancel_imp_of_and, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_setOf_eq] at hx hy
  if hvw : G.Adj v w then
    refine hne ?_ |>.elim
    suffices G.degree_in {v, w} v = 1 ∧ G.degree_in {v, w} w = 1 by grind
    refine ⟨?_, ?_⟩
    · refine card_singleton w ▸ congrArg Finset.card ?_
      simp only [mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true, inter_insert_of_notMem,
        inter_eq_right, singleton_subset_iff, hvw]
    · refine pair_comm v w ▸ card_singleton v ▸ congrArg Finset.card ?_
      simp only [mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true, inter_insert_of_notMem,
        inter_eq_right, singleton_subset_iff, hvw.symm]
  else
    grind [not_adj_symm]

lemma InducesForestOfStars_triplet {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : ¬G.Adj u w) :
    G.InducesForestOfStars {u, v, w} := by
  intro x hx y hy hxney
  simp only [degree_in, coe_sdiff, coe_insert, coe_singleton, coe_filter, mem_insert, mem_singleton,
    Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, not_and,
    cancel_imp_of_and] at hx hy
  refine Adj.ne.mt <| ?_
  simp only [ne_eq, Decidable.not_not]
  have hxeqv : x = v := by
    obtain ⟨hx, hdx⟩ := hx
    rcases hx with hx | hx | hx
    · refine hdx (hx ▸ ?_) |>.elim
      rw [← card_singleton v]
      refine congrArg Finset.card ?_
      grind [degree, mem_neighborFinset, G.irrefl]
    · exact hx
    · refine hdx (hx ▸ ?_) |>.elim
      rw [← card_singleton v]
      refine congrArg Finset.card ?_
      grind [degree, mem_neighborFinset, G.irrefl, Adj.symm]
  have hyeqv : y = v := by
    obtain ⟨hy, hdy⟩ := hy
    rcases hy with hy | hy | hy
    · refine hdy (hy ▸ ?_) |>.elim
      rw [← card_singleton v]
      refine congrArg Finset.card ?_
      grind [degree, mem_neighborFinset, G.irrefl]
    · exact hy
    · refine hdy (hy ▸ ?_) |>.elim
      rw [← card_singleton v]
      refine congrArg Finset.card ?_
      grind [degree, mem_neighborFinset, G.irrefl, Adj.symm]
  rw [hxeqv, hyeqv]

lemma InducesForestOfStars_union_disjoint_neighborhoods {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s₁ s₂ : Finset V} (hs₁ : G.InducesForestOfStars s₁)
    (hs₂ : G.InducesForestOfStars s₂) (h : ∀ x ∈ s₁, ∀ y ∈ s₂, ¬G.Adj x y) :
    G.InducesForestOfStars (s₁ ∪ s₂) := by
  intro x hx y hy hne
  simp only [coe_sdiff, coe_union, coe_filter, mem_union, Set.mem_diff, Set.mem_union,
    SetLike.mem_coe, Set.mem_setOf_eq, not_and, cancel_imp_of_and] at hx hy
  match hx.1, hy.1 with
  | Or.inl hx', Or.inr hy' => exact h _ hx' _ hy'
  | Or.inr hx', Or.inl hy' => exact not_adj_symm <| h _ hy' _ hx'
  | Or.inl hx', Or.inl hy' =>
      refine hs₁ ?_ ?_ hne
      · simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe,
          Set.mem_setOf_eq, hx', true_and]
        refine ne_of_eq_of_ne ?_ hx.2
        refine Eq.symm (degree_in_union_eq ?_)
        ext z
        simp only [mem_inter, mem_neighborFinset, notMem_empty, iff_false, not_and]
        exact fun hz ↦ h _ hx' _ hz
      · simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe,
          Set.mem_setOf_eq, hy', true_and]
        refine ne_of_eq_of_ne ?_ hy.2
        refine Eq.symm (degree_in_union_eq ?_)
        ext z
        simp only [mem_inter, mem_neighborFinset, notMem_empty, iff_false, not_and]
        exact fun hz ↦ h _ hy' _ hz
  | Or.inr hx', Or.inr hy' =>
      rw [union_comm s₁ s₂] at hx hy
      refine hs₂ ?_ ?_ hne
      · simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe,
          Set.mem_setOf_eq, hx', true_and]
        refine ne_of_eq_of_ne ?_ hx.2
        refine Eq.symm (degree_in_union_eq ?_)
        ext z
        simp only [mem_inter, mem_neighborFinset, notMem_empty, iff_false, not_and]
        exact fun hz ↦ not_adj_symm <| h _ hz _ hx'
      · simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe,
          Set.mem_setOf_eq, hy', true_and]
        refine ne_of_eq_of_ne ?_ hy.2
        refine Eq.symm (degree_in_union_eq ?_)
        ext z
        simp only [mem_inter, mem_neighborFinset, notMem_empty, iff_false, not_and]
        exact fun hz ↦ not_adj_symm <| h _ hz _  hy'

lemma InducesForestOfStars_union_isolated {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset V} {v : V} (hdv : G.degree_in s v = 0)
    (hs : G.InducesForestOfStars s) :
    G.InducesForestOfStars (s ∪ {v}) := by
  refine InducesForestOfStars_union_disjoint_neighborhoods hs G.InducesForestOfStars_singleton ?_
  intro x hx y hy hxy
  rw [mem_singleton.mp hy] at hxy
  simp only [degree_in, card_eq_zero] at hdv
  have := hdv ▸ notMem_empty x
  simp only [mem_inter, mem_neighborFinset, hxy.symm, hx, and_self, not_true_eq_false] at this

lemma InducesForestOfStars_union_singleton {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset V} {v : V} (hdv : G.degree v = 0)
    (hs : G.InducesForestOfStars s) :
    G.InducesForestOfStars (s ∪ {v}) := by
  refine InducesForestOfStars_union_isolated  ?_ hs
  exact le_antisymm (le_of_le_of_eq degree_in_le_degree hdv) (Nat.zero_le _)

lemma InducesForestOfStars_union_leaf' {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset V} {v w : V} (hdv : G.degree_in s v = 1)
    (hws : w ∈ s) (hvw : G.Adj v w) (hdw : G.degree_in s w ≠ 1) (hs : G.InducesForestOfStars s) :
    G.InducesForestOfStars (s ∪ {v}) := by
  have hNv := Finset_singleton_unique hdv
  intro x hx y hy hne
  simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe, Set.mem_setOf_eq, not_and,
    cancel_imp_of_and] at hx hy
  obtain ⟨hx, hdx⟩ := hx
  obtain ⟨hy, hdy⟩ := hy
  simp only [union_singleton, mem_insert] at hx hy
  match hx, hy with
  | Or.inl hx', Or.inl hy' =>
      rw [hx', hy']
      exact G.irrefl
  | Or.inl hx', Or.inr hy' =>
      rw [hx'] at hdx ⊢
      exact hdx ((degree_in_union_self v s).symm.trans hdv) |>.elim
  | Or.inr hx', Or.inl hy' =>
      rw [hy'] at hdy ⊢
      exact hdy ((degree_in_union_self v s).symm.trans hdv) |>.elim
  | Or.inr hx', Or.inr hy' =>
      refine hs ?_ ?_ hne
      · simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe, hx',
          Set.mem_setOf_eq, true_and]
        if hxeqw : x = w then
          exact hxeqw ▸ hdw
        else
          refine ne_of_eq_of_ne ?_ hdx
          refine Eq.symm <| degree_in_union_eq ?_
          simp only [singleton_inter_eq_empty_iff, mem_neighborFinset]
          have := hNv.unique (mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr hvw, hws⟩) |>.mt
            <| Ne.symm hxeqw
          simp only [mem_inter, mem_neighborFinset, hx', and_true] at this
          exact not_adj_symm this
      · simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe, hy',
          Set.mem_setOf_eq, true_and]
        if hyeqw : y = w then
          exact hyeqw ▸ hdw
        else
          refine ne_of_eq_of_ne ?_ hdy
          refine Eq.symm <| degree_in_union_eq ?_
          simp only [singleton_inter_eq_empty_iff, mem_neighborFinset]
          have := hNv.unique (mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr hvw, hws⟩) |>.mt
            <| Ne.symm hyeqw
          simp only [mem_inter, mem_neighborFinset, hy', and_true] at this
          exact not_adj_symm this

lemma InducesForestOfStars_union_leaf {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset V} {v w : V} (hdv : G.degree v = 1)
    (hvw : G.Adj v w) (hdw : G.degree_in s w ≠ 1) (hs : G.InducesForestOfStars s) :
    G.InducesForestOfStars (s ∪ {v}) := by
  have hNv : ∃! u, G.Adj v u := degree_eq_one_iff_existsUnique_adj.mp hdv
  if hws : w ∉ s then
    refine InducesForestOfStars_union_disjoint_neighborhoods hs G.InducesForestOfStars_singleton ?_
    intro x hx y hy
    refine not_adj_symm <| mem_singleton.mp hy ▸ hNv.unique hvw |>.mt ?_
    exact Ne.symm <| ne_of_mem_of_not_mem hx hws
  else
    simp only [Decidable.not_not] at hws
    refine InducesForestOfStars_union_leaf' ?_ hws hvw hdw hs
    refine le_antisymm ?_ ?_
    · exact hdv ▸ degree_in_le_degree
    · rw [← card_singleton w]
      refine card_le_card ?_
      exact singleton_subset_iff.mpr <| mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr hvw, hws⟩

lemma InducesForestOfStars_union_leaf_on_K2 {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset V} {u v w : V}
    (hdu : G.degree_in s u = 1) (hdv : G.degree_in s v = 1) (hdw : G.degree_in s w = 1)
    (hvw : G.Adj v w) (huw : G.Adj u w) (hus : u ∈ s) (hws : w ∈ s)
    (hunev : u ≠ v) (hs : G.InducesForestOfStars s) :
    G.InducesForestOfStars (s ∪ {v}) := by
  have hNv : ∃! u, G.Adj v u ∧ u ∈ s := by
    have := Finset_singleton_unique hdv
    simp only [mem_inter, mem_neighborFinset] at this
    exact this
  intro x hx y hy hne
  simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe, Set.mem_setOf_eq, not_and,
    cancel_imp_of_and] at hx hy
  obtain ⟨hx, hdx⟩ := hx
  obtain ⟨hy, hdy⟩ := hy
  simp only [union_singleton, mem_insert] at hx hy
  have hd'v : G.degree_in (s ∪ {v}) v = 1 := by
    rw [← degree_in_union_self, ← card_singleton w]
    refine congrArg Finset.card ?_
    ext z
    simp only [mem_inter, mem_neighborFinset, mem_singleton]
    exact ⟨fun hz ↦ Eq.symm <| hNv.unique ⟨hvw, hws⟩ hz, fun heq ↦ ⟨heq ▸ hvw, heq ▸ hws⟩⟩
  have hxnev : x ≠ v := fun heq ↦ (heq ▸ hdx) hd'v
  have hynev : y ≠ v := fun heq ↦ (heq ▸ hdy) hd'v
  simp only [hxnev, hynev, false_or] at hx hy
  if hxeqw : x = w then
    subst hxeqw
    have : y ≠ u := by
      refine fun heq ↦ hdy ?_
      rw [heq, ← hdu]
      refine degree_in_union_eq ?_
      simp only [singleton_inter_eq_empty_iff, mem_neighborFinset]
      refine fun h ↦ hNv.unique ⟨hvw, hx⟩ |>.mt huw.ne' ⟨h.symm, heq ▸ hy⟩
    refine fun hxy ↦ this ?_
    refine eq_of_mem_of_mem_of_singleton hdw ?_ ?_
    · exact mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr hxy, hy⟩
    · exact mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr huw.symm, hus⟩
  else if hyeqw : y = w then
    subst hyeqw
    have : x ≠ u := by
      refine fun heq ↦ hdx ?_
      rw [heq, ← hdu]
      refine degree_in_union_eq ?_
      simp only [singleton_inter_eq_empty_iff, mem_neighborFinset]
      exact fun h ↦ hNv.unique ⟨hvw, hy⟩ |>.mt huw.ne' ⟨h.symm, heq ▸ hx⟩
    refine fun hxy ↦ this ?_
    refine eq_of_mem_of_mem_of_singleton hdw ?_ ?_
    · exact mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr hxy.symm, hx⟩
    · exact mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr huw.symm, hus⟩
  else if hxequ : x = u then
    subst hxequ
    have H : w ∈ G.neighborFinset x ∩ s := mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr huw, hws⟩
    have := eq_of_mem_of_mem_of_singleton hdu H |>.mt <| Ne.symm hyeqw
    simp only [mem_inter, mem_neighborFinset, hy, and_true] at this
    exact this
  else if hyequ : y = u then
    subst hyequ
    have H : w ∈ G.neighborFinset y ∩ s := mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr huw, hws⟩
    have := eq_of_mem_of_mem_of_singleton hdu H |>.mt <| Ne.symm hxeqw
    simp only [mem_inter, mem_neighborFinset, hx, and_true] at this
    exact not_adj_symm this
  else
    refine hs ?_ ?_ hne
    · simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe, hx,
        Set.mem_setOf_eq, true_and]
      refine ne_of_eq_of_ne ?_ hdx
      refine Eq.symm (degree_in_union_eq ?_)
      refine singleton_inter_of_notMem ?_
      have := hNv.unique ⟨hvw, hws⟩ |>.mt <| Ne.symm hxeqw
      simp only [hx, and_true, mem_neighborFinset] at this ⊢
      exact not_adj_symm this
    · simp only [coe_sdiff, coe_filter, Set.mem_diff, SetLike.mem_coe, hy,
        Set.mem_setOf_eq, true_and]
      refine ne_of_eq_of_ne ?_ hdy
      refine Eq.symm (degree_in_union_eq ?_)
      refine singleton_inter_of_notMem ?_
      have := hNv.unique ⟨hvw, hws⟩ |>.mt <| Ne.symm hyeqw
      simp only [hy, and_true, mem_neighborFinset] at this ⊢
      exact not_adj_symm this

lemma InducesForestOfStars_triplet_of_nonadj {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V} (huv : ¬G.Adj u v) :
    G.InducesForestOfStars {u, v, w} := by
  if hvw : ¬G.Adj v w then
    rw [(by grind : {u, v, w} = ({u, w} ∪ {v} : Finset _))]
    refine InducesForestOfStars_union_isolated ?_ InducesForestOfStars_pair
    refine card_eq_zero.mpr ?_
    grind [mem_neighborFinset, Adj.symm]
  else if hvequ : v = u then
    rw [(by grind : {u, v, w} = ({v, w} : Finset _))]
    exact InducesForestOfStars_pair
  else
    rw [(by grind : {u, v, w} = ({v, w} ∪ {u} : Finset _))]
    if hdu : G.degree_in {v, w} u = 0 then
      exact InducesForestOfStars_union_isolated hdu InducesForestOfStars_pair
    else
      have hu : G.neighborFinset u ∩ {v, w} = {w} := by
        refine eq_of_subset_and_eq_card ?_ ?_
        · intro x hx
          simp only [mem_inter, mem_neighborFinset, mem_insert, mem_singleton] at hx ⊢
          grind
        · refine card_singleton _ ▸ le_antisymm ?_ ?_
          · rw [← card_singleton w]
            refine card_le_card <| by grind [mem_neighborFinset]
          · exact Nat.one_le_iff_ne_zero.mpr hdu
      obtain ⟨x, hx⟩ : (G.neighborFinset u ∩ {v, w}).Nonempty := card_ne_zero.mp hdu
      simp only [mem_inter, mem_neighborFinset, mem_insert, mem_singleton] at hx
      obtain ⟨hux, hx⟩ := hx
      have hx : w = x := by
        rcases hx with hx | hx
        · exact huv (hx ▸ hux) |>.elim
        · exact hx.symm
      subst hx; clear hx
      have hv : v ∈ ({v, w} : Finset _) := by exact mem_insert_self v {w}
      refine InducesForestOfStars_union_leaf_on_K2 ?_ (congrArg Finset.card hu) ?_ hux ?_
          (mem_insert_self v _) (by grind) hvequ InducesForestOfStars_pair
      · rw [← card_singleton w]
        refine congrArg Finset.card ?_
        ext x
        grind [mem_neighborFinset, ne_of_mem_neighborFinset, Adj.symm]
      · rw [← card_singleton v]
        refine congrArg Finset.card ?_
        ext x
        grind [mem_neighborFinset, ne_of_mem_neighborFinset, Adj.symm]
      · exact Decidable.not_not.mp hvw

lemma InducesForest_of_iso {V V' : Type} [DecidableEq V] [Fintype V] [DecidableEq V'] [Fintype V']
    {G : SimpleGraph V} {G' : SimpleGraph V'} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (φ : G ≃g G') {s : Finset V} (h : G.InducesForest s) :
    G'.InducesForest (s.image φ.toFun) :=
  IsDegenerateSet_of_graph_iso φ s h

lemma InducesCaterpillar_of_iso {V V' : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableEq V'] [Fintype V'] {G' : SimpleGraph V'} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (φ : G ≃g G') {s : Finset V} (h : G.InducesCaterpillar s) :
    G'.InducesCaterpillar (s.image φ.toFun) := by
  obtain ⟨h, h'⟩ := h
  refine ⟨?_, ?_⟩
  · suffices (s \ {x ∈ s | G.degree_in s x = 1}).image φ.toFun
        = (s.image φ.toFun \ {x ∈ image φ.toFun s | G'.degree_in (image φ.toFun s) x = 1}) by
      exact this ▸ InducesForest_of_iso φ h
    ext u
    simp only [mem_image, mem_sdiff, mem_filter, not_and]
    constructor
    · intro ⟨x, ⟨⟨h, h'⟩, hxu⟩⟩
      refine ⟨⟨x, h, hxu⟩, fun _ ↦ ?_⟩
      refine ne_of_eq_of_ne (hxu ▸ (degree_in_eq_of_iso _ s φ).symm) (h' h)
    · intro ⟨⟨x, hx, hxu⟩, h⟩
      refine ⟨x, ⟨hx, fun _ ↦ ?_⟩, hxu⟩
      exact ne_of_eq_of_ne (hxu ▸ degree_in_eq_of_iso _ s φ) (h ⟨x, hx, hxu⟩)
  · intro u
    simp only [mem_sdiff, mem_filter, not_and, and_imp, mem_image,
      forall_exists_index] at h' ⊢
    intro x hx hxu H
    refine le_of_eq_of_le ?_ (h' x hx ?_)
    · rw [← hxu]
      refine Eq.symm ?_
      have := degree_in_eq_of_iso x (s \ {x ∈ s | #(G.neighborFinset x ∩ s) = 1}) φ
      refine this.trans ?_
      refine congrArg (G'.degree_in · (φ.toFun x)) ?_
      ext u
      simp only [mem_image, mem_sdiff, mem_filter, not_and]
      constructor
      · intro ⟨x, ⟨hx, h⟩, hxu⟩
        refine ⟨⟨x, hx, hxu⟩, fun _ ↦ ?_⟩
        refine ne_of_eq_of_ne ?_ (h hx)
        rw [← degree_in, ← hxu]
        exact (degree_in_eq_of_iso x s φ).symm
      · intro ⟨⟨x, hx, hxu⟩, h'⟩
        refine ⟨x, ⟨⟨hx, fun _ ↦ ?_⟩, hxu⟩⟩
        refine ne_of_eq_of_ne ?_ (h' ⟨x, hx, hxu⟩)
        rw [← degree_in, ← hxu]
        exact degree_in_eq_of_iso x s φ
    · exact fun _ ↦ ne_of_eq_of_ne (hxu ▸ degree_in_eq_of_iso _ s φ) (H x hx hxu)

lemma InducesForestOfStars_of_iso {V V' : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableEq V'] [Fintype V'] {G' : SimpleGraph V'} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (φ : G ≃g G') {s : Finset V} (h : G.InducesForestOfStars s) :
    G'.InducesForestOfStars (s.image φ.toFun) := by
  simp only [InducesForestOfStars, IsIndepSet, degree_in] at h ⊢
  intro x hx y hy hne
  suffices ¬G.Adj (φ.invFun x) (φ.invFun y) by
    have hobj := not_iff_not.mpr φ.map_rel_iff' |>.mpr this
    simp only [Equiv.invFun_as_coe, Equiv.apply_symm_apply] at hobj
    exact hobj
  simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, coe_sdiff, coe_image, coe_filter, mem_image,
    Set.mem_diff, Set.mem_image, SetLike.mem_coe, Set.mem_setOf_eq, not_and, forall_exists_index,
    and_imp] at hx hy
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  obtain ⟨x', hx's, hxx'⟩ := hx
  obtain ⟨y', hy's, hyy'⟩ := hy
  refine h ?_ ?_ ?_
  · have : φ.symm x ∈ s := φ.symm_apply_eq.mpr hxx'.symm ▸ hx's
    simp only [coe_sdiff, coe_filter, Equiv.invFun_as_coe, Set.mem_diff, SetLike.mem_coe,
      Set.mem_setOf_eq, not_and]
    refine ⟨this, fun _ ↦ ?_⟩
    refine ne_of_eq_of_ne ?_ (hx' x' hx's hxx')
    refine Set.BijOn.finsetCard_eq φ.toFun ⟨?_, ?_, ?_⟩
    · intro u hu
      simp only [coe_inter, coe_neighborFinset, Set.mem_inter_iff, mem_neighborSet, SetLike.mem_coe,
        Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, coe_image, Set.mem_image,
        EmbeddingLike.apply_eq_iff_eq, exists_eq_right] at hu ⊢
      obtain ⟨hu, hus⟩ := hu
      refine ⟨?_, hus⟩
      refine φ.symm.map_adj_iff.mp ?_
      simp only [RelIso.symm_apply_apply]
      exact hu
    · exact Function.Injective.injOn φ.injective
    · intro u hu
      simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, coe_inter, coe_neighborFinset,
        coe_image, Set.mem_inter_iff, mem_neighborSet, Set.mem_image, SetLike.mem_coe] at hu ⊢
      obtain ⟨hxu, ⟨v, hv, huv⟩⟩ := hu
      refine ⟨v, ⟨φ.map_adj_iff.mp ?_, hv⟩, huv⟩
      have : φ (φ.symm x) = x := φ.apply_symm_apply x
      rw [← this, ← huv] at hxu
      exact hxu
  · have : φ.symm y ∈ s := φ.symm_apply_eq.mpr hyy'.symm ▸ hy's
    simp only [coe_sdiff, coe_filter, Equiv.invFun_as_coe, Set.mem_diff, SetLike.mem_coe,
      Set.mem_setOf_eq, not_and]
    refine ⟨this, fun _ ↦ ?_⟩
    refine ne_of_eq_of_ne ?_ (hy' y' hy's hyy')
    refine Set.BijOn.finsetCard_eq φ.toFun ⟨?_, ?_, ?_⟩
    · intro u hu
      simp only [coe_inter, coe_neighborFinset, Set.mem_inter_iff, mem_neighborSet, SetLike.mem_coe,
        Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, coe_image, Set.mem_image,
        EmbeddingLike.apply_eq_iff_eq, exists_eq_right] at hu ⊢
      obtain ⟨hu, hus⟩ := hu
      refine ⟨?_, hus⟩
      refine φ.symm.map_adj_iff.mp ?_
      simp only [RelIso.symm_apply_apply]
      exact hu
    · exact Function.Injective.injOn φ.injective
    · intro u hu
      simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, coe_inter, coe_neighborFinset,
        coe_image, Set.mem_inter_iff, mem_neighborSet, Set.mem_image, SetLike.mem_coe] at hu ⊢
      obtain ⟨hyu, ⟨v, hv, huv⟩⟩ := hu
      refine ⟨v, ⟨φ.map_adj_iff.mp ?_, hv⟩, huv⟩
      have : φ (φ.symm y) = y := φ.apply_symm_apply y
      rw [← this, ← huv] at hyu
      exact hyu
  · rw [← hxx', ← hyy']
    simp only [Equiv.invFun_as_coe, ne_eq, EmbeddingLike.apply_eq_iff_eq]
    intro heq
    rw [← hxx', ← hyy', heq] at hne
    exact false_of_ne hne

lemma InducesCaterpillarIsUnionStable {V : Type*} [DecidableEq V] [Fintype V] :
    IsNonAdjacentUnionStableProp (fun G _ s ↦ @SimpleGraph.InducesCaterpillar V _ _ G _ s) := by
  intro G _ s s' hss' h ⟨hslf, hs⟩ ⟨hs'lf, hs'⟩
  have hdegree_in_s {u} (hu : u ∈ s) :
      G.neighborFinset u ∩ s = G.neighborFinset u ∩ (s ∪ s') := by
    ext w
    simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff, iff_self_or]
    exact fun huw hw ↦ h u hu w hw huw |>.elim
  have hdegree_in_s' {u} (hu : u ∈ s') :
      G.neighborFinset u ∩ s' = G.neighborFinset u ∩ (s ∪ s') := by
    ext w
    simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff, iff_or_self]
    exact fun huw hw ↦ h w hw u hu huw.symm |>.elim
  refine ⟨?_, ?_⟩
  · suffices ((s ∪ s') \ {x ∈ s ∪ s' | G.degree_in (s ∪ s') x = 1})
        = (s \ {x ∈ s | G.degree_in s x = 1}) ∪ (s' \ {x ∈ s' | G.degree_in s' x = 1}) by
      rw [this]
      refine InducesForestIsUnionStable G _ _ ?_ ?_ hslf hs'lf
      · ext u
        simp only [mem_inter, mem_sdiff, mem_filter, not_and, notMem_empty, iff_false,
          Classical.not_imp, Decidable.not_not, and_imp]
        exact fun hus _ h ↦ notMem_of_mem_of_empty_inter hus hss' h |>.elim
      · exact fun x hx y hy ↦ h x (mem_sdiff.mp hx |>.1) y (mem_sdiff.mp hy |>.1)
    ext u
    simp only [degree_in, mem_sdiff, mem_union, mem_filter, not_and]
    constructor
    · intro ⟨hu, hu'⟩
      simp only [hu, forall_const] at hu'
      rcases hu with hu | hu
      · refine Or.inl <| ⟨hu, fun _ ↦ ne_of_eq_of_ne ?_ hu'⟩
        exact congrArg Finset.card <| hdegree_in_s hu
      · refine Or.inr <| ⟨hu, fun _ ↦ ne_of_eq_of_ne ?_ hu'⟩
        exact congrArg Finset.card <| hdegree_in_s' hu
    · intro h
      rcases h with ⟨hu, hu'⟩ | ⟨hu, hu'⟩
      · simp only [hu, true_or, forall_const, true_and]
        refine ne_of_eq_of_ne (Eq.symm <| ?_) (hu' hu)
        exact congrArg Finset.card <| hdegree_in_s hu
      · simp only [hu, or_true, forall_const, true_and]
        refine ne_of_eq_of_ne (Eq.symm <| ?_) (hu' hu)
        exact congrArg Finset.card <| hdegree_in_s' hu
  · intro x hx
    obtain ⟨hx, hx'⟩ := mem_sdiff.mp hx
    rcases mem_union.mp hx with hx | hx
    · refine le_of_eq_of_le ?_ (hs x ?_)
      · refine congrArg Finset.card ?_
        ext u
        simp only [degree_in, mem_inter, mem_neighborFinset, mem_sdiff, mem_union, mem_filter,
          not_and, and_congr_right_iff]
        grind
      · simp only [degree_in, mem_filter, mem_union, not_and, mem_sdiff] at hx' ⊢
        refine ⟨hx, fun _ ↦ ?_⟩
        refine ne_of_eq_of_ne ?_ (hx' <| Or.inl hx)
        exact congrArg Finset.card (hdegree_in_s hx)
    · refine le_of_eq_of_le ?_ (hs' x ?_)
      · refine congrArg Finset.card ?_
        ext u
        simp only [degree_in, mem_inter, mem_neighborFinset, mem_sdiff, mem_union, mem_filter,
          not_and, and_congr_right_iff]
        intro hxu
        have hu' : u ∉ s := fun hu ↦ h u hu x hx hxu.symm
        grind
      · simp only [degree_in, mem_filter, mem_union, not_and, mem_sdiff] at hx' ⊢
        refine ⟨hx, fun _ ↦ ?_⟩
        refine ne_of_eq_of_ne ?_ (hx' <| Or.inr hx)
        exact congrArg Finset.card (hdegree_in_s' hx)

lemma no_induced_K3_of_InducesForest {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V)
    {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) :
    G.InducesForest s → ¬{x, y, z} ⊆ s := by
  intro hf ht
  obtain ⟨w, hw, hwdeg⟩ := hf _ ht <| insert_ne_empty _ _
  simp only [mem_insert, mem_singleton] at hw
  simp only [degree_in] at hwdeg
  rcases hw with h | h | h <;> {
    suffices G.neighborFinset w ∩ {x, y, z} = ({x, y, z} : Finset _) \ {w} by
      grind [Adj.ne]
    subst h
    ext u
    simp only [mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true, inter_insert_of_notMem,
      mem_inter, mem_insert, mem_singleton, mem_sdiff]
    grind [Adj.ne, Adj.symm]
  }

lemma InducesLinearForest_mono' {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s₁ s₂ : Finset V} (hcap : s₁ ∩ s₂ = ∅)
    (hs : (G.deleteIncidencesOf s₂).InducesLinearForest s₁) :
    G.InducesLinearForest s₁ := by
  obtain ⟨hs, hsdeg⟩ := hs
  refine ⟨InducesForest_graph_mono' hcap hs, fun x hx ↦ le_trans ?_ <| hsdeg x hx⟩
  refine degree_in_deleteIncidencesOf_of_le (inter_comm s₁ s₂ ▸ hcap) ?_ (le_refl _)
  exact notMem_of_mem_of_empty_inter hx hcap

lemma InducesCaterpillar_mono' {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s₁ s₂ : Finset V} (hcap : s₁ ∩ s₂ = ∅)
    (hs : (G.deleteIncidencesOf s₂).InducesCaterpillar s₁) :
    G.InducesCaterpillar s₁ := by
  simp only [InducesCaterpillar] at hs
  refine @InducesLinearForest_mono' _ _ _ G _ _ s₂ ?_ ?_
  · ext u
    simp only [notMem_empty, iff_false, mem_inter, not_and]
    exact fun h ↦ notMem_of_mem_of_empty_inter (mem_sdiff.mp h |>.1) hcap
  · suffices (s₁ \ {x ∈ s₁ | (G.deleteIncidencesOf s₂).degree_in s₁ x = 1})
        = (s₁ \ {x ∈ s₁ | G.degree_in s₁ x = 1}) by
      exact this ▸ hs
    ext u
    simp only [mem_sdiff, mem_filter]
    constructor <;> {
      intro ⟨hus₁, h⟩
      simp only [hus₁, true_and] at h ⊢
      refine ne_of_eq_of_ne ?_ h
      refine le_antisymm_iff.mpr ?_
      simp only [degree_in_mono' deleteIncidencesOf_le, true_and, and_true]
      refine card_le_card ?_
      intro w
      simp only [mem_inter] at ⊢
      intro ⟨hw, hws₁⟩
      refine ⟨?_, hws₁⟩
      refine (mem_neighborFinset_deleteIncidencesOf_iff_of_notMem ?_ ?_).mp hw
      · exact notMem_of_mem_of_empty_inter hws₁ hcap
      · exact notMem_of_mem_of_empty_inter hus₁ hcap
    }

lemma InducesCaterpillar_union_deg_le_1 {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s₁ s₂ : Finset V} (hs₂ : ∀ x ∈ s₂, G.degree x ≤ 1)
    (hs₁ : G.InducesLinearForest s₁) :
    G.InducesCaterpillar (s₁ ∪ s₂) := by
  refine ⟨?_, ?_⟩
  · intro t ht htne
    if h : ∃ x, x ∈ t ∩ s₂ then
      obtain ⟨x, hx⟩ := h
      obtain ⟨hxt, hxs₂⟩ := mem_inter.mp hx
      exact ⟨x, hxt, le_trans degree_in_le_degree (hs₂ _ hxs₂)⟩
    else
      simp only [mem_inter, not_exists, not_and] at h
      refine hs₁.1 t ?_ htne
      intro x hxt
      have hxt' := ht hxt
      simp only [degree_in, mem_sdiff, mem_union, mem_filter, not_and] at hxt' ⊢
      obtain ⟨hx, hd⟩ := hxt'
      rcases hx with hx | hx
      · exact hx
      · exact h x hxt hx |>.elim
  · intro x hx
    simp only [degree_in, mem_sdiff, mem_union, mem_filter, not_and] at hx
    obtain ⟨hxs, hxd⟩ := hx
    rcases hxs with hxs₁ | hxs₂
    · refine le_trans ?_ (hs₁.2 x hxs₁)
      refine card_le_card ?_
      intro u hu
      simp only [degree_in, mem_inter, mem_neighborFinset, mem_sdiff, mem_union, mem_filter,
        not_and] at hu ⊢
      obtain ⟨hxu, hus, hu⟩ := hu
      refine ⟨hxu, ?_⟩
      refine hus.elim (·) (fun hus₂ ↦ ?_)
      simp only [hus, forall_const] at hu
      have : #(G.neighborFinset u ∩ (s₁ ∪ s₂)) = 0 := by
        refine le_antisymm ?_ (Nat.zero_le _)
        grind [degree_in_le_degree]
      suffices x ∈ (∅ : Finset _) by grind
      rw [← card_eq_zero.mp this]
      exact mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr hxu.symm, mem_union_left _ hxs₁⟩
    · exact le_trans degree_in_le_degree (le_trans (hs₂ x hxs₂) NeZero.one_le)

lemma InducesCaterpillar_iff {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (s : Finset V) :
    G.InducesCaterpillar s ↔ G.InducesForest s ∧
      ∀ v x y z, v ∈ s → x ∈ s → y ∈ s → z ∈ s → x ≠ y → x ≠ z → y ≠ z
        → 3 ≤ G.degree_in s v → 2 ≤ G.degree_in s x → 2 ≤ G.degree_in s y → 2 ≤ G.degree_in s z
        → G.Adj v x → G.Adj v y → ¬G.Adj v z := by
  constructor
  · intro hs
    refine ⟨InducesForest_of_InducesCaterpillar G hs, ?_⟩
    intro v x y z hvs hxs hys hzs hxy hxz hyz hdv hdx hdy hdz hvx hvy hvz
    have : 3 ≤ G.degree_in (s \ {x ∈ s | G.degree_in s x = 1}) v := by
      have : #({x, y, z} : Finset _) = 3 := by grind
      refine this ▸ card_le_card ?_
      refine subset_inter_iff.mpr ⟨by grind [mem_neighborFinset], ?_⟩
      intro u hu
      simp only [mem_insert, mem_singleton] at hu
      refine mem_sdiff.mpr ⟨by grind, ?_⟩
      simp only [degree_in, mem_filter, not_and]
      grind
    have H := by
      refine hs.2 v (mem_sdiff.mpr ⟨hvs, ?_⟩)
      simp only [mem_filter, hvs, true_and]
      have : 3 ≤ G.degree_in s v := le_trans this (degree_in_mono sdiff_subset)
      lia
    linarith
  · intro ⟨hsf, h⟩
    refine ⟨fun t ht ↦ hsf t (subset_eq_inter ht), ?_⟩
    intro v hv
    simp only [mem_sdiff, mem_filter, not_and] at hv
    obtain ⟨hvs, hvd⟩ := hv
    simp only [hvs, forall_const] at hvd
    by_contra
    simp only [not_le] at this
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset_three_le_card_iff _ |>.mp this
    have h2led {u : V} : u ∈ G.neighborFinset v ∩ (s \ {x ∈ s | G.degree_in s x = 1})
        → 2 ≤ G.degree_in s u := by
      intro hu
      suffices G.degree_in s u ≠ 0 ∧ G.degree_in s u ≠ 1 by lia
      refine ⟨?_, by grind⟩
      suffices 1 ≤ G.degree_in s u by linarith
      rw [degree_in, ← card_singleton v]
      refine card_le_card ?_
      refine singleton_subset_iff.mpr <| mem_inter.mpr ⟨?_, hvs⟩
      exact mem_neighborFinset_symm <| mem_inter.mp hu |>.1
    refine h v x y z hvs (mem_sdiff.mp (mem_inter.mp hx |>.2) |>.1)
      (mem_sdiff.mp (mem_inter.mp hy |>.2) |>.1) (mem_sdiff.mp (mem_inter.mp hz |>.2) |>.1)
      hxy hxz hyz (le_trans this (degree_in_mono sdiff_subset)) (h2led hx) (h2led hy) (h2led hz)
      (mem_neighborFinset .. |>.mp <| mem_inter.mp hx |>.1)
      (mem_neighborFinset .. |>.mp <| mem_inter.mp hy |>.1) ?_
    exact mem_neighborFinset .. |>.mp <| mem_inter.mp hz |>.1

lemma InducesCaterpillar_graph_mono' {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s₁ s₂ : Finset V} (hs : s₁ ∩ s₂ = ∅)
    (h : (G.deleteIncidencesOf s₂).InducesCaterpillar s₁) :
    G.InducesCaterpillar s₁ := by
  obtain ⟨hs₁f, h⟩ := InducesCaterpillar_iff _ |>.mp h
  refine InducesCaterpillar_iff _ |>.mpr ⟨InducesForest_graph_mono' hs hs₁f, ?_⟩
  intro v x y z hv hx hy hz hxy hxz hyz hdv hdx hdy hdz hvx hvy
  have hs' := inter_comm s₁ s₂ ▸ hs
  have := by
    refine h v x y z hv hx hy hz hxy hxz hyz
      (le_of_le_of_eq hdv <| Eq.symm <| degree_in_deleteIncidencesOf _ _ hs'
        (notMem_of_mem_of_empty_inter hv hs))
      (le_of_le_of_eq hdx <| Eq.symm <| degree_in_deleteIncidencesOf _ _ hs'
        (notMem_of_mem_of_empty_inter hx hs))
      (le_of_le_of_eq hdy <| Eq.symm <| degree_in_deleteIncidencesOf _ _ hs'
        (notMem_of_mem_of_empty_inter hy hs))
      (le_of_le_of_eq hdz <| Eq.symm <| degree_in_deleteIncidencesOf _ _ hs'
        (notMem_of_mem_of_empty_inter hz hs))
      (deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj
        (notMem_of_mem_of_empty_inter hv hs) (notMem_of_mem_of_empty_inter hx hs) hvx)
      (deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj
        (notMem_of_mem_of_empty_inter hv hs) (notMem_of_mem_of_empty_inter hy hs) hvy)
  refine not_iff_not.mpr (deleteIncidencesOf_adj_iff_of_notMem ?_ ?_) |>.mpr this
  · exact notMem_of_mem_of_empty_inter hv hs
  · exact notMem_of_mem_of_empty_inter hz hs

lemma InducesCaterpillar_pair {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v w : V} :
    G.InducesCaterpillar {v, w} := by
  refine ⟨InducesForest_mono sdiff_subset InducesForest_pair, ?_⟩
  exact fun x hx ↦ le_trans₃ (degree_in_le_card_minus_one_of_mem hx) (by grind) one_le_two

lemma InducesCaterpillar_singleton {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V} :
    G.InducesCaterpillar {v} :=
  pair_eq_singleton v ▸ G.InducesCaterpillar_pair

end SimpleGraph
