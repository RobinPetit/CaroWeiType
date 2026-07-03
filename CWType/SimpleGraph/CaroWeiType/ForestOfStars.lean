import CWType.SimpleGraph.CaroWeiType.Calc
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.ABLemma

import CWType.SimpleGraph.CaroWeiType.Forests.Basic
import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas

import Mathlib.Combinatorics.SimpleGraph.Circulant

namespace SimpleGraph

private def Λ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  {v | G.degree v = 1}

lemma Λ_subset_support {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] :
    G.Λ ⊆ G.support.toFinset := by
  intro v hv
  simp only [Λ, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  exact Set.mem_toFinset.mpr <| (degree_pos_iff_mem_support G v).mp <| Nat.lt_of_sub_eq_succ hv

end SimpleGraph

open SimpleGraph
open Finset

namespace CaroWeiType
open AB

private lemma inter_empty_of_subset {α : Type*} [DecidableEq α] {X Y Z : Finset α}
    (h : X ⊆ Y) (h' : Y ∩ Z = ∅) :
    X ∩ Z = ∅ := by
  refine subset_empty.mp ?_
  intro x hx
  obtain ⟨hxX, hxZ⟩ := mem_inter.mp hx
  exact h' ▸ mem_inter.mpr ⟨h hxX, hxZ⟩

private lemma inter_empty_of_subset' {α : Type*} [DecidableEq α] {X Y Z : Finset α}
    (h : X ⊆ Y) (h' : Y ∩ Z = ∅) :
    Z ∩ X = ∅ := by
  rw [inter_comm Z X]
  exact inter_empty_of_subset h h'

lemma deleteIncidencesOf_support' {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset V} :
    (G.deleteIncidencesOf s).support.toFinset ∩ s = ∅ := by
  ext v
  simp only [mem_inter, Set.mem_toFinset, notMem_empty, iff_false, not_and']
  intro hv
  have := by
    refine @deleteIncidencesOf_support _ G _ (G.support.toFinset) s ?_
    simp only [Set.coe_toFinset, subset_refl]
  simp only [coe_sdiff, Set.coe_toFinset] at this
  intro H
  have := this H
  simp only [Set.mem_diff, SetLike.mem_coe, hv, not_true_eq_false, and_false] at this

private lemma singleton_of_mem {α : Type*} {s : Finset α} {x : α} (hs : #s = 1) (hx : x ∈ s) :
    s = {x} := by
  refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
  · exact singleton_subset_iff.mpr hx
  · rw [hs, card_singleton]

lemma adj_leaves {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y u v : V} (hxy : G.Adj x y) (hxΛ : x ∈ G.Λ) (hyΛ : y ∈ G.Λ)
    (hu : u ∈ ({x, y} : Finset _)) (hv : v ∉ ({x, y} : Finset _)) :
    ¬G.Adj u v := by
  simp only [mem_insert, mem_singleton] at hu
  rcases hu with hu | hu
  · have hNw : G.neighborFinset u = {y} := by
      refine singleton_of_mem ?_ ?_
      · simpa only [Λ, ← hu, mem_filter, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
          mem_of_singleton_inter_ne_emty, true_and] using hxΛ
      · exact hu ▸ (mem_neighborFinset .. |>.mpr hxy)
    exact not_iff_not.mpr (mem_neighborFinset ..) |>.mp <| by grind
  · have hNw : G.neighborFinset u = {x} := by
      refine singleton_of_mem ?_ ?_
      · simpa only [Λ, ← hu, mem_filter, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
          mem_of_singleton_inter_ne_emty, true_and] using hyΛ
      · exact hu ▸ (mem_neighborFinset .. |>.mpr hxy.symm)
    exact not_iff_not.mpr (mem_neighborFinset ..) |>.mp <| by grind

lemma Λ_sdiff_eq {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V} (hxy : G.Adj x y) (hxΛ : x ∈ G.Λ) (hyΛ : y ∈ G.Λ) :
    (G.deleteIncidencesOf {x, y}).Λ = G.Λ \ {x, y} := by
  ext v
  simp only [Λ, mem_filter, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
    mem_of_singleton_inter_ne_emty, true_and, mem_sdiff]
  have H {v : V} (hvxy : v ∉ ({x, y} : Finset _)) : {x, y} ∩ G.neighborFinset v = ∅ := by
    ext w
    simp only [mem_inter, mem_neighborFinset, notMem_empty, iff_false, not_and]
    exact fun hw ↦ not_adj_symm <| adj_leaves hxy hxΛ hyΛ hw hvxy
  constructor
  · intro hdv
    have hv_xy : v ∉ ({x, y} : Finset _) := by
      intro hv
      have : (G.deleteIncidencesOf {x, y}).degree v = 0 := by
        exact deleteIncidencesOf_degree_eq_zero_of_mem hv
      linarith
    refine ⟨?_, hv_xy⟩
    rw [← hdv]
    exact degree_eq_deleteIncidencesOf_degree_of_inter_neighborhood_empty hv_xy (H hv_xy)
  · intro ⟨hdv, hv_xy⟩
    rw [← hdv]
    exact Eq.symm <| degree_eq_deleteIncidencesOf_degree_of_inter_neighborhood_empty hv_xy (H hv_xy)

lemma adj_leaves_support {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V} (hxy : G.Adj x y) (hxΛ : x ∈ G.Λ) (hyΛ : y ∈ G.Λ) :
    (G.deleteIncidencesOf {x, y}).support = G.support \ {x, y} := by
  ext v
  constructor
  · intro hv
    refine Set.mem_diff _ |>.mpr ⟨?_, ?_⟩
    · obtain ⟨w, hw⟩ := mem_support .. |>.mp hv
      exact mem_support .. |>.mpr ⟨w, adj_of_deleteIncidencesOf_adj hw⟩
    · have := notMem_of_empty_inter_of_mem' deleteIncidencesOf_support' (Set.mem_toFinset.mpr hv)
      grind
  · simp only [Set.mem_diff]
    intro ⟨hv, hvxy⟩
    obtain ⟨w, hvw⟩ := mem_support .. |>.mp hv
    refine mem_support .. |>.mpr ⟨w, ?_⟩
    refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ hvw
    · grind
    · exact fun hw ↦ adj_leaves hxy hxΛ hyΛ hw (by grind : v ∉ {x, y}) hvw.symm

namespace GraphParameter

def ForestOfStars : GraphParameter where
  toFun := fun G _ s ↦ G.InducesForestOfStars s
  invariant := by
    intro V V' _ _ _ _ G _ G' _ φ s
    constructor
    · exact InducesForestOfStars_of_iso φ
    · intro h
      suffices (image φ.symm.toFun (image φ.toFun s)) = s by
        exact this ▸ (InducesForestOfStars_of_iso φ.symm h)
      ext
      simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, mem_image, exists_exists_and_eq_and,
        RelIso.symm_apply_apply, exists_eq_right]

end GraphParameter

private noncomputable def φ (ε : ℝ) (d : ℕ) : ℝ :=
  if      d = 0 then 1
  else if d = 1 then 1 - ε
  else if d = 2 then min (1 / (2 : ℝ) + ε) (3 / (5 : ℝ))
  else               min (1 / (d : ℝ) + ε) (2 / (d + 1 : ℝ))

private lemma φ_le_1 {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) : φ ε d ≤ 1 := by
  if hd0 : d = 0 then
    simp only [φ, hd0, ↓reduceIte, le_refl]
  else if hd1 : d = 1 then
    simp only [φ, hd1, one_ne_zero, ↓reduceIte]
    exact sub_le_self 1 hε
  else if hd2 : d = 2 then
    simp only [φ, hd0, hd1]
    simp only [hd2, ↓reduceIte]
    exact Std.min_le_right.trans (by linarith)
  else
    have : φ ε d ≤ 2 / (d + 1 : ℝ) := by grind [φ]
    refine le_trans this ?_
    refine (div_le_one₀ add_one_pos).mpr ?_
    rw [← Nat.cast_two, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    lia

private lemma φ_decreasing {d d' : ℕ} (h : d' ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 6) :
    φ ε d ≤ φ ε d' := by
  simp only [φ]
  split_ifs
  any_goals grind
  · refine le_trans Std.min_le_right ?_
    refine (div_le_one₀ add_one_pos).mpr ?_
    rw [← Nat.cast_two, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    lia
  · have : 2 / (d + 1 : ℝ) ≤ 2 / 3 := by
      refine (div_le_div_iff_of_pos_left two_pos add_one_pos three_pos).mpr ?_
      rw [← Nat.cast_three, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
      lia
    exact le_trans₃ Std.min_le_right (by linarith) (tsub_le_tsub_left hε' 1)
  · have : min (1 / ↑d + ε) (2 / (↑d + 1)) ≤ 1 / 2 := by
      refine le_trans Std.min_le_left ?_
      have : 1 / (d : ℝ) + ε ≤ 1 / 3 + ε := by
        have : 3 ≤ d := by lia
        refine add_le_add_iff_right _ |>.mpr ?_
        refine (one_div_le_one_div ?_ three_pos).mpr ?_
        · simp only [Nat.cast_pos]
          lia
        · simp [this]
      linarith
    refine le_trans this ?_; clear this
    simp only [le_inf_iff, le_add_iff_nonneg_right, hε, true_and]
    linarith
  · simp only [le_inf_iff, inf_le_iff, add_le_add_iff_right]
    refine ⟨Or.inl ?_, Or.inr ?_⟩
    · refine one_div_le_one_div_of_le ?_ ?_
      · simp only [Nat.cast_pos]
        lia
      · simp only [Nat.cast_le, h]
    · refine div_le_div_of_nonneg_left zero_le_two add_one_pos ?_
      simp only [add_le_add_iff_right, Nat.cast_le, h]

private lemma cycle_not_forest {n : ℕ} :
    ¬(cycleGraph (n + 3)).InducesForest univ := by
  simp only [InducesForest, IsDegenerateSet, subset_univ, ne_eq, degree_in, forall_const,
    not_forall, not_exists, not_and, not_le]
  refine ⟨univ, ?_, ?_⟩
  · exact nonempty_iff_ne_empty.mp <| ⟨⟨0, by linarith⟩, mem_univ ..⟩
  · simp only [inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
      mem_of_singleton_inter_ne_emty, card_neighborFinset_eq_degree, cycleGraph_degree_three_le,
      Nat.one_lt_ofNat, imp_self, implies_true]

private lemma _f2_ok (f : ℕ → ℝ)
    (hf : IsCaroWeiTypeLowerBound f GraphParameter.ForestOfStars) :
    f 2 ≤ 3 / 5 := by
  obtain ⟨s, hsf, hscard⟩ := hf (cycleGraph 5)
  simp only [GraphParameter.ForestOfStars] at hsf
  have : ∀ v, (cycleGraph 5).degree v = 2 := fun v ↦ cycleGraph_degree_three_le
  have hf2 : 5 * f 2 ≤ #s := by
    refine le_of_eq_of_le ?_ hscard
    have : ∑ v, f ((cycleGraph 5).degree v) = ∑ (v : Fin 5), f 2 :=
      sum_congr rfl fun v _ ↦ congrArg f cycleGraph_degree_three_le
    rw [this]; clear this
    simp only [sum_const', card_univ, Fintype.card_fin, Nat.cast_ofNat]
  suffices (#s : ℝ) ≤ 3 by linarith
  rw [← Nat.cast_three, Nat.cast_le]
  have hs' : s ≠ univ := by
    refine ne_of_ne_congr (cycleGraph 5).InducesForest ?_
    simp only [cycle_not_forest, InducesForest_of_InducesForestOfStars _ hsf]
    exact true_ne_false
  have : ∃ x, x ∉ s := by
    have : ¬univ ⊆ s := fun h ↦ hs' (univ_subset_iff.mp h) |>.elim
    obtain ⟨x, hx, hxs⟩ := Set.not_subset.mp this
    refine ⟨x, hxs⟩
  obtain ⟨x, hxs⟩ := this
  by_contra hcard
  have : s = univ \ {x} := by
    refine eq_of_subset_of_card_le ?_ ?_
    · exact fun _ h ↦ mem_sdiff.mpr ⟨mem_univ _, notMem_singleton.mpr (ne_of_mem_of_not_mem h hxs)⟩
    · rw [card_sdiff]
      simp only [card_univ, Fintype.card_fin, inter_univ, card_singleton, Nat.add_one_sub_one]
      linarith
  have := by
    refine InducesForestOfStars_iff.mp hsf |>.2 (x+1) (x+2) (x+3) (x+4) ?_ ?_ ?_ ?_ ?_ ?_
    <;> simp [this]
  simp [cycleGraph] at this

private lemma _f_ok_6_le_d {d : ℕ} (hd : 0 < d) (hd' : 6 ≤ d) :
    2 / (d + 1 : ℝ) ≤ 1 / d + 1 / 6 := by
  refine le_of_lt ?_
  calc 2 / (d + 1 : ℝ)
    _ < 2 / d := by
      refine div_lt_div_of_pos_left two_pos (Nat.cast_pos'.mpr hd) ?_
      simp only [lt_add_iff_pos_right, zero_lt_one]
    _ = 1 / d + 1 / d := by
      grind only
    _ ≤ 1 / d + 1 / 6 := by
      simp only [add_le_add_iff_left]
      exact one_div_le_one_div (Nat.cast_pos'.mpr hd) six_pos |>.mpr <| Nat.ofNat_le_cast.mpr hd'

def K' (n : ℕ) : SimpleGraph (Fin n × Fin 2) where
  Adj u v := u ≠ v ∧ (u.2 = 0 ∧ v.2 = 0 ∨ u.2 = 1 ∧ u.1 = v.1 ∨ v.2 = 1 ∧ u.1 = v.1)

instance {n : ℕ} : DecidableRel (K' n |>.Adj) := by
  simp only [K']
  infer_instance

private lemma fos_K'n {d : ℕ} (hd : 1 ≤ d) {s : Finset _} (hs : (K' d).InducesForestOfStars s) :
    #s ≤ d + 1 := by
  have : #(s ∩ ({x : Fin d × Fin 2 | x.2 = 0} : Finset _)) ≤ 2 := by
    refine card_le_2_iff_no_triplet.mpr ?_
    intro x y z ⟨hxney, hxnez, hynez⟩
    suffices x.2 = 0 ∧ y.2 = 0 ∧ z.2 = 0 → ¬{x, y, z} ⊆ s by
      by_contra H
      refine this ?_ ?_
      · refine ⟨?_, ?_, ?_⟩
        · have := mem_inter.mp (@H x (by member_of)) |>.2
          simpa only [mem_filter, mem_univ, true_and] using this
        · have := mem_inter.mp (@H y (by member_of)) |>.2
          simpa only [mem_filter, mem_univ, true_and] using this
        · have := mem_inter.mp (@H z (by member_of)) |>.2
          simpa only [mem_filter, mem_univ, true_and] using this
      · exact fun u hu ↦ mem_inter.mp (H hu) |>.1
    intro ⟨hx, hy, hz⟩
    refine @no_induced_K3_of_InducesForest _ _ _ _ _ _ x y z ?_ ?_ ?_
        (InducesForest_of_InducesForestOfStars _ hs) <;> grind [K']
  have : #(s ∩ ({x : Fin d × Fin 2 | x.2 = 0} : Finset _)) ≤ 1
      ∨ #(s ∩ ({x : Fin d × Fin 2 | x.2 = 0} : Finset _)) = 2 := by lia
  have hs' : s = (s ∩ ({x : Fin d × Fin 2 | x.2 = 1} : Finset _))
            ∪ (s ∩ ({x : Fin d × Fin 2 | x.2 = 0} : Finset _)) := by
    ext x
    simp only [Fin.isValue, mem_union, mem_inter, mem_filter, inter_univ, ne_eq, singleton_ne_empty,
      not_false_eq_true, mem_of_singleton_inter_ne_emty, true_and]
    grind
  have Hs : (s ∩ ({x : Fin d × Fin 2 | x.2 = 1} : Finset _)) ∩
           (s ∩ ({x : Fin d × Fin 2 | x.2 = 0} : Finset _)) = ∅ := by
    grind
  have hcard1 : #({x : Fin d × Fin 2 | x.2 = 1} : Finset _) = d := by
    let f : Fin d → Fin d × Fin 2 := (⟨·, 1⟩)
    have : #{x : Fin d × Fin 2 | x.2 = 1} = #(univ.image f) := by
      refine congrArg Finset.card ?_
      grind
    rw [this]; clear this
    have : #(image f univ) = #(@Finset.univ (Fin d) _) := by
      refine card_image_iff.mpr ?_
      intro x hx y hy h
      simpa only [Fin.isValue, Prod.mk.injEq, and_true, f] using h
    rw [this]; clear this
    simp only [card_univ, Fintype.card_fin]
  rcases this with H | H
  · rw [hs', card_union, Hs, card_empty, tsub_zero]
    refine add_le_add ?_ H
    refine le_of_le_of_eq (card_le_card inter_subset_right) hcard1
  · rw [hs', card_union, Hs, card_empty, tsub_zero, H]
    suffices #(s ∩ ({x : Fin d × Fin 2 | x.2 = 1} : Finset _)) ≤ d - 1 by lia
    suffices ∃ x, x.2 = 1 ∧ x ∉ s by
      obtain ⟨x, hx, hxs⟩ := this
      have : (s ∩ ({x : Fin d × Fin 2 | x.2 = 1} : Finset _))
          ⊆ ({x : Fin d × Fin 2 | x.2 = 1} : Finset _) \ {x} := by
        intro y hy
        simp only [Fin.isValue, mem_inter, mem_filter, inter_univ, ne_eq, singleton_ne_empty,
          not_false_eq_true, mem_of_singleton_inter_ne_emty, true_and, mem_sdiff,
          mem_singleton] at hy ⊢
        exact ⟨hy.2, ne_of_mem_of_not_mem hy.1 hxs⟩
      refine le_trans (card_le_card this) ?_
      rw [card_sdiff]
      have : (({x} : Finset _) ∩ ({x : Fin d × Fin 2 | x.2 = 1} : Finset _)) = {x} := by
        simp only [Fin.isValue, ne_eq, singleton_inter_eq_empty_iff, mem_filter, mem_univ, hx,
          and_self, not_true_eq_false, not_false_eq_true, mem_of_singleton_inter_ne_emty,
          singleton_inter_of_mem]
      rw [this, card_singleton]; clear this
      lia
    by_contra hins
    simp only [Fin.isValue, Prod.exists, exists_eq_left, not_exists, Decidable.not_not] at hins
    have := InducesForestOfStars_iff.mp hs |>.2
    obtain ⟨x, y, hxney, h⟩ := Finset_card_eq_two_iff _ H
    refine this ⟨x.1, 1⟩ x y ⟨y.1, 1⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact hins _
    · have hx : x ∈ ({x, y} : Finset _) := by member_of
      rw [← h] at hx
      exact mem_inter.mp hx |>.1
    · have hy : y ∈ ({x, y} : Finset _) := by member_of
      rw [← h] at hy
      exact mem_inter.mp hy |>.1
    · exact hins _
    · grind
    · grind
    · grind [K']
    · grind [K']
    · grind [K']

private lemma fK'n {d : ℕ} (hd : 1 ≤ d) (f : ℕ → ℝ)
    (hf : IsCaroWeiTypeLowerBound f GraphParameter.ForestOfStars) :
    d * (f d + f 1) ≤ d + 1 := by
  obtain ⟨s, hsf, hscard⟩ := hf (K' d)
  have : (#s : ℝ) ≤ d + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    exact fos_K'n hd hsf
  refine le_trans₃ (le_of_eq ?_) hscard this
  let g : Fin d → Finset (Fin d × Fin 2) := fun v ↦ {⟨v, 0⟩, ⟨v, 1⟩}
  have := by
    refine @split_sum _ _ _ _ _ (fun v ↦ f ((K' d).degree v)) univ univ g ?_ ?_
    · ext u
      simp only [mem_sup, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
        mem_of_singleton_inter_ne_emty, true_and, iff_true, g]
      refine ⟨u.1, ?_⟩
      suffices u.2 ∈ ({0, 1} : Finset (Fin 2)) by grind
      have : @Finset.univ (Fin 2) _ = {0, 1} := rfl
      rw [← this]
      exact mem_univ _
    · exact fun x y hxney ↦ by grind
  rw [this]; clear this
  simp only [Fin.isValue, mem_singleton, Prod.mk.injEq, zero_ne_one, and_false, not_false_eq_true,
    sum_insert, sum_singleton, g]
  rw [@sum_const' _ _ (f d + f 1) _]
  · simp only [card_univ, Fintype.card_fin]
  · intro x _
    refine add_congr ?_ ?_
    · refine congrArg _ ?_
      suffices (K' d).neighborFinset ⟨x, 0⟩
          = ({y | y.2 = 0 ∧ y.1 ≠ x} : Finset (Fin d × Fin 2)) ∪ {⟨x, 1⟩} by
        rw [degree, this, card_union, card_singleton]
        simp only [Fin.isValue, ne_eq, mem_filter, inter_univ, singleton_ne_empty,
          not_false_eq_true, mem_of_singleton_inter_ne_emty, one_ne_zero, not_true_eq_false,
          and_self, and_false, inter_singleton_of_notMem, card_empty, tsub_zero]
        suffices ({y | y.2 = 0 ∧ ¬y.1 = x} : Finset (Fin d × Fin 2))
            = (univ \ {x}).image (fun v ↦ ⟨v, 0⟩) by
          rw [this]
          suffices #(image (fun v ↦ ((v, 0) : Fin d × Fin 2)) (univ \ {x})) = d - 1 by
            have := (@Nat.add_left_inj _ _ 1).mpr this
            rw [this, Nat.sub_add_cancel hd]
          have : #(@Finset.univ (Fin d) _ \ {x}) = d - 1 := by
            rw [card_sdiff, inter_univ, card_fin d, card_singleton]
          rw [← this]
          refine card_image_iff.mpr ?_
          intro u hu v hv hne
          simpa only [Fin.isValue, Prod.mk.injEq, and_true] using hne
        grind
      ext y
      simp only [K', ne_eq, Fin.isValue, mem_neighborFinset, true_and, zero_ne_one, false_and,
        false_or, union_singleton, mem_insert, mem_filter, inter_univ, singleton_ne_empty,
        not_false_eq_true, mem_of_singleton_inter_ne_emty]
      grind
    · refine congrArg _ ?_
      suffices (K' d).neighborFinset ⟨x, 1⟩ = {⟨x, 0⟩} by
        have := congrArg Finset.card this
        rw [degree, this, card_singleton]
      ext y
      simp only [K', ne_eq, Fin.isValue, mem_neighborFinset, one_ne_zero, false_and, true_and,
        false_or, mem_singleton]
      grind

private lemma _lb_bounded_by_extremal (f : ℕ → ℝ)
    (hf : IsCaroWeiTypeLowerBound f GraphParameter.ForestOfStars) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ 1 / 6 ∧ f ≤ φ ε := by
  have hfle1 : ∀ d, f d ≤ 1 := f_le_1_of_IsCaroWeiTypeLowerBound hf
  have fKn : ∀ d ≥ 2, f d ≤ 2 / (d + 1 : ℝ) := by
    intro d hd
    rw [← Nat.cast_two]
    refine f_on_complete_graph' hf ?_
    intro s hs
    simp only [GraphParameter.ForestOfStars] at hs
    have hf := InducesForest_of_InducesForestOfStars _ hs
    refine card_le_2_iff_no_triplet.mpr ?_
    intro x y z hne
    refine no_induced_K3_of_InducesForest _ _ ?_ ?_ ?_ hf
    <;> simp [hne, Ne.symm]
  have fK'n : ∀ d ≥ 2, d * (f d + f 1) ≤ d + 1 := fun _ _ ↦ fK'n (by linarith) _ hf
  let ε := 1 - f 1
  have hε_nonneg : 0 ≤ ε := by linarith [hfle1 1]
  if hkε : 1 / 6 ≤ ε then
    refine ⟨1 / 6, by linarith, le_refl _, ?_⟩
    · intro d
      simp only [φ]
      split_ifs
      · exact hfle1 _
      · rename_i hd
        subst hd
        linarith
      · suffices f d ≤ 3 / 5 by
          refine le_of_le_of_eq this <| right_eq_inf.mpr <| by linarith
        rename_i hd
        exact hd ▸ _f2_ok f hf
      · suffices f d ≤ 2 / (d + 1 : ℝ) by
          refine le_of_le_of_eq this <| right_eq_inf.mpr ?_
          have : 3 ≤ d := by lia
          if hd : 6 ≤ d then
            exact _f_ok_6_le_d (by lia) hd
          else
            have : d = 3 ∨ d = 4 ∨ d = 5 := by lia
            clear * - this
            rcases this with hd | hd | hd <;> { rw [hd]; linarith }
        exact fKn _ (by lia)
  else
    have fK'n : ∀ d ≥ 2, f d ≤ 1 / d + ε := by
      intro d hd
      have := fK'n _ hd
      have : f d + f 1 ≤ (d + 1) / d := by
        refine (le_div_iff₀' ?_).mpr this
        rw [← Nat.cast_zero, Nat.cast_lt]
        exact Nat.zero_lt_of_lt hd
      have : f d ≤ (d + 1) / d - f 1 := by linarith
      have tmp : f 1 = 1 - ε := by linarith
      rw [tmp] at this; clear tmp
      ring_nf at this
      rw [CommGroupWithZero.mul_inv_cancel (d : ℝ)] at this
      · grind
      · rw [← Nat.cast_zero]
        simp only [CharP.cast_eq_zero, ne_eq, Nat.cast_eq_zero]
        linarith
    refine ⟨ε, hε_nonneg, le_of_not_ge hkε, ?_⟩
    intro d
    simp only [φ]
    split_ifs
    · exact hfle1 _
    · lia
    · refine le_min ?_ (by simp_all [_f2_ok f hf])
      refine le_of_le_of_eq (fK'n d (by linarith)) ?_
      rename_i hd
      rw [← Nat.cast_two, hd]
    · refine le_min ?_ (fKn _ (by lia))
      exact fK'n d (by lia)

private lemma _f_is_lb_support_no_adj_leaves {V : Type} [DecidableEq V] [Fintype V]
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 6)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hΛ : ∀ x ∈ G.Λ, ∀ y ∈ G.Λ, ¬G.Adj x y) :
    ∃ s : Finset V, s ⊆ G.support.toFinset ∧ GraphParameter.ForestOfStars.toFun G s ∧
      ∑ v ∈ G.support, φ ε (G.degree v) ≤ #s := by
  let AB' : Bipartition V := {
    A x := x ∈ G.support.toFinset \ G.Λ ∧ (G.neighborFinset x ∩ G.Λ) = ∅
    B x := x ∈ G.support.toFinset \ G.Λ ∧ (G.neighborFinset x ∩ G.Λ) ≠ ∅
    sound := by grind only
  }
  have : AB'.Decidable := by refine { A := ?_, B := ?_ } <;> infer_instance
  obtain ⟨s, hs, hsf, hsresp, hscard⟩ := by
    refine ABLemma (G.deleteIncidencesOf G.Λ) AB' ?_
    intro x hx
    simp only [SetLike.mem_coe]
    refine AB'.mem_toFinset.mp <| AB'.mem_iff.mpr ?_
    obtain ⟨y, hy⟩ := mem_support .. |>.mp hx
    have hxΛ : x ∉ G.Λ := notMem_of_adj_deleteIncidencesOf' hy.symm
    simp only [mem_sdiff, Set.mem_toFinset, hxΛ, not_false_eq_true, and_true, ne_eq, AB']
    have : x ∈ G.support := Set.mem_diff .. |>.mp (deleteIncidencesOf_support_subset hx) |>.1
    simp only [this, true_and, Classical.em]
  have hsΛ : s ∩ G.Λ = ∅ := by
    ext x
    simp only [mem_inter, notMem_empty, iff_false, not_and]
    intro hx
    have := AB'.mem_iff.mp <| AB'.mem_toFinset.mpr <| hs hx
    simp only [ne_eq, AB'] at this
    grind
  have hAB' : AB'.toFinset = G.support.toFinset \ G.Λ := by
    ext
    simp only [ne_eq, ← AB'.mem_toFinset, mem_sdiff, Set.mem_toFinset, Bipartition.mem_iff, AB']
    grind
  have hs' : s ⊆ G.support.toFinset := subset_trans hs (hAB' ▸ sdiff_subset)
  refine ⟨s ∪ G.Λ, ?_, ?_, ?_⟩
  · exact union_subset_iff.mpr ⟨hs', Λ_subset_support⟩
  · simp only [GraphParameter.ForestOfStars]
    obtain ⟨hsforest, hsf⟩ := InducesForestOfStars_iff.mp hsf
    refine InducesForestOfStars_iff.mpr ⟨?_, ?_⟩
    · refine IsDegenerateSet_union _ _ _ (InducesForest_graph_mono' hsΛ hsforest) ?_
      intro x hx
      refine le_of_le_of_eq degree_in_le_degree ?_
      simpa [Λ] using hx
    · intro u v w x hu hv hw hx hunew hvnex huv hvw
      have hvs : v ∈ s := by
        rcases mem_union.mp hv with hv | hv
        · exact hv
        · simp only [Λ, mem_filter, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
            mem_of_singleton_inter_ne_emty, true_and] at hv
          suffices 2 ≤ G.degree v by linarith
          rw [← card_pair hunew]
          refine card_le_card (fun z hz ↦ mem_neighborFinset .. |>.mpr ?_)
          grind [Adj.symm]
      match mem_union.mp hu, mem_union.mp hw with
      | _, Or.inr hwΛ =>
          simp only [Λ, mem_filter, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
            mem_of_singleton_inter_ne_emty, true_and] at hwΛ
          have hNw : G.neighborFinset w = {v} := by
            refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
            · simp only [singleton_subset_iff, mem_neighborFinset, hvw.symm]
            · rw [← degree, card_singleton, hwΛ]
          exact hNw ▸ not_iff_not.mpr (mem_neighborFinset ..) |>.mp
            <| notMem_singleton.mpr hvnex.symm
      | Or.inl hus, Or.inl hws =>
          intro hwx
          rcases mem_union.mp hx with hxs | hxΛ
          · refine hsf _ _ _ _ hus hvs hws hxs hunew hvnex ?_ ?_ ?_
            · refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ huv
              · exact notMem_of_mem_of_empty_inter hus hsΛ
              · exact notMem_of_mem_of_empty_inter hvs hsΛ
            · refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ hvw
              · exact notMem_of_mem_of_empty_inter hvs hsΛ
              · exact notMem_of_mem_of_empty_inter hws hsΛ
            · refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ hwx
              · exact notMem_of_mem_of_empty_inter hws hsΛ
              · exact notMem_of_mem_of_empty_inter hxs hsΛ
          · have hBw : AB'.B w := by
              have hwΛ : w ∉ G.Λ := notMem_of_mem_of_empty_inter hws hsΛ
              simp only [mem_sdiff, hs' hws, hwΛ, not_false_eq_true, and_self,
                singleton_inter_of_mem, ne_eq, singleton_ne_empty, mem_of_singleton_inter_ne_emty,
                true_and, AB']
              refine nonempty_iff_ne_empty.mp <| ⟨x, mem_inter.mpr ⟨?_, hxΛ⟩⟩
              exact mem_neighborFinset .. |>.mpr hwx
            obtain ⟨hAv, hd'v⟩ := by
              refine hsresp w hws hBw v hvs ?_
              refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ hvw
              · exact notMem_of_mem_of_empty_inter hvs hsΛ
              · exact notMem_of_mem_of_empty_inter hws hsΛ
            suffices 2 ≤ (G.deleteIncidencesOf G.Λ).degree_in s v by linarith
            rw [← card_pair hunew]
            refine card_le_card ?_
            intro z hz
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with hz | hz
            · refine hz ▸ mem_inter.mpr ⟨?_, hus⟩
              refine (mem_neighborFinset_deleteIncidencesOf_iff_of_notMem ?_ ?_).mp ?_
              · exact notMem_of_mem_of_empty_inter hus hsΛ
              · exact notMem_of_mem_of_empty_inter hvs hsΛ
              · exact mem_neighborFinset .. |>.mpr huv.symm
            · refine hz ▸ mem_inter.mpr ⟨?_, hws⟩
              refine (mem_neighborFinset_deleteIncidencesOf_iff_of_notMem ?_ ?_).mp ?_
              · exact notMem_of_mem_of_empty_inter hws hsΛ
              · exact notMem_of_mem_of_empty_inter hvs hsΛ
              · exact mem_neighborFinset .. |>.mpr hvw
      | Or.inr huΛ, Or.inl hws =>
          have hBv : AB'.B v := by
            have hvΛ : v ∉ G.Λ := notMem_of_mem_of_empty_inter hvs hsΛ
            simp only [mem_sdiff, hs' hvs, hvΛ, not_false_eq_true, and_self, singleton_inter_of_mem,
              ne_eq, singleton_ne_empty, mem_of_singleton_inter_ne_emty, true_and, AB']
            refine nonempty_iff_ne_empty.mp ?_
            exact ⟨u, mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr huv.symm, huΛ⟩⟩
          obtain ⟨hAw, hd'w⟩ := by
            refine hsresp v hvs hBv w hws ?_
            refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ (id (adj_symm G hvw))
            <;> exact notMem_of_mem_of_empty_inter (by simp only [hvs, hws]) hsΛ
          rcases mem_union.mp hx with hxs | hxΛ
          · intro hwx
            suffices 2 ≤ (G.deleteIncidencesOf G.Λ).degree_in s w by linarith
            rw [← card_pair hvnex]
            refine card_le_card ?_
            intro z hz
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with hz | hz
            · refine hz ▸ mem_inter.mpr ⟨?_, hvs⟩
              refine (mem_neighborFinset_deleteIncidencesOf_iff_of_notMem ?_ ?_).mp ?_
              · exact notMem_of_mem_of_empty_inter hvs hsΛ
              · exact notMem_of_mem_of_empty_inter hws hsΛ
              · exact mem_neighborFinset .. |>.mpr hvw.symm
            · refine hz ▸ mem_inter.mpr ⟨?_, hxs⟩
              refine (mem_neighborFinset_deleteIncidencesOf_iff_of_notMem ?_ ?_).mp ?_
              · exact notMem_of_mem_of_empty_inter hxs hsΛ
              · exact notMem_of_mem_of_empty_inter hws hsΛ
              · exact mem_neighborFinset .. |>.mpr hwx
          · simp only [AB'] at hAw
            have := hAw.2 ▸ notMem_empty x
            simpa [hxΛ] using this
  · let g : V → Finset V := by
      intro v
      if v ∈ G.Λ then exact ∅
      else exact {v} ∪ G.neighborFinset v ∩ G.Λ
    have := by
      refine @split_sum _ _ _ _ _ (fun v ↦ φ ε (G.degree v)) (G.support.toFinset \ G.Λ)
          G.support.toFinset g ?_ ?_
      · ext x
        simp only [mem_sup, mem_sdiff, Set.mem_toFinset]
        if hx : x ∈ G.Λ then
          have hdx : G.degree x = 1 := by grind [Λ]
          obtain ⟨y, hxy⟩ := (degree_pos_iff_exists_adj G x).mp <| Nat.lt_of_sub_eq_succ hdx
          have hy : y ∉ G.Λ := fun hy ↦ hΛ x hx y hy hxy
          have hx' : x ∈ G.support := G.mem_support.mpr ⟨y, hxy⟩
          simp only [hx', iff_true]
          refine ⟨y, ⟨G.mem_support.mpr ⟨x, hxy.symm⟩, hy⟩, ?_⟩
          simp only [g, hy, ↓reduceDIte]
          exact mem_union.mpr <| Or.inr <| mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr hxy.symm, hx⟩
        else if hx' : x ∈ G.support then
          simp only [hx', iff_true]
          refine ⟨x, ⟨hx', hx⟩, ?_⟩
          simp only [g, hx, ↓reduceDIte]
          exact mem_union.mpr <| Or.inl <| mem_singleton.mpr rfl
        else
          simp only [hx', iff_false, not_exists, not_and, and_imp]
          intro z hz hzΛ
          simp only [singleton_union, dite_eq_ite, hzΛ, ↓reduceIte, mem_insert, mem_inter,
            mem_neighborFinset, hx, and_false, or_false, g]
          exact Ne.symm <| ne_of_mem_of_not_mem hz hx'
      · intro x y hxney
        simp only [singleton_union, dite_eq_ite, g]
        split_ifs
        · exact inter_self _
        · exact inter_empty_of_subset (subset_refl _) rfl
        · exact inter_empty_of_subset' (subset_refl _) rfl
        · ext z
          simp only [mem_inter, mem_insert, mem_neighborFinset, notMem_empty, iff_false, not_and,
            not_or]
          intro h
          rcases h with h | h
          · refine ⟨ne_of_eq_of_ne h hxney, by grind⟩
          · refine ⟨ne_of_mem_of_not_mem h.2 (by grind only), ?_⟩
            simp only [h.2, not_true_eq_false, imp_false]
            have hNz : G.neighborFinset z = {x} := by
              refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
              · simp only [singleton_subset_iff, mem_neighborFinset, h.1.symm,
                  singleton_inter_of_mem, ne_eq, singleton_ne_empty, not_false_eq_true,
                  mem_of_singleton_inter_ne_emty]
              · simp only [Λ, mem_filter, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
                  mem_of_singleton_inter_ne_emty, true_and] at h
                rw [card_singleton, ← degree, h.2]
            refine not_adj_symm <| not_iff_not.mpr (mem_neighborFinset ..) |>.mp <| hNz ▸ ?_
            exact notMem_singleton.mpr hxney.symm
    rw [this]; clear this
    have : ∀ x ∈ G.support.toFinset \ G.Λ, ∑ y ∈ g x, φ ε (G.degree y)
        = φ ε (G.degree x) + #(G.neighborFinset x ∩ G.Λ) * φ ε 1 := by
      intro x hx
      simp only [mem_sdiff, Set.mem_toFinset] at hx
      obtain ⟨hx, hxΛ⟩ := hx
      simp only [singleton_union, dite_eq_ite, hxΛ, ↓reduceIte, mem_inter, mem_neighborFinset,
        SimpleGraph.irrefl, and_self, not_false_eq_true, sum_insert, add_right_inj, g]
      rw [sum_const']
      intro y hy
      refine congrArg _ ?_
      simp only [Λ, mem_inter, mem_neighborFinset, mem_filter, inter_univ, ne_eq,
        singleton_ne_empty, not_false_eq_true, mem_of_singleton_inter_ne_emty, true_and] at hy
      exact hy.2
    have hφ1 : φ ε 1 = 1 - ε := by simp [φ]
    rw [sum_congr rfl this, hφ1]  --, sum_add_distrib]
    have : ∑ x ∈ G.support.toFinset \ G.Λ,
            (φ ε (G.degree x) + #(G.neighborFinset x ∩ G.Λ) * (1 - ε))
        = ∑ x ∈ G.support.toFinset \ G.Λ, (φ ε (G.degree x) - #(G.neighborFinset x ∩ G.Λ) * ε )
          + ∑ x ∈ G.support.toFinset \ G.Λ, #(G.neighborFinset x ∩ G.Λ) := by
      calc _
        _ = ∑ x ∈ G.support.toFinset \ G.Λ,
            ((φ ε (G.degree x) - #(G.neighborFinset x ∩ G.Λ) * ε)
              + #(G.neighborFinset x ∩ G.Λ)) :=
          sum_congr rfl fun x hx ↦ by linarith
      rw [sum_add_distrib]
      simp only [sum_sub_distrib, Nat.cast_sum]
    rw [this, card_union, hsΛ, card_empty, tsub_zero, Nat.cast_add]; clear this
    refine add_le_add ?_ ?_
    · refine le_trans ?_ hscard
      simp only [eval, hAB']
      refine sum_le_sum fun z hz ↦ ?_
      have hdz : 2 ≤ G.degree z := by
        simp only [Λ, mem_sdiff, Set.mem_toFinset, mem_filter, inter_univ, ne_eq,
          singleton_ne_empty, not_false_eq_true, mem_of_singleton_inter_ne_emty, true_and] at hz
        by_contra
        have : G.degree z = 0 := by lia
        suffices 0 < G.degree z by lia
        exact degree_pos_iff_mem_support G z |>.mpr hz.1
      have hz' : z ∈ AB' := AB'.mem_toFinset.mpr <| hAB' ▸ hz
      rcases hz' with hAz' | hBz'
      · simp only [f, hAz', ↓reduceDIte, fA]
        refine le_trans (sub_le_self _ (Left.mul_nonneg (Nat.cast_nonneg' _) hε)) ?_
        split_ifs
        · exact φ_le_1 hε
        · refine le_trans (φ_decreasing (by lia : 2 ≤ G.degree z) hε hε') ?_
          simp only [φ, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, inf_le_iff]
          exact Or.inr <| by linarith
        · refine le_trans (φ_decreasing (by lia : 2 ≤ G.degree z) hε hε') ?_
          simp only [φ, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, inf_le_right]
        · have hdz : 3 ≤ G.degree z := by
            have : 3 ≤ (G.deleteIncidencesOf G.Λ).degree z := by lia
            exact le_trans this deleteIncidencesOf_degree_le
          have : φ ε (G.degree z) ≤ 2 / (G.degree z + 1 : ℝ) := by grind [φ]
          refine le_trans this ?_
          refine (div_le_div_iff_of_pos_left two_pos add_one_pos add_one_pos).mpr ?_
          simp only [add_le_add_iff_right, Nat.cast_le, deleteIncidencesOf_degree_le]
      · simp only [f, not_A_of_B, hBz', ↓reduceDIte, fB]
        simp only [mem_sdiff, Set.mem_toFinset, ne_eq, AB'] at hBz'
        obtain ⟨_, H⟩ := hBz'
        have : φ ε (G.degree z) ≤ 1 / (G.degree z : ℝ) + ε := by
          simp only [φ]
          split_ifs
          any_goals grind
          refine le_trans Std.min_le_left ?_
          rename_i hd
          rw [← Nat.cast_two, hd]
        calc _
          _ ≤ 1 / (G.degree z : ℝ) + ε - ↑(#(G.neighborFinset z ∩ G.Λ)) * ε := by
            linarith
          _ ≤ 1 / (G.degree z : ℝ) := by
            simp only [tsub_le_iff_right, add_le_add_iff_left]
            have : ε = 1 * ε := by exact Eq.symm (one_mul ε)
            nth_rewrite 1 [this]
            have : (1 : ℝ) ≤ #(G.neighborFinset z ∩ G.Λ) := by
              rw [← Nat.cast_one, Nat.cast_le]
              suffices 0 < #(G.neighborFinset z ∩ G.Λ) by exact Nat.one_le_of_lt this
              exact card_pos.mpr <| nonempty_iff_ne_empty.mpr H
            refine mul_le_mul ?_ (le_refl _) hε ?_ <;> linarith
        simp only [one_div]
        suffices (((G.deleteIncidencesOf G.Λ).degree z) + 1 : ℝ) ≤ G.degree z by
          exact inv_anti₀ add_one_pos this
        rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
        suffices (G.deleteIncidencesOf G.Λ).degree z < G.degree z by
          linarith
        obtain ⟨z', hz'⟩ : (G.neighborFinset z ∩ G.Λ).Nonempty := nonempty_iff_ne_empty.mpr H
        simp only [mem_inter, mem_neighborFinset] at hz'
        exact deleteIncidencesOf_degree_lt hz'.1 hz'.2
    · refine le_of_eq ?_
      rw [Nat.cast_inj]
      let g : V → Finset V := by
        intro v
        if h : v ∈ G.Λ then exact ∅
        else exact G.neighborFinset v ∩ G.Λ
      have : ∑ x ∈ G.support.toFinset \ G.Λ, #(G.neighborFinset x ∩ G.Λ)
          = ∑ x ∈ G.support.toFinset \ G.Λ, ∑ y ∈ G.neighborFinset x ∩ G.Λ, 1 :=
        sum_congr rfl fun _ _ ↦ card_eq_sum_ones _
      rw [this, card_eq_sum_ones]; clear this
      have := by
        refine Eq.symm <| @split_sum _ _ _ _ _ (fun _ ↦ 1) (G.support.toFinset \ G.Λ) G.Λ g ?_ ?_
        · ext x
          simp only [dite_eq_ite, mem_sup, mem_sdiff, Set.mem_toFinset, g]
          constructor
          · intro ⟨y, ⟨hy, hyΛ⟩, h⟩
            split_ifs at h
            exact mem_inter.mp h |>.2
          · intro hxΛ
            have hdx : 0 < G.degree x := by grind [Λ]
            have : x ∈ G.support := degree_pos_iff_mem_support G x |>.mp hdx
            obtain ⟨y, hxy⟩ := G.mem_support.mp this
            have hyΛ : y ∉ G.Λ := mt (fun h ↦ hΛ x hxΛ y h) <| Decidable.not_not.mpr hxy
            refine ⟨y, ⟨G.mem_support.mpr ⟨x, hxy.symm⟩, hyΛ⟩, ?_⟩
            simp only [hyΛ, ↓reduceIte, mem_inter, mem_neighborFinset, hxy.symm, hxΛ, and_self,
              singleton_inter_of_mem, ne_eq, singleton_ne_empty, not_false_eq_true,
              mem_of_singleton_inter_ne_emty]
        · intro x y hxney
          simp only [g]
          split_ifs
          any_goals grind
          ext z
          simp only [inter_assoc, mem_inter, mem_neighborFinset, notMem_empty, iff_false, not_and]
          intro hxz hz
          simp only [hz, not_true_eq_false, imp_false]
          have hdz : G.degree z = 1 := by grind [Λ]
          have hNz : G.neighborFinset z = {x} := by
            refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
            · simp only [singleton_subset_iff, mem_neighborFinset, hxz.symm,
              singleton_inter_of_mem, ne_eq, singleton_ne_empty, not_false_eq_true,
              mem_of_singleton_inter_ne_emty]
            · rw [← degree, hdz, card_singleton]
          refine not_adj_symm <| not_iff_not.mpr (mem_neighborFinset ..) |>.mp <| hNz ▸ ?_
          exact notMem_singleton.mpr hxney.symm
      rw [← this]; clear this
      refine sum_congr rfl fun x hx ↦ sum_congr ?_ fun _ _ ↦ rfl
      simp only [mem_sdiff, Set.mem_toFinset] at hx
      simp only [g, hx.2, ↓reduceDIte]

private lemma _f_is_lb_support {V : Type} [DecidableEq V] [Fintype V]
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 6)
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ s : Finset V, s ⊆ G.support.toFinset ∧ GraphParameter.ForestOfStars.toFun G s ∧
      ∑ v ∈ G.support, φ ε (G.degree v) ≤ #s := by
  if hΛ : ∃ x y, x ∈ G.Λ ∧ y ∈ G.Λ ∧ G.Adj x y then
    obtain ⟨x, y, hx, hy, hxy⟩ := hΛ
    obtain ⟨s, hs, hsf, hscard⟩ := _f_is_lb_support hε hε' (G.deleteIncidencesOf {x, y})
    have hsxy : s ∩ {x, y} = ∅ := by
      ext z
      simp only [mem_inter, notMem_empty, iff_false, not_and]
      intro hz
      have := hs hz
      simp only [Set.mem_toFinset, mem_support] at this
      obtain ⟨z', hz'⟩ := this
      exact fun H ↦ deleteIncidencesOf_notadj H hz'
    refine ⟨s ∪ {x, y}, ?_, ?_, ?_⟩
    · refine union_subset_iff.mpr ⟨subset_trans hs ?_, subset_trans ?_ Λ_subset_support⟩
      · exact Set.toFinset_subset_toFinset.mpr <| support_mono deleteIncidencesOf_le
      · clear * - hx hy; grind
    · simp only [GraphParameter.ForestOfStars]
      refine InducesForestOfStars_union_disjoint_neighborhoods ?_ ?_ ?_
      · simp only [GraphParameter.ForestOfStars] at hsf
        exact InducesForestOfStars_graph_mono' hsxy hsf
      · exact InducesForestOfStars_pair
      · intro u hu v hv
        exact not_adj_symm <| adj_leaves hxy hx hy hv (notMem_of_mem_of_empty_inter hu hsxy)
    · have : G.support.toFinset = (G.deleteIncidencesOf {x, y}).support.toFinset ∪ {x, y} := by
        ext z
        simp only [Set.mem_toFinset, adj_leaves_support hxy hx hy, Set.toFinset_diff,
          Set.toFinset_insert, Set.toFinset_singleton, union_insert, union_singleton, mem_insert,
          mem_sdiff, mem_singleton, not_or]
        constructor
        · grind
        · intro H
          rcases H with H | H | H
          · exact Set.mem_toFinset.mp <| H ▸ Λ_subset_support hx
          · exact Set.mem_toFinset.mp <| H ▸ Λ_subset_support hy
          · exact H.1
      rw [this, card_union, card_pair hxy.ne, hsxy, card_empty, tsub_zero, Nat.cast_add]; clear this
      have : ∑ v ∈ (G.deleteIncidencesOf {x, y}).support.toFinset ∪ {x, y}, φ ε (G.degree v)
          = ∑ v ∈ (G.deleteIncidencesOf {x, y}).support.toFinset, φ ε (G.degree v)
            + ∑ v ∈ {x, y}, φ ε (G.degree v) :=
        Eq.symm <| sum_disjoint_union rfl deleteIncidencesOf_support'
      obtain ⟨hdx, hdy⟩ : G.degree x = 1 ∧ G.degree y = 1 := by grind [Λ]
      have hφ1 : φ ε 1 = 1 - ε := by simp [φ]
      rw [this, sum_pair hxy.ne, hdx, hdy, hφ1]; clear this
      refine add_le_add ?_ ?_
      · refine le_of_eq_of_le ?_ hscard
        refine sum_congr rfl fun z hz ↦ ?_
        refine congrArg _ ?_
        refine degree_eq_deleteIncidencesOf_degree_of_inter_neighborhood_empty ?_ ?_
        · exact notMem_of_mem_of_empty_inter hz deleteIncidencesOf_support'
        · suffices G.neighborFinset z ⊆ (G.deleteIncidencesOf {x, y}).support.toFinset by
            exact inter_comm {x, y} _ ▸ inter_empty_of_subset this deleteIncidencesOf_support'
          intro u huz
          have : u ∈ G.support :=
            mem_support .. |>.mpr ⟨z, Adj.symm <| mem_neighborFinset .. |>.mp huz⟩
          simp only [adj_leaves_support hxy hx hy, Set.toFinset_diff, Set.toFinset_insert,
            Set.toFinset_singleton, mem_sdiff, Set.mem_toFinset, this, singleton_inter_of_mem,
            ne_eq, singleton_ne_empty, not_false_eq_true, mem_of_singleton_inter_ne_emty,
            true_and]
          have hz : z ∉ ({x, y} : Finset _) :=
            notMem_of_mem_of_empty_inter hz deleteIncidencesOf_support'
          exact fun hu ↦ adj_leaves hxy hx hy hu hz (Adj.symm <| mem_neighborFinset .. |>.mp huz)
      · rw [Nat.cast_two]
        linarith
  else
    simp only [exists_and_left, not_exists, not_and] at hΛ
    exact _f_is_lb_support_no_adj_leaves hε hε' G hΛ
  termination_by #G.Λ decreasing_by
  suffices (G.deleteIncidencesOf {x, y}).Λ = G.Λ \ {x, y} by
    rw [this, card_sdiff]
    simp only [tsub_lt_self_iff, card_pos]
    exact ⟨⟨x, hx⟩, ⟨x, mem_inter.mpr ⟨by member_of, hx⟩⟩⟩
  exact Λ_sdiff_eq hxy hx hy

lemma InducesForestOfStars_of_IndepSet {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V} (hs : G.IsIndepSet s) :
    G.InducesForestOfStars s := by
  refine InducesForestOfStars_iff.mpr ⟨InducesForest_of_IndepSet G hs, ?_⟩
  intro u v w x hu hv hw hx hunew hvnex huv hvw
  if hxw : w = x then exact hxw ▸ G.irrefl
  else exact hs hw hx hxw

private lemma f_is_lb {f : ℕ → ℝ} {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 6) (hf : f ≤ φ ε) :
    IsCaroWeiTypeLowerBound f GraphParameter.ForestOfStars := by
  refine CaroWeiTypeLowerBound_mono hf ?_
  intro V _ _ G _
  obtain ⟨s, hs, hsf, hscard⟩ := _f_is_lb_support hε hε' G
  simp only [GraphParameter.ForestOfStars] at hsf
  refine ⟨s ∪ (univ \ G.support.toFinset), ?_, ?_⟩
  · simp only [GraphParameter.ForestOfStars]
    refine InducesForestOfStars_union_disjoint_neighborhoods hsf ?_ ?_
    · refine InducesForestOfStars_of_IndepSet G ?_
      intro x hx y hy hxney
      simp only [coe_sdiff, coe_univ, Set.coe_toFinset, Set.mem_diff, Set.mem_univ,
        true_and] at hx hy
      exact forall_not_of_not_exists hx y
    · intro x hx y hy
      simp only [mem_sdiff, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
        mem_of_singleton_inter_ne_emty, Set.mem_toFinset, true_and] at hy
      exact not_adj_symm <| not_exists.mp (not_iff_not.mpr G.mem_support |>.mp hy) x
  · calc _
      _ = ∑ v ∈ univ \ G.support.toFinset, φ ε (G.degree v)
          + ∑ v ∈ G.support.toFinset, φ ε (G.degree v) :=
        Eq.symm (sum_sdiff <| subset_univ _)
      _ = ∑ v ∈ G.support.toFinset, φ ε (G.degree v)
          + ∑ v ∈ univ \ G.support.toFinset, φ ε (G.degree v) := by linarith
    have : (s ∩ (univ \ G.support.toFinset)) = ∅ := by
      ext
      simp only [mem_inter, mem_sdiff, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
        mem_of_singleton_inter_ne_emty, true_and, notMem_empty, iff_false, not_and,
          Decidable.not_not]
      exact (hs ·)
    rw [card_union, this, card_empty, tsub_zero, Nat.cast_add]; clear this
    refine add_le_add hscard ?_
    rw [cast_card]
    refine sum_le_sum fun x hx ↦ ?_
    suffices G.degree x = 0 by simp only [φ, this, ↓reduceIte, le_refl]
    simp only [mem_sdiff, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
      mem_of_singleton_inter_ne_emty, Set.mem_toFinset, true_and] at hx
    have := not_iff_not.mpr (degree_pos_iff_mem_support ..) |>.mpr hx
    linarith

theorem BoundedDegreeCaterpillar_LowerBound_iff (f : ℕ → ℝ) :
    IsCaroWeiTypeLowerBound f GraphParameter.ForestOfStars
      ↔ ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ 1 / 6 ∧ f ≤ φ ε :=
  ⟨_lb_bounded_by_extremal f, fun ⟨_, ⟨hε, hε', hf⟩⟩ _ _ _ G ↦ f_is_lb hε hε' hf G⟩

end CaroWeiType
