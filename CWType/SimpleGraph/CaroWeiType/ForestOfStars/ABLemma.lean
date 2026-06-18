import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claims

open Finset
open SimpleGraph

namespace CaroWeiType
namespace AB

open Bipartition

private lemma twonethree : 2 ≠ 3 := by lia

variable {V : Type} [DecidableEq V]

private lemma sdiff_inter_distrib {X Y Z : Finset V} : (X ∩ (Y \ Z)) = ((X ∩ Y) \ Z) := by
  grind

variable [Fintype V]

lemma sdiff_singleton_complement {s : Finset V} {x : V} : (s \ {x})ᶜ = sᶜ ∪ {x} := by
  ext y
  simp only [mem_compl, mem_sdiff, mem_singleton, not_and_or, Decidable.not_not, union_singleton,
    mem_insert, Or.comm]

lemma union_singleton_complement {s : Finset V} {x : V} : (s ∪ {x})ᶜ = sᶜ \ {x} := by
  ext y
  simp only [union_singleton, compl_insert, mem_erase, ne_eq, mem_compl, mem_sdiff, mem_singleton,
    And.comm]

private lemma sum_degree_in_sdiff
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset V} {v : V} (hvs : v ∈ s) :
    ∑ x ∈ s \ {v}, G.degree_in (s \ {v}) x
      = ∑ x ∈ s, G.degree_in s x - G.degree_in s v - G.degree_in s v := by
  have hs : s = (s \ {v}) ∪ {v} := by grind
  have H : ∀ x ∈ G.neighborFinset v ∩ s, 1 ≤ G.degree_in s x := by
    intro x hx
    rw [← card_singleton v]
    refine card_le_card ?_
    simp only [mem_inter, mem_neighborFinset, singleton_subset_iff, hvs, and_true] at hx ⊢
    exact hx.1.symm
  calc _
    _ = ∑ x ∈ s, G.degree_in (s \ {v}) x - G.degree_in (s \ {v}) v := by
      rw [← sum_sdiff <| singleton_subset_iff.mpr hvs, sum_singleton]
      simp only [add_tsub_cancel_right]
    _ = ∑ x ∈ s, G.degree_in (s \ {v}) x - G.degree_in s v := by
      suffices G.degree_in (s \ {v}) v =  G.degree_in s v by
        rw [this]
      nth_rewrite 2 [hs]
      exact degree_in_union_self ..
    _ = ∑ x ∈ (s \ (G.neighborFinset v ∩ s)), G.degree_in (s \ {v}) x
        + ∑ x ∈ (G.neighborFinset v ∩ s), G.degree_in (s \ {v}) x - G.degree_in s v := by
      rw [← sum_sdiff inter_subset_right]
    _ = ∑ x ∈ (s \ (G.neighborFinset v ∩ s)), G.degree_in s x
        + ∑ x ∈ (G.neighborFinset v ∩ s), G.degree_in (s \ {v}) x - G.degree_in s v := by
      suffices ∑ x ∈ s \ (G.neighborFinset v ∩ s), G.degree_in (s \ {v}) x
          = ∑ x ∈ s \ (G.neighborFinset v ∩ s), G.degree_in s x by
        rw [this]
      refine sum_congr rfl fun x hx ↦ ?_
      nth_rewrite 2 [hs]
      refine Eq.symm <| degree_in_union_eq ?_
      refine singleton_inter_of_notMem ?_
      refine not_mem_neighborFinset_symm ?_
      have := mem_sdiff.mp hx |>.2
      simp only [mem_inter, mem_sdiff.mp hx |>.1, and_true] at this
      exact this
    _ = ∑ x ∈ (s \ (G.neighborFinset v ∩ s)), G.degree_in s x
        + ∑ x ∈ (G.neighborFinset v ∩ s), (G.degree_in s x - 1) - G.degree_in s v := by
      suffices ∑ x ∈ (G.neighborFinset v ∩ s), G.degree_in (s \ {v}) x
          = ∑ x ∈ (G.neighborFinset v ∩ s), (G.degree_in s x - 1) by
        rw [this]
      refine sum_congr rfl fun x hx ↦ ?_
      rw [degree_in, degree_in, sdiff_inter_distrib, card_sdiff]
      suffices ({v} ∩ (G.neighborFinset x ∩ s)) = {v} by rw [this, card_singleton]
      refine singleton_inter_of_mem ?_
      simp only [mem_inter, mem_neighborFinset, hvs, and_true] at hx ⊢
      exact hx.1.symm
    _ = ∑ x ∈ (s \ (G.neighborFinset v ∩ s)), G.degree_in s x
        + ∑ x ∈ (G.neighborFinset v ∩ s), G.degree_in s x
        - ∑ x ∈ (G.neighborFinset v ∩ s), 1 - G.degree_in s v := by
      suffices ∑ x ∈ (G.neighborFinset v ∩ s), (G.degree_in s x - 1)
          = ∑ x ∈ (G.neighborFinset v ∩ s), G.degree_in s x - ∑ x ∈ (G.neighborFinset v ∩ s), 1 by
        rw [this]
        suffices ∑ x ∈ s \ (G.neighborFinset v ∩ s), G.degree_in s x +
            (∑ x ∈ G.neighborFinset v ∩ s, G.degree_in s x - ∑ x ∈ G.neighborFinset v ∩ s, 1)
            = ∑ x ∈ s \ (G.neighborFinset v ∩ s), G.degree_in s x
              + ∑ x ∈ G.neighborFinset v ∩ s, G.degree_in s x
              - ∑ x ∈ G.neighborFinset v ∩ s, 1 by rw [this]
        exact Eq.symm <| Nat.add_sub_assoc (sum_le_sum H) _
      have : ∑ x ∈ G.neighborFinset v ∩ s, G.degree_in s x
          = ∑ x ∈ G.neighborFinset v ∩ s, (G.degree_in s x - 1 + 1) := by
        exact sum_congr rfl fun x hx ↦ (Nat.sub_eq_iff_eq_add (H x hx)).mp rfl
      have : ∑ x ∈ G.neighborFinset v ∩ s, G.degree_in s x
          = ∑ x ∈ G.neighborFinset v ∩ s, (G.degree_in s x - 1)
          + ∑ x ∈ G.neighborFinset v ∩ s, 1 := by
        rw [this, sum_add_distrib]
      grind
    _ = ∑ x ∈ (s \ (G.neighborFinset v ∩ s)), G.degree_in s x
        + ∑ x ∈ (G.neighborFinset v ∩ s), G.degree_in s x
        - G.degree_in s v - G.degree_in s v := by
      suffices ∑ x ∈ (G.neighborFinset v ∩ s), 1 = G.degree_in s v by
        rw [this]
      simp only [sum_const, smul_eq_mul, mul_one, degree_in]
    _ = ∑ x ∈ s, G.degree_in s x - G.degree_in s v - G.degree_in s v := by
      suffices ∑ x ∈ (s \ (G.neighborFinset v ∩ s)), G.degree_in s x
              + ∑ x ∈ (G.neighborFinset v ∩ s), G.degree_in s x
          = ∑ x ∈ s, G.degree_in s x by
        rw [this]
      exact sum_sdiff inter_subset_right

private lemma sum_degree_in_union
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset V} {v : V} (hvs : v ∉ s) :
    ∑ x ∈ s ∪ {v}, G.degree_in (s ∪ {v}) x
      = ∑ x ∈ s, G.degree_in s x + G.degree_in s v + G.degree_in s v := by
  have hs : s = (s ∪ {v}) \ {v} := by grind
  have H : ∀ x ∈ G.neighborFinset v ∩ s, 1 ≤ G.degree_in (s ∪ {v}) x := by
    intro x hx
    rw [← card_singleton v]
    refine card_le_card ?_
    simp only [mem_inter, mem_neighborFinset, union_singleton, singleton_subset_iff, mem_insert,
      true_or, and_true] at hx ⊢
    exact hx.1.symm
  calc _
    _ = ∑ x ∈ s, G.degree_in (s ∪ {v}) x + G.degree_in (s ∪ {v}) v := by
      rw [← sum_sdiff (subset_union_right : {v} ⊆ s ∪ {v}), sum_singleton, ← hs]
    _ = ∑ x ∈ s, G.degree_in (s ∪ {v}) x + G.degree_in s v := by
      rw [← degree_in_union_self]
    _ = ∑ x ∈ (s \ (G.neighborFinset v ∩ s)), G.degree_in (s ∪ {v}) x
        + ∑ x ∈ (G.neighborFinset v ∩ s), G.degree_in (s ∪ {v}) x + G.degree_in s v := by
      rw [← sum_sdiff inter_subset_right]
    _ = ∑ x ∈ (s \ (G.neighborFinset v ∩ s)), G.degree_in s x
        + ∑ x ∈ (G.neighborFinset v ∩ s), G.degree_in (s ∪ {v}) x + G.degree_in s v := by
      suffices ∑ x ∈ s \ (G.neighborFinset v ∩ s), G.degree_in (s ∪ {v}) x
          = ∑ x ∈ s \ (G.neighborFinset v ∩ s), G.degree_in s x by
        rw [this]
      refine sum_congr rfl fun x hx ↦ ?_
      refine degree_in_union_eq ?_
      refine singleton_inter_of_notMem <| not_mem_neighborFinset_symm ?_
      simp only [sdiff_inter_self_right, mem_sdiff, mem_neighborFinset] at hx ⊢
      exact hx.2
    _ = ∑ x ∈ (s \ (G.neighborFinset v ∩ s)), G.degree_in s x
        + ∑ x ∈ (G.neighborFinset v ∩ s), (G.degree_in s x + 1) + G.degree_in s v := by
      suffices ∑ x ∈ (G.neighborFinset v ∩ s), G.degree_in (s ∪ {v}) x
          = ∑ x ∈ (G.neighborFinset v ∩ s), (G.degree_in s x + 1) by
        rw [this]
      refine sum_congr rfl fun x hx ↦ ?_
      refine degree_in_neighbor s ?_ hvs
      exact Adj.symm <| mem_neighborFinset .. |>.mp <| mem_inter.mp hx |>.1
    _ = ∑ x ∈ (s \ (G.neighborFinset v ∩ s)), G.degree_in s x
        + ∑ x ∈ (G.neighborFinset v ∩ s), G.degree_in s x
        + ∑ x ∈ (G.neighborFinset v ∩ s), 1 + G.degree_in s v := by
      suffices ∑ x ∈ (G.neighborFinset v ∩ s), (G.degree_in s x + 1)
          = ∑ x ∈ (G.neighborFinset v ∩ s), G.degree_in s x + ∑ x ∈ (G.neighborFinset v ∩ s), 1 by
        linarith
      exact sum_add_distrib
    _ = ∑ x ∈ (s \ (G.neighborFinset v ∩ s)), G.degree_in s x
        + ∑ x ∈ (G.neighborFinset v ∩ s), G.degree_in s x
        + G.degree_in s v + G.degree_in s v := by
      suffices ∑ x ∈ (G.neighborFinset v ∩ s), 1 = G.degree_in s v by
        rw [this]
      simp only [sum_const, smul_eq_mul, mul_one, degree_in]
    _ = ∑ x ∈ s, G.degree_in s x + G.degree_in s v + G.degree_in s v := by
      suffices ∑ x ∈ (s \ (G.neighborFinset v ∩ s)), G.degree_in s x
              + ∑ x ∈ (G.neighborFinset v ∩ s), G.degree_in s x
          = ∑ x ∈ s, G.degree_in s x by
        rw [this]
      exact sum_sdiff inter_subset_right

private lemma _TMP_ {x y z : ℕ} (h : y < z) (h' : z ≤ x + y) : x + y - z < x := by lia

private lemma _handshaking_degree_in {G : SimpleGraph V} [DecidableRel G.Adj]
    {s : Finset V} {v : V} (hvs : v ∈ s) :
    2 * G.degree_in s v ≤ ∑ x ∈ s, G.degree_in s x := by
  rw [sum_eq_sum_diff_singleton_add hvs _]
  suffices G.degree_in s v ≤ ∑ x ∈ s \ {v}, G.degree_in s x by lia
  have : ∑ x ∈ G.neighborFinset v ∩ s, G.degree_in s x ≤ ∑ x ∈ s \ {v}, G.degree_in s x := by
    refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ Nat.zero_le _
    grind [ne_of_mem_neighborFinset]
  refine le_trans ?_ this; clear this
  have : G.degree_in s v = ∑ z ∈ G.neighborFinset v ∩ s, 1 := by
    simp only [degree_in, sum_const, smul_eq_mul, mul_one]
  refine le_of_eq_of_le this (sum_le_sum fun x hx ↦ ?_); clear this
  rw [← card_singleton v]
  refine card_le_card <| singleton_subset_iff.mpr ?_
  exact mem_inter.mpr ⟨mem_neighborFinset_symm <| mem_inter.mp hx |>.1, hvs⟩

private lemma Lovász' {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsRegularOfDegree 3) :
    ∃ s : Finset V, (∀ x ∈ s, G.degree_in s x ≤ 1) ∧ (∀ x ∈ sᶜ, G.degree_in sᶜ x ≤ 1) := by
  let f : Finset V → ℕ := fun s ↦ ∑ x ∈ s, G.degree_in s x + ∑ x ∈ sᶜ, G.degree_in sᶜ x
  obtain ⟨s, _, hs⟩ := exists_argmin univ_nonempty f
  simp only [mem_univ, forall_const] at hs
  refine ⟨s, ?_⟩
  have hdcomp {x : V} : G.degree_in sᶜ x = 3 - G.degree_in s x := by
    rw [degree_in, ← sdiff_eq_inter_compl, card_sdiff, degree_in, ← degree, h.degree_eq x]
    suffices #(s ∩ G.neighborFinset x) = #(G.neighborFinset x ∩ s) by rw [this]
    exact congrArg Finset.card (inter_comm s _ ▸ rfl)
  have Hx : ∀ x ∈ s, G.degree_in s x ≤ G.degree_in sᶜ x := by
    by_contra
    simp only [not_forall] at this
    obtain ⟨x, hx, hd'x⟩ := this
    have hobj := hs (s \ {x})
    simp only [f] at hobj
    rw [sum_degree_in_sdiff hx, sdiff_singleton_complement] at hobj
    rw [sum_degree_in_union <| notMem_compl.mpr hx] at hobj
    have : ∑ x ∈ s, G.degree_in s x + ∑ x ∈ sᶜ, G.degree_in sᶜ x
          ≤ ∑ x ∈ s, G.degree_in s x - ((2 : ℕ) : ℝ) * G.degree_in s x
            + ∑ x ∈ sᶜ, G.degree_in sᶜ x + ((2 : ℕ) : ℝ) * G.degree_in sᶜ x := by
      rw [← Nat.cast_add, ← Nat.cast_mul, ← Nat.cast_mul,
        ← Nat.cast_sub (_handshaking_degree_in hx), ← Nat.cast_add, ← Nat.cast_add, Nat.cast_le]
      grind only
    refine hd'x ?_
    have : ((2 : ℕ) : ℝ) * G.degree_in s x ≤ ((2 : ℕ) : ℝ) * G.degree_in sᶜ x := by
      grind
    suffices ((G.degree_in s x) : ℝ) ≤ G.degree_in sᶜ x by simpa only [Nat.cast_le] using this
    exact le_of_mul_le_mul_left this two_pos
  have Hxc : ∀ x ∉ s, G.degree_in sᶜ x ≤ G.degree_in s x := by
    by_contra
    simp only [not_forall] at this
    obtain ⟨x, hx, hd'x⟩ := this
    have hobj := hs (s ∪ {x})
    simp only [f] at hobj
    rw [sum_degree_in_union hx, union_singleton_complement] at hobj
    rw [sum_degree_in_sdiff <| mem_compl.mpr hx] at hobj
    have (a : ℕ) : a + (∑ x ∈ sᶜ, G.degree_in sᶜ x - G.degree_in sᶜ x - G.degree_in sᶜ x)
        = (a + ∑ x ∈ sᶜ, G.degree_in sᶜ x) - 2 * G.degree_in sᶜ x := by
      repeat rw [← Nat.add_sub_assoc]
      · lia
      · rw [← sum_singleton (G.degree_in sᶜ ·)]
        refine sum_le_sum_of_subset_of_nonneg (singleton_subset_iff.mpr <| mem_compl.mpr hx) ?_
        exact fun _ _ _ ↦ Nat.zero_le _
      · suffices 2 * G.degree_in sᶜ x ≤ ∑ x ∈ sᶜ, G.degree_in sᶜ x by lia
        exact _handshaking_degree_in <| mem_compl.mpr hx
    rw [this] at hobj
    have : (∑ x ∈ s, G.degree_in s x + ∑ x ∈ sᶜ, G.degree_in sᶜ x
        ≤ ∑ x ∈ s, G.degree_in s x + ∑ x ∈ sᶜ, G.degree_in sᶜ x
          + 2 * G.degree_in s x - 2 * G.degree_in sᶜ x) := by
      lia
    have := by
      refine lt_of_lt_of_le (_TMP_ (not_le.mp hd'x) ?_) this
      suffices G.degree_in sᶜ x ≤ ∑ x ∈ sᶜ, G.degree_in sᶜ x by lia
      rw [← sum_singleton (G.degree_in sᶜ ·)]
      refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ Nat.zero_le _
      exact singleton_subset_iff.mpr <| mem_compl.mpr hx
    grind
  grind [mem_compl]

private lemma LovászCorollary {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsRegularOfDegree 3) :
    ∃ s : Finset V, (∀ x ∈ s, G.degree_in s x ≤ 1) ∧ ((Fintype.card V) * (1 / (2 : ℝ)) ≤ #s) := by
  obtain ⟨s, hs, hsc⟩ := Lovász' h
  if H : (Fintype.card V) * (1 / (2 : ℝ)) ≤ (#s) then
    exact ⟨s, hs, H⟩
  else
    simp only [not_le] at H
    refine ⟨sᶜ, hsc, ?_⟩
    rw [card_compl, Nat.cast_sub <| card_le_univ s]
    linarith

private lemma _InducesForestOfStars
    {G : SimpleGraph V} [DecidableRel G.Adj] {s s' : Finset V}
    (hs : ∀ x ∈ s, G.degree_in s x ≤ 1)
    (h's : ∀ x ∈ s, G.degree_in s' x ≤ 1)
    (hs' : ∀ x ∈ s', G.degree_in s' x = 0)
    (h's' : ∀ x ∈ s', G.degree_in s x ≤ 2)
    (H : ∀ x ∈ s', G.degree_in s x = 2 → ∀ y ∈ G.neighborFinset x ∩ s, G.degree_in s y = 0)
    (hs'ss' : ∀ x' ∈ s', ∀ y ∈ s, ∀ z' ∈ s', x' ≠ z' → G.Adj x' y → ¬G.Adj y z')
    (hs'sss' : ∀ x' ∈ s', ∀ y ∈ s, ∀ z ∈ s, ∀ u' ∈ s',
      x' ≠ u' → G.Adj x' y → G.Adj y z → ¬G.Adj z u') :
    G.InducesForestOfStars (s ∪ s') := by
  have hss'f : G.InducesForest (s ∪ s') := by
    intro t ht htne
    if hts' : t ∩ s' = ∅ then
      have hts : t ⊆ s := by
        intro x hxt
        rcases mem_union.mp (ht hxt) with hx | hx
        · exact hx
        · exact notMem_empty x (hts' ▸ mem_inter.mpr ⟨hxt, hx⟩) |>.elim
      obtain ⟨x, hxt⟩ := by exact nonempty_iff_ne_empty.mpr htne
      exact ⟨x, hxt, le_trans (degree_in_mono hts) (hs _ (hts hxt))⟩
    else
      obtain ⟨x, hx⟩ := by exact nonempty_iff_ne_empty.mpr hts'
      simp only [mem_inter] at hx
      obtain ⟨hxt, hxs'⟩ := hx
      have Hx := (h's' x hxs')
      have H' : G.degree_in t x ≤ 2 := by
        refine le_trans₃ (degree_in_mono ht) degree_in_union_le_sum ?_
        rw [hs' _ hxs', add_zero]
        exact Hx
      if hdtx : G.degree_in t x = 2 then
        have H' {z} (hzs' : z ∈ s') : G.degree_in t z ≤ G.degree_in s z := by
          refine le_trans₃ (degree_in_mono ht) degree_in_union_le_sum ?_
          suffices G.degree_in s' z = 0 by linarith
          exact hs' _ hzs'
        have Hxs : G.degree_in s x = 2 := le_antisymm Hx (hdtx ▸ H' hxs')
        obtain ⟨y, hy⟩ : (G.neighborFinset x ∩ t).Nonempty := card_pos.mp <| by linarith
        refine ⟨y, mem_inter.mp hy |>.2, ?_⟩
        refine le_trans₃ (degree_in_mono ht) degree_in_union_le_sum ?_
        have : G.neighborFinset x ∩ t = G.neighborFinset x ∩ s := by
          refine eq_of_subset_and_eq_card ?_ ?_
          · intro u hu
            simp only [mem_inter, mem_neighborFinset] at hu ⊢
            obtain ⟨hxu, hut⟩ := hu
            refine ⟨hxu, ?_⟩
            rcases mem_union.mp (ht hut) with hu | hu
            · exact hu
            · suffices 1 ≤ G.degree_in s' x by
                have := hs' x hxs'
                linarith
              rw [← card_singleton u]
              refine card_le_card <| singleton_subset_iff.mpr ?_
              exact mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr hxu, hu⟩
          · rw [← degree_in, ← degree_in, Hxs, hdtx]
        rw [H x hxs' Hxs y (this ▸ hy), zero_add]
        exact h's _ (mem_inter.mp (this ▸ hy) |>.2)
      else
        exact ⟨x, hxt, by lia⟩
  refine InducesForestOfStars_iff.mpr ⟨hss'f, ?_⟩
  have hs's' : ∀ x' ∈ s', ∀ y' ∈ s', ¬G.Adj x' y' := by
    intro x' hxs' y' hys' hx'y'
    have := hs' _ hxs'
    suffices 1 ≤ G.degree_in s' x' by linarith
    rw [← card_singleton y']
    refine card_le_card ?_
    refine singleton_subset_iff.mpr ?_
    simp only [mem_inter, mem_neighborFinset, hx'y', hys', and_self]
  intro v w x y hv hw hx hy hvnex hwney hvw hwx
  if hvney : v = y then
    intro hxy
    have := no_induced_K3_of_InducesForest G (s ∪ s') hvw hwx (hvney ▸ hxy) hss'f
    grind
  else if hys' : y ∈ s' then
    if hxs' : x ∈ s' then
      exact hs's' _ hxs' _ hys'
    else
      have hxs : x ∈ s := by grind
      if hws : w ∈ s then
        refine hs'sss' v ?_ w hws x hxs y hys' hvney hvw hwx
        by_contra
        have hvs : v ∈ s := by grind
        have := hs w hws
        suffices 2 ≤ G.degree_in s w by linarith
        rw [← card_pair hvnex]
        refine card_le_card ?_
        intro u hu
        simp only [mem_insert, mem_singleton, mem_inter, mem_neighborFinset] at hu ⊢
        rcases hu with hu | hu
        · exact ⟨hu ▸ hvw.symm, hu ▸ hvs⟩
        · exact ⟨hu ▸ hwx, hu ▸ hxs⟩
      else
        exact hs'ss' w (by grind) x hxs y hys' hwney hwx
  else
    have hys : y ∈ s := by grind
    if hxs : x ∈ s then
      if hws : w ∈ s then
        have := hs x hxs
        intro hxy
        suffices 2 ≤ G.degree_in s x by linarith
        rw [← card_pair hwney]
        refine card_le_card ?_
        intro u hu
        simp only [mem_insert, mem_singleton, mem_inter, mem_neighborFinset] at hu ⊢
        rcases hu with hu | hu
        · exact ⟨hu ▸ hwx.symm, hu ▸ hws⟩
        · exact ⟨hu ▸ hxy, hu ▸ hys⟩
      else
        have hws' : w ∈ s' := by grind
        have hvs : v ∈ s := by
          by_contra
          have hvs' : v ∈ s' := by grind
          refine hs's' v hvs' w hws' hvw
        have := by
          refine H w hws' ?_ x ?_
          · refine le_antisymm (h's' _ hws') ?_
            rw [← card_pair hvnex]
            refine card_le_card ?_
            intro u hu
            simp only [mem_insert, mem_singleton, mem_inter, mem_neighborFinset] at hu ⊢
            rcases hu with hu | hu
            · exact ⟨hu ▸ hvw.symm, hu ▸ hvs⟩
            · exact ⟨hu ▸ hwx, hu ▸ hxs⟩
          · simp only [mem_inter, mem_neighborFinset, hwx, hxs, and_self]
        simp only [degree_in, card_eq_zero] at this
        have := this ▸ notMem_empty y
        simpa only [mem_inter, mem_neighborFinset, hys, and_true] using this
    else
      have hxs' : x ∈ s' := by grind
      have hws : w ∈ s := by grind [(fun H ↦ hs's' w H x hxs').mt <| Decidable.not_not.mpr hwx]
      intro hxy
      have hdsw := by
        refine H x hxs' (le_antisymm (h's' x hxs') ?_) w ?_
        · rw [← card_pair hwney]
          refine card_le_card ?_
          intro u hu
          simp only [mem_insert, mem_singleton, mem_inter, mem_neighborFinset] at hu ⊢
          rcases hu with hu | hu
          · exact ⟨hu ▸ hwx.symm, hu ▸ hws⟩
          · exact ⟨hu ▸ hxy, hu ▸ hys⟩
        · exact mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr hwx.symm, hws⟩
      simp only [degree_in, card_eq_zero] at hdsw
      have hvs' : v ∈ s' := by
        by_contra
        have hvs : v ∈ s := by grind
        have := hdsw ▸ notMem_empty v
        simp only [mem_inter, mem_neighborFinset, hvw.symm, hvs, and_self,
          not_true_eq_false] at this
      exact hs'ss' v hvs' w hws x hxs' hvnex hvw hwx

theorem ABLemma (G : SimpleGraph V) [DecidableRel G.Adj] (AB : Bipartition V) [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) :
    Objective G AB := by
  induction hcard : AB.card using Nat.strong_induction_on generalizing G AB with | h k ih
  if hk : k = 0 then
    refine ⟨∅, empty_subset _, InducesForestOfStars_empty, respects_empty, ?_⟩
    simp only [eval, card_eq_zero.mp (hk ▸ hcard), sum_empty, card_empty, Nat.cast_zero, le_refl]
  else
    have ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
        [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB' :=
      fun G' _ ABC' _ hsupp' hcardABC' ↦ ih ABC'.card (hcard ▸ hcardABC') G' ABC' hsupp' rfl
    cases Claim6' hG ih with
    | inr h => exact h
    | inl h => ?_
    simp only [← and_or_left] at h
    if hA2A2 : ∃ v ∈ AB.toFinset, ∃ w ∈ AB.toFinset,
        G.degree v = 2 ∧ G.degree w ≠ 3 ∧ G.Adj v w then
      obtain ⟨v, hv, w, hw, hdv, Hdw, hvw⟩ := hA2A2
      refine Claim9 hG hvw hdv ?_ ih
      exact (h _ hw |>.2).elim (·) (fun _ ↦ by contradiction)
    else
    simp only [ne_eq, not_exists, not_and] at hA2A2
    if hA2AA2 : ∃ v ∈ AB.toFinset, ∃ w ∈ AB.toFinset, ∃ x ∈ AB.toFinset,
          v ≠ w ∧ G.degree v = 2 ∧ G.degree w = 2 ∧ G.Adj v x ∧ G.Adj x w then
      obtain ⟨v, hv, w, hw, x, hx, hvnew, hdv, hdw, hvx, hxw⟩ := hA2AA2
      refine Claim7 hG hvx hxw hvnew ?_ hdv hdw ih
      exact Decidable.not_not.mp <| hA2A2 v hv x hx hdv |>.mt <| Decidable.not_not.mpr hvx
    else
    simp only [not_exists, not_and] at hA2AA2
    if hA2AAA2 : ∃ v ∈ AB.toFinset, ∃ w ∈ AB.toFinset, ∃ x ∈ AB.toFinset, ∃ y ∈ AB.toFinset,
          v ≠ w ∧ G.degree v = 2 ∧ G.degree w = 2 ∧ G.Adj v x ∧ G.Adj x y ∧ G.Adj y w then
      obtain ⟨v, hv, w, hw, x, hx, y, hy, hvnew, hdv, hdw, hvx, hxy, hyw⟩ := hA2AAA2
      exact Claim12_of_dist_3 hG hdv hdw hvnew hvx hxy hyw ih
    else
    simp only [ne_eq, not_exists, not_and] at hA2AAA2
    if htriangle : ∃ u v w,
        G.Adj u v ∧ G.Adj v w ∧ G.Adj u w ∧ G.degree u = 2 ∧ G.degree v = 3 ∧ G.degree w = 3 then
      obtain ⟨u, v, w, hu, hvw, huw, hdu, hdv, hdw⟩ := htriangle
      refine Claim11 hG hdu ?_ ih
      obtain ⟨v', hvv', hunev', hwnev'⟩ := Finset_get_other_other (le_of_eq hdv.symm) u w
      obtain ⟨w', hww', hunew', hvnew'⟩ := Finset_get_other_other (le_of_eq hdw.symm) u v
      have hNu : G.neighborFinset u = {v, w} := by
        refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
        · intro u' hu'
          simp only [mem_insert, mem_singleton] at hu'
          rcases hu' with hu' | hu'
          · exact mem_neighborFinset .. |>.mpr <| hu' ▸ hu
          · exact mem_neighborFinset .. |>.mpr <| hu' ▸ huw
        · rw [card_pair hvw.ne, ← degree, hdu]
      have hNv : G.neighborFinset v = {u, w, v'} := by
        refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
        · intro u' hu'
          simp only [mem_insert, mem_singleton] at hu'
          rcases hu' with hu' | hu' | hu'
          · exact mem_neighborFinset .. |>.mpr <| hu' ▸ hu.symm
          · exact mem_neighborFinset .. |>.mpr <| hu' ▸ hvw
          · exact hu' ▸ hvv'
        · rw [card_triplet' huw.ne hunev' hwnev', ← degree, hdv]
      have hNw : G.neighborFinset w = {u, v, w'} := by
        refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
        · intro u' hu'
          simp only [mem_insert, mem_singleton] at hu'
          rcases hu' with hu' | hu' | hu'
          · exact mem_neighborFinset .. |>.mpr <| hu' ▸ huw.symm
          · exact mem_neighborFinset .. |>.mpr <| hu' ▸ hvw.symm
          · exact hu' ▸ hww'
        · rw [card_triplet' hu.ne hunew' hvnew', ← degree, hdw]
      suffices #(G.N2_of_Finset {u}) ≤ 2 by linarith
      have : ({u, v, w} : Finset _) = {v, w} ∪ {u} := by grind only [= union_singleton]
      rw [N2_of_Finset, closed_neighborFinset_of_singleton_eq, hNu, ← this,
        closed_neighborFinset_of_triplet_eq, hNu, hNv, hNw]
      have : (({v, w} ∪ {u, w, v'} ∪ {u, v, w'} ∪ {u, v, w}) \ {u, v, w}) ⊆ ({v', w'} : Finset _) := by
        intro z
        simp only [union_insert, insert_union, singleton_union, ne_eq,
          singleton_inter_eq_empty_iff, mem_insert, mem_singleton, true_or, or_true,
          not_true_eq_false, not_false_eq_true, mem_of_singleton_inter_ne_emty, insert_eq_of_mem,
          insert_sdiff_insert, mem_sdiff, not_or]
        grind
      refine le_trans (card_le_card this) card_le_two
    else if hC4 : ∃ u v w x, v ≠ x
        ∧ G.Adj u v ∧ G.Adj v w ∧ G.Adj w x ∧ G.Adj x u
        ∧ G.degree u = 2 ∧ G.degree v = 3 ∧ G.degree w = 3 ∧ G.degree x = 3 then
      obtain ⟨u, v, w, x, hvnex, huv, hvw, hwx, hxu, hdu, hdv, hdw, hdx⟩ := hC4
      refine Claim11 hG hdu ?_ ih
      refine _card_N2_of_adj huv.symm hxu.symm hwx hvw hvnex ?_ hdv hdu hdx
      refine ne_of_ne_congr (G.degree ·) ?_
      simp only [hdu, hdw, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
    else
      simp only [exists_and_left, not_exists, not_and] at htriangle
      let G' : SimpleGraph ({v | G.degree v = 3} : Finset _) := {
          Adj v w := G.Adj v w ∨ (v ≠ w ∧ ∃ z, G.degree z = 2 ∧ G.Adj v z ∧ G.Adj z w),
          symm v w hvw := by
            simp only at hvw ⊢
            rcases hvw with hvw | hvw
            · exact Or.inl hvw.symm
            · obtain ⟨hvnew, z, hdz, hvz, hzw⟩ := hvw
              exact Or.inr ⟨hvnew.symm, z, hdz, hzw.symm, hvz.symm⟩
          loopless := {
            irrefl := fun v ↦ by simp only [SimpleGraph.irrefl, ne_eq, not_true_eq_false,
              false_and, or_self, not_false_eq_true]
          }
        }
      obtain ⟨s, hds, hscard⟩ := by
        refine @LovászCorollary _ _ _ G' _ ?_
        intro v
        obtain ⟨x, y, z, hNv, hdzledy, hdyledx⟩ := by
          refine @neighborFinset_eq_deg3 _ G _ v (G.degree ·) _ ?_
          have := v.2
          simpa only [mem_filter, mem_univ, true_and] using this
        have hdv : G.degree v = 3 := by
          have := v.2
          simpa only [mem_filter, mem_univ, true_and] using this
        have hdx := by
          refine h x (hG <| G.mem_support.mpr ⟨v, ?_⟩) |>.2
          exact Adj.symm <| mem_neighborFinset .. |>.mp <| hNv ▸ by member_of
        have hdy := by
          refine h y (hG <| G.mem_support.mpr ⟨v, ?_⟩) |>.2
          exact Adj.symm <| mem_neighborFinset .. |>.mp <| hNv ▸ by member_of
        have hdz := by
          refine h z (hG <| G.mem_support.mpr ⟨v, ?_⟩) |>.2
          exact Adj.symm <| mem_neighborFinset .. |>.mp <| hNv ▸ by member_of
        simp only [Nat.cast_le] at hdzledy hdyledx
        rcases hdz with hdz | hdz
        · obtain ⟨z', hz', hvnez'⟩ := Finset_get_other (le_of_eq hdz.symm) v
          simp only [mem_neighborFinset] at hz'
          have hNz : G.neighborFinset z = {v.1, z'} := by
            refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
            · intro u' hu'
              simp only [mem_insert, mem_singleton, mem_neighborFinset] at hu' ⊢
              rcases hu' with hu' | hu'
              · exact Adj.symm <| mem_neighborFinset .. |>.mp <| hu' ▸ hNv ▸ by member_of
              · exact hu' ▸ hz'
            · rw [← degree, hdz, card_pair hvnez']
          have hdy : G.degree y = 3 := by
            rcases hdy with hdy | hdy
            · have hzv : G.Adj z v := by
                exact Adj.symm <| mem_neighborFinset .. |>.mp <| hNv ▸ by member_of
              have hvy : G.Adj v y := by
                exact mem_neighborFinset .. |>.mp <| hNv ▸ by member_of
              refine hA2AA2 z ?_ y ?_ v ?_ (by grind [degree]) hdz hdy hzv hvy |>.elim
              <;> exact hG <| G.degree_pos_iff_mem_support _ |>.mp <| by grind [degree]
            · exact hdy
          have hdx : G.degree x = 3 := by
            lia
          have hdz' : G.degree z' = 3 := by
            have := h z' (hG <| G.mem_support.mpr ⟨z, hz'.symm⟩) |>.2
            rcases this with hdz' | hdz'
            · refine hA2A2 z ?_ z' ?_ hdz (by simp [hdz', twonethree]) hz' |>.elim
              <;> exact hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith
            · exact hdz'
          have hynex : y ≠ x := by
            clear * - hNv
            grind [degree]
          have hxnez' : x ≠ z' := by
            refine ne_of_ne_congr (G.Adj z ·) ?_
            simp only [hz', ne_eq, eq_iff_iff, iff_true]
            intro hzx
            refine htriangle z x hzx v.1 ?_ ?_ hdz hdx hdv |>.elim
            <;> refine Adj.symm <| mem_neighborFinset .. |>.mp <| by simp [hNv]
          have hynez' : y ≠ z' := by
            refine ne_of_ne_congr (G.Adj z ·) ?_
            simp only [hz', ne_eq, eq_iff_iff, iff_true]
            intro hzy
            refine htriangle z y hzy v.1 ?_ ?_ hdz hdy hdv |>.elim
            <;> refine Adj.symm <| mem_neighborFinset .. |>.mp <| by simp [hNv]
          suffices G'.neighborFinset v
              = {⟨y, by simp [hdy]⟩, ⟨x, by simp [hdx]⟩, ⟨z', by simp [hdz']⟩} by
            have := congrArg Finset.card this
            rw [card_triplet'] at this
            · exact this
            · simp only [ne_eq, Subtype.mk.injEq, hynex, not_false_eq_true]
            · simp only [ne_eq, Subtype.mk.injEq, hynez', not_false_eq_true]
            · simp only [ne_eq, Subtype.mk.injEq, hxnez', not_false_eq_true]
          refine subset_antisymm ?_ ?_
          · intro u' hu'
            simp only [ne_eq, mem_neighborFinset, mem_insert, mem_singleton, G'] at hu' ⊢
            rcases hu' with hu' | hu'
            · suffices u'.1 ∈ G.neighborFinset v by
                simp only [hNv, mem_insert, mem_singleton] at this
                clear * - this z hdz
                rcases this with hu' | hu' | hu'
                · grind only
                · grind only
                · have := u'.prop
                  simp only [hu', mem_filter, inter_univ, ne_eq, singleton_ne_empty,
                    not_false_eq_true, mem_of_singleton_inter_ne_emty, hdz, twonethree,
                    and_false] at this
              exact mem_neighborFinset .. |>.mpr hu'
            · obtain ⟨hvneu', z'', hdz'', hvz'', hz''u⟩ := hu'
              have hz''eqz : z'' = z := by
                have := mem_neighborFinset .. |>.mpr <| hvz''
                simp only [hNv, mem_insert, mem_singleton] at this
                rcases this with hz'' | hz'' | hz''
                · refine ne_of_ne_congr (G.degree ·) ?_ hz'' |>.elim
                  simp only [hdz'', hdx]
                  exact twonethree
                · refine ne_of_ne_congr (G.degree ·) ?_ hz'' |>.elim
                  simp only [hdz'', hdy]
                  exact twonethree
                · exact hz''
              have := mem_neighborFinset .. |>.mpr <| hz''eqz ▸ hz''u
              simp only [hNz, mem_insert, SetLike.coe_eq_coe, Ne.symm hvneu', mem_singleton,
                false_or] at this
              exact Or.inr <| Or.inr <| SetLike.coe_eq_coe.mp this
          · intro u' hu'
            simp only [mem_insert, mem_singleton, ne_eq, mem_neighborFinset, G'] at hu' ⊢
            rcases hu' with hu' | hu' | hu'
            · refine Or.inl <| mem_neighborFinset .. |>.mp <| hNv ▸ hu' ▸ by simp
            · refine Or.inl <| mem_neighborFinset .. |>.mp <| hNv ▸ hu' ▸ by simp
            · refine Or.inr <| ⟨by grind [ne_of_mem_neighborFinset], z, hdz, ?_, hu' ▸ hz'⟩
              refine mem_neighborFinset .. |>.mp <| hNv ▸ by member_of
        · obtain ⟨hdx, hdy⟩ : G.degree x = 3 ∧ G.degree y = 3 := by grind
          have hdv : G.degree v = 3 := by grind
          suffices G'.degree v = G.degree v by
            simpa only [hdv] using this
          simp only [degree]
          refine Set.BijOn.finsetCard_eq (fun v ↦ v) ⟨?_, ?_, ?_⟩
          · intro u hu
            simp only [G', ne_eq, coe_neighborFinset, mem_neighborSet] at hu ⊢
            rcases hu with hu | hu
            · exact hu
            · obtain ⟨u', hdu', huv, _⟩ := hu.2
              have := hNv ▸ (mem_neighborFinset .. |>.mpr huv)
              simp only [mem_insert, mem_singleton] at this
              rcases this with hu' | hu' | hu'
              <;> refine (ne_of_ne_congr (G.degree ·) (by simp [hdu', hdx, hdy, hdz])) hu' |>.elim
          · exact fun _ _ _ _ ↦ Subtype.ext
          · intro u hu
            simp only [card_neighborFinset_eq_degree, ne_eq, coe_neighborFinset, Set.mem_image,
              mem_neighborSet, Subtype.exists, exists_and_right, exists_eq_right]
            simp only [card_neighborFinset_eq_degree, hNv, coe_insert, coe_singleton,
              Set.mem_insert_iff, Set.mem_singleton_iff] at hu
            simp only [G']
            rcases hu with hu | hu | hu
            <;> refine ⟨by simp [hu, hdx, hdy, hdz],
                Or.inl <| mem_neighborFinset .. |>.mp <| hNv ▸ hu ▸ by member_of⟩
      have hABs' : s.image (·.1) ∪ ({w | G.degree w = 2} : Finset _) ⊆ AB.toFinset := by
        intro u hu
        simp only [mem_union, mem_image, Subtype.exists, mem_filter, inter_univ, ne_eq,
          singleton_ne_empty, not_false_eq_true, mem_of_singleton_inter_ne_emty, true_and,
          exists_and_right, exists_eq_right] at hu
        rcases hu with ⟨hdu, _⟩ | ⟨hdu⟩
        <;> refine hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith
      refine ⟨s.image (·.1) ∪ ({w | G.degree w = 2} : Finset _), hABs', ?_, ?_, ?_⟩
      · refine _InducesForestOfStars ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · intro x hx
          simp only [mem_image, Subtype.exists, mem_filter, inter_univ, ne_eq, singleton_ne_empty,
            not_false_eq_true, mem_of_singleton_inter_ne_emty, true_and, exists_and_right,
            exists_eq_right] at hx
          obtain ⟨hdx, Hx⟩ := hx
          refine le_trans ?_ (hds _ Hx)
          refine card_le_card_of_surjOn (·) ?_
          intro u hu
          simp only [coe_inter, coe_neighborFinset, coe_image, Set.mem_inter_iff, mem_neighborSet,
            Set.mem_image, SetLike.mem_coe, Subtype.exists, mem_filter, inter_univ, ne_eq,
            singleton_ne_empty, not_false_eq_true, mem_of_singleton_inter_ne_emty, true_and,
            exists_and_right, exists_eq_right] at hu ⊢
          obtain ⟨hxu, hdu, hus⟩ := hu
          refine ⟨hdu, ?_, hus⟩
          simp only [hxu, true_or, G']
        · intro x hx
          by_contra
          have : 2 ≤ G.degree_in ({w | G.degree w = 2} : Finset _) x :=
            Nat.succ_le_of_lt <| not_le.mp this
          obtain ⟨u, v, hu, hv, hunev⟩ := Finset_two_le_card_iff _ |>.mp this
          simp only [mem_inter, mem_neighborFinset, mem_filter, inter_univ, ne_eq,
            singleton_ne_empty, not_false_eq_true, mem_of_singleton_inter_ne_emty,
            true_and] at hu hv
          obtain ⟨hxu, hdu⟩ := hu
          obtain ⟨hxv, hdv⟩ := hv
          refine hA2AA2 u ?_ v ?_ x ?_ hunev hdu hdv hxu.symm hxv
          · exact hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith
          · exact hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith
          · exact hG <| G.mem_support.mpr ⟨u, hxu⟩
        · intro x hx
          simp only [mem_filter, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
            mem_of_singleton_inter_ne_emty, true_and, degree_in, card_eq_zero] at hx ⊢
          ext y
          simp only [mem_inter, mem_neighborFinset, mem_filter, mem_univ, true_and, notMem_empty,
            iff_false, not_and']
          intro hdy
          refine hA2A2 x ?_ y ?_ hx ?_
          · exact hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith
          · exact hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith
          · simp only [hdy, twonethree, not_false_eq_true]
        · intro x hx
          simp only [mem_filter, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
            mem_of_singleton_inter_ne_emty, true_and] at hx
          exact le_of_le_of_eq degree_in_le_degree hx
        · intro x hx hd'x y hy
          simp only [mem_filter, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
            mem_of_singleton_inter_ne_emty, true_and, mem_inter, mem_neighborFinset, mem_image,
            Subtype.exists, exists_and_right, exists_eq_right] at hx hy hd'x
          obtain ⟨hxy, hdy, hy⟩ := hy
          obtain ⟨z, hz, hynez⟩ := Finset_get_other (le_of_eq hd'x.symm) y
          simp only [mem_inter, mem_neighborFinset, mem_image, Subtype.exists, mem_filter,
            inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
            mem_of_singleton_inter_ne_emty, true_and, exists_and_right, exists_eq_right] at hz
          obtain ⟨hxz, hdz, hz⟩ := hz
          have := hds _ hy
          have hyz : ¬G.Adj y z := fun hyz ↦ htriangle x y hxy z hyz hxz hx hdy hdz
          have hN'y : G'.neighborFinset ⟨y, by simp [hdy]⟩ ∩ s = {⟨z, by simp [hdz]⟩} := by
            refine Eq.symm <| eq_of_subset_and_ge_card ?_ ?_
            · refine singleton_subset_iff.mpr ?_
              simp only [ne_eq, mem_inter, mem_neighborFinset, hyz, Subtype.mk.injEq, hynez,
                not_false_eq_true, true_and, false_or, hz, and_true, G']
              exact ⟨x, hx, hxy.symm, hxz⟩
            · rw [card_singleton]
              exact hds _ hy
          by_contra
          have : 1 ≤ G.degree_in (s.image (·.1)) y := Nat.one_le_iff_ne_zero.mpr this
          obtain ⟨z', hz'⟩ := card_pos.mp this
          simp only [mem_inter, mem_neighborFinset, mem_image, Subtype.exists, mem_filter,
            inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
            mem_of_singleton_inter_ne_emty, true_and, exists_and_right, exists_eq_right] at hz'
          obtain ⟨hyz', hdz', hz'⟩ := hz'
          have : ⟨z', by simp [hdz']⟩ ∈ G'.neighborFinset ⟨y, by simp [hdy]⟩ ∩ s := by
            simp only [ne_eq, mem_inter, mem_neighborFinset, hyz', Subtype.mk.injEq, true_or, hz',
              and_self, singleton_inter_of_mem, singleton_ne_empty, not_false_eq_true,
              mem_of_singleton_inter_ne_emty, G']
          rw [hN'y] at this
          simp only [mem_singleton, Subtype.mk.injEq] at this
          exact hyz (this ▸ hyz')
        · intro x hx y hy z hz hxnez hxy
          simp only [mem_filter, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
            mem_of_singleton_inter_ne_emty, true_and, mem_image, Subtype.exists, exists_and_right,
            exists_eq_right] at hx hy hz
          obtain ⟨hdy, hy⟩ := hy
          refine hA2AA2 x ?_ z ?_ y ?_ hxnez hx hz hxy
          <;> refine hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith
        · intro x hx y hy z hz u hu hxneu hxy hyz
          simp only [mem_filter, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
            mem_of_singleton_inter_ne_emty, true_and, mem_image, Subtype.exists, exists_and_right,
            exists_eq_right] at hx hy hz hu
          obtain ⟨hdy, hy⟩ := hy
          obtain ⟨hdz, hz⟩ := hz
          refine hA2AAA2 x ?_ u ?_ y ?_ z ?_  hxneu hx hu hxy hyz
          <;> refine hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith
      · exact respects_of_A fun u hu ↦ h _ (hABs' hu) |>.1
      · rw [card_union]
        have : s.image (·.1) ∩ ({w | G.degree w = 2} : Finset _) = ∅ := by
          ext u
          simp only [mem_inter, mem_image, Subtype.exists, mem_filter, inter_univ, ne_eq,
            singleton_ne_empty, not_false_eq_true, mem_of_singleton_inter_ne_emty, true_and,
            exists_and_right, exists_eq_right, notMem_empty, iff_false, not_and']
          intro hdu
          simp only [hdu, twonethree, IsEmpty.exists_iff, not_false_eq_true]
        rw [this, card_empty, tsub_zero]; clear this
        have : eval G AB
            = ∑ x ∈ AB.toFinset \ ({x | G.degree x = 2} : Finset _), f G AB x
              + ∑ x ∈ ({x | G.degree x = 2} : Finset _), f G AB x := by
          exact Eq.symm <| sum_sdiff <| subset_trans subset_union_right hABs'
        rw [this]; clear this
        have : ∑ x ∈ ({x | G.degree x = 2} : Finset _),
                f G AB x ≤ #({x | G.degree x = 2} : Finset _) := by
          refine le_of_le_of_eq (sum_le_sum fun _ _ ↦ f_le_one) ?_
          simp only [sum_const', mul_one]
        rw [Nat.cast_add]
        refine add_le_add ?_ this
        refine le_trans₃ ?_ hscard ?_
        · rw [Fintype.card_coe]
          have : ∑ x ∈ AB.toFinset \ ({x | G.degree x = 2} : Finset _), f G AB x
              = ∑ x ∈ {x | G.degree x = 3}, f G AB x := by
            refine sum_congr ?_ fun _ _ ↦ rfl
            ext u
            simp only [mem_sdiff, mem_filter, inter_univ, ne_eq, singleton_ne_empty,
              not_false_eq_true, mem_of_singleton_inter_ne_emty, true_and]
            constructor
            · intro ⟨hu, hdu⟩
              have := h u hu |>.2
              simpa only [hdu, false_or] using this
            · refine fun hdu ↦ ⟨?_, by simp only [hdu, twonethree.symm, not_false_eq_true]⟩
              exact hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith
          rw [this]; clear this
          have : ∑ x ∈ {x | G.degree x = 3}, f G AB x = ∑ x ∈ {x | G.degree x = 3}, 1 / 2 := by
            refine sum_congr rfl fun x hx ↦ ?_
            simp only [mem_filter, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
              mem_of_singleton_inter_ne_emty, true_and] at hx
            refine fA3 (h _ ?_ |>.1) hx
            refine hG <| G.degree_pos_iff_mem_support x |>.mp <| by linarith
          rw [this]; clear this
          simp only [one_div, sum_const', le_refl]
        · refine le_of_eq ?_
          exact Nat.cast_inj.mpr <| Eq.symm <| card_image_of_injOn fun _ _ _ _ ↦ Subtype.ext

end AB
end CaroWeiType
