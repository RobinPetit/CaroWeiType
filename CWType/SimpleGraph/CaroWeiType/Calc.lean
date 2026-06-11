import CWType.SimpleGraph.CaroWeiType.Lemmas

namespace Finset

lemma exists_argmin {α β : Type*} [LinearOrder β] {s : Finset α} (hs : s.Nonempty)
    (f : α → β) : ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y := by
  classical
  induction s using Finset.induction_on_min_value f with
  | h0 => simp only [Finset.not_nonempty_empty] at hs
  | step a s' ha hmin ih => ?_
  refine ⟨a, mem_insert_self .., ?_⟩
  intro y hy
  simp only [mem_insert] at hy
  rcases hy with hy | hy
  · simp only [hy, le_refl]
  · exact hmin _ hy

lemma one_sixth_pos : (0 : ℝ) < 1 / 6 := by linarith

lemma one_third_pos : (0 : ℝ) < 1 / 3 := by linarith

lemma two_thirds_pos : (0 : ℝ) < 2 / 3 := by linarith

lemma four_thirds_pos : (0 : ℝ) < 4 / 3 := by linarith

lemma zero_le_one_tenth : (0 : ℝ) ≤ 1 / 10 := by linarith

lemma zero_le_one_sixth : (0 : ℝ) ≤ 1 / 6 := by linarith

lemma zero_le_one_third : (0 : ℝ) ≤ 1 / 3 := by linarith

lemma zero_le_one_half : (0 : ℝ) ≤ 1 / 2 := by linarith

lemma zero_le_two_thirds : (0 : ℝ) ≤ 2 / 3 := by linarith

lemma zero_le_five_sixths : (0 : ℝ) ≤ 5 / 6 := by linarith

lemma zero_le_four_thirds : (0 : ℝ) ≤ 4 / 3 := by linarith

lemma two_thirds_le_five_sixths : (2 : ℝ) / 3 ≤ 5 / 6 := by linarith

lemma two_thirds_le_one : (2 : ℝ) / 3 ≤ 1 := by linarith

lemma four_thirds_le_two : (4 : ℝ) / 3 ≤ 2 := by linarith

lemma five_pos : (0 : ℝ) < 5 := by
  exact Nat.ofNat_pos'

lemma six_pos : (0 : ℝ) < 6 := by
  exact Nat.ofNat_pos'

lemma two_le_of_ne_zero_of_ne_one {n : ℕ} (h0 : n ≠ 0) (h1 : n ≠ 1) : 2 ≤ n := by
  lia

lemma two_le_of_one_le_of_ne_one {n : ℕ} (h0 : 1 ≤ n) (h1 : n ≠ 1) : 2 ≤ n := by
  lia

lemma zero_or_two_le_of_ne_one {n : ℕ} (h : n ≠ 1) : n = 0 ∨ 2 ≤ n := by
  lia

lemma Δf_eq {c : ℝ} {d : ℕ} :
    c / (d + 1 : ℝ) - c / (d + 1 + 1 : ℝ) = c / ((d + 1 : ℝ)*(d + 1 + 1 : ℝ)) := by
  grind only

lemma Δf_eq' {c : ℝ} {d : ℕ} (hd : 0 < d) :
    c / (d : ℝ) - c / (d + 1 : ℝ) = c / ((d : ℝ)*(d + 1 : ℝ)) := by
  have heq : (d : ℝ) = ((d - 1 : ℕ) + 1 : ℝ) := by
    rw [← @Nat.cast_one ℝ _, ← Nat.cast_add]
    exact Nat.cast_inj.mpr <| Nat.sub_eq_iff_eq_add hd |>.mp rfl
  let hobj := @Δf_eq c (d - 1)
  rw [← heq] at hobj
  exact hobj

lemma Δf_eq'' {c : ℝ} {d : ℕ} (hd : 0 < d) :
    c / ((d - 1 : ℕ) + 1 : ℝ) - c / (d + 1 : ℝ) = c / ((d : ℝ)*(d + 1 : ℝ)) := by
  let hobj := @Δf_eq c (d - 1)
  have heq : (d : ℝ) = ((d - 1 : ℕ) + 1 : ℝ) := by
    rw [← @Nat.cast_one ℝ _, ← Nat.cast_add]
    exact Nat.cast_inj.mpr <| Nat.sub_eq_iff_eq_add hd |>.mp rfl
  exact heq ▸ hobj

lemma split_sum {α β ι : Type*} [DecidableEq ι] [Ring β] {f : ι → β} (s : Finset α) (s' : Finset ι)
    {g : α → Finset ι} (h : s.sup g = s')
    (h' : ∀ x y, x ≠ y → g x ∩ g y = ∅) :
    ∑ x ∈ s', f x = ∑ x ∈ s, ∑ y ∈ g x, f y := by
  induction s using Finset.cons_induction generalizing s' with
  | empty =>
    simp_all only [ne_eq, Finset.sup_empty, Finset.bot_eq_empty, Finset.sum_empty,
      not_false_eq_true, implies_true]
    rw [← h, Finset.sum_empty]
  | cons y _s hys ih => ?_
  simp only [Finset.sum_cons]
  simp only [Finset.sup_cons, Finset.sup_eq_union'] at h
  rw [← ih _ rfl, ← h]
  rw [Finset.sum_union]
  refine Finset.disjoint_iff_inter_eq_empty.mpr ?_
  ext u
  simp only [Finset.notMem_empty, iff_false, Finset.mem_inter, not_and', Finset.mem_sup]
  intro ⟨x, hxs, hx⟩
  exact notMem_of_mem_of_empty_inter hx <| h' _ _ (ne_of_mem_of_not_mem hxs hys)

lemma sum_disjoint_union {α β : Type*} [DecidableEq α] [Ring β] {s s' t : Finset α} {f : α → β}
    (ht : t = s ∪ s') (hss' : s ∩ s' = ∅) :
    ∑ x ∈ s, f x + ∑ x ∈ s', f x = ∑ x ∈ t, f x := by
  refine Eq.symm <| Eq.trans ?_ sum_union_inter
  simp only [ht, hss', sum_empty, add_zero]

lemma sum_triplet {α β : Type*} [DecidableEq α] [Ring β] {a b c : α} {f : α → β}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ x ∈ {a, b, c}, f x = f a + f b + f c := by
  have : ∑ x ∈ insert a {b, c}, f x = f a + ∑ x ∈ {b, c}, f x := by
    refine sum_insert <| by grind
  rw [this]
  suffices ∑ x ∈ {b, c}, f x = f b + f c by
    grind
  exact sum_pair hbc

lemma sum_quadruplet {α β : Type*} [DecidableEq α] [Ring β] {a b c d : α} {f : α → β}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∑ x ∈ {a, b, c, d}, f x = f a + f b + f c + f d := by
  repeat rw [sum_insert (by grind)]
  grind

end Finset

open SimpleGraph
open Finset

lemma sum_sdiff_singleton {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (f : (H : SimpleGraph V) → (w : V) → [Fintype (H.neighborSet w)] → ℝ) {X : Finset V}
    {v : V} (hv : v ∈ X) (hNv : G.neighborFinset v ⊆ X)
    (H : ∀ w ∈ X \ G.closed_neighborFinset_of_Finset {v}, f G w = f (G.deleteIncidencesOf {v}) w) :
    ∑ w ∈ X, f G w
      = ∑ w ∈ X \ {v}, f (G.deleteIncidencesOf {v}) w
        + ∑ w ∈ G.neighborFinset v, (f G w - f (G.deleteIncidencesOf {v}) w)
        + f G v := by
  calc _
    _ = ∑ w ∈ X \ G.closed_neighborFinset_of_Finset {v}, f G w
        + ∑ w ∈ G.closed_neighborFinset_of_Finset {v}, f G w := by
      refine Eq.symm (sum_sdiff ?_)
      intro w hw
      have := mem_closed_neighborFinset_iff.mp hw
      grind [mem_neighborFinset]
    _ = ∑ w ∈ X \ G.closed_neighborFinset_of_Finset {v}, f (G.deleteIncidencesOf {v}) w
        + ∑ w ∈ G.closed_neighborFinset_of_Finset {v}, f G w := by
      simp only [add_left_inj]
      refine sum_congr rfl H
    _ = (∑ w ∈ X \ G.closed_neighborFinset_of_Finset {v}, f (G.deleteIncidencesOf {v}) w
        + ∑ w ∈ G.neighborFinset v, f (G.deleteIncidencesOf {v}) w)
        - ∑ w ∈ G.neighborFinset v, f (G.deleteIncidencesOf {v}) w
        + ∑ w ∈ G.closed_neighborFinset_of_Finset {v}, f G w := by
      linarith
    _ = ∑ w ∈ X \ {v}, f (G.deleteIncidencesOf {v}) w
        - ∑ w ∈ G.neighborFinset v, f (G.deleteIncidencesOf {v}) w
        + ∑ w ∈ G.closed_neighborFinset_of_Finset {v}, f G w := by
      simp only [add_left_inj, sub_left_inj]
      rw [closed_neighborFinset_of_singleton_eq]
      refine sum_disjoint_union ?_ (by grind)
      grind [ne_of_mem_neighborFinset]
    _ = ∑ w ∈ X \ {v}, f (G.deleteIncidencesOf {v}) w
        - ∑ w ∈ G.neighborFinset v, f (G.deleteIncidencesOf {v}) w
        + (∑ w ∈ G.neighborFinset v, f G w + f G v) := by
      rw [closed_neighborFinset_of_singleton_eq]
      simp only [union_singleton, mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true,
        sum_insert, add_right_inj]
      rw [add_comm]
  simp only [sum_sub_distrib]
  grind

lemma sum_sdiff_singleton' {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {f : ℕ → ℝ} {X : Finset V}
    {v : V} (hv : v ∈ X) (hNv : G.neighborFinset v ⊆ X) :
    ∑ w ∈ X, f (G.degree w)
      = ∑ w ∈ X \ {v}, f ((G.deleteIncidencesOf {v}).degree w)
        + ∑ w ∈ G.neighborFinset v, (f (G.degree w) - f ((G.deleteIncidencesOf {v}).degree w))
        + f (G.degree v) := by
  refine sum_sdiff_singleton G (fun G v _ ↦ f <| G.degree v) hv hNv ?_
  intro w hw
  refine congrArg (f ∘ Finset.card) ?_
  refine Eq.symm <| neighborFinset_eq_delelteIncidencesOf_of_empty_inter_neighborFinset ?_ ?_
  · simp only [inter_singleton_eq_empty_iff]
    refine not_mem_neighborFinset_symm <| notMem_mono ?_ (mem_sdiff.mp hw |>.2)
    intro u hu
    refine mem_closed_neighborFinset_iff.mpr <| Or.inr ⟨v, mem_singleton.mpr rfl, ?_⟩
    exact mem_neighborFinset .. |>.mp hu
  · exact notMem_mono G.closed_neighborFinset_contains_Finset (mem_sdiff.mp hw |>.2)

theorem cw_bound_mono (f : ℕ → ℝ) {V : Type*} [DecidableEq V] [Fintype V] {v : V}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hv : G.degree v = G.maxDegree)
    {δ : ℕ} (hΔ : G.maxDegree > δ) (X : Finset V) (hX : G.support ⊆ X)
    (hγ : ∀ d₁ d₂, δ < d₁ → d₁ ≤ d₂ → f (d₂ - 1) - f d₂ ≤ f (d₁ - 1) - f d₁)
    (hNv : ∀ x ∈ G.neighborFinset v, G.degree x > δ)
    (hγ' : ∀ d, δ < d → d * (f (d - 1) - f d) ≥ f d) :
    ∑ x ∈ X, f (G.degree x) ≤ ∑ x ∈ (X \ {v}), f ((G.deleteIncidencesOf {v}).degree x) := by
  have Nv_subs_X : G.neighborFinset v ⊆ X :=
    subset_trans neighborFinset_subset_support (Set.toFinset_subset.mpr hX)
  suffices f (G.degree v)
      ≤ ∑ x ∈ G.neighborFinset v, (f ((G.deleteIncidencesOf {v}).degree x) - f (G.degree x)) by
    calc ∑ x ∈ X, f (G.degree x)
      _ = ∑ x ∈ (X \ G.neighborFinset v), f (G.degree x)
          + ∑ x ∈ G.neighborFinset v, f (G.degree x) :=
        (sum_sdiff <| Nv_subs_X).symm
      _ = ∑ x ∈ ((X \ G.neighborFinset v) \ {v}), f (G.degree x) + f (G.degree v)
          + ∑ x ∈ G.neighborFinset v, f (G.degree x) := by
        simp only [add_left_inj]
        rw [← sum_singleton (fun x ↦ f (G.degree x)) v]
        refine Eq.symm <| sum_sdiff ?_
        simp only [singleton_subset_iff, mem_sdiff, notMem_neighborFinset_self, not_false_eq_true,
          and_true]
        exact mem_of_subset_of_degree_pos hX <| hv ▸ Nat.zero_lt_of_lt hΔ
      _ = ∑ x ∈ ((X \ G.neighborFinset v) \ {v}), f ((G.deleteIncidencesOf {v}).degree x)
          + f (G.degree v)
          + ∑ x ∈ G.neighborFinset v, f (G.degree x) := by
        simp only [add_left_inj]
        refine sum_congr rfl ?_
        intro x hx
        refine congrArg (f ∘ card) ?_
        ext w
        constructor
        · intro hw
          refine (mem_neighborFinset_deleteIncidencesOf_iff_of_notMem ?_ ?_).mp hw
          · refine notMem_singleton.mpr <| ne_of_mem_of_not_mem hw ?_
            exact not_mem_neighborFinset_symm <| mem_sdiff.mp (mem_sdiff.mp hx |>.1) |>.2
          · exact mem_sdiff.mp hx |>.2
        · exact mem_neighborFinset_of_deleteIncidencesOf_mem_neighborFinset
      _ = ∑ x ∈ ((X \ G.neighborFinset v) \ {v}), f ((G.deleteIncidencesOf {v}).degree x)
          + f (G.degree v)
          + ∑ x ∈ G.neighborFinset v, f ((G.deleteIncidencesOf {v}).degree x)
          + ∑ x ∈ G.neighborFinset v,
            (f (G.degree x) - f ((G.deleteIncidencesOf {v}).degree x)) := by
        simp only [sum_sub_distrib, add_add_sub_cancel]
      _ = (∑ x ∈ ((X \ G.neighborFinset v) \ {v}), f ((G.deleteIncidencesOf {v}).degree x)
          + f (G.degree v)
          + ∑ x ∈ G.neighborFinset v, f ((G.deleteIncidencesOf {v}).degree x))
          + ∑ x ∈ G.neighborFinset v,
            (f (G.degree x) - f ((G.deleteIncidencesOf {v}).degree x)) := by
        simp only [sum_sub_distrib, add_add_sub_cancel]
      _ = ∑ x ∈ (X \ G.neighborFinset v) \ {v}, f ((G.deleteIncidencesOf {v}).degree x)
          + ∑ x ∈ G.neighborFinset v, f ((G.deleteIncidencesOf {v}).degree x)
          + f (G.degree v)
          + ∑ x ∈ G.neighborFinset v,
            (f (G.degree x) - f ((G.deleteIncidencesOf {v}).degree x)) := by
        linarith
      _ = ∑ x ∈ X \ {v}, f ((G.deleteIncidencesOf {v}).degree x)
          + f (G.degree v)
          + ∑ x ∈ G.neighborFinset v,
            (f (G.degree x) - f ((G.deleteIncidencesOf {v}).degree x)) := by
        simp only [add_left_inj]
        apply Eq.symm
        have cup : ((X \ G.neighborFinset v) \ {v}) ∪ G.neighborFinset v = X \ {v} := by
          ext x
          simp only [mem_union, mem_sdiff, mem_neighborFinset,
            mem_singleton]
          refine ⟨?_, by grind⟩
          intro h
          match h with
          | Or.inl h => exact ⟨h.1.1, h.2⟩
          | Or.inr h => exact ⟨mem_of_subset_of_adj hX h, h.ne'⟩
        have cap : ((X \ G.neighborFinset v) \ {v}) ∩ G.neighborFinset v = ∅ := by
          rw [sdiff_inter_right_comm]
          refine eq_empty_of_subset_empty <| sdiff_subset_of_subset
            <| subset_of_eq <| sdiff_inter_self ..
        let hobj := cup ▸ cap ▸
          @sum_union_inter _ ℝ ((X \ G.neighborFinset v) \ {v}) (G.neighborFinset v)
          _ (fun w ↦ f ((G.deleteIncidencesOf {v}).degree w)) _
        simp only [sum_empty, add_zero] at hobj
        exact hobj
      _ = (∑ x ∈ X \ {v}, f ((G.deleteIncidencesOf {v}).degree x))
          + (f (G.degree v)
          + ∑ x ∈ G.neighborFinset v,
            (f (G.degree x) - f ((G.deleteIncidencesOf {v}).degree x))) := by
        linarith
    refine (add_le_iff_nonpos_right _).mpr <| le_neg_iff_add_nonpos_right.mp ?_
    exact le_trans this (by simp only [sum_sub_distrib, neg_sub, le_refl])
  calc ∑ x ∈ G.neighborFinset v, (f ((G.deleteIncidencesOf {v}).degree x) - f (G.degree x))
    _ = ∑ x ∈ G.neighborFinset v, (f (G.degree x - 1) - f (G.degree x)) := by
      refine sum_congr rfl ?_
      intro x hx
      simp only [sub_left_inj]
      refine congrArg _ <| ?_
      simp only [degree]
      calc _
        _ = #(G.neighborFinset x \ {v}) := by
          refine congrArg (Finset.card) ?_
          rw [deleteIncidencesOf_neighborFinset_eq]
          exact notMem_singleton.mpr <| ne_of_mem_neighborFinset hx
      exact card_setminus_singleton <| mem_neighborFinset_symm hx
    _ ≥ ∑ x ∈ G.neighborFinset v, (f (G.maxDegree - 1) - f G.maxDegree) := by
      refine sum_le_sum ?_
      exact fun x hx ↦ hγ (G.degree x) G.maxDegree (hNv x hx) (G.degree_le_maxDegree _)
    _ ≥ f (G.degree v) := by
      simp only [sum_const,
        card_neighborFinset_eq_degree, nsmul_eq_mul, ge_iff_le]
      exact hv ▸ hγ' G.maxDegree hΔ
