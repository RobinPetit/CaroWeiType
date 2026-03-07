-- import Mathlib

import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

import CWType.SimpleGraph.CaroWeiType.Basic

open SimpleGraph
open CaroWeiType

lemma Nonempty_if_card_pos {α : Type*} {s : Finset α} (h : 0 < s.card) :
    Nonempty s := by
  exact Finset.Nonempty.to_subtype <| Finset.card_pos.mp h

lemma Nonempty_if_card_pos' {α : Type*} {s : Finset α} (h : 0 < s.card) :
    Nonempty α := by
  exact Nonempty.intro (Classical.choice <| Nonempty_if_card_pos h).1

lemma card_setminus_singleton {α : Type*} [DecidableEq α] {s : Finset α} {x : α}
    (h : x ∈ s) : (s \ {x}).card = s.card - 1 := by grind

theorem Finset_unique_elems {α : Type*} [inst : Nonempty α] (s : Finset α) :
    ∃ f : ℕ → α,
      (∀ (k : ℕ), k < s.card → f k ∈ s)
        ∧ (∀ (k k' : ℕ), k < s.card → k' < s.card → k ≠ k' → f k ≠ f k') := by
  classical
  induction hcard : s.card generalizing s with
  | zero => exact ⟨fun _ ↦ @Classical.choice α inst, by simp_all⟩
  | succ n ih => ?_
  have hsNonempty : Nonempty s := Nonempty_if_card_pos <| Nat.lt_of_sub_eq_succ hcard
  obtain ⟨xₙ, hxₙ⟩ := Classical.choice hsNonempty
  obtain ⟨f', ⟨hf'₁, hf'₂⟩⟩ := ih (s \ {xₙ}) (by simp [card_setminus_singleton hxₙ, hcard])
  use fun k ↦ if k < n then f' k else xₙ
  constructor
  · intro k _
    split_ifs with hk
    · exact Finset.sdiff_subset <| hf'₁ k hk
    · exact hxₙ
  · intro k k' hk hk' hneq
    split_ifs with hif hif' hif'
    · simp_all only [ne_eq, not_false_eq_true]
    · simp_all only [ne_eq, Finset.mem_sdiff, Finset.mem_singleton, not_false_eq_true]
    · intro this
      let contr := this ▸ (Finset.mem_sdiff.mp <| hf'₁ _ hif').2
      simp at contr
    · have hkn : k = n := by exact Nat.eq_of_lt_succ_of_not_lt hk hif
      have hk'n : k' = n := by exact Nat.eq_of_lt_succ_of_not_lt hk' hif'
      exact hneq (hkn.trans hk'n.symm) |>.elim

theorem Finset_get_one {α : Type*} (s : Finset α) (h : 1 ≤ s.card) :
    ∃ x, x ∈ s := by
  have _ : Nonempty α := Nonempty_if_card_pos' h
  obtain ⟨f, ⟨hf, _⟩⟩ := Finset_unique_elems s
  exact ⟨f 0, hf _ h⟩

theorem Finset_get_two {α : Type*} (s : Finset α) (h : 2 ≤ s.card) :
    ∃ x y, x ∈ s ∧ y ∈ s ∧ x ≠ y := by
  have _ : Nonempty α := Nonempty_if_card_pos' (Nat.zero_lt_of_lt h)
  obtain ⟨f, ⟨hf₁, hf₂⟩⟩ := Finset_unique_elems s
  refine ⟨f 0, f 1, ?_, ?_, ?_⟩
  · exact hf₁ _ (Nat.zero_lt_of_lt h)
  · exact hf₁ _ (Nat.lt_of_succ_le h)
  · refine hf₂ 0 1 (Nat.zero_lt_of_lt h) (Nat.lt_of_succ_le h) (by simp)

lemma sum_const' {ι : Type*} {f : ι → ℝ} {c : ℝ} (X : Finset ι) (h : ∀ x ∈ X, f x = c) :
    ∑ x ∈ X, f x = X.card * c := by
  simp_all only [Finset.sum_const, nsmul_eq_mul]

lemma ne_symm {α : Type*} {a b : α} (h : ¬a = b) : ¬b = a :=
  fun hba ↦ h hba.symm

theorem deleteIncidenceSet_degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : ∀ w ∈ G.neighborFinset v, (G.deleteIncidenceSet v).degree w = G.degree w - 1 := by
  intro w hw
  suffices (G.deleteIncidenceSet v).neighborFinset w = G.neighborFinset w \ {v} by
    calc (G.deleteIncidenceSet v).degree w
      _ = ((G.deleteIncidenceSet v).neighborFinset w).card := rfl
      _ = (G.neighborFinset w \ {v}).card := by rw [this]
      _ = (G.neighborFinset w).card - ({v} : Finset _).card := by
        refine Finset.card_sdiff_of_subset ?_
        simp only [Finset.singleton_subset_iff, mem_neighborFinset]
        exact (G.mem_neighborFinset v w).mp hw |>.symm
  ext x
  constructor
  · intro hx
    simp_all only [mem_neighborFinset, deleteIncidenceSet,
      incidenceSet, deleteEdges_adj, Set.mem_setOf_eq,
      mem_edgeSet, Sym2.mem_iff, not_and, not_or, Finset.mem_sdiff,
      Finset.mem_singleton, true_and]
    exact ne_symm <| hx.2 hx.1 |>.2
  · intro hx
    simp_all only [mem_neighborFinset, Finset.mem_sdiff, Finset.mem_singleton,
      deleteIncidenceSet, incidenceSet, deleteEdges_adj,
      Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, true_and, not_or]
    exact ⟨hw.ne, ne_symm hx.2⟩

theorem cw_bound_mono (f : ℕ → ℝ) {n : ℕ} {v : Fin n}
    (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (hv : G.degree v = G.maxDegree)
    (hΔ : G.maxDegree > 0)
    (X : Finset (Fin n))
    (hX : G.support ⊆ X)
    (hγ : ∀ d, d > 0 → d ≤ G.maxDegree → (f (d - 1) - f d) ≥ (f (G.maxDegree - 1) - f G.maxDegree))
    (hγ' : G.maxDegree * (f (G.maxDegree - 1) - f G.maxDegree) ≥ f G.maxDegree) :
    ∑ x ∈ X, f (G.degree x) ≤ ∑ x ∈ (X \ {v}), f ((G.deleteIncidenceSet v).degree x) := by
  have Nv_subs_X : G.neighborFinset v ⊆ X := by
    intro x hx
    refine hX ?_
    simp only [support, SetRel.mem_dom, Set.mem_setOf_eq]
    refine ⟨v, ?_⟩
    simp_all [Adj.symm]
  suffices f (G.degree v)
      ≤ ∑ x ∈ G.neighborFinset v, (f ((G.deleteIncidenceSet v).degree x) - f (G.degree x)) by
    calc ∑ x ∈ X, f (G.degree x)
      _ = ∑ x ∈ (X \ G.neighborFinset v), f (G.degree x)
        + ∑ x ∈ G.neighborFinset v, f (G.degree x) := Eq.symm (Finset.sum_sdiff Nv_subs_X)
      _ = ∑ x ∈ ((X \ G.neighborFinset v) \ {v}), f (G.degree x) + f (G.degree v)
        + ∑ x ∈ G.neighborFinset v, f (G.degree x) := by
          simp only [add_left_inj]
          rw [← Finset.sum_singleton (fun x ↦ f (G.degree x)) v]
          refine Eq.symm <| Finset.sum_sdiff ?_
          simp only [Finset.singleton_subset_iff, Finset.mem_sdiff, mem_neighborFinset,
            SimpleGraph.irrefl, not_false_eq_true, and_true]
          refine hX <| G.degree_pos_iff_mem_support v |>.mp (hv ▸ hΔ)
      _ = ∑ x ∈ ((X \ G.neighborFinset v) \ {v}), f ((G.deleteIncidenceSet v).degree x)
        + f (G.degree v)
        + ∑ x ∈ G.neighborFinset v, f (G.degree x) := by
          simp only [add_left_inj]
          refine Finset.sum_congr rfl ?_
          intro x hx
          refine congrArg (f ∘ Finset.card) ?_
          ext w
          constructor
          · intro hw
            simp_all only [gt_iff_lt, ge_iff_le, tsub_le_iff_right, deleteIncidenceSet,
              incidenceSet, Finset.mem_sdiff, mem_neighborFinset,
              Finset.mem_singleton, deleteEdges_adj, Set.mem_setOf_eq,
              mem_edgeSet, Sym2.mem_iff, ne_eq, not_false_eq_true, Ne.symm, false_or,
              true_and]
            exact fun heq ↦ hx.1.2 (heq ▸ hw.symm)
          · intro hw
            simp_all [deleteIncidenceSet, Finset.mem_sdiff]
      _ = ∑ x ∈ ((X \ G.neighborFinset v) \ {v}), f ((G.deleteIncidenceSet v).degree x)
        + f (G.degree v)
        + ∑ x ∈ G.neighborFinset v, f ((G.deleteIncidenceSet v).degree x)
        + ∑ x ∈ G.neighborFinset v, (f (G.degree x) - f ((G.deleteIncidenceSet v).degree x)) := by
          simp only [Finset.sum_sub_distrib, add_add_sub_cancel]
      _ = (∑ x ∈ ((X \ G.neighborFinset v) \ {v}), f ((G.deleteIncidenceSet v).degree x)
        + f (G.degree v)
        + ∑ x ∈ G.neighborFinset v, f ((G.deleteIncidenceSet v).degree x))
        + (∑ x ∈ G.neighborFinset v, (f (G.degree x) - f ((G.deleteIncidenceSet v).degree x))) := by
          simp only [Finset.sum_sub_distrib, add_add_sub_cancel]
      _ = ∑ x ∈ (X \ G.neighborFinset v) \ {v}, f ((G.deleteIncidenceSet v).degree x)
        + ∑ x ∈ G.neighborFinset v, f ((G.deleteIncidenceSet v).degree x)
        + f (G.degree v)
        + ∑ x ∈ G.neighborFinset v, (f (G.degree x) - f ((G.deleteIncidenceSet v).degree x)) := by
          grind only
      _ = ∑ x ∈ X \ {v}, f ((G.deleteIncidenceSet v).degree x)
        + f (G.degree v)
        + ∑ x ∈ G.neighborFinset v, (f (G.degree x) - f ((G.deleteIncidenceSet v).degree x)) := by
          simp only [add_left_inj]
          apply Eq.symm
          have cup : ((X \ G.neighborFinset v) \ {v}) ∪ G.neighborFinset v = X \ {v} := by
            ext x
            simp only [Finset.mem_union, Finset.mem_sdiff, mem_neighborFinset,
              Finset.mem_singleton]
            refine ⟨?_, by grind⟩
            intro h
            match h with
            | Or.inl h => exact ⟨h.1.1, h.2⟩
            | Or.inr h =>
                exact ⟨hX (G.degree_pos_iff_mem_support x |>.mp h.symm.degree_pos_left), h.ne'⟩
          have cap : ((X \ G.neighborFinset v) \ {v}) ∩ G.neighborFinset v = ∅ := by grind
          let hobj := cup ▸ cap ▸
            @Finset.sum_union_inter _ ℝ ((X \ G.neighborFinset v) \ {v}) (G.neighborFinset v)
            _ (fun w ↦ f ((G.deleteIncidenceSet v).degree w)) _
          simp only [Finset.sum_empty, add_zero] at hobj
          exact hobj
      _ = (∑ x ∈ X \ {v}, f ((G.deleteIncidenceSet v).degree x))
        + (f (G.degree v)
        + ∑ x ∈ G.neighborFinset v, (f (G.degree x) - f ((G.deleteIncidenceSet v).degree x))) := by
          grind
    refine (add_le_iff_nonpos_right
      <| ∑ x ∈ X \ {v}, f ((G.deleteIncidenceSet v).degree x)).mpr ?_
    refine (@le_neg_iff_add_nonpos_right ℝ _ _ _ (f (G.degree v)) _).mp ?_
    exact le_trans this (by simp)
  calc ∑ x ∈ G.neighborFinset v, (f ((G.deleteIncidenceSet v).degree x) - f (G.degree x))
    _ = ∑ x ∈ G.neighborFinset v, (f (G.degree x - 1) - f (G.degree x)) := by
      refine @Finset.sum_congr _ ℝ _ _ _ _ _ rfl ?_
      intro x hx
      simp only [sub_left_inj]
      exact congrArg _ <| deleteIncidenceSet_degree G v x hx
    _ ≥ ∑ x ∈ G.neighborFinset v, (f (G.maxDegree - 1) - f G.maxDegree) := by
      refine Finset.sum_le_sum (fun x hx ↦ hγ (G.degree x) ?_ (G.degree_le_maxDegree _))
      exact ((G.mem_neighborFinset v x).mp hx |>.degree_pos_right)
    _ ≥ f (G.degree v) := by
      simp only [Finset.sum_const,
        card_neighborFinset_eq_degree, nsmul_eq_mul, ge_iff_le]
      exact hv ▸ hγ'

theorem bound_of_completeGraph (f : ℕ → ℝ) {n : ℕ}
    [DecidableRel (completeGraph (Fin (n + 1))).Adj] :
    ∑ v, f ((completeGraph (Fin (n + 1))).degree v) = (n + 1) * f n := by
  calc ∑ v, f ((completeGraph (Fin (n + 1))).degree v)
    _ = ∑ _ : Fin (n + 1), f n := by
        refine Finset.sum_congr rfl (fun x _ ↦ congrArg _ ?_)
        simp only [completeGraph_eq_top, degree, neighborFinset, neighborSet, top_adj]
        suffices {w | x ≠ w} = Set.univ \ {x} by simp [this, Finset.card_sdiff]
        ext w
        constructor <;> exact fun hw ↦ by grind
    _ = (n + 1) * f n := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

theorem CaroWeiTypeLB_le_1 (f : ℕ → ℝ)
    {π : {n : ℕ} → FiniteSimpleGraph n → Finset (Fin n) → Prop} :
    IsCaroWeiTypeLowerBound f π → f ≤ 1 := by
  intro hf d
  simp only [Pi.one_apply]
  obtain ⟨s, ⟨_, hcard⟩⟩:= hf (FiniteCompleteGraph (d + 1))
  let _ := (FiniteCompleteGraph (d + 1)).decAdj
  simp only [FiniteCompleteGraph] at hcard
  suffices (d + 1) * f d ≤ (d + 1 : ℝ) * 1 by
    exact mul_le_mul_iff_of_pos_left (Nat.cast_add_one_pos d) |>.mp this
  simp only [mul_one]
  calc (d + 1) * f d
    _ ≤ s.card := by
      exact (@bound_of_completeGraph f d).symm ▸ hcard
    _ ≤ (d + 1 : ℝ) := by
      suffices s.card ≤ d + 1 by
        rw [← Nat.cast_add_one d]
        exact Nat.cast_le.mpr this
      refine le_trans (Finset.card_le_card <| Finset.subset_univ s) ?_
      simp only [Finset.card_univ, Fintype.card_fin, le_refl]

#min_imports
