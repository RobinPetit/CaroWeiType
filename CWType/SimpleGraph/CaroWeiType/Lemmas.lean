import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

import CWType.SimpleGraph.CaroWeiType.Basic

@[simp]
lemma ne_of_mem_finset_empty_inter {α : Type*} [DecidableEq α]
    {x y : α} (s t : Finset α)
    (h : s ∩ t = ∅) (hx : x ∈ s) (hy : y ∈ t) :
    x ≠ y := by
  intro this
  haveI := Finset.mem_inter.mpr ⟨hx, this ▸ hy⟩
  grind

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

lemma card_setminus_singleton' {n : ℕ} {α : Type*} [DecidableEq α] {s : Finset α} {x : α}
    (hx : x ∈ s) (hcard : s.card = n + 1) : (s \ {x}).card = n := by
  grind

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

lemma discrete_derivative_inv_eq (d : ℕ) (hd_pos : 0 < d) :
    ((d - 1 : ℕ) + 1 : ℝ)⁻¹ - (d + 1 : ℝ)⁻¹ = ((d * (d + 1)) : ℝ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [Nat.cast_pred hd_pos]
  simp only [sub_add_cancel]
  have hdR_pos : (d : ℝ) ≠ 0 := by exact Nat.cast_ne_zero.mpr <| Nat.ne_zero_of_lt hd_pos
  calc ((d : ℝ)⁻¹ - (d + 1 : ℝ)⁻¹) * ((d : ℝ) * (d + 1 : ℝ))
    _ = (d : ℝ)⁻¹ * ((d : ℝ) * (d + 1 : ℝ)) - (d + 1 : ℝ)⁻¹ * ((d : ℝ) * (d + 1 : ℝ)) := by
      exact sub_mul ..
    _ = ((d : ℝ)⁻¹ * (d : ℝ)) * (d + 1 : ℝ) - (d + 1 : ℝ)⁻¹ * ((d : ℝ) * (d + 1 : ℝ)) := by
      simp only [sub_left_inj]
      exact Eq.symm <| mul_assoc ..
    _ = (d + 1 : ℝ) - (d + 1 : ℝ)⁻¹ * ((d : ℝ) * (d + 1 : ℝ)) := by
      have h' : (d : ℝ)⁻¹ * (d : ℝ) = 1 := by grind
      simp only [h', one_mul]
    _ = 1 := by grind

lemma avg_gain (d : ℕ) (hd_pos : 0 < d) :
    d * (((d - 1 : ℕ) + 1 : ℝ)⁻¹ - (d + 1 : ℝ)⁻¹) = (d + 1 : ℝ)⁻¹ := by
  rw [discrete_derivative_inv_eq d hd_pos]
  simp only [mul_inv_rev]
  calc (d : ℝ) * ((d + 1 : ℝ)⁻¹ * (d : ℝ)⁻¹)
    _ = (d : ℝ) * ((d : ℝ)⁻¹ * (d + 1 : ℝ)⁻¹) := by
      simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero]
      refine Or.inl ?_
      exact mul_comm ..
    _ = ((d : ℝ) * (d : ℝ)⁻¹) * (d + 1 : ℝ)⁻¹ := Eq.symm <| mul_assoc ..
    _ = 1 * (d + 1 : ℝ)⁻¹ := by
      simp only [mul_eq_mul_right_iff]
      refine Or.inl ?_
      refine mul_inv_cancel₀ ?_
      exact Ne.symm <| ne_of_lt <| Nat.cast_pos'.mpr hd_pos
    _ = (d + 1 : ℝ)⁻¹ := by simp only [one_mul]

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

lemma subset_eq_inter {α : Type*} [DecidableEq α] {s₁ s₂ t : Finset α} (h : t ⊆ (s₁ \ s₂)) :
    t ⊆ s₁ :=
  fun _ hx ↦ Finset.mem_sdiff.mp (h hx) |>.1

theorem deleteIncidenceSet_support {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (X : Finset V) (hX : G.support ⊆ X) {v : V} :
    (G.deleteIncidenceSet v).support ⊆ ((X \ {v}) : Finset V) := by
  intro w
  simp only [support, deleteIncidenceSet, incidenceSet, deleteEdges_adj, Prod.mk.eta,
    Set.mem_setOf_eq, not_and, SetRel.mem_dom, mem_edgeSet, Sym2.mem_iff, not_or, Finset.coe_sdiff,
    Finset.coe_singleton, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff, forall_exists_index,
    and_imp]
  intro x hwx h
  constructor
  · refine hX ?_
    simp only [support, SetRel.mem_dom, Set.mem_setOf_eq]
    exact ⟨x, hwx⟩
  · exact Ne.symm <| h hwx |>.1

lemma closed_neighborFinset_of_singleton_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.closed_neighborFinset_of_Finset {v} = G.neighborFinset v ∪ {v} := by
  ext w
  simp only [closed_neighborFinset_of_Finset, Finset.mem_singleton, exists_eq_left,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.union_singleton, Finset.mem_insert,
    mem_neighborFinset]
  if h : w = v then
    simp only [h, SimpleGraph.irrefl, or_false]
  else
    simp only [h, false_or]
    exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

lemma closed_neighborFinset_contains_Finset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    s ⊆ G.closed_neighborFinset_of_Finset s := by
  intro u hu
  simp only [closed_neighborFinset_of_Finset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.symm (Or.inr hu)

lemma deleteIncidencesOf_singleton_eq_deleteIncidenceSet
    {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    G.deleteIncidencesOf {v} = G.deleteIncidenceSet v := by
  simp [deleteIncidencesOf, deleteIncidenceSet_le]

lemma deleteIncidencesOf_notadj {n : ℕ} (G : SimpleGraph (Fin n)) {s : Finset (Fin n)}
    {x y : Fin n} (hx : x ∈ s) :
    ¬(G.deleteIncidencesOf s).Adj x y := by
  simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, inf_adj, iInf_adj,
    deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq,
    Decidable.not_not]
  intro hxy h
  exact false_of_ne (h x |>.1 hx |>.2 hxy |>.1) |>.elim

theorem cw_bound_mono (f : ℕ → ℝ) {n : ℕ} {v : Fin n}
    (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (hv : G.degree v = G.maxDegree)
    {δ : ℕ}
    (hΔ : G.maxDegree > δ)
    (X : Finset (Fin n))
    (hX : G.support ⊆ X)
    (hγ : ∀ d₁ d₂, δ < d₁ → d₁ ≤ d₂ → f (d₂ - 1) - f d₂ ≤ f (d₁ - 1) - f d₁)
    (hNv : ∀ x ∈ G.neighborFinset v, G.degree x > δ)
    (hγ' : ∀ d, δ < d → d * (f (d - 1) - f d) ≥ f d) :
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
          refine hX <| G.degree_pos_iff_mem_support v |>.mp (hv ▸ Nat.zero_lt_of_lt hΔ)
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
      refine Finset.sum_le_sum ?_
      exact fun x hx ↦ hγ (G.degree x) G.maxDegree (hNv x hx) (G.degree_le_maxDegree _)
    _ ≥ f (G.degree v) := by
      simp only [Finset.sum_const,
        card_neighborFinset_eq_degree, nsmul_eq_mul, ge_iff_le]
      exact hv ▸ hγ' G.maxDegree hΔ

theorem cw_bound_deleteIncidenceSet_le (f : ℕ → ℝ) {n : ℕ} {v : Fin n}
    (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (X : Finset (Fin n)) (hv : v ∈ X)
    (hf : ∀ d d', d ≤ d' → f d' ≤ f d) :
    ∑ x ∈ X, f (G.degree x)
      ≤ ∑ x ∈ X \ {v}, f ((G.deleteIncidenceSet v).degree x) + f (G.degree v) := by
  calc ∑ x ∈ X, f (G.degree x)
    _ = ∑ x ∈ X \ {v}, f (G.degree x) + ∑ x ∈ {v}, f (G.degree x) :=
      Eq.symm <| Finset.sum_sdiff <| Finset.singleton_subset_iff.mpr hv
    _ = ∑ x ∈ X \ {v}, f (G.degree x) + f (G.degree v) := by simp only [Finset.sum_singleton]
    _ ≤ ∑ x ∈ X \ {v}, f ((G.deleteIncidenceSet v).degree x) + f (G.degree v) := by
      simp only [add_le_add_iff_right]
      refine Finset.sum_le_sum ?_
      intro w hw
      refine hf _ _ ?_
      exact degree_le_of_le <| G.deleteIncidenceSet_le v

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

lemma induced_degree_eq {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (v : V) (hv : v ∈ s) [Fintype (G.neighborSet v)] :
    (G.induce s).degree ⟨v, hv⟩ = (G.neighborFinset v ∩ s).card := by
  rw [degree]
  refine Set.BijOn.finsetCard_eq ?_ ⟨?_, ?_, ?_⟩
  · exact fun x ↦ x.1
  · intro x hx
    simp only [SetLike.coe_sort_coe, coe_neighborFinset, mem_neighborSet, comap_adj,
      Finset.coe_inter, Set.mem_inter_iff, Subtype.coe_prop, and_true] at hx ⊢
    exact hx
  · intro x hx y hy hne
    simp_all
  · intro y hy
    simp only [Finset.coe_inter, coe_neighborFinset, Set.mem_inter_iff, mem_neighborSet,
      SetLike.mem_coe, SetLike.coe_sort_coe, Set.mem_image, comap_adj, Subtype.exists,
      exists_and_right, exists_eq_right] at hy ⊢
    exact ⟨hy.2, hy.1⟩

lemma induced_degree_eq' {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) (v : Fin n) (hv : v ∈ s) :
    (G.induce s).degree ⟨v, hv⟩ = ({w ∈ s | G.Adj v w}).card := by
  classical
  rw [induced_degree_eq]
  refine congrArg _ ?_
  ext w
  simp only [Finset.mem_inter, mem_neighborFinset, Finset.mem_filter, And.comm]

namespace SimpleGraph

theorem exists_minimal_degree_vertex_in {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) [Nonempty X] :
    ∃ v, v ∈ X ∧ ∀ w ∈ X, (G.neighborFinset v ∩ X).card ≤ (G.neighborFinset w ∩ X).card := by
  obtain ⟨v, hv⟩ := (G.induce X).exists_minimal_degree_vertex
  refine ⟨v.1, v.2, ?_⟩
  intro w hw
  calc (G.neighborFinset v ∩ X).card
    _ = (G.induce X).degree v := Eq.symm <| induced_degree_eq G X v.1 v.2
    _ = (G.induce X).minDegree := Eq.symm <| hv
    _ ≤ (G.induce X).degree ⟨w, hw⟩ := (G.induce X).minDegree_le_degree _
    _ = (G.neighborFinset w ∩ X).card := induced_degree_eq G X w hw

theorem exists_maximal_degree_vertex_in {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) [Nonempty X] :
    ∃ v, v ∈ X ∧ ∀ w ∈ X, (G.neighborFinset v ∩ X).card ≥ (G.neighborFinset w ∩ X).card := by
  obtain ⟨v, hv⟩ := (G.induce X).exists_maximal_degree_vertex
  refine ⟨v.1, v.2, ?_⟩
  intro w hw
  calc (G.neighborFinset v ∩ X).card
    _ = (G.induce X).degree v := Eq.symm <| induced_degree_eq G X v.1 v.2
    _ = (G.induce X).maxDegree := Eq.symm <| hv
    _ ≥ (G.induce X).degree ⟨w, hw⟩ := (G.induce X).degree_le_maxDegree _
    _ = (G.neighborFinset w ∩ X).card := induced_degree_eq G X w hw

theorem degree_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (hX : G.support ⊆ X) :
    ∀ x, G.degree x = (G.neighborFinset x ∩ X).card := by
  intro x
  rw [degree]
  refine congrArg _ ?_
  refine Finset.ext_iff.mpr ?_
  intro y
  constructor
  · intro hy
    simp_all only [mem_neighborFinset, Finset.mem_inter, true_and]
    exact hX <| G.mem_support.mpr ⟨_, hy.symm⟩
  · exact fun hy ↦ Finset.mem_inter.mp hy |>.1

open Finset in
lemma degree_eq' {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : G.degree v = (G.neighborFinset v ∩ G.support.toFinset).card := by
  rw [degree]
  refine congrArg _ ?_
  ext w
  constructor
  · intro hw
    have _ : w ∈ G.support := by
      refine G.degree_pos_iff_mem_support w |>.mp ?_
      exact Adj.degree_pos_left (G.mem_neighborFinset v w |>.mp hw).symm
    simp_all only [mem_neighborFinset, mem_inter, Set.mem_toFinset, and_self]
  · intro hx
    exact mem_of_mem_filter w hx


theorem minDegree_iff {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V} :
    G.degree v = G.minDegree ↔ ∀ w, G.degree v ≤ G.degree w := by
  if h : Nonempty V then
    constructor
    · intro hδ w
      exact hδ ▸ G.minDegree_le_degree _
    · intro h
      obtain ⟨w, hw⟩ := G.exists_minimal_degree_vertex
      exact Nat.le_antisymm (hw ▸ h w) (G.minDegree_le_degree _)
  else
    exact h (Nonempty.intro v) |>.elim

theorem maxDegree_iff {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V} :
    G.degree v = G.maxDegree ↔ ∀ w, G.degree w ≤ G.degree v := by
  if h : Nonempty V then
    constructor
    · intro hΔ w
      exact hΔ ▸ G.degree_le_maxDegree _
    · intro h
      obtain ⟨w, hw⟩ := G.exists_maximal_degree_vertex
      exact (Nat.le_antisymm (G.degree_le_maxDegree _) (hw ▸ h w))
  else
    exact h (Nonempty.intro v) |>.elim

theorem minDegree_iff' {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (X : Finset V) (hX : X.Nonempty) (hv : v ∈ X) :
    G.degree v = (X.image fun x ↦ G.degree x).min' (Finset.image_nonempty.mpr hX)
      ↔ ∀ w ∈ X, G.degree v ≤ G.degree w := by
  constructor
  · intro hdegv w hw
    exact hdegv ▸ Finset.min'_le _ _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  · intro h
    refine Nat.le_antisymm ?_ ?_
    · refine Finset.le_min'_iff _ (Finset.image_nonempty.mpr hX) |>.mpr ?_
      intro y
      simp only [Finset.mem_image, forall_exists_index, and_imp]
      intro z hz hdz
      exact hdz ▸ h _ hz
    · exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hv)

end SimpleGraph
