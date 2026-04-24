import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

import CWType.SimpleGraph.CaroWeiType.Basic

open Finset

lemma add_congr {a b c d : ℝ} (h₁ : a = c) (h₂ : b = d) :
    a + b = c + d := by
  let hobj1 := add_right_inj a |>.mpr h₂
  let hobj2 := add_left_inj d |>.mpr h₁
  exact hobj1.trans hobj2

lemma cast_five : ((5 : ℕ) : ℝ) = (5 : ℝ) := rfl

@[simp]
lemma le_add_one {x : ℝ} : x ≤ x + 1 :=
  le_of_lt <| lt_add_one x

@[simp]
lemma add_one_pos {n : ℕ} : 0 < n + (1 : ℝ) := by
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_pos]
  exact Nat.zero_lt_succ n

@[simp]
lemma add_one_add_one_pos {n : ℕ} : 0 < n + (1 : ℝ) + 1 := by
  rw [← Nat.cast_add_one n]
  exact add_one_pos

@[simp]
lemma add_two_pos {n : ℕ} : 0 < n + (2 : ℝ) := by
  rw [← one_add_one_eq_two, ← add_assoc]
  exact add_one_add_one_pos

@[simp]
lemma one_add_pos {n : ℕ} : 0 < (1 : ℝ) + n := by
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_pos]
  exact Nat.pos_of_neZero (1 + n)

@[simp]
lemma p_and_p_implies {p q : Prop} : (p → (p ∧ q)) ↔ (p → q) :=
  ⟨fun h hp ↦ h hp |>.2, fun hpq hp ↦ ⟨hp, hpq hp⟩⟩

@[simp]
lemma p_imp_q_imp_p {p q : Prop} : p → q → p :=
  fun h _ ↦ h

@[simp]
lemma neq_of_notin {α : Type*} {s : Finset α} {x y : α} (hy : y ∈ s) (hx : x ∉ s) :
    x ≠ y := by
  exact fun heq ↦ hx <| heq ▸ hy

@[simp]
lemma eq_of_subset_and_eq_card {α : Type*} {A B : Finset α} (h : A ⊆ B) (h' : #A = #B) :
    A = B := by
  classical
  induction hA : #A generalizing A B with
  | zero =>
      have : A = ∅ := card_eq_zero.mp hA
      have : B = ∅ := card_eq_zero.mp (h'.symm.trans hA)
      simp_all
  | succ n ih => ?_
  obtain ⟨a, ha⟩ := nonempty_def.mp <| card_pos.mp <| Nat.lt_of_sub_eq_succ hA
  let A' := A \ {a}
  let B' := B \ {a}
  have hsubset : A' ⊆ B' := by grind
  have hA : A = A' ∪ {a} := by ext _; simp [A', ha]
  have hB : B = B' ∪ {a} := by ext _; simp [B', h ha]
  grind

lemma one_lt_card_iff_exists_a_b {α : Type*} [DecidableEq α] {s : Finset α} :
    1 < #s ↔ ∃ x y, {x, y} ⊆ s ∧ x ≠ y := by
  constructor
  · intro hs
    have : s.Nonempty := nonempty_iff_ne_empty.mpr (by grind)
    obtain ⟨x, hx⟩ := nonempty_def.mp this
    have : (s \ {x}).Nonempty := sdiff_nonempty_of_card_lt_card hs
    obtain ⟨y, hy⟩ := nonempty_def.mp this
    refine ⟨x, y, ?_, ?_⟩ <;> grind
  · intro ⟨x, y, hxy, hxney⟩
    grind [card_le_card hxy]

lemma pair_eq {α : Type*} [DecidableEq α] {a b x y : α} (hab : a ≠ b)
    (h : ({a, b} : Finset _) = {x, y}) : a = x ∧ b = y ∨ a = y ∧ b = x := by
  if hax : a = x then
    refine Or.inl ⟨hax, ?_⟩
    have hb : b ∈ ({a, b} : Finset _) := by simp only [mem_insert, mem_singleton, or_true]
    rw [h] at hb
    simp only [mem_insert, mem_singleton] at hb
    rcases hb with hb | hb
    · simp only [hb, ← hax, ne_eq, not_true_eq_false] at hab
    · exact hb
  else
    simp_all only [ne_eq, false_and, false_or]
    refine ⟨?_, ?_⟩
    · have ha : a ∈ ({a, b} : Finset _) := by simp only [mem_insert, mem_singleton, true_or]
      rw [h] at ha
      simp only [mem_insert, hax, mem_singleton, false_or] at ha
      exact ha
    · have ha : a ∈ ({a, b} : Finset _) := by simp only [mem_insert, mem_singleton, true_or]
      have hb : b ∈ ({a, b} : Finset _) := by simp only [mem_insert, mem_singleton, or_true]
      rw [h] at ha hb
      simp only [mem_insert, hax, mem_singleton, false_or] at ha
      simp only [mem_insert, mem_singleton, Ne.symm <| ha ▸ hab, or_false] at hb
      exact hb

lemma sorted_pair {α : Type*} {β : Type*} [LinearOrder β] [DecidableEq α] (f : α → β) (x y : α) :
    ∃ a b, ({a, b} : Finset _) = {x, y} ∧ f a ≤ f b :=
  if h : f x ≤ f y then
    ⟨x, y, rfl, h⟩
  else
    ⟨y, x, pair_comm .., le_of_not_ge h⟩

private lemma sorted_finset {α : Type*} [DecidableEq α] {s : Finset α} (k : ℕ) [NeZero k]
    (hs : #s = k) (f : α → ℝ) :
    ∃ σ : Fin k → α,
      (Finset.image σ univ) = s
        ∧ (∀ i j : Fin k, i ≤ j → f (σ i) ≤ f (σ j)) := by
  induction s using Finset.induction_on_max_value f generalizing k with
  | h0 => exact (ne_of_lt <| Nat.pos_of_neZero k) (card_empty ▸ hs) |>.elim
  | step x t hx hmax ih => ?_
  have hcard : #t = k - 1 := by grind
  if hk : k = 1 then
    have ht : t = ∅ := card_eq_zero.mp (by simp [hcard, hk])
    use fun _ ↦ x
    simp only [le_refl, implies_true, and_true, ht]
    ext y
    simp only [mem_image, mem_univ, true_and, exists_const, eq_comm, insert_empty_eq, mem_singleton]
  else
    have _ : NeZero (k - 1) := { out := by grind }
    obtain ⟨σ, hσ, hinc⟩ := ih _ hcard
    let σ' : Fin k → α := by
      refine fun i ↦ if hi : i < k - 1 then σ ⟨i, hi⟩ else x
    refine ⟨σ', ?_, ?_⟩
    · ext z
      constructor
      · simp only [mem_image, mem_univ, true_and, mem_insert, forall_exists_index]
        intro i hiz
        if hi : i < k - 1 then
          simp only [σ', hi, ↓reduceDIte] at hiz
          rw [← hiz, ← hσ]
          exact Or.inr <| mem_image_of_mem σ <| mem_univ _
        else
          simp only [σ', hi, ↓reduceDIte] at hiz
          exact Or.inl hiz.symm
      · simp only [mem_insert, mem_image, mem_univ, true_and, σ']
        intro h
        rcases h with h | h
        · exact ⟨⟨k-1, by simp [Nat.pos_of_neZero k]⟩, by simp [h]⟩
        · simp only [← hσ, mem_image, mem_univ,
          true_and] at h
          obtain ⟨i, hi⟩ := h
          refine ⟨⟨i, lt_of_lt_of_le i.isLt <| Nat.sub_le k 1⟩, by simp [hi]⟩
    · intro i j hij
      if heq : i = j then
        simp only [heq, le_refl]
      else
        have hiltj : i < j := lt_of_le_of_ne hij heq
        if hj : j < k - 1 then
          have hi : i < k - 1 := lt_trans hiltj hj
          simp only [hi, ↓reduceDIte, hj, ge_iff_le, σ']
          refine hinc _ _ hij
        else
          have hi : i < k - 1 := lt_of_lt_of_le hiltj (by grind)
          simp only [hi, ↓reduceDIte, hj, ge_iff_le, σ']
          refine hmax _ ?_
          rw [← hσ]
          refine mem_image_of_mem σ <| mem_univ _

lemma pairwise_ne_of_triplet {α : Type*} [DecidableEq α] {x y z : α}
    (h : #({x, y, z} : Finset _) = 3) : x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  refine ⟨?_, ?_, ?_⟩ <;> {
    intro heq; subst heq
    suffices 3 ≤ 2 by grind
    simp [← h, card_le_two]
  }

lemma triplet_of_2 {α : Type*} [DecidableEq α] {x y : α} {s : Finset α}
    (hs : #s = 3) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    ∃ z, s = {x, y, z} := by
  have _ : #(s \ {x, y}) = #s - 2 := by
    rw [← card_pair hxy]
    refine card_sdiff_of_subset ?_
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with hz | hz
    · exact hz ▸ hx
    · exact hz ▸ hy
  have _ : ∃ z, (s \ {x, y}) = {z} := card_eq_one.mp <| by lia
  grind only [= card_sdiff_of_subset, = card_sdiff, usr card_sdiff_add_card_inter,
    = insert_eq_of_mem, = subset_iff, usr card_union_add_card_inter, = inter_insert,
    = mem_singleton, = singleton_inter, = union_insert, = union_singleton, = mem_insert,
    = mem_sdiff, = mem_inter]

@[simp]
lemma ne_of_mem_finset_empty_inter {α : Type*} [DecidableEq α]
    {x y : α} (s t : Finset α)
    (h : s ∩ t = ∅) (hx : x ∈ s) (hy : y ∈ t) :
    x ≠ y := by
  intro this
  haveI := mem_inter.mpr ⟨hx, this ▸ hy⟩
  grind

lemma eq_of_mem_of_notMem {α : Type*} [DecidableEq α] {u v x y z : α}
    (hu : u ∈ ({v, x, y} : Finset _)) (hu' : u ∉ ({x, y, z} : Finset _)) : u = v := by
  simp only [mem_insert, mem_singleton, not_or] at hu hu'
  rcases hu with h | h | h
  · exact h
  · exact hu'.1 h |>.elim
  · exact hu'.2.1 h |>.elim

open SimpleGraph
open CaroWeiType

lemma mem_neighborFinset_symm {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} : u ∈ G.neighborFinset v → v ∈ G.neighborFinset u := by
  intro hu
  simp only [mem_neighborFinset] at hu ⊢
  exact hu.symm

lemma ne_of_mem_neighborFinset {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} : u ∈ G.neighborFinset v → u ≠ v := by
  exact fun h ↦ Adj.ne' <| G.mem_neighborFinset .. |>.mp h

lemma ne'_of_mem_neighborFinset {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} : u ∈ G.neighborFinset v → v ≠ u := by
  exact fun h ↦ Adj.ne' <| G.mem_neighborFinset .. |>.mp <| mem_neighborFinset_symm h

lemma Nonempty_if_card_pos {α : Type*} {s : Finset α} (h : 0 < s.card) :
    Nonempty s := by
  exact Nonempty.to_subtype <| card_pos.mp h

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
    · exact sdiff_subset <| hf'₁ k hk
    · exact hxₙ
  · intro k k' hk hk' hneq
    split_ifs with hif hif' hif'
    · simp_all only [ne_eq, not_false_eq_true]
    · simp_all only [ne_eq, mem_sdiff, mem_singleton, not_false_eq_true]
    · intro this
      let contr := this ▸ (mem_sdiff.mp <| hf'₁ _ hif').2
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
  simp_all only [sum_const, nsmul_eq_mul]

lemma ne_symm {α : Type*} {a b : α} (h : ¬a = b) : ¬b = a :=
  fun hba ↦ h hba.symm

theorem deleteIncidenceSet_notAdj {n : ℕ} {G : SimpleGraph (Fin n)} {v w : Fin n} :
    ¬(G.deleteIncidenceSet v).Adj v w := by
  simp only [deleteIncidenceSet, deleteEdges_adj, mem_incidenceSet, and_not_self, not_false_eq_true]

theorem deleteIncidenceSet_degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : ∀ w ∈ G.neighborFinset v, (G.deleteIncidenceSet v).degree w = G.degree w - 1 := by
  intro w hw
  suffices (G.deleteIncidenceSet v).neighborFinset w = G.neighborFinset w \ {v} by
    calc (G.deleteIncidenceSet v).degree w
      _ = ((G.deleteIncidenceSet v).neighborFinset w).card := rfl
      _ = (G.neighborFinset w \ {v}).card := by rw [this]
      _ = (G.neighborFinset w).card - ({v} : Finset _).card := by
        refine card_sdiff_of_subset ?_
        simp only [singleton_subset_iff, mem_neighborFinset]
        exact (G.mem_neighborFinset v w).mp hw |>.symm
  ext x
  constructor
  · intro hx
    simp_all only [mem_neighborFinset, deleteIncidenceSet,
      incidenceSet, deleteEdges_adj, Set.mem_setOf_eq,
      mem_edgeSet, Sym2.mem_iff, not_and, not_or, mem_sdiff,
      mem_singleton, true_and]
    exact ne_symm <| hx.2 hx.1 |>.2
  · intro hx
    simp_all only [mem_neighborFinset, mem_sdiff, mem_singleton,
      deleteIncidenceSet, incidenceSet, deleteEdges_adj,
      Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, true_and, not_or]
    exact ⟨hw.ne, ne_symm hx.2⟩

lemma subset_eq_inter {α : Type*} [DecidableEq α] {s₁ s₂ t : Finset α} (h : t ⊆ (s₁ \ s₂)) :
    t ⊆ s₁ :=
  fun _ hx ↦ mem_sdiff.mp (h hx) |>.1

theorem deleteIncidenceSet_support {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (X : Finset V) (hX : G.support ⊆ X) {v : V} :
    (G.deleteIncidenceSet v).support ⊆ ((X \ {v}) : Finset V) := by
  intro w
  simp only [support, deleteIncidenceSet, incidenceSet, deleteEdges_adj, Prod.mk.eta,
    Set.mem_setOf_eq, not_and, SetRel.mem_dom, mem_edgeSet, Sym2.mem_iff, not_or, coe_sdiff,
    coe_singleton, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff, forall_exists_index,
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
  simp only [closed_neighborFinset_of_Finset, mem_singleton, exists_eq_left,
    mem_filter, mem_univ, true_and, union_singleton, mem_insert,
    mem_neighborFinset]
  if h : w = v then
    simp only [h, SimpleGraph.irrefl, or_false]
  else
    simp only [h, false_or]
    exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

lemma mem_closed_neighborFinset_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V} {F : Finset V} :
    v ∈ G.closed_neighborFinset_of_Finset F
      ↔ v ∈ F ∨ ∃ x ∈ F, v ∈ G.neighborFinset x := by
  simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
  constructor
  · intro hv
    rcases hv with hv | hv
    · exact Or.inl hv
    · obtain ⟨x, hx, hvx⟩ := hv
      exact Or.inr ⟨x, hx, G.mem_neighborFinset .. |>.mpr hvx.symm⟩
  · intro hv
    rcases hv with hv | hv
    · exact Or.inl hv
    · obtain ⟨x, hx, hvx⟩ := hv
      exact Or.inr ⟨x, hx, Adj.symm <| G.mem_neighborFinset .. |>.mp hvx⟩

lemma closed_neighborFinset_pair_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v w : V} :
    G.closed_neighborFinset_of_Finset {v, w}
      = G.closed_neighborFinset_of_Finset {v} ∪ G.closed_neighborFinset_of_Finset {w} := by
  ext u
  simp only [mem_closed_neighborFinset_iff, mem_insert, mem_singleton, mem_neighborFinset,
    exists_eq_or_imp, ↓existsAndEq, true_and, mem_union, exists_eq_left]
  grind

lemma closed_neighborFinset_pair_eq' {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v w : V} :
    G.closed_neighborFinset_of_Finset {v, w}
      = {v, w} ∪ G.neighborFinset v ∪ G.neighborFinset w := by
  ext u
  simp only [mem_closed_neighborFinset_iff, mem_insert, mem_singleton, mem_neighborFinset,
    exists_eq_or_imp, ↓existsAndEq, true_and, insert_union, singleton_union, mem_union]
  grind

lemma closed_neighborFinset_contains_Finset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    s ⊆ G.closed_neighborFinset_of_Finset s := by
  intro u hu
  simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
  exact Or.symm (Or.inr hu)

lemma deleteIncidencesOf_singleton_eq_deleteIncidenceSet
    {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    G.deleteIncidencesOf {v} = G.deleteIncidenceSet v := by
  simp [deleteIncidencesOf, deleteIncidenceSet_le]

lemma deleteIncidenceSet_of_isolated {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {x : Fin n} (hx : G.degree x = 0) :
    (G.deleteIncidencesOf {x}) = G := by
  rw [deleteIncidencesOf_singleton_eq_deleteIncidenceSet]
  ext u v
  simp only [deleteIncidenceSet, incidenceSet, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet,
    Sym2.mem_iff, not_and, not_or, and_iff_left_iff_imp, forall_self_imp]
  intro huv
  have hobj {y z} : G.degree z = 0 → ¬G.Adj y z := by
    intro hdeg hyz
    refine Ne.elim (ne_of_gt <| hyz.symm.degree_pos_left) hdeg
  constructor
  · intro heq; subst heq
    exact hobj hx huv.symm
  · intro heq; subst heq
    exact hobj hx huv

lemma deleteIncidencesOf_notadj {n : ℕ} (G : SimpleGraph (Fin n)) {s : Finset (Fin n)}
    {x y : Fin n} (hx : x ∈ s) :
    ¬(G.deleteIncidencesOf s).Adj x y := by
  simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, inf_adj, iInf_adj,
    deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq,
    Decidable.not_not]
  intro hxy h
  exact false_of_ne (h x |>.1 hx |>.2 hxy |>.1) |>.elim

lemma deleteIncidencesOf_le_mono {n : ℕ} {G₁ G₂ : SimpleGraph (Fin n)} {s : Finset (Fin n)}
    (hle : G₁ ≤ G₂) : G₁.deleteIncidencesOf s ≤ G₂.deleteIncidencesOf s := by
  intro u v
  simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, inf_adj, iInf_adj,
    deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq, and_imp]
  intro h₁uv h hne
  simp only [hle h₁uv, forall_const, true_and, hne, not_false_eq_true, and_true]
  exact fun _ hw ↦  h _ |>.1 hw |>.2 h₁uv

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
        + ∑ x ∈ G.neighborFinset v, f (G.degree x) := Eq.symm (sum_sdiff Nv_subs_X)
      _ = ∑ x ∈ ((X \ G.neighborFinset v) \ {v}), f (G.degree x) + f (G.degree v)
        + ∑ x ∈ G.neighborFinset v, f (G.degree x) := by
          simp only [add_left_inj]
          rw [← sum_singleton (fun x ↦ f (G.degree x)) v]
          refine Eq.symm <| sum_sdiff ?_
          simp only [singleton_subset_iff, mem_sdiff, mem_neighborFinset,
            SimpleGraph.irrefl, not_false_eq_true, and_true]
          refine hX <| G.degree_pos_iff_mem_support v |>.mp (hv ▸ Nat.zero_lt_of_lt hΔ)
      _ = ∑ x ∈ ((X \ G.neighborFinset v) \ {v}), f ((G.deleteIncidenceSet v).degree x)
        + f (G.degree v)
        + ∑ x ∈ G.neighborFinset v, f (G.degree x) := by
          simp only [add_left_inj]
          refine sum_congr rfl ?_
          intro x hx
          refine congrArg (f ∘ card) ?_
          ext w
          constructor
          · intro hw
            simp_all only [gt_iff_lt, ge_iff_le, tsub_le_iff_right, deleteIncidenceSet,
              incidenceSet, mem_sdiff, mem_neighborFinset,
              mem_singleton, deleteEdges_adj, Set.mem_setOf_eq,
              mem_edgeSet, Sym2.mem_iff, ne_eq, not_false_eq_true, Ne.symm, false_or,
              true_and]
            exact fun heq ↦ hx.1.2 (heq ▸ hw.symm)
          · intro hw
            simp_all [deleteIncidenceSet, mem_sdiff]
      _ = ∑ x ∈ ((X \ G.neighborFinset v) \ {v}), f ((G.deleteIncidenceSet v).degree x)
        + f (G.degree v)
        + ∑ x ∈ G.neighborFinset v, f ((G.deleteIncidenceSet v).degree x)
        + ∑ x ∈ G.neighborFinset v, (f (G.degree x) - f ((G.deleteIncidenceSet v).degree x)) := by
          simp only [sum_sub_distrib, add_add_sub_cancel]
      _ = (∑ x ∈ ((X \ G.neighborFinset v) \ {v}), f ((G.deleteIncidenceSet v).degree x)
        + f (G.degree v)
        + ∑ x ∈ G.neighborFinset v, f ((G.deleteIncidenceSet v).degree x))
        + (∑ x ∈ G.neighborFinset v, (f (G.degree x) - f ((G.deleteIncidenceSet v).degree x))) := by
          simp only [sum_sub_distrib, add_add_sub_cancel]
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
            simp only [mem_union, mem_sdiff, mem_neighborFinset,
              mem_singleton]
            refine ⟨?_, by grind⟩
            intro h
            match h with
            | Or.inl h => exact ⟨h.1.1, h.2⟩
            | Or.inr h =>
                exact ⟨hX (G.degree_pos_iff_mem_support x |>.mp h.symm.degree_pos_left), h.ne'⟩
          have cap : ((X \ G.neighborFinset v) \ {v}) ∩ G.neighborFinset v = ∅ := by grind
          let hobj := cup ▸ cap ▸
            @sum_union_inter _ ℝ ((X \ G.neighborFinset v) \ {v}) (G.neighborFinset v)
            _ (fun w ↦ f ((G.deleteIncidenceSet v).degree w)) _
          simp only [sum_empty, add_zero] at hobj
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
      refine @sum_congr _ ℝ _ _ _ _ _ rfl ?_
      intro x hx
      simp only [sub_left_inj]
      exact congrArg _ <| deleteIncidenceSet_degree G v x hx
    _ ≥ ∑ x ∈ G.neighborFinset v, (f (G.maxDegree - 1) - f G.maxDegree) := by
      refine sum_le_sum ?_
      exact fun x hx ↦ hγ (G.degree x) G.maxDegree (hNv x hx) (G.degree_le_maxDegree _)
    _ ≥ f (G.degree v) := by
      simp only [sum_const,
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
      Eq.symm <| sum_sdiff <| singleton_subset_iff.mpr hv
    _ = ∑ x ∈ X \ {v}, f (G.degree x) + f (G.degree v) := by simp only [sum_singleton]
    _ ≤ ∑ x ∈ X \ {v}, f ((G.deleteIncidenceSet v).degree x) + f (G.degree v) := by
      simp only [add_le_add_iff_right]
      refine sum_le_sum ?_
      intro w hw
      refine hf _ _ ?_
      exact degree_le_of_le <| G.deleteIncidenceSet_le v

theorem bound_of_completeGraph (f : ℕ → ℝ) {n : ℕ}
    [DecidableRel (completeGraph (Fin (n + 1))).Adj] :
    ∑ v, f ((completeGraph (Fin (n + 1))).degree v) = (n + 1) * f n := by
  calc ∑ v, f ((completeGraph (Fin (n + 1))).degree v)
    _ = ∑ _ : Fin (n + 1), f n := by
        refine sum_congr rfl (fun x _ ↦ congrArg _ ?_)
        simp only [completeGraph_eq_top, degree, neighborFinset, neighborSet, top_adj]
        suffices {w | x ≠ w} = Set.univ \ {x} by simp [this, card_sdiff]
        ext w
        constructor <;> exact fun hw ↦ by grind
    _ = (n + 1) * f n := by simp only [sum_const, card_univ, Fintype.card_fin,
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
      refine le_trans (card_le_card <| subset_univ s) ?_
      simp only [card_univ, Fintype.card_fin, le_refl]

lemma induced_degree_eq {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (v : V) (hv : v ∈ s) [Fintype (G.neighborSet v)] :
    (G.induce s).degree ⟨v, hv⟩ = (G.neighborFinset v ∩ s).card := by
  rw [degree]
  refine Set.BijOn.finsetCard_eq ?_ ⟨?_, ?_, ?_⟩
  · exact fun x ↦ x.1
  · intro x hx
    simp only [SetLike.coe_sort_coe, coe_neighborFinset, mem_neighborSet, comap_adj,
      coe_inter, Set.mem_inter_iff, Subtype.coe_prop, and_true] at hx ⊢
    exact hx
  · intro x hx y hy hne
    simp_all
  · intro y hy
    simp only [coe_inter, coe_neighborFinset, Set.mem_inter_iff, mem_neighborSet,
      SetLike.mem_coe, SetLike.coe_sort_coe, Set.mem_image, comap_adj, Subtype.exists,
      exists_and_right, exists_eq_right] at hy ⊢
    exact ⟨hy.2, hy.1⟩

namespace SimpleGraph

@[simp]
lemma ne_of_deg0_of_adj {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v w : V} (h : G.degree u = 0) (hvw : G.Adj v w) : u ≠ v := by
  intro heq; subst heq
  exact (ne_of_lt hvw.degree_pos_left) h.symm

@[simp]
lemma ne_of_deg0_of_adj' {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v w : V} (h : G.degree u = 0) (hvw : G.Adj w v) : u ≠ v := by
  exact ne_of_deg0_of_adj h hvw.symm

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
  ext y
  constructor
  · intro hy
    simp_all only [mem_neighborFinset, mem_inter, true_and]
    exact hX <| G.mem_support.mpr ⟨_, hy.symm⟩
  · exact fun hy ↦ mem_inter.mp hy |>.1

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
    G.degree v = (X.image fun x ↦ G.degree x).min' (image_nonempty.mpr hX)
      ↔ ∀ w ∈ X, G.degree v ≤ G.degree w := by
  constructor
  · intro hdegv w hw
    exact hdegv ▸ min'_le _ _ (mem_image.mpr ⟨w, hw, rfl⟩)
  · intro h
    refine Nat.le_antisymm ?_ ?_
    · refine le_min'_iff _ (image_nonempty.mpr hX) |>.mpr ?_
      intro y
      simp only [mem_image, forall_exists_index, and_imp]
      intro z hz hdz
      exact hdz ▸ h _ hz
    · exact min'_le _ _ (mem_image_of_mem _ hv)

lemma neighborFinset_subset_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {v : Fin n} : G.neighborFinset v ⊆ G.support.toFinset := by
  intro w hw
  refine Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨v, Adj.symm ?_⟩
  exact G.mem_neighborFinset .. |>.mp hw

lemma neighborFinset_eq_deg2' {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {v : Fin n}
    (f : Fin n → ℝ) :
    G.degree v = 2 → ∃ u w, G.neighborFinset v = {u, w} ∧ f w ≤ f u := by
  intro h
  obtain ⟨u, w, _, huw⟩ := card_eq_two.mp h
  obtain ⟨u', w', heq, hle⟩ := sorted_pair f u w
  refine ⟨w', u', ?_, hle⟩
  rw [huw, ← heq]
  exact pair_comm ..

lemma neighborFinset_eq_deg3' {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {v : Fin n}
    (f : Fin n → ℝ) :
    G.degree v = 3 → ∃ x y z, G.neighborFinset v = {x, y, z} ∧ f z ≤ f y ∧ f y ≤ f x := by
  intro h
  obtain ⟨σ, hσ, hinc⟩ := sorted_finset 3 h f
  have : Finset.image σ univ = {σ 2, σ 1, σ 0} := by
    ext x
    simp only [mem_image, mem_univ, true_and, Fin.isValue, mem_insert, mem_singleton]
    constructor
    · intro ⟨i, hi⟩
      suffices i = 0 ∨ i = 1 ∨ i = 2 by grind
      grind
    · grind
  refine ⟨σ 2, σ 1, σ 0, hσ.symm.trans this, by grind⟩

lemma notMem_of_degree_in_eq_zero_of_adj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {s : Finset (Fin n)} {v w : Fin n} (hdv : G.degree_in s v = 0) (hvw : G.Adj v w) :
    w ∉ s := by
  intro hw
  suffices 1 ≤ 0 by grind
  rw [← hdv, ← card_singleton w]
  refine card_le_card ?_
  simp [hvw, hw]

lemma degree_in_le_degree {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u : Fin n} {s : Finset (Fin n)} :
    G.degree_in s u ≤ G.degree u := by
  refine card_le_card inter_subset_left

lemma degree_in_mono {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u : Fin n} {s t : Finset (Fin n)} (h : s ⊆ t) :
    G.degree_in s u ≤ G.degree_in t u := by
  exact card_le_card <| inter_subset_inter (subset_refl _) h

lemma degree_in_union_self {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u : Fin n} {s : Finset (Fin n)} :
    G.degree_in s u = G.degree_in (s ∪ {u}) u := by
  refine congrArg Finset.card ?_
  ext v
  simp only [mem_inter, mem_neighborFinset, union_singleton, SimpleGraph.irrefl, not_false_eq_true,
    inter_insert_of_notMem]

lemma degree_in_union_le {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u : Fin n} {s t : Finset (Fin n)} :
    G.degree_in (s ∪ t) u ≤ G.degree_in s u + #t := by
  simp_rw [degree_in]
  suffices G.neighborFinset u ∩ (s ∪ t) ⊆ (G.neighborFinset u ∩ s) ∪ t by
    exact le_trans (card_le_card this) <| card_union_le ..
  grind

lemma degree_in_union_eq {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u : Fin n} {s t : Finset (Fin n)} (ht : t ∩ G.neighborFinset u = ∅) :
    G.degree_in (s ∪ t) u = G.degree_in s u := by
  refine congrArg Finset.card ?_
  ext w
  simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff, or_iff_left_iff_imp]
  intro huw hwt
  have h : w ∈ (∅ : Finset _) := ht ▸ mem_inter.mpr ⟨hwt, G.mem_neighborFinset .. |>.mpr huw⟩
  simp at h

lemma degree_in_deleteIncidenceSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v : Fin n} (s : Finset (Fin n)) (hu : u ∉ s) (hu' : u ≠ v) :
    (G.deleteIncidenceSet u).degree_in s v = G.degree_in s v := by
  simp only [degree_in]
  refine congrArg card ?_
  ext w
  simp only [deleteIncidenceSet, incidenceSet, mem_inter, mem_neighborFinset, deleteEdges_adj,
    Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, hu', false_or, not_and, and_congr_left_iff,
    and_iff_left_iff_imp, forall_self_imp]
  intro hw hvw
  exact fun heq ↦ hu (heq ▸ hw)

lemma degree_in_deleteIncidenceSet' {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v : Fin n} (s : Finset (Fin n)) (hu : u ∉ s) (huv : G.Adj u v) :
    G.degree_in (s ∪ {u}) v ≤ (G.deleteIncidenceSet u).degree_in s v + 1 := by
  unfold degree_in
  calc #(G.neighborFinset v ∩ (s ∪ {u}))
    _ ≤ #(((G.deleteIncidenceSet u).neighborFinset v ∩ (s ∪ {u})) ∪ {u}) := by
      refine card_le_card ?_
      intro w
      simp only [union_singleton, mem_inter, mem_neighborFinset, mem_insert, deleteIncidenceSet,
        incidenceSet, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, or_true,
        and_true, and_not_self, not_false_eq_true, inter_insert_of_notMem, not_and, not_or, and_imp]
      intro hvw hw
      rcases hw with hw | hw
      · simp only [hw, not_true_eq_false, and_false, imp_false, and_not_self, false_and, or_false]
      · refine Or.inr ⟨⟨hvw, ?_⟩, hw⟩
        simp only [hvw, huv.ne, not_false_eq_true, true_and, forall_const]
        exact fun heq ↦ hu (heq ▸ hw)
    _ ≤ #((G.deleteIncidenceSet u).neighborFinset v ∩ (s ∪ {u})) + #({u} : Finset _) := by
      exact card_union_le ..
    _ = #((G.deleteIncidenceSet u).neighborFinset v ∩ s) + #({u} : Finset _) := by
      simp only [union_singleton, card_singleton, Nat.add_right_cancel_iff]
      refine congrArg card ?_
      ext w
      simp [deleteIncidenceSet, incidenceSet]
    _ = #((G.deleteIncidenceSet u).neighborFinset v ∩ s) + 1 := by
      simp

lemma degree_in_neighbor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {u v : Fin n}
    (s : Finset (Fin n)) (huv : G.Adj u v) (hv : v ∉ s) :
    G.degree_in (s ∪ {v}) u = G.degree_in s u + 1 := by
  simp only [degree_in]
  suffices G.neighborFinset u ∩ (s ∪ {v}) = (G.neighborFinset u ∩ s) ∪ {v} by
    rw [this]
    grind
  ext w
  simp only [union_singleton, mem_inter, mem_neighborFinset, mem_insert]
  constructor
  · intro ⟨huw, hw⟩
    rcases hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr ⟨huw, hw⟩
  · intro hw
    rcases hw with hw | ⟨hw, hws⟩
    · refine ⟨hw ▸ huv, Or.inl hw⟩
    · refine ⟨hw, Or.inr hws⟩

lemma one_le_degree_of_adj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {u v : Fin n}
    (huv : G.Adj u v) : 1 ≤ G.degree u := by
  rw [← card_singleton v]
  refine card_le_card ?_
  simp only [singleton_subset_iff, mem_neighborFinset, huv]

lemma one_le_degree_of_adj' {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {u v : Fin n}
    (huv : G.Adj v u) : 1 ≤ G.degree u := by
  exact one_le_degree_of_adj huv.symm

lemma one_le_degree_of_mem_neighborFinset {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (huv : v ∈ G.neighborFinset u) : 1 ≤ G.degree u := by
  rw [← card_singleton v]
  refine card_le_card ?_
  simp only [singleton_subset_iff, huv]

lemma one_le_degree_of_mem_neighborFinset' {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (huv : u ∈ G.neighborFinset v) : 1 ≤ G.degree u := by
  exact one_le_degree_of_mem_neighborFinset <| mem_neighborFinset_symm huv

lemma one_le_degree_of_walk_begin {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hunev : u ≠ v) (w : G.Walk u v) : 1 ≤ G.degree u := by
  match w with
  | Walk.nil => grind only
  | Walk.cons h _ => exact one_le_degree_of_adj h

lemma one_le_degree_of_walk_end {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hunev : u ≠ v) (w : G.Walk u v) : 1 ≤ G.degree v := by
  exact one_le_degree_of_walk_begin hunev.symm w.reverse

lemma card_connectedComponent_at_least_deg_plus_one {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {v : Fin n} [Fintype (G.connectedComponentMk v)] :
    G.degree v + 1 ≤ #(G.connectedComponentMk v).supp.toFinset := by
  suffices G.neighborFinset v ∪ {v} ⊆ (G.connectedComponentMk v).supp.toFinset by
    refine le_of_eq_of_le ?_ (card_le_card this)
    rw [← card_singleton v, degree]
    refine Eq.symm <| card_union_of_disjoint ?_
    simp only [disjoint_singleton_right, mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true]
  intro x hx
  simp only [union_singleton, mem_insert, mem_neighborFinset] at hx
  rcases hx with hx | hx
  · simp only [hx, Set.mem_toFinset, ConnectedComponent.mem_supp_iff]
  · simp only [Set.mem_toFinset, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    exact hx.symm.reachable

end SimpleGraph
