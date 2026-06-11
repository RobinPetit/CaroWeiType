import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

import CWType.SimpleGraph.CaroWeiType.Basic

open Finset

lemma add_congr {a b c d : ℝ} (h₁ : a = c) (h₂ : b = d) :
    a + b = c + d := by
  have hobj1 := add_right_inj a |>.mpr h₂
  have hobj2 := add_left_inj d |>.mpr h₁
  exact hobj1.trans hobj2

lemma sum_const' {ι : Type*} {f : ι → ℝ} {c : ℝ} {X : Finset ι} (h : ∀ x ∈ X, f x = c) :
    ∑ x ∈ X, f x = X.card * c := by
  simp_all only [sum_const, nsmul_eq_mul]

private lemma inv_mul_prod_eq {x y : ℝ} (hx : x ≠ 0) : x⁻¹ * (y * x) = y := by
  ring_nf
  exact (mul_inv_cancel₀ <| hx) ▸ one_mul y

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
      have h' : (d : ℝ)⁻¹ * (d : ℝ) = 1 := inv_mul_cancel₀ hdR_pos
      simp only [h', one_mul]
    _ = 1 := by
      suffices (d + 1 : ℝ)⁻¹ * (d * (d + 1)) = d by
        rw [this, ← add_comm]
        exact add_sub_cancel_right ..
      refine inv_mul_prod_eq <| Nat.cast_add_one_ne_zero d

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

lemma cast_five : ((5 : ℕ) : ℝ) = (5 : ℝ) := rfl

lemma le_add_one {x : ℝ} : x ≤ x + 1 :=
  le_of_lt <| lt_add_one _

lemma one_le_add_one_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 1 ≤ x + 1 :=
  le_add_of_nonneg_left hx

lemma one_le_add_one_of_nat {n : ℕ} : 1 ≤ (n + 1 : ℝ) :=
  one_le_add_one_of_nonneg <| Nat.cast_nonneg' _

lemma add_one_pos {n : ℕ} : 0 < n + (1 : ℝ) := by
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_pos]
  exact Nat.zero_lt_succ _

lemma two_le_add_one_add_one {n : ℕ} : 2 ≤ n + (1 : ℝ) + 1 := by
  rw [← Nat.cast_two, ← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.cast_le]
  simp only [le_add_iff_nonneg_left, zero_le]

lemma add_one_add_one_pos {n : ℕ} : 0 < n + (1 : ℝ) + 1 :=
  lt_of_lt_of_le zero_lt_two two_le_add_one_add_one

lemma add_one_nonneg {n : ℕ} : 0 ≤ n + (1 : ℝ) :=
  le_of_lt add_one_pos

lemma add_one_add_one_nonneg {n : ℕ} : 0 ≤ n + (1 : ℝ) + 1 :=
  le_of_lt add_one_add_one_pos

lemma add_two_pos {n : ℕ} : 0 < n + (2 : ℝ) := by
  rw [← one_add_one_eq_two, ← add_assoc]
  exact add_one_add_one_pos

lemma one_add_pos {n : ℕ} : 0 < (1 : ℝ) + n := by
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_pos]
  exact Nat.pos_of_neZero _

lemma p_and_p_implies {p q : Prop} : (p → (p ∧ q)) ↔ (p → q) :=
  ⟨fun h hp ↦ h hp |>.2, fun hpq hp ↦ ⟨hp, hpq hp⟩⟩

lemma p_imp_q_imp_p {p q : Prop} : p → q → p :=
  fun h _ ↦ h

lemma not_p_of_p_imp_false {p : Prop} : (p → False) → ¬p :=
  fun h hp ↦ h hp

lemma cancel_imp_of_and {p q : Prop} : (p ∧ (p → q)) ↔ (p ∧ q) :=
  ⟨fun ⟨hp, hpq⟩ ↦ ⟨hp, hpq hp⟩, fun ⟨hp, hq⟩ ↦ ⟨hp, fun _ ↦ hq⟩⟩

@[simp]
lemma and_or_2 {p₁ p₂ q : Prop} : (p₁ ∧ q) ∨ (p₂ ∧ q) ↔ (p₁ ∨ p₂) ∧ q := by
  constructor
  · intro h
    rcases h with h | h <;> simp only [h, true_or, or_true, and_true]
  · intro ⟨hp, hq⟩
    rcases hp with hp | hp <;> simp only [hp, true_and, hq, true_or, or_true]

@[simp]
lemma and_or_3 {p₁ p₂ p₃ q : Prop} : (p₁ ∧ q) ∨ (p₂ ∧ q) ∨ (p₃ ∧ q) ↔ (p₁ ∨ p₂ ∨ p₃) ∧ q := by
  constructor
  · intro h
    rcases h with h | h | h <;> simp only [h, true_or, or_true, and_self]
  · intro ⟨hp, hq⟩
    rcases hp with h | h | h <;> simp only [hq, and_true, h, and_self, true_or, or_true]

lemma not_and_iff_not_or {p q : Prop} : ¬(p ∧ q) ↔ (¬p) ∨ (¬q) := by
  constructor
  · intro h
    simp only [not_and] at h
    if hp : p then
      exact Or.inr <| h hp
    else
      exact Or.inl hp
  · intro h
    rcases h with h | h <;> simp only [h, false_and, and_false, not_false_eq_true]

variable {α : Type*}

lemma le_trans₃ [Preorder α] {a b c d : α} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    a ≤ d :=
  le_trans (le_trans hab hbc) hcd

lemma eq_or_eq_of_eq_Sym2 {a b x y : α} (h : s(a, b) = s(x, y)) :
    a = x ∨ a = y := by grind

lemma eq_or_eq_of_eq_Sym2' {a b x y : α} (h : s(a, b) = s(x, y)) :
    b = x ∨ b = y :=
  eq_or_eq_of_eq_Sym2 (Sym2.eq_swap ▸ h)

lemma eq_empty_of_subset_empty {s : Finset α} (h : s ⊆ ∅) :
    s = ∅ :=
  subset_antisymm h (empty_subset _)

lemma eq_of_subset_and_eq_card {A B : Finset α} (h : A ⊆ B) (h' : #A = #B) :
    A = B := by
  classical
  refine subset_antisymm h <| sdiff_eq_empty_iff_subset.mp <| card_eq_zero.mp ?_
  rw [card_sdiff, inter_eq_left.mpr h]
  exact (Nat.eq_sub_of_add_eq' h').symm

lemma eq_of_subset_and_ge_card {A B : Finset α} (h : A ⊆ B) (h' : #A ≥ #B) :
    A = B :=
  eq_of_subset_and_eq_card h (le_antisymm (card_le_card h) h')

lemma Nonempty_if_card_pos {s : Finset α} (h : 0 < s.card) :
    Nonempty s := by
  exact Nonempty.to_subtype <| card_pos.mp h

lemma Nonempty_if_card_pos' {s : Finset α} (h : 0 < s.card) :
    Nonempty α := by
  exact Nonempty.intro (Classical.choice <| Nonempty_if_card_pos h).1

theorem Finset_unique_elems [Nonempty α] (s : Finset α) :
    ∃ f : ℕ → α,
      (∀ (k : ℕ), k < s.card → f k ∈ s)
        ∧ (∀ (k k' : ℕ), k < s.card → k' < s.card → k ≠ k' → f k ≠ f k') := by
  classical
  induction hcard : s.card generalizing s with
  | zero =>
      exact ⟨@Classical.choice _ (by infer_instance),
        by simp only [not_lt_zero, IsEmpty.forall_iff, implies_true, ne_eq, and_self]⟩
  | succ n ih => ?_
  have hsNonempty : Nonempty s := Nonempty_if_card_pos <| Nat.lt_of_sub_eq_succ hcard
  obtain ⟨xₙ, hxₙ⟩ := Classical.choice hsNonempty
  obtain ⟨f', ⟨hf'₁, hf'₂⟩⟩ := by
    refine ih (s \ {xₙ}) ?_
    simp only [card_sdiff, singleton_inter_of_mem, card_singleton,
      add_tsub_cancel_right, hcard, hxₙ]
  use fun k ↦ if k < n then f' k else xₙ
  constructor
  · intro k _
    split_ifs with hk
    · exact sdiff_subset <| hf'₁ k hk
    · exact hxₙ
  · intro k k' hk hk' hneq
    split_ifs with hif hif' hif'
    · exact hf'₂ _ _ hif hif' hneq
    · exact notMem_singleton.mp <| mem_sdiff.mp (hf'₁ _ hif) |>.2
    · intro this
      let contr := this ▸ (mem_sdiff.mp <| hf'₁ _ hif').2
      simp only [mem_singleton, not_true_eq_false] at contr
    · have hkn : k = n := Nat.eq_of_lt_succ_of_not_lt hk hif
      have hk'n : k' = n := Nat.eq_of_lt_succ_of_not_lt hk' hif'
      exact hneq (hkn.trans hk'n.symm) |>.elim

theorem Finset_get_one (s : Finset α) (h : 1 ≤ s.card) :
    ∃ x, x ∈ s := by
  have _ : Nonempty α := Nonempty_if_card_pos' h
  obtain ⟨f, ⟨hf, _⟩⟩ := Finset_unique_elems s
  exact ⟨f 0, hf _ h⟩

theorem Finset_get_two (s : Finset α) (h : 2 ≤ s.card) :
    ∃ x y, x ∈ s ∧ y ∈ s ∧ x ≠ y := by
  have _ : Nonempty α := Nonempty_if_card_pos' (Nat.zero_lt_of_lt h)
  obtain ⟨f, ⟨hf₁, hf₂⟩⟩ := Finset_unique_elems s
  refine ⟨f 0, f 1, ?_, ?_, ?_⟩
  · exact hf₁ _ (Nat.zero_lt_of_lt h)
  · exact hf₁ _ (Nat.lt_of_succ_le h)
  · exact hf₂ 0 1 (Nat.zero_lt_of_lt h) (Nat.lt_of_succ_le h) zero_ne_one

theorem Finset_singleton_unique {s : Finset α} (hs : #s = 1) :
    ∃! x, x ∈ s := by
  classical
  refine existsUnique_of_exists_of_unique ?_ ?_
  · exact Finset_get_one s (le_of_eq <| hs.symm)
  · intro x y hxs hys
    by_contra
    suffices 2 ≤ 1 by linarith
    rw [← hs, ← card_pair this]
    refine card_le_card ?_
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with hx | hy
    · exact hx ▸ hxs
    · exact hy ▸ hys

theorem Finset_two_le_card_iff (s : Finset α) :
    2 ≤ s.card ↔ ∃ x y, x ∈ s ∧ y ∈ s ∧ x ≠ y := by
  classical
  constructor
  · exact Finset_get_two s
  · intro ⟨x, y, hxs, hys, hxy⟩
    rw [← card_pair hxy]
    exact card_le_card (by grind)

theorem Finset_card_eq_two_iff [DecidableEq α] (s : Finset α) (hs : #s = 2) :
    ∃ x y, x ≠ y ∧ s = {x, y} := by
  obtain ⟨x, y, hx, hy, hne⟩ := Finset_two_le_card_iff _ |>.mp (le_of_eq hs.symm)
  refine ⟨x, y, hne, ?_⟩
  refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
  · intro z hz
    simp only [mem_insert, mem_singleton] at hz
    exact hz.elim (· ▸ hx) (· ▸ hy)
  · rw [card_pair hne, hs]

theorem Finset_get_other {s : Finset α} (hs : 2 ≤ #s) (x : α) :
    ∃ y ∈ s, x ≠ y := by
  obtain ⟨z₁, z₂, hz₁, hz₂, hne⟩ := Finset_get_two _ hs
  if heq : z₁ = x then
    exact ⟨z₂, hz₂, heq ▸ hne⟩
  else
    exact ⟨z₁, hz₁, Ne.symm heq⟩

theorem Finset_three_le_card_iff (s : Finset α) :
    3 ≤ s.card ↔ ∃ x y z, x ∈ s ∧ y ∈ s ∧ z ∈ s ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  classical
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := Finset_get_one s (Nat.one_le_of_lt hs)
    obtain ⟨y, z, hy, hz, hyz⟩ := by
      refine Finset_two_le_card_iff (s \ {x}) |>.mp ?_
      rw [card_sdiff, singleton_inter_of_mem hx, card_singleton]
      exact Nat.le_sub_one_of_lt hs
    refine ⟨x, y, z, hx, mem_sdiff.mp hy |>.1, mem_sdiff.mp hz |>.1, ?_, ?_, hyz⟩
    · exact Ne.symm <| notMem_singleton.mp <| mem_sdiff.mp hy |>.2
    · exact Ne.symm <| notMem_singleton.mp <| mem_sdiff.mp hz |>.2
  · intro ⟨x, y, z, hxs, hys, hzs, hxy, hxz, hyz⟩
    suffices {x, y, z} ⊆ s by exact le_of_eq_of_le (by grind) (card_le_card this)
    grind

theorem Finset_get_other_other {s : Finset α} (hs : 3 ≤ #s) (x y : α) :
    ∃ z ∈ s, x ≠ z ∧ y ≠ z := by
  classical
  obtain ⟨z₁, z₂, z₃, hz₁, hz₂, hz₃, hne₁₂, hne₁₃, hne₂₃⟩ := Finset_three_le_card_iff _ |>.mp hs
  have : #({z₁, z₂, z₃} : Finset _) = 3 := by grind
  obtain ⟨z, hz⟩ : ({z₁, z₂, z₃} : Finset _) \ {x, y} |>.Nonempty :=
    sdiff_nonempty_of_card_lt_card <| lt_of_le_of_lt card_le_two <| this ▸ Nat.lt_add_one 2
  refine ⟨z, ?_, ?_⟩ <;> grind

variable [DecidableEq α]

lemma ne_of_ne_congr {α β : Type*} (f : α → β) {x y : α} (h : f x ≠ f y) : x ≠ y :=
  fun heq ↦ h (congrArg f heq)

lemma pair_nonempty {x y : α} : ({x, y} : Finset _).Nonempty :=
  insert_nonempty ..

lemma eq_sdiff_of_empty_inter {s t : Finset α} (hcap : t ∩ s = ∅) :
    (s = s \ t) := by
  ext
  simp only [mem_sdiff, iff_self_and]
  exact fun hus hut ↦ notMem_empty _ <| hcap ▸ mem_inter.mpr ⟨hut, hus⟩

@[simp]
lemma singleton_inter_eq_empty_iff {s : Finset α} {x : α} :
    ({x} ∩ s) = ∅ ↔ x ∉ s := by
  constructor
  · exact fun h hxs ↦ notMem_empty _ <| h ▸ mem_inter.mpr ⟨mem_singleton.mpr rfl, hxs⟩
  · intro hx
    ext
    simp only [hx, not_false_eq_true, singleton_inter_of_notMem, notMem_empty]

@[simp]
lemma inter_singleton_eq_empty_iff {s : Finset α} {x : α} :
    (s ∩ {x}) = ∅ ↔ x ∉ s := by
  exact (inter_comm s {x}) ▸ singleton_inter_eq_empty_iff

@[simp]
lemma singleton_inter_ne_empty_iff {s : Finset α} {x : α} :
    ({x} ∩ s) ≠ ∅ ↔ x ∈ s := by
  refine (not_iff_not.mpr singleton_inter_eq_empty_iff).trans ?_
  simp only [Decidable.not_not]

@[simp]
lemma inter_singleton_ne_empty_iff {s : Finset α} {x : α} :
    (s ∩ {x}) ≠ ∅ ↔ x ∈ s := by
  refine (not_iff_not.mpr inter_singleton_eq_empty_iff).trans ?_
  simp only [Decidable.not_not]

@[simp]
lemma disjoint_of_sdiff {X Y Z : Finset α} (h : X ⊆ Y \ Z) :
    X ∩ Z = ∅ := by
  ext x
  simp only [mem_inter, notMem_empty, iff_false, not_and]
  exact fun hx ↦ mem_sdiff.mp (h hx) |>.2

lemma disjoint_of_sdiff' {X Y Z Z' : Finset α} (h : X ⊆ Y \ Z) (h' : Z' ⊆ Z) :
    X ∩ Z' = ∅ := by
  ext x
  simp only [mem_inter, notMem_empty, iff_false, not_and]
  exact fun hx ↦ mt (h' ·) (mem_sdiff.mp (h hx) |>.2)

lemma notMem_of_empty_inter_of_mem {s t : Finset α} {x : α}
    (h : s ∩ t = ∅) (hxt : x ∈ t) : x ∉ s :=
  fun hxs ↦ notMem_empty x (h ▸ mem_inter.mpr ⟨hxs, hxt⟩)

lemma notMem_of_empty_inter_of_mem' {s t : Finset α} {x : α}
    (h : s ∩ t = ∅) (hxs : x ∈ s) : x ∉ t :=
  notMem_of_empty_inter_of_mem (inter_comm s t ▸ h) hxs

lemma subset_eq_inter {s₁ s₂ t : Finset α} (h : t ⊆ (s₁ \ s₂)) :
    t ⊆ s₁ :=
  fun _ hx ↦ mem_sdiff.mp (h hx) |>.1

lemma sdiff_subset_of_subset {s₁ s₂ t : Finset α} (h : s₁ ⊆ t) :
    (s₁ \ s₂) ⊆ t :=
  fun _ hx ↦ h <| mem_sdiff.mp hx |>.1

lemma union_subset {s₁ s₂ t : Finset α} (ht : t ⊆ (s₁ \ s₂)) (hs₁ : s₂ ⊆ s₁) :
    (t ∪ s₂) ⊆ s₁ :=
  fun _ hx ↦ (mem_union.mp hx).elim (fun hx ↦ mem_sdiff.mp (ht hx) |>.1) (hs₁ ·)

lemma mem_pair {x y : α} : x ∈ ({x, y} : Finset _) :=
  mem_insert_self ..

lemma mem_pair' {x y : α} : x ∈ ({y, x} : Finset _) :=
  pair_comm x y ▸ mem_pair

@[simp]
lemma mem_of_singleton_inter_ne_emty {s : Finset α} {x : α}
    (h : {x} ∩ s ≠ ∅) : x ∈ s := by
  obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.mpr h
  simp only [mem_inter, mem_singleton] at hy
  exact hy.1 ▸ hy.2

lemma notMem_of_mem_of_empty_inter {s t : Finset α} {x : α}
    (hxs : x ∈ s) (hst : s ∩ t = ∅) :
    x ∉ t := by
  intro hxt
  suffices x ∈ (∅ : Finset _) by exact (List.mem_nil_iff x).mp this
  exact hst ▸ mem_inter.mpr ⟨hxs, hxt⟩

lemma triplet_subset_of_mem_of_mem_of_mem {x y z : α} {s : Finset α}
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) : {x, y, z} ⊆ s := by
  intro u hu
  simp only [mem_insert, mem_singleton] at hu
  rcases hu with hu | hu | hu
  · exact hu ▸ hx
  · exact hu ▸ hy
  · exact hu ▸ hz

lemma pair_subset_of_mem_of_mem {x y : α} {s : Finset α} (hx : x ∈ s) (hy : y ∈ s) :
    {x, y} ⊆ s := by
  refine subset_of_eq_of_subset ?_ <| triplet_subset_of_mem_of_mem_of_mem hx hx hy
  simp only [mem_insert, mem_singleton, true_or, insert_eq_of_mem]

lemma eq_of_mem_of_mem_of_singleton {α : Type*} {s : Finset α} (hs : #s = 1) {x y : α}
    (hx : x ∈ s) (hy : y ∈ s) : x = y := by
  classical
  by_contra
  have : 2 ≤ 1 := by
    rw [← hs, ← card_pair this]
    exact card_le_card <| pair_subset_of_mem_of_mem hx hy
  linarith

lemma card_triplet {x y z : α} (h : x ≠ y) (hz : z ∉ ({x, y} : Finset _)) :
    #{x, y, z} = 3 := by
  have H : ({z, x, y} : Finset _) = {x, y, z} := by grind
  rw [← H, card_insert_of_notMem hz, card_insert_of_notMem (notMem_singleton.mpr h), card_singleton]

lemma card_triplet' {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    #{x, y, z} = 3 :=
  card_triplet hxy (by grind)

lemma card_quadruplet {a b c d : α} (ha : a ∉ ({b, c, d} : Finset _))
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    #{a, b, c, d} = 4 := by
  rw [card_insert_of_notMem ha, card_triplet' hbc hbd hcd]

lemma triplet_eq (x y z : α) : ({x, y, z} : Finset α) = {x, z, y} := by
  grind

lemma one_lt_card_iff_exists_a_b {s : Finset α} :
    1 < #s ↔ ∃ x y, {x, y} ⊆ s ∧ x ≠ y := by
  constructor
  · intro hs
    obtain ⟨x, y, hx, hy, hxy⟩ := Finset_get_two _ hs
    exact ⟨x, y, by grind, hxy⟩
  · intro ⟨x, y, hxy, hxney⟩
    exact lt_of_lt_of_le Nat.one_lt_two ((card_pair hxney) ▸ card_le_card hxy)

lemma pair_eq {a b x y : α} (hab : a ≠ b) (h : ({a, b} : Finset _) = {x, y}) :
    a = x ∧ b = y ∨ a = y ∧ b = x := by
  if hax : a = x then
    subst hax
    refine Or.inl ⟨rfl, ?_⟩
    have hb : b ∈ ({a, y} : Finset _) := by simp only [← h, mem_insert, mem_singleton, or_true]
    simp only [mem_insert, mem_singleton, hab.symm, false_or] at hb
    exact hb
  else
    have ha : a ∈ ({x, y} : Finset _) := by simp only [← h, mem_insert, mem_singleton, true_or]
    have hay : a = y := by
      simp only [mem_insert, mem_singleton, hax, false_or] at ha
      exact ha
    refine Or.inr ⟨hay, ?_⟩
    have hb : b ∈ ({x, y} : Finset _) := by simp only [← h, mem_insert, mem_singleton, or_true]
    simp only [mem_insert, mem_singleton, Ne.symm <| hay ▸ hab, or_false] at hb
    exact hb

lemma sorted_pair {β : Type*} [LinearOrder β] (f : α → β) (x y : α) :
    ∃ a b, ({a, b} : Finset _) = {x, y} ∧ f a ≤ f b :=
  if h : f x ≤ f y then
    ⟨x, y, rfl, h⟩
  else
    ⟨y, x, pair_comm .., le_of_not_ge h⟩

private lemma sorted_finset {β : Type*} [LinearOrder β] {s : Finset α} (k : ℕ) [NeZero k]
    (hs : #s = k) (f : α → β) :
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

lemma sorted_triplet {β : Type*} [LinearOrder β] (f : α → β) (x y z : α) :
    ∃ a b c, ({a, b, c} : Finset _) = {x, y, z} ∧ f a ≤ f b ∧ f b ≤ f c := by
  if h1 : x = y ∧ y = z then
    exact ⟨x, x, x, by grind, le_refl _, le_refl _⟩
  else if h2 : x = y ∨ y = z ∨ x = z then
    rcases h2 with hxy | hyz | hxz
    · obtain ⟨a, b, heq, hfab⟩ := sorted_pair f y z
      exact ⟨a, a, b, by grind, le_refl _, hfab⟩
    · obtain ⟨a, b, heq, hfab⟩ := sorted_pair f x y
      exact ⟨a, a, b, by grind, le_refl _, hfab⟩
    · obtain ⟨a, b, heq, hfab⟩ := sorted_pair f y z
      exact ⟨a, a, b, by grind, le_refl _, hfab⟩
  else
    obtain ⟨hxney, hynez⟩ : x ≠ y ∧ y ≠ z := by grind
    have hcard : #{x, y, z} = 3 := by grind
    obtain ⟨σ, hσ, hf⟩ := sorted_finset 3 hcard f
    refine ⟨σ 0, σ 1, σ 2, ?_, hf 0 1 <| Fin.zero_le 1, hf 1 2 <| ?_⟩
    · rw [← hσ]
      ext u
      simp only [Fin.isValue, mem_insert, mem_singleton, mem_image, inter_univ, ne_eq,
        singleton_ne_empty, not_false_eq_true, mem_of_singleton_inter_ne_emty, true_and]
      constructor
      · grind
      · intro ⟨i, hi⟩
        grind [i.isLt]
    · exact Fin.coe_sub_iff_le.mp rfl

lemma pairwise_ne_of_triplet {x y z : α} (h : #({x, y, z} : Finset _) = 3) :
    x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  grind only [= insert_eq_of_mem, = card_insert_of_notMem, = mem_insert, = mem_singleton,
    = card_singleton]

lemma triplet_of_mem_of_mem_of_ne {x y : α} {s : Finset α}
    (hs : #s = 3) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    ∃ z, s = {x, y, z} := by
  have hscard : #(s \ {x, y}) = #s - 2 := by
    rw [← card_pair hxy]
    refine card_sdiff_of_subset ?_
    exact pair_subset_of_mem_of_mem hx hy
  have H : ∃ z, (s \ {x, y}) = {z} := card_eq_one.mp <| (hscard ▸ hs ▸ rfl)
  obtain ⟨z, hz⟩ := H
  refine ⟨z, ?_⟩
  refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
  · exact triplet_subset_of_mem_of_mem_of_mem hx hy (mem_sdiff.mp (hz ▸ mem_singleton.mpr rfl) |>.1)
  · exact hs ▸ card_triplet hxy (mem_sdiff.mp (hz ▸ mem_singleton.mpr rfl) |>.2)

lemma ne_of_mem_finset_empty_inter {x y : α} (s t : Finset α)
    (h : s ∩ t = ∅) (hx : x ∈ s) (hy : y ∈ t) :
    x ≠ y := by
  intro heq
  suffices x ∈ (∅ : Finset _) by
    exact (List.mem_nil_iff x).mp this
  exact h ▸ mem_inter.mpr ⟨hx, heq ▸ hy⟩

lemma eq_of_mem_of_notMem {u v x y z : α}
    (hu : u ∈ ({v, x, y} : Finset _)) (hu' : u ∉ ({x, y, z} : Finset _)) : u = v := by
  simp only [mem_insert, mem_singleton, not_or] at hu hu'
  rcases hu with h | h | h
  · exact h
  · exact hu'.1 h |>.elim
  · exact hu'.2.1 h |>.elim

lemma card_setminus_singleton {s : Finset α} {x : α} (h : x ∈ s) :
    #(s \ {x}) = #s - 1 := by
  rw [card_sdiff, singleton_inter_of_mem h, card_singleton]

lemma card_setminus_singleton' {n : ℕ} {s : Finset α} {x : α} (hx : x ∈ s) (hcard : #s = n + 1) :
    #(s \ {x}) = n := by
  rw [card_setminus_singleton hx, hcard]
  exact Nat.add_sub_self_right ..

lemma card_le_2_iff_no_triplet {s : Finset α} :
    #s ≤ 2 ↔ ∀ x y z, (x ≠ y ∧ x ≠ z ∧ y ≠ z) → ¬{x, y, z} ⊆ s := by
  constructor
  · intro hs x y z h hcard
    suffices 3 ≤ 2 by lia
    refine le_trans (le_of_eq_of_le ?_ (card_le_card hcard)) hs
    grind
  · contrapose
    simp only [not_le, ne_eq, and_imp, not_forall, Decidable.not_not]
    intro hs
    obtain ⟨x, hx⟩ := card_ne_zero.mp <| Nat.ne_zero_of_lt hs
    obtain ⟨y, hy⟩ : (s \ {x}).Nonempty :=
      sdiff_nonempty_of_card_lt_card <| by linarith [card_singleton x]
    obtain ⟨z, hz⟩ : (s \ {x, y}).Nonempty :=
      sdiff_nonempty_of_card_lt_card (lt_of_le_of_lt card_le_two hs)
    exact ⟨x, y, z, by grind⟩

open SimpleGraph
open CaroWeiType

namespace SimpleGraph

private noncomputable instance {α : Type*} {s t : Set α} [Fintype s] [Fintype t] :
    Fintype ((s ∪ t) : Set _) := by
  classical
  exact Set.fintypeUnion s t

variable {V : Type*}

lemma degree_eq_of_eq {G G' : SimpleGraph V} (h : G = G') {v : V}
    [Fintype (G.neighborSet v)] [Fintype (G'.neighborSet v)] :
    G.degree v = G'.degree v := by
  refine congrArg Finset.card ?_
  ext u
  simp only [mem_neighborFinset, h]

noncomputable instance {s : Set (Sym2 V)} [Fintype s] : fromEdgeSet s |>.LocallyFinite := by
  intro v
  simp only [neighborSet, fromEdgeSet_adj]
  let f : (fromEdgeSet s).neighborSet v → s := by
    intro ⟨w, hw⟩
    simp only [mem_neighborSet, fromEdgeSet_adj, ne_eq] at hw
    exact ⟨s(v, w), hw.1⟩
  have hf : Function.Injective f := by
    intro u u' h
    have hu := u.2
    have hu' := u'.2
    simp only [Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk,
      f] at h
    simp only [mem_neighborSet, fromEdgeSet_adj, ne_eq] at hu hu'
    match h with
    | Or.inl h => exact SetCoe.ext h
    | Or.inr h => simp only [hu'.2, false_and] at h
  exact Fintype.ofInjective _ hf

variable {G : SimpleGraph V}

noncomputable instance {G' : SimpleGraph V} [inst : G.LocallyFinite] [inst' : G'.LocallyFinite] :
    (G ⊔ G').LocallyFinite := by
  intro v
  have : ((G ⊔ G').neighborSet v) = G.neighborSet v ∪ G'.neighborSet v := rfl
  rw [this]
  infer_instance

noncomputable instance [G.LocallyFinite] {s : Set (Sym2 V)} [Fintype s] :
    fromEdgeSet (G.edgeSet ∪ s) |>.LocallyFinite := by
  rw [fromEdgeSet_union, fromEdgeSet_edgeSet]
  infer_instance

lemma neighborFinset_eq_of_deg_eq_one_of_adj {v w : V} [Fintype (G.neighborSet v)]
    (hdv : G.degree v = 1) (hvw : G.Adj v w) : G.neighborFinset v = {w} := by
  refine Eq.symm <| eq_of_subset_and_eq_card ?_ hdv.symm
  intro u
  simp only [mem_singleton, mem_neighborFinset]
  exact fun heq ↦ heq ▸ hvw

lemma mem_of_subset_of_degree_pos {s : Finset V} {v : V}
    [Fintype (G.neighborSet v)] (h : G.support ⊆ s) (hv : 0 < G.degree v) :
    v ∈ s :=
  h <| G.degree_pos_iff_mem_support _ |>.mp hv

lemma mem_of_subset_of_adj {s : Finset V} {v w : V}
    (h : G.support ⊆ s) (hv : G.Adj w v) :
    v ∈ s :=
  h <| G.mem_support.mpr ⟨w, hv.symm⟩

lemma mem_of_subset_of_mem_neighborFinset {s : Finset V} {v w : V}
    [Fintype (G.neighborSet w)] (h : G.support ⊆ s) (hv : v ∈ G.neighborFinset w) :
    v ∈ s :=
  mem_of_subset_of_adj h (G.mem_neighborFinset .. |>.mp hv)

lemma neighborFinset_subset_support {v : V} [Fintype (G.neighborSet v)] [Fintype G.support] :
    G.neighborFinset v ⊆ G.support.toFinset := by
  intro u hu
  refine Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨v, ?_⟩
  refine Adj.symm <| G.mem_neighborFinset .. |>.mp hu

lemma neighborFinset_of_adj_of_adj_of_ne [DecidableEq V] {v x y : V} [Fintype (G.neighborSet v)]
    (hdv : G.degree v = 3) (hxy : x ≠ y) (hvx : G.Adj v x) (hvy : G.Adj v y) :
    ∃ z, G.neighborFinset v = {x, y, z} := by
  refine triplet_of_mem_of_mem_of_ne hdv ?_ ?_ hxy
  · exact G.mem_neighborFinset .. |>.mpr hvx
  · exact G.mem_neighborFinset .. |>.mpr hvy

lemma adj_iff_adj {u v : V} :
    G.Adj u v ↔ G.Adj v u :=
  ⟨Adj.symm, Adj.symm⟩

lemma not_adj_symm {u v : V} :
    ¬G.Adj u v → ¬G.Adj v u :=
  fun hnotuv hvu ↦ hnotuv hvu.symm

lemma mem_neighborFinset_symm {u v : V} [Fintype (G.neighborSet u)] [Fintype (G.neighborSet v)] :
    u ∈ G.neighborFinset v → v ∈ G.neighborFinset u := by
  intro hu
  simp only [mem_neighborFinset] at hu ⊢
  exact hu.symm

lemma not_mem_neighborFinset_symm
    {u v : V} [Fintype (G.neighborSet u)] [Fintype (G.neighborSet v)] :
    u ∉ G.neighborFinset v → v ∉ G.neighborFinset u :=
  mem_neighborFinset_symm.mt

lemma ne_of_mem_neighborFinset {u v : V} [Fintype (G.neighborSet v)] :
    u ∈ G.neighborFinset v → u ≠ v :=
  fun h ↦ Adj.ne' <| G.mem_neighborFinset .. |>.mp h

lemma ne'_of_mem_neighborFinset {u v : V} [Fintype (G.neighborSet v)] :
    u ∈ G.neighborFinset v → v ≠ u :=
  fun h ↦ Adj.ne <| G.mem_neighborFinset .. |>.mp h

lemma notMem_singleton_of_mem_neighborFinset {u v : V} [Fintype (G.neighborSet v)] :
    u ∈ G.neighborFinset v → u ∉ ({v} : Finset _) :=
  fun h ↦ notMem_singleton.mpr <| ne_of_mem_neighborFinset h

lemma notMem_singleton_of_mem_neighborFinset' {u v : V} [Fintype (G.neighborSet v)] :
    u ∈ G.neighborFinset v → v ∉ ({u} : Finset _) :=
  fun h ↦ notMem_singleton.mpr <| ne'_of_mem_neighborFinset h

lemma le_fromEdgeSet_left {s t : Set (Sym2 V)} : fromEdgeSet s ≤ fromEdgeSet (s ∪ t) := by
  simp only [fromEdgeSet_union, le_sup_left]

lemma le_fromEdgeSet_right {s t : Set (Sym2 V)} : fromEdgeSet t ≤ fromEdgeSet (s ∪ t) := by
  simp only [fromEdgeSet_union, le_sup_right]

lemma le_fromEdgeSet_union {s : Set (Sym2 V)} :
    G ≤ (fromEdgeSet <| G.edgeSet ∪ s) :=
  fun _ _ hvw ↦ fromEdgeSet_adj _ |>.mpr ⟨Set.mem_union_left _ <| G.mem_edgeSet.mpr hvw, hvw.ne⟩

lemma le_fromEdgeSet_union' {s : Set (Sym2 V)} {u v : V}
    [Fintype (G.neighborSet v)] [Fintype ((fromEdgeSet <| G.edgeSet ∪ s).neighborSet v)] :
    u ∈ G.neighborFinset v →  u ∈ (fromEdgeSet <| G.edgeSet ∪ s).neighborFinset v :=
  fun huv ↦ mem_neighborFinset .. |>.mpr
    <| G.le_fromEdgeSet_union (G.mem_neighborFinset .. |>.mp huv)

lemma adj_fromEdgeSet_union_iff {v w : V} {s : Set (Sym2 V)} :
    (fromEdgeSet <| G.edgeSet ∪ s).Adj w v ↔ (G.Adj w v ∨ (s(w, v) ∈ s ∧ w ≠ v)) := by
  simp only [fromEdgeSet_union, fromEdgeSet_edgeSet, sup_adj, fromEdgeSet_adj, ne_eq]

lemma mem_fromEdgeSet_union_neighborFinset_iff {v w : V} {s : Set (Sym2 V)}
    [Fintype (G.neighborSet w)] [Fintype ((fromEdgeSet <| G.edgeSet ∪ s).neighborSet w)] :
    v ∈ (fromEdgeSet <| G.edgeSet ∪ s).neighborFinset w
      ↔ (v ∈ G.neighborFinset w ∨ (s(w, v) ∈ s ∧ w ≠ v)) := by
  refine (mem_neighborFinset ..).trans ?_
  refine adj_fromEdgeSet_union_iff.trans ?_
  exact or_congr_left <| (mem_neighborFinset ..).symm

lemma eq_fromEdgeSet_of_union_le_right {s : Set (Sym2 V)}
    (h : fromEdgeSet s ≤ G) : fromEdgeSet (G.edgeSet ∪ s) = G := by
  refine le_antisymm ?_ le_fromEdgeSet_union
  intro v w hw
  rcases adj_fromEdgeSet_union_iff.mp hw with hw | hw
  · exact hw
  · exact h (by simp only [fromEdgeSet_adj, hw, ne_eq, not_false_eq_true, and_self])

lemma fromEdgeSet_union_neighborSet_eq {v : V} {s t : Set (Sym2 V)} :
    (fromEdgeSet (s ∪ t) |>.neighborSet v)
      = (fromEdgeSet s |>.neighborSet v) ∪ (fromEdgeSet t |>.neighborSet v) := by
  ext
  simp only [fromEdgeSet_union, mem_neighborSet, sup_adj, Set.mem_union]

lemma fromEdgeSet_union_neighborFinet_eq [DecidableEq V] {v : V} {s t : Set (Sym2 V)}
    [Fintype ((fromEdgeSet s).neighborSet v)]
    [Fintype ((fromEdgeSet t).neighborSet v)]
    [Fintype ((fromEdgeSet <| s ∪ t).neighborSet v)] :
    (fromEdgeSet (s ∪ t) |>.neighborFinset v)
      = (fromEdgeSet s |>.neighborFinset v) ∪ (fromEdgeSet t |>.neighborFinset v) := by
  simp only [neighborFinset, ← Set.toFinset_union, fromEdgeSet_union_neighborSet_eq]

lemma fromEdgeSet_union_degree_le {v : V} {s t : Set (Sym2 V)}
    [Fintype ((fromEdgeSet <| s).neighborSet v)]
    [Fintype ((fromEdgeSet <| t).neighborSet v)]
    [Fintype ((fromEdgeSet <| s ∪ t).neighborSet v)] :
    (fromEdgeSet (s ∪ t) |>.degree v)
      ≤ (fromEdgeSet s |>.degree v) + (fromEdgeSet t |>.degree v) := by
  classical
  simp only [degree]
  rw [fromEdgeSet_union_neighborFinet_eq]
  exact card_union_le ..

lemma fromEdgeSet_union_degree_le' {v : V} {G : SimpleGraph V} [G.LocallyFinite] {s : Set (Sym2 V)}
    [Fintype ((fromEdgeSet <| s).neighborSet v)]
    [Fintype ((fromEdgeSet <| G.edgeSet ∪ s).neighborSet v)] :
    (fromEdgeSet (G.edgeSet ∪ s) |>.degree v)
      ≤ G.degree v + (fromEdgeSet s).degree v := by
  classical
  refine le_trans ?_ (card_union_le _ _)
  refine card_le_card ?_
  simp only [neighborFinset, ← Set.toFinset_union, fromEdgeSet_union_neighborSet_eq]
  refine Set.toFinset_subset_toFinset.mpr (subset_of_eq ?_)
  nth_rewrite 2 [← G.fromEdgeSet_edgeSet]
  exact fromEdgeSet_union_neighborSet_eq

lemma fromEdgeSet_singleton_degree_eq_0_of_ne {v x y : V} (hvx : v ≠ x) (hvy : v ≠ y) :
    (fromEdgeSet {s(x, y)}).degree v = 0 := by
  refine card_eq_zero.mpr ?_
  ext u
  simp only [mem_neighborFinset, fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff',
    Prod.mk.injEq, hvx, false_and, Prod.swap_prod_mk, hvy, or_self, ne_eq, notMem_empty]

lemma fromEdgeSet_singleton_degree_le_1 {v x y : V} :
    (fromEdgeSet {s(x, y)}).degree v ≤ 1 := by
  if hxy : x = y then
    subst hxy
    refine le_of_eq_of_le ?_ zero_le_one
    refine card_eq_zero.mpr ?_
    ext u
    simp only [mem_neighborFinset, fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, Prod.swap_prod_mk, or_self, ne_eq, notMem_empty, iff_false, not_and, not_not,
      and_imp]
    exact fun h h' ↦ h.trans h'.symm
  else if hvx : v = x then
    rw [← card_singleton y]
    refine card_le_card ?_
    intro u
    simp only [mem_neighborFinset, hvx, fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq,
      Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk, hxy, false_and, or_false, ne_eq,
      mem_singleton, and_imp]
    exact fun h _ ↦ h
  else if hvy : v = y then
    rw [← card_singleton x]
    refine card_le_card ?_
    intro u
    simp only [mem_neighborFinset, hvy, fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq,
      Sym2.rel_iff', Prod.mk.injEq, Ne.symm hxy, false_and, Prod.swap_prod_mk, true_and, false_or,
      ne_eq, mem_singleton, and_imp]
    exact fun h _ ↦ h
  else
    exact le_of_eq_of_le (fromEdgeSet_singleton_degree_eq_0_of_ne hvx hvy) zero_le_one

lemma fromEdgeSet_insert_degree_eq {v x y : V} {s : Set (Sym2 V)}
    [Fintype ((fromEdgeSet (Set.insert s(x, y) s)).neighborSet v)]
    [Fintype ((fromEdgeSet s).neighborSet v)]
    (hvx : v ≠ x) (hvy : v ≠ y) :
    (fromEdgeSet (insert s(x, y) s)).degree v = (fromEdgeSet s).degree v := by
  refine le_antisymm ?_ ?_
  · refine card_le_card ?_
    intro u hu
    simp only [mem_neighborFinset, fromEdgeSet_adj, Set.mem_insert_iff, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, hvx, false_and, Prod.swap_prod_mk, hvy, or_self, false_or, ne_eq] at hu
    exact mem_neighborFinset .. |>.mpr hu
  · exact degree_le_of_le le_fromEdgeSet_right

lemma fromEdgeSet_singleton_union_degree_eq {v x y : V} {s : Set (Sym2 V)} [Fintype s]
    (hvx : v ≠ x) (hvy : v ≠ y) :
    (fromEdgeSet ({s(x, y)} ∪ s)).degree v = (fromEdgeSet s).degree v := by
  refine le_antisymm ?_ ?_
  · refine le_trans fromEdgeSet_union_degree_le ?_
    simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero]
    exact fromEdgeSet_singleton_degree_eq_0_of_ne hvx hvy
  · exact degree_le_of_le le_fromEdgeSet_right

section

variable {V : Type}

lemma degree_deleteIncidencesOf_neighbor (G : SimpleGraph V) {s : Finset V} {w : V}
    [Fintype (G.neighborSet w)] [Fintype ((G.deleteIncidencesOf s).neighborSet w)]
    (hs : s ⊆ G.neighborFinset w) :
    G.degree w = (G.deleteIncidencesOf s).degree w + #s := by
  classical
  suffices G.neighborFinset w = (G.deleteIncidencesOf s).neighborFinset w ∪ s by
    simp only [degree, congrArg card this]
    refine card_union_of_disjoint ?_
    refine disjoint_iff_inter_eq_empty.mpr ?_
    ext u
    simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_inter, mem_neighborFinset,
      inf_adj, iInf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and,
      not_or, ne_eq, notMem_empty, iff_false, and_imp]
    intro hwu h hne hus
    exact (h u |>.1 hus |>.2 hwu |>.2) rfl
  ext u
  simp only [mem_neighborFinset, deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_union,
    inf_adj, iInf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and,
    not_or, ne_eq]
  constructor
  · intro h
    simp only [h, forall_const, true_and, h.ne, not_false_eq_true, and_true]
    if hus : u ∈ s then
      exact Or.inr hus
    else
      refine Or.inl ?_
      intro i hi
      refine ⟨?_, ?_⟩
      · have hws : w ∉ s := hs.mt <| notMem_neighborFinset_self G _
        exact fun heq ↦ hws (heq ▸ hi)
      · exact fun heq ↦ hus (heq ▸ hi)
  · intro h
    rcases h with h | h
    · exact h.1
    · exact G.mem_neighborFinset .. |>.mp <| hs h

lemma degree_deleteIncidencesOf_neighbor_singleton (G : SimpleGraph V) {v w : V}
    [Fintype (G.neighborSet w)] [Fintype ((G.deleteIncidencesOf {v}).neighborSet w)]
    (hw : G.Adj v w) :
    G.degree w = (G.deleteIncidencesOf {v}).degree w + 1 := by
  rw [← card_singleton v]
  refine degree_deleteIncidencesOf_neighbor G ?_
  simp only [singleton_subset_iff, mem_neighborFinset, hw.symm]

lemma degree_deleteIncidencesOf_neighbor' (G : SimpleGraph V) {s : Finset V} {w : V}
    [Fintype (G.neighborSet w)] [Fintype ((G.deleteIncidencesOf s).neighborSet w)]
    (hs : s ⊆ G.neighborFinset w) :
    G.degree w - #s = (G.deleteIncidencesOf s).degree w :=
  Nat.sub_eq_of_eq_add <| G.degree_deleteIncidencesOf_neighbor hs

lemma degree_deleteIncidencesOf_neighbor_singleton' (G : SimpleGraph V) {v w : V}
    [Fintype (G.neighborSet w)] [Fintype ((G.deleteIncidencesOf {v}).neighborSet w)]
    (hw : G.Adj v w) :
    G.degree w - 1 = (G.deleteIncidencesOf {v}).degree w :=
  Nat.sub_eq_of_eq_add <| G.degree_deleteIncidencesOf_neighbor_singleton hw

end  -- temporary section

theorem deleteIncidencesOf_notAdj {v w : V} {s : Finset V} (hv : v ∈ s) :
    ¬(G.deleteIncidencesOf s).Adj v w := by
  simp only [deleteIncidencesOf, deleteIncidenceSet, inf_adj, iInf_adj, deleteEdges_adj, ne_eq,
    not_and, not_not]
  intro h
  simp only [h, incidenceSet, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, true_and, not_or, h.ne,
    not_false_eq_true, and_true, imp_false, not_forall, not_and, not_not]
  refine ⟨v, hv, by simp only [not_true_eq_false, IsEmpty.forall_iff]⟩

theorem deleteIncidencesOf_notAdj' {v w : V} {s : Finset V} (hv : v ∈ s) :
    ¬(G.deleteIncidencesOf s).Adj w v :=
  not_adj_symm <| deleteIncidencesOf_notAdj hv

theorem deleteIncidencesOf_neighborFinset_empty {v : V} {s : Finset V} (hv : v ∈ s)
    [Fintype ↑((G.deleteIncidencesOf s).neighborSet v)] :
    (G.deleteIncidencesOf s).neighborFinset v = ∅ := by
  ext u
  simp only [mem_neighborFinset, notMem_empty, iff_false]
  exact deleteIncidencesOf_notAdj hv

theorem deleteIncidenceSet_degree {v w : V} [Fintype (G.neighborSet v)] [Fintype (G.neighborSet w)]
    (hw : w ∈ G.neighborFinset v) [Fintype ((G.deleteIncidenceSet v).neighborSet w)] :
    (G.deleteIncidenceSet v).degree w = G.degree w - 1 := by
  classical
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
    exact Ne.symm <| hx.2 hx.1 |>.2
  · intro hx
    simp_all only [mem_neighborFinset, mem_sdiff, mem_singleton,
      deleteIncidenceSet, incidenceSet, deleteEdges_adj,
      Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, true_and, not_or]
    exact ⟨hw.ne, Ne.symm hx.2⟩

theorem deleteIncidenceSet_support [DecidableEq V] {X : Finset V} (hX : G.support ⊆ X) {v : V} :
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

lemma closed_neighborFinset_contains_Finset [DecidableEq V] [G.LocallyFinite] {s : Finset V} :
    s ⊆ G.closed_neighborFinset_of_Finset s := by
  intro u hu
  simp only [closed_neighborFinset_of_Finset, mem_union, hu, mem_biUnion, mem_neighborFinset,
    true_or]

lemma mem_closed_neighborFinset_of_adj' [DecidableEq V] [G.LocallyFinite] {s : Finset V}
    {v w : V} (hv : v ∈ s) (hvw : G.Adj v w) :
    w ∈ G.closed_neighborFinset_of_Finset s := by
  simp only [closed_neighborFinset_of_Finset, mem_union, mem_biUnion, mem_neighborFinset]
  exact Or.inr ⟨v, hv, hvw⟩

lemma mem_closed_neighborFinset_of_adj [DecidableEq V] [G.LocallyFinite] {s : Finset V}
    {v w : V} (hv : v ∈ s) (hvw : G.Adj w v) :
    w ∈ G.closed_neighborFinset_of_Finset s :=
  mem_closed_neighborFinset_of_adj' hv hvw.symm

lemma mem_closed_neighborFinset_iff [DecidableEq V] [G.LocallyFinite] {s : Finset V} {v : V} :
    v ∈ G.closed_neighborFinset_of_Finset s ↔ v ∈ s ∨ ∃ w ∈ s, G.Adj w v := by
  simp only [closed_neighborFinset_of_Finset, mem_union, mem_biUnion, mem_neighborFinset]

lemma neighborhood_subset_closed_neighbordFinset_of_mem [DecidableEq V] [G.LocallyFinite]
    {s : Finset V} {v : V} (hv : v ∈ s) :
    G.neighborFinset v ⊆ G.closed_neighborFinset_of_Finset s :=
  fun _ hu ↦ mem_closed_neighborFinset_iff.mpr <| Or.inr <| ⟨v, hv, mem_neighborFinset .. |>.mp hu⟩

lemma closed_neighborFinset_of_union [DecidableEq V] [G.LocallyFinite] {s s' : Finset V} :
    G.closed_neighborFinset_of_Finset (s ∪ s')
        = G.closed_neighborFinset_of_Finset s ∪ G.closed_neighborFinset_of_Finset s' := by
  grind [mem_closed_neighborFinset_iff]

lemma closed_neighborFinset_of_singleton_eq [DecidableEq V] [G.LocallyFinite]
    {v : V} : G.closed_neighborFinset_of_Finset {v} = G.neighborFinset v ∪ {v} := by
  ext w
  simp only [closed_neighborFinset_of_Finset, singleton_biUnion, singleton_union, mem_insert,
    mem_neighborFinset, union_singleton]

lemma card_closed_neighborFinset_singleton [DecidableEq V] [G.LocallyFinite] {v : V} :
    #(G.closed_neighborFinset_of_Finset {v}) = G.degree v + 1 := by
  rw [closed_neighborFinset_of_singleton_eq, card_union, ← degree, card_singleton,
    inter_singleton_eq_empty_iff.mpr <| G.notMem_neighborFinset_self v, card_empty, tsub_zero]

lemma mem_of_subset_of_mem_closed_neighborhood [DecidableEq V] [G.LocallyFinite]
    {s : Finset V} {v : V} (h : G.support ⊆ s) {F : Finset _} (hF : F ⊆ s)
    (hv : v ∈ G.closed_neighborFinset_of_Finset F) : v ∈ s := by
  refine mem_closed_neighborFinset_iff.mp hv |>.elim (hF ·) (fun hv ↦ ?_)
  obtain ⟨w, hw, hwv⟩ := hv
  refine h <| G.mem_support.mpr ⟨w, hwv.symm⟩

lemma closed_neighborFinset_of_pair_eq [DecidableEq V] [G.LocallyFinite]
    {v w : V} :
    G.closed_neighborFinset_of_Finset {v, w}
      = G.neighborFinset v ∪ G.neighborFinset w ∪ {v, w} := by
  ext w
  simp only [closed_neighborFinset_of_Finset, biUnion_insert, singleton_biUnion, insert_union,
    singleton_union, mem_insert, mem_union, mem_neighborFinset, union_insert, union_singleton]

lemma closed_neighborFinset_of_triplet_eq [DecidableEq V] [G.LocallyFinite]
    {u v w : V} :
    G.closed_neighborFinset_of_Finset {u, v, w}
      = G.neighborFinset u ∪ G.neighborFinset v ∪ G.neighborFinset w ∪ {u, v, w} := by
  ext z
  simp only [closed_neighborFinset_of_Finset, biUnion_insert, singleton_biUnion, insert_union,
    singleton_union, mem_insert, mem_union, mem_neighborFinset, union_assoc, union_insert,
    union_singleton]

lemma mem_open_neighborFinset_iff [DecidableEq V] [G.LocallyFinite] {s : Finset V} {v : V} :
    v ∈ (G.closed_neighborFinset_of_Finset s) \ s ↔ (∃ w ∈ s, G.Adj w v) ∧ v ∉ s := by
  simp only [mem_sdiff]
  constructor
  · intro ⟨hv, hvs⟩
    exact ⟨Or.resolve_left (mem_closed_neighborFinset_iff.mp hv) hvs, hvs⟩
  · intro ⟨h, hvs⟩
    refine ⟨?_, hvs⟩
    refine mem_closed_neighborFinset_iff.mpr <| Or.inr h

lemma mem_N2_of_Finset_iff [DecidableEq V] [G.LocallyFinite] {s : Finset V} {v : V} :
    v ∈ G.N2_of_Finset s
      ↔ (v ∉ s ∧ (∀ x ∈ s, ¬G.Adj v x) ∧ ∃ x ∈ s, ∃ w ∉ s, G.Adj v w ∧ G.Adj w x) := by
  simp only [N2_of_Finset]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact closed_neighborFinset_contains_Finset.mt <| mem_sdiff.mp h |>.2
    · exact fun _ hx ↦ mem_closed_neighborFinset_of_adj hx |>.mt <| mem_sdiff.mp h |>.2
    · have := mem_closed_neighborFinset_iff.mp <| mem_sdiff.mp h |>.1
      simp only [mem_sdiff.mp h |>.2, false_or] at this
      obtain ⟨w, hw, hwv⟩ := this
      have hw' : w ∉ s := (mem_closed_neighborFinset_of_adj' · hwv) |>.mt <| mem_sdiff.mp h |>.2
      have := mem_closed_neighborFinset_iff.mp hw
      simp only [hw', false_or] at this
      obtain ⟨x, hx, hxw⟩ := this
      refine ⟨x, hx, w, hw', hwv.symm, hxw.symm⟩
  · intro ⟨hv₀, hv₁, hv₂⟩
    refine mem_sdiff.mpr ⟨?_, ?_⟩
    · refine mem_closed_neighborFinset_iff.mpr <| Or.inr ?_
      obtain ⟨x, hx, w, hw, hvw, hwx⟩ := hv₂
      refine ⟨w, ?_, hvw.symm⟩
      refine mem_closed_neighborFinset_iff.mpr <| Or.inr ?_
      exact ⟨x, hx, hwx.symm⟩
    · refine not_iff_not.mpr mem_closed_neighborFinset_iff |>.mpr ?_
      simp only [hv₀, false_or, not_exists, not_and]
      exact fun x hx ↦ not_adj_symm <| hv₁ x hx

lemma mem_N2_of_Finset_iff' [DecidableEq V] [G.LocallyFinite] {s : Finset V} {v : V} :
    v ∈ G.N2_of_Finset s
      ↔ (v ∉ G.closed_neighborFinset_of_Finset s ∧ ∃ x ∈ s, ∃ w ∉ s, G.Adj v w ∧ G.Adj w x) := by
  refine mem_N2_of_Finset_iff.trans ?_
  simp only [mem_closed_neighborFinset_iff, not_or, not_exists, not_and]
  constructor
  · intro ⟨h₁, h₂, h₃⟩
    exact ⟨⟨h₁, fun x hx ↦ not_adj_symm <| h₂ x hx⟩, h₃⟩
  · intro ⟨⟨h₁, h₂⟩, h₃⟩
    exact ⟨h₁, fun x hx ↦ not_adj_symm <| h₂ x hx, h₃⟩

lemma mem_N2_of_Finset_iff'' [DecidableEq V] [G.LocallyFinite] {s : Finset V} {v : V} :
    v ∈ G.N2_of_Finset s
      ↔ (v ∉ G.closed_neighborFinset_of_Finset s
          ∧ ∃ w ∈ G.closed_neighborFinset_of_Finset s, G.Adj v w) := by
  simp only [mem_N2_of_Finset_iff, mem_closed_neighborFinset_iff, not_or, not_exists, not_and]
  grind [Adj.symm]

lemma N2_inter_Nle1_empty [DecidableEq V] [G.LocallyFinite] {s : Finset V} :
    G.N2_of_Finset s ∩ G.closed_neighborFinset_of_Finset s = ∅ :=
  disjoint_of_sdiff (subset_refl _)

lemma Nle1_inter_N2_empty [DecidableEq V] [G.LocallyFinite] {s : Finset V} :
    G.closed_neighborFinset_of_Finset s ∩ G.N2_of_Finset s = ∅ :=
  inter_comm (G.closed_neighborFinset_of_Finset s) _ ▸ N2_inter_Nle1_empty

lemma notMem_closed_neighborFinset_of_mem_N2 [DecidableEq V] [G.LocallyFinite]
    {s : Finset V} {v : V} (h : v ∈ G.N2_of_Finset s) :
    v ∉ G.closed_neighborFinset_of_Finset s :=
  notMem_of_empty_inter_of_mem Nle1_inter_N2_empty h

lemma notMem_closed_neighborFinset_of_adj_of_notMem_closed_N2 [DecidableEq V] [G.LocallyFinite]
    {s : Finset V} {v w : V} (hvw : G.Adj v w)
    (hw₂ : w ∉ G.N2_of_Finset s) (hw : w ∉ G.closed_neighborFinset_of_Finset s) :
    v ∉ G.closed_neighborFinset_of_Finset s := by
  refine not_iff_not.mpr mem_closed_neighborFinset_iff |>.mpr ?_
  have hw := not_iff_not.mpr mem_closed_neighborFinset_iff |>.mp hw
  have hw₂ := not_iff_not.mpr mem_N2_of_Finset_iff |>.mp hw₂
  simp only [not_or, not_exists, not_and] at hw hw₂ ⊢
  have hvs : v ∉ s := fun hvs ↦ hw.2 _ hvs hvw
  refine ⟨hvs, ?_⟩
  exact fun x hx ↦ not_adj_symm <| hw₂ hw.1 (fun _ h ↦ not_adj_symm <| hw.2 _ h) x hx v hvs hvw.symm

lemma deleteIncidencesOf_le {s : Finset V} :
    (G.deleteIncidencesOf s) ≤ G := by
  intro v w
  simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, inf_adj, iInf_adj,
    deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq, and_imp]
  intro hvw
  simp only [hvw, forall_const, true_and, hvw.ne, not_false_eq_true, and_true, implies_true]

lemma deleteIncidencesOf_neighborFinset_subset {s : Finset V} {v : V}
    [Fintype ((G.deleteIncidencesOf s).neighborSet v)] [Fintype (G.neighborSet v)] :
    (G.deleteIncidencesOf s).neighborFinset v ⊆ G.neighborFinset v :=
  fun _ hw ↦ mem_neighborFinset .. |>.mpr <| deleteIncidencesOf_le <| mem_neighborFinset .. |>.mp hw

lemma deleteIncidencesOf_degree_le {s : Finset V} {v : V}
    [Fintype ((G.deleteIncidencesOf s).neighborSet v)] [Fintype (G.neighborSet v)] :
    (G.deleteIncidencesOf s).degree v ≤ G.degree v :=
  degree_le_of_le deleteIncidencesOf_le

lemma deleteIncidencesOf_singleton_eq_deleteIncidenceSet (v : V) :
    G.deleteIncidencesOf {v} = G.deleteIncidenceSet v := by
  simp [deleteIncidencesOf, deleteIncidenceSet_le]

theorem deleteIncidenceSet_notAdj {v w : V} :
    ¬(G.deleteIncidenceSet v).Adj v w :=
  (deleteIncidencesOf_singleton_eq_deleteIncidenceSet v)
    ▸ deleteIncidencesOf_notAdj (mem_singleton.mpr rfl)

theorem deleteIncidenceSet_notAdj' {v w : V} :
    ¬(G.deleteIncidenceSet v).Adj w v :=
  not_adj_symm <| deleteIncidenceSet_notAdj

lemma deleteIncidenceSet_of_isolated {x : V} [G.LocallyFinite] (hx : G.degree x = 0) :
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

lemma deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj
    {u v : V} {s : Finset V} (hu : u ∉ s) (hv : v ∉ s) (huv : G.Adj u v) :
    (G.deleteIncidencesOf s).Adj u v := by
  simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, inf_adj, huv, iInf_adj,
    deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, true_and, not_or, ne_eq, huv.ne,
    not_false_eq_true, and_true]
  intro w hw
  refine ⟨?_, ?_⟩ <;> refine ne_of_mem_of_not_mem hw (by simp only [hu, hv, not_false_eq_true])

lemma deleteIncidencesOf_degree_le' {s : Finset V} {v : V} (hvs : v ∉ s)
    [Fintype ((G.deleteIncidencesOf s).neighborSet v)] [Fintype (G.neighborSet v)] :
    G.degree v ≤ (G.deleteIncidencesOf s).degree v + #s := by
  classical
  suffices G.neighborFinset v ⊆ ((G.deleteIncidencesOf s).neighborFinset v ∪ s) by
    simp only [degree]
    refine le_trans (card_le_card this) (card_union_le ..)
  intro u
  simp only [mem_neighborFinset, mem_union]
  intro hvu
  if hus : u ∈ s then
    exact Or.inr hus
  else
    exact Or.inl <| deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj hvs hus hvu

lemma adj_of_deleteIncidencesOf_adj
    {u v : V} {s : Finset V} (huv : (G.deleteIncidencesOf s).Adj u v) :
    G.Adj u v :=
  deleteIncidencesOf_le huv

lemma deleteIncidencesOf_adj_iff_of_notMem
    {u v : V} {s : Finset V} (hu : u ∉ s) (hv : v ∉ s) :
    G.Adj u v ↔ (G.deleteIncidencesOf s).Adj u v :=
  ⟨deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj hu hv, adj_of_deleteIncidencesOf_adj⟩

lemma degree_eq_deleteIncidencesOf_degree_of_inter_neighborhood_empty
    [DecidableEq V] {s : Finset V} {v : V} (hvs : v ∉ s)
    [Fintype (G.neighborSet v)] [Fintype ((G.deleteIncidencesOf s).neighborSet v)]
    (hNvs : s ∩ G.neighborFinset v = ∅) :
    G.degree v = (G.deleteIncidencesOf s).degree v := by
  refine congrArg Finset.card ?_
  ext u
  simp only [mem_neighborFinset]
  refine ⟨?_, adj_of_deleteIncidencesOf_adj⟩
  refine fun h ↦ deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj hvs ?_ h
  exact notMem_of_empty_inter_of_mem hNvs <| mem_neighborFinset .. |>.mpr h

lemma mem_neighborFinset_deleteIncidencesOf_of_notMem_of_notMem_of_mem_neighborFinset
    {u v : V} {s : Finset V}
    [Fintype (G.neighborSet v)] [Fintype ((G.deleteIncidencesOf s).neighborSet v)]
    (hu : u ∉ s) (hv : v ∉ s) (huv : u ∈ G.neighborFinset v) :
    u ∈ (G.deleteIncidencesOf s).neighborFinset v :=
  mem_neighborFinset .. |>.mpr
    <| deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj hv hu <| mem_neighborFinset .. |>.mp huv

lemma mem_neighborFinset_of_deleteIncidencesOf_mem_neighborFinset
    {u v : V} {s : Finset V}
    [Fintype (G.neighborSet v)] [Fintype ((G.deleteIncidencesOf s).neighborSet v)]
    (huv : u ∈ (G.deleteIncidencesOf s).neighborFinset v) :
    u ∈ G.neighborFinset v :=
  G.mem_neighborFinset .. |>.mpr
    <| adj_of_deleteIncidencesOf_adj <| mem_neighborFinset .. |>.mp huv

lemma mem_neighborFinset_deleteIncidencesOf_iff_of_notMem
    {u v : V} {s : Finset V} (hu : u ∉ s) (hv : v ∉ s)
    [Fintype (G.neighborSet v)] [Fintype ((G.deleteIncidencesOf s).neighborSet v)] :
    u ∈ G.neighborFinset v ↔ u ∈ (G.deleteIncidencesOf s).neighborFinset v :=
  ⟨mem_neighborFinset_deleteIncidencesOf_of_notMem_of_notMem_of_mem_neighborFinset hu hv,
    mem_neighborFinset_of_deleteIncidencesOf_mem_neighborFinset⟩

lemma neighborFinset_eq_delelteIncidencesOf_of_empty_inter_neighborFinset [DecidableEq V]
    {u : V} {s : Finset V} [Fintype (G.neighborSet u)]
    [Fintype ((G.deleteIncidencesOf s).neighborSet u)]
    (hu : G.neighborFinset u ∩ s = ∅) (hus : u ∉ s) :
    (G.deleteIncidencesOf s).neighborFinset u = G.neighborFinset u := by
  ext v
  refine ⟨?_, ?_⟩
  · exact mem_neighborFinset_of_deleteIncidencesOf_mem_neighborFinset
  · intro hv
    refine (mem_neighborFinset_deleteIncidencesOf_iff_of_notMem ?_ hus).mp hv
    exact notMem_of_mem_of_empty_inter hv hu

lemma deleteIncidencesOf_degree_lt {s : Finset V} {v w : V}
    (hvw : G.Adj v w) (hvs : w ∈ s)
    [Fintype ((G.deleteIncidencesOf s).neighborSet v)] [Fintype (G.neighborSet v)] :
    (G.deleteIncidencesOf s).degree v < G.degree v := by
  refine card_lt_card ?_
  refine (ssubset_iff_of_subset ?_).mpr ?_
  · intro
    simp only [mem_neighborFinset]
    exact fun hu ↦ adj_of_deleteIncidencesOf_adj hu
  · refine ⟨w, ?_, ?_⟩
    · exact G.mem_neighborFinset .. |>.mpr hvw
    · exact not_iff_not.mpr (mem_neighborFinset ..) |>.mpr <| deleteIncidencesOf_notAdj' hvs

lemma deleteIncidencesOf_notadj {s : Finset V} {x y : V} (hx : x ∈ s) :
    ¬(G.deleteIncidencesOf s).Adj x y := by
  simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, inf_adj, iInf_adj,
    deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq]
  intro hxy h
  exact false_of_ne (h x |>.1 hx |>.2 hxy |>.1) |>.elim

lemma deleteIncidencesOf_notadj' {s : Finset V} {x y : V} (hx : x ∈ s) :
    ¬(G.deleteIncidencesOf s).Adj y x :=
  not_adj_symm <| deleteIncidencesOf_notadj hx

lemma notMem_of_adj_deleteIncidencesOf {s : Finset V} {v w : V}
    (h : (G.deleteIncidencesOf s).Adj v w) : v ∉ s :=
  deleteIncidencesOf_notadj |>.mt <| not_not_intro h

lemma notMem_of_adj_deleteIncidencesOf' {s : Finset V} {v w : V}
    (h : (G.deleteIncidencesOf s).Adj v w) : w ∉ s :=
  notMem_of_adj_deleteIncidencesOf h.symm

lemma notMem_of_mem_neighborFinset_deleteIncidencesOf
    {s : Finset V} {v w : V} [Fintype ((G.deleteIncidencesOf s).neighborSet w)]
    (h : v ∈ (G.deleteIncidencesOf s).neighborFinset w) : v ∉ s :=
  notMem_of_adj_deleteIncidencesOf' <| mem_neighborFinset .. |>.mp h

lemma notMem_of_mem_neighborFinset_deleteIncidencesOf'
    {s : Finset V} {v w : V}
    [Fintype ((G.deleteIncidencesOf s).neighborSet w)]
    (h : v ∈ (G.deleteIncidencesOf s).neighborFinset w) : w ∉ s :=
  notMem_of_adj_deleteIncidencesOf <| mem_neighborFinset .. |>.mp h

lemma notMem_of_mem_support_deleteIncidencesOf {s : Finset V}
    {v : V} (h : v ∈ (G.deleteIncidencesOf s).support) : v ∉ s := by
  obtain ⟨_, hw⟩ := mem_support _ |>.mp h
  exact notMem_of_adj_deleteIncidencesOf hw

lemma deleteIncidencesOf_le_of_le {s : Finset V} {G' : SimpleGraph V}
    (hle : G ≤ G') :
    G.deleteIncidencesOf s ≤ G'.deleteIncidencesOf s := by
  intro v w hvw
  refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ ?_
  · exact notMem_of_adj_deleteIncidencesOf hvw
  · exact notMem_of_adj_deleteIncidencesOf' hvw
  · exact hle <| adj_of_deleteIncidencesOf_adj hvw

lemma deleteIncidencesOf_support_subset {s : Finset V} :
    (G.deleteIncidencesOf s).support ⊆ G.support \ s := by
  intro u hu
  obtain ⟨v, hv⟩ := mem_support _ |>.mp hu
  refine (Set.mem_diff u).mpr ⟨?_, ?_⟩
  · exact (mem_support G).mpr ⟨v, adj_of_deleteIncidencesOf_adj hv⟩
  · exact deleteIncidencesOf_notadj |>.mt <| not_not.mpr hv

theorem deleteIncidencesOf_support [DecidableEq V] {X s : Finset V} (hX : G.support ⊆ X) :
    (G.deleteIncidencesOf s).support ⊆ ((X \ s) : Finset V) := by
  refine subset_trans deleteIncidencesOf_support_subset ?_
  intro w hw
  refine mem_def.mp <| mem_sdiff.mpr ⟨?_, ?_⟩
  · exact mem_def.mpr <| hX <| (Set.mem_diff _).mp hw |>.1
  · exact Set.mem_diff _ |>.mp hw |>.2

lemma deleteIncidencesOf_neighborFinset_eq [DecidableEq V] {v : V} {s : Finset V} (hvs : v ∉ s)
    [Fintype (G.neighborSet v)] [Fintype ((G.deleteIncidencesOf s).neighborSet v)] :
    (G.deleteIncidencesOf s).neighborFinset v = (G.neighborFinset v \ s) := by
  ext u
  constructor
  · intro hu
    refine mem_sdiff.mpr ⟨?_, ?_⟩
    · exact mem_neighborFinset_of_deleteIncidencesOf_mem_neighborFinset hu
    · exact notMem_of_mem_neighborFinset_deleteIncidencesOf hu
  · intro hu
    obtain ⟨huv, hus⟩ := mem_sdiff.mp hu
    exact (mem_neighborFinset_deleteIncidencesOf_iff_of_notMem hus hvs).mp huv

lemma deleteIncidencesOf_le_mono {V : Type*} {G₁ G₂ : SimpleGraph V} {s : Finset V}
    (hle : G₁ ≤ G₂) : G₁.deleteIncidencesOf s ≤ G₂.deleteIncidencesOf s := by
  intro u v
  simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, inf_adj, iInf_adj,
    deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq, and_imp]
  intro h₁uv h hne
  simp only [hle h₁uv, forall_const, true_and, hne, not_false_eq_true, and_true]
  exact fun _ hw ↦  h _ |>.1 hw |>.2 h₁uv

end SimpleGraph

theorem cw_bound_deleteIncidenceSet_le (f : ℕ → ℝ) {V : Type*} [DecidableEq V] [Fintype V] {v : V}
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (hv : v ∈ X)
    (hf : ∀ d d', d ≤ d' → f d' ≤ f d) :
    ∑ x ∈ X, f (G.degree x)
      ≤ ∑ x ∈ X \ {v}, f ((G.deleteIncidencesOf {v}).degree x) + f (G.degree v) := by
  calc ∑ x ∈ X, f (G.degree x)
    _ = ∑ x ∈ X \ {v}, f (G.degree x) + ∑ x ∈ {v}, f (G.degree x) :=
      Eq.symm <| sum_sdiff <| singleton_subset_iff.mpr hv
    _ = ∑ x ∈ X \ {v}, f (G.degree x) + f (G.degree v) := by simp only [sum_singleton]
    _ ≤ ∑ x ∈ X \ {v}, f ((G.deleteIncidencesOf {v}).degree x) + f (G.degree v) := by
      simp only [add_le_add_iff_right]
      refine sum_le_sum ?_
      intro w hw
      refine hf _ _ ?_
      exact degree_le_of_le deleteIncidencesOf_le

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
variable {V : Type*} {G : SimpleGraph V}

@[simp]
lemma ne_of_deg0_of_adj {u v w : V} [Fintype (G.neighborSet u)] (h : G.degree u = 0)
    (hvw : G.Adj v w) : u ≠ v :=
  fun heq ↦ (ne_of_lt (heq ▸ hvw).degree_pos_left) h.symm

@[simp]
lemma ne_of_deg0_of_adj' {u v w : V} [Fintype (G.neighborSet u)] (h : G.degree u = 0)
    (hvw : G.Adj w v) : u ≠ v := by
  exact ne_of_deg0_of_adj h hvw.symm

theorem exists_minimal_degree_vertex_in [DecidableEq V] (X : Finset V) [Nonempty X]
    [G.LocallyFinite] :
    ∃ v, v ∈ X ∧ ∀ w ∈ X, (G.neighborFinset v ∩ X).card ≤ (G.neighborFinset w ∩ X).card := by
  classical
  obtain ⟨v, hv⟩ := (G.induce X).exists_minimal_degree_vertex
  refine ⟨v.1, v.2, ?_⟩
  intro w hw
  calc (G.neighborFinset v ∩ X).card
    _ = (G.induce X).degree v := Eq.symm <| induced_degree_eq G X v.1 v.2
    _ = (G.induce X).minDegree := Eq.symm <| hv
    _ ≤ (G.induce X).degree ⟨w, hw⟩ := (G.induce X).minDegree_le_degree _
    _ = (G.neighborFinset w ∩ X).card := induced_degree_eq G X w hw

theorem exists_maximal_degree_vertex_in [DecidableEq V] (X : Finset V) [Nonempty X]
    [G.LocallyFinite] :
    ∃ v, v ∈ X ∧ ∀ w ∈ X, (G.neighborFinset v ∩ X).card ≥ (G.neighborFinset w ∩ X).card := by
  classical
  obtain ⟨v, hv⟩ := (G.induce X).exists_maximal_degree_vertex
  refine ⟨v.1, v.2, ?_⟩
  intro w hw
  calc (G.neighborFinset v ∩ X).card
    _ = (G.induce X).degree v := Eq.symm <| induced_degree_eq G X v.1 v.2
    _ = (G.induce X).maxDegree := Eq.symm <| hv
    _ ≥ (G.induce X).degree ⟨w, hw⟩ := (G.induce X).degree_le_maxDegree _
    _ = (G.neighborFinset w ∩ X).card := induced_degree_eq G X w hw

theorem degree_eq [DecidableEq V] (X : Finset V) (hX : G.support ⊆ X) [G.LocallyFinite] :
    ∀ x, G.degree x = (G.neighborFinset x ∩ X).card := by
  intro x
  refine congrArg Finset.card ?_
  ext y
  constructor
  · intro hy
    simp_all only [mem_neighborFinset, mem_inter, true_and]
    exact hX <| G.mem_support.mpr ⟨_, hy.symm⟩
  · exact fun hy ↦ mem_inter.mp hy |>.1

lemma degree_eq' [DecidableEq V] (v : V) [G.LocallyFinite] [Fintype G.support] :
    G.degree v = (G.neighborFinset v ∩ G.support.toFinset).card := by
  refine congrArg Finset.card ?_
  ext w
  constructor
  · intro hw
    simp_all only [mem_neighborFinset, mem_inter, Set.mem_toFinset, true_and]
    exact G.degree_pos_iff_mem_support w |>.mp <| hw.symm.degree_pos_left
  · exact fun hx ↦ mem_of_mem_filter w hx

theorem minDegree_iff {v : V} [DecidableRel G.Adj] [Fintype V] :
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

theorem maxDegree_iff {v : V} [DecidableRel G.Adj] [Fintype V] :
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

theorem minDegree_iff' {v : V} (X : Finset V) (hX : X.Nonempty) (hv : v ∈ X) [G.LocallyFinite] :
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

lemma neighborFinset_eq_deg2' [DecidableEq V] {v : V} (f : V → ℝ) [Fintype (G.neighborSet v)] :
    G.degree v = 2 → ∃ u w, G.neighborFinset v = {u, w} ∧ f w ≤ f u := by
  intro h
  obtain ⟨u, w, _, huw⟩ := card_eq_two.mp h
  obtain ⟨u', w', heq, hle⟩ := sorted_pair f u w
  refine ⟨w', u', ?_, hle⟩
  rw [huw, ← heq]
  exact pair_comm ..

lemma neighborFinset_eq_deg3 [DecidableEq V] {v : V} (f : V → ℝ) [Fintype (G.neighborSet v)] :
    G.degree v = 3 → ∃ x y z, G.neighborFinset v = {x, y, z} ∧ f z ≤ f y ∧ f y ≤ f x := by
  intro h
  obtain ⟨σ, hσ, hinc⟩ := sorted_finset 3 h f
  have : Finset.image σ univ = {σ 2, σ 1, σ 0} := by
    ext x
    simp only [mem_image, mem_univ, true_and, Fin.isValue, mem_insert, mem_singleton]
    constructor
    · intro ⟨i, hi⟩
      suffices i = 0 ∨ i = 1 ∨ i = 2 by grind only
      grind only
    · grind only
  refine ⟨σ 2, σ 1, σ 0, hσ.symm.trans this, by grind only⟩

lemma neighborFinset_eq_deg3' [DecidableEq V] {v x : V} [Fintype (G.neighborSet v)]
    (hx : x ∈ G.neighborFinset v) (f : V → ℝ) :
    G.degree v = 3 → ∃ y z, G.neighborFinset v = {x, y, z} ∧ f z ≤ f y := by
  intro h
  obtain ⟨σ, hσ, hinc⟩ := sorted_finset 3 h f
  have : Finset.image σ univ = {σ 2, σ 1, σ 0} := by
    ext x
    simp only [mem_image, mem_univ, true_and, Fin.isValue, mem_insert, mem_singleton]
    constructor
    · intro ⟨i, hi⟩
      suffices i = 0 ∨ i = 1 ∨ i = 2 by grind only
      grind only
    · grind only
  simp only [← hσ, this, Fin.isValue, mem_insert, mem_singleton] at hx ⊢
  rcases hx with hx | hx | hx
  · refine ⟨σ 1, σ 0, ?_, hinc _ _ <| Fin.zero_le 1⟩
    simp only [Fin.isValue, hx]
  · refine ⟨σ 2, σ 0, ?_, hinc _ _ <| Fin.zero_le 2⟩
    simp only [Fin.isValue, hx]
    grind only [= mem_insert]
  · refine ⟨σ 2, σ 1, ?_, hinc _ _ <| Fin.coe_sub_iff_le.mp rfl⟩
    simp only [Fin.isValue, hx]
    grind only [= mem_insert, = mem_singleton]

lemma neighborFinset_eq_deg3'' [DecidableEq V] {v x y : V} [Fintype (G.neighborSet v)]
    (hx : x ∈ G.neighborFinset v) (hy : y ∈ G.neighborFinset v) (hxy : x ≠ y) :
    G.degree v = 3 → ∃ z, G.neighborFinset v = {x, y, z} :=
  fun hdv ↦ triplet_of_mem_of_mem_of_ne hdv hx hy hxy

lemma notMem_of_degree_in_eq_zero_of_adj [DecidableEq V] {s : Finset V} {v w : V}
    [Fintype (G.neighborSet v)] (hdv : G.degree_in s v = 0) (hvw : G.Adj v w) :
    w ∉ s := by
  intro hw
  suffices 1 ≤ 0 by exact Nat.not_succ_le_zero 0 this
  rw [← hdv, ← card_singleton w]
  refine card_le_card ?_
  simp [hvw, hw]

lemma degree_in_le_degree [DecidableEq V] {u : V} {s : Finset V} [Fintype (G.neighborSet u)] :
    G.degree_in s u ≤ G.degree u := by
  refine card_le_card inter_subset_left

lemma degree_in_le_card [DecidableEq V] {u : V} {s : Finset V} [Fintype (G.neighborSet u)] :
    G.degree_in s u ≤ #s := by
  rw [degree_in]
  exact card_le_card inter_subset_right

lemma degree_in_le_card_minus_one_of_mem [DecidableEq V] {u : V} {s : Finset V} (hu : u ∈ s)
    [Fintype (G.neighborSet u)] :
    G.degree_in s u ≤ #s - 1 := by
  have : #(s \ {u}) = #s - #{u} :=
    card_sdiff_of_subset <| by simp only [singleton_subset_iff, hu]
  rw [degree_in, ← card_singleton u, ← this]
  refine card_le_card ?_
  intro x hx
  simp only [mem_inter, mem_neighborFinset] at hx
  exact mem_sdiff.mpr ⟨hx.2, notMem_singleton.mpr hx.1.ne'⟩

lemma degree_in_mono [DecidableEq V] {u : V} {s t : Finset V} (h : s ⊆ t)
    [Fintype (G.neighborSet u)] : G.degree_in s u ≤ G.degree_in t u := by
  exact card_le_card <| inter_subset_inter (subset_refl _) h

lemma degree_in_mono' [DecidableEq V] {u : V} {s : Finset V} {G' : SimpleGraph V}
    [Fintype (G.neighborSet u)] [Fintype (G'.neighborSet u)] (h : G ≤ G') :
    G.degree_in s u ≤ G'.degree_in s u := by
  refine card_le_card <| inter_subset_inter_right ?_
  exact fun v hv ↦ G'.mem_neighborFinset .. |>.mpr <| h <| G.mem_neighborFinset .. |>.mp hv

lemma degree_in_union_self [DecidableEq V] (u : V) (s : Finset V) [Fintype (G.neighborSet u)] :
    G.degree_in s u = G.degree_in (s ∪ {u}) u := by
  refine congrArg Finset.card ?_
  ext v
  simp only [mem_inter, mem_neighborFinset, union_singleton, SimpleGraph.irrefl, not_false_eq_true,
    inter_insert_of_notMem]

lemma degree_in_union_self' [DecidableEq V] (u : V) (s : Finset V) [Fintype (G.neighborSet u)] :
    G.degree_in s u = G.degree_in ({u} ∪ s) u := by
  rw [union_comm]
  exact degree_in_union_self u s

lemma degree_in_union_le [DecidableEq V] {u : V} {s t : Finset V} [Fintype (G.neighborSet u)] :
    G.degree_in (s ∪ t) u ≤ G.degree_in s u + #t := by
  simp_rw [degree_in]
  suffices G.neighborFinset u ∩ (s ∪ t) ⊆ (G.neighborFinset u ∩ s) ∪ t by
    exact le_trans (card_le_card this) <| card_union_le ..
  rw [inter_union_distrib_right]
  exact inter_subset_inter subset_union_left (subset_refl _)

lemma degree_in_union_of_empty_inter [DecidableEq V] {u : V} {s t : Finset V} (hcap : s ∩ t = ∅)
    [Fintype (G.neighborSet u)] :
    G.degree_in (s ∪ t) u = G.degree_in s u + G.degree_in t u := by
  simp only [degree_in]
  rw [← card_union_of_disjoint (disjoint_iff_inter_eq_empty.mpr <| by grind)]
  refine congrArg Finset.card <| inter_union_distrib_left ..

lemma degree_in_subpair_le_one_of_mem [DecidableEq V] {u : V} {s : Finset V}
    [Fintype (G.neighborSet u)] (hu : u ∈ s) (hs : #s ≤ 2) :
    G.degree_in s u ≤ 1 := by
  suffices G.neighborFinset u ∩ s ⊆ s \ {u} by
    refine le_trans (card_le_card this) ?_
    rw [card_sdiff, singleton_inter_of_mem hu, card_singleton]
    exact Nat.sub_le_of_le_add hs
  intro w hw
  refine mem_sdiff.mpr ⟨?_, ?_⟩
  · exact mem_inter.mp hw |>.2
  · exact notMem_singleton.mpr <| Adj.ne' <| G.mem_neighborFinset .. |>.mp (mem_inter.mp hw |>.1)

lemma degree_in_union_eq [DecidableEq V] {u : V} {s t : Finset V} [Fintype (G.neighborSet u)]
    (ht : t ∩ G.neighborFinset u = ∅) :
    G.degree_in (s ∪ t) u = G.degree_in s u := by
  refine congrArg Finset.card ?_
  ext w
  simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff, or_iff_left_iff_imp]
  intro huw hwt
  have h : w ∈ (∅ : Finset _) := ht ▸ mem_inter.mpr ⟨hwt, G.mem_neighborFinset .. |>.mpr huw⟩
  simp at h

lemma degree_in_deleteIncidencesOf [DecidableEq V] {v : V} (s t : Finset V)
    [Fintype (G.neighborSet v)] [Fintype ((G.deleteIncidencesOf t).neighborSet v)]
    (hu : t ∩ s = ∅) (hu' : v ∉ t) :
    (G.deleteIncidencesOf t).degree_in s v = G.degree_in s v := by
  simp only [degree_in]
  refine congrArg card ?_
  ext w
  simp only [mem_inter, mem_neighborFinset, and_congr_left_iff]
  intro hw
  constructor
  · exact adj_of_deleteIncidencesOf_adj
  · exact deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj hu' (notMem_of_empty_inter_of_mem hu hw)

set_option linter.unusedFintypeInType false
lemma degree_in_deleteIncidencesOf_of_le [DecidableEq V] {v : V}
    {s t : Finset V} {G' : SimpleGraph V}
    [Fintype (G.neighborSet v)] [Fintype (G'.neighborSet v)]
    [Fintype ((G'.deleteIncidencesOf t).neighborSet v)]
    (hu : t ∩ s = ∅) (hu' : v ∉ t) (hle : G ≤ G') :
    G.degree_in s v ≤ (G'.deleteIncidencesOf t).degree_in s v :=
  le_of_le_of_eq (degree_in_mono' hle) (Eq.symm <| degree_in_deleteIncidencesOf _ _ hu hu')

lemma degree_in_deleteIncidencesOf' [DecidableEq V] {v : V} (s t : Finset V)
    [Fintype (G.neighborSet v)] [Fintype ((G.deleteIncidencesOf t).neighborSet v)]
    (hu : t ∩ s = ∅) (hv : v ∉ t) :
    G.degree_in (s ∪ t) v ≤ (G.deleteIncidencesOf t).degree_in s v + #t := by
  unfold degree_in
  suffices (G.neighborFinset v ∩ (s ∪ t)) ⊆ (((G.deleteIncidencesOf t).neighborFinset v ∩ s) ∪ t) by
    refine le_trans (card_le_card this) (card_union_le ..)
  intro w hw
  simp only [mem_inter, mem_neighborFinset, mem_union] at hw ⊢
  rcases hw.2 with hws | hwt
  · refine Or.inl ⟨?_, hws⟩
    refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj hv ?_ hw.1
    exact notMem_of_empty_inter_of_mem hu hws
  · exact Or.inr hwt

lemma degree_in_neighbor [DecidableEq V] {u v : V} (s : Finset V) (huv : G.Adj u v) (hv : v ∉ s)
    [Fintype (G.neighborSet u)] :
    G.degree_in (s ∪ {v}) u = G.degree_in s u + 1 := by
  simp only [degree_in]
  suffices G.neighborFinset u ∩ (s ∪ {v}) = (G.neighborFinset u ∩ s) ∪ {v} by
    rw [this, card_union, card_singleton]
    suffices (G.neighborFinset u ∩ s ∩ {v}) = ∅ by
      rw [this]
      exact (Nat.add_succ _ 0).symm
    ext w
    simp only [inter_assoc, mem_inter, mem_neighborFinset, mem_singleton, notMem_empty, iff_false,
      not_and]
    exact fun  _ h ↦ ne_of_mem_of_not_mem h hv
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

lemma degree_in_eq_of_iso [DecidableEq V] {V' : Type*} [DecidableEq V'] {G' : SimpleGraph V'}
    (v : V) (s : Finset V) (φ : G ≃g G')
    [Fintype (G.neighborSet v)] [Fintype (G'.neighborSet (φ.toFun v))] :
    G.degree_in s v = G'.degree_in (s.image φ.toFun) (φ.toFun v) := by
  simp only [degree_in]
  refine Set.BijOn.finsetCard_eq φ ⟨?_, ?_, ?_⟩
  · intro u hu
    simp only [coe_inter, coe_neighborFinset, Set.mem_inter_iff, mem_neighborSet, SetLike.mem_coe,
      Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, coe_image, Set.mem_image,
      EmbeddingLike.apply_eq_iff_eq, exists_eq_right] at hu ⊢
    exact ⟨φ.map_rel_iff' .. |>.mpr hu.1, hu.2⟩
  · intro _ _ _ _ heq
    obtain ⟨hinj, _⟩ := Function.bijective_iff_has_inverse.mpr ⟨φ.invFun, φ.left_inv, φ.right_inv⟩
    exact hinj heq
  · intro u hu
    simp only [coe_inter, coe_neighborFinset, coe_image, Set.mem_inter_iff, mem_neighborSet,
      Set.mem_image, SetLike.mem_coe] at hu ⊢
    obtain ⟨hvu, ⟨w, hw, hwu⟩⟩ := hu
    refine ⟨w, ⟨?_, hw⟩, hwu⟩
    refine φ.map_rel_iff'.mp ?_
    simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv] at hvu hwu ⊢
    exact hwu ▸ hvu

lemma eq_of_degree_eq_one {u v w : V} [Fintype (G.neighborSet u)]
    (huv : G.Adj u v) (huw : G.Adj u w) (hdu : G.degree u = 1) :
    v = w :=
  degree_eq_one_iff_existsUnique_adj.mp hdu |>.unique huv huw

lemma one_le_degree_of_adj {u v : V} (huv : G.Adj u v) [Fintype (G.neighborSet u)] :
    1 ≤ G.degree u := by
  rw [← card_singleton v]
  refine card_le_card ?_
  simp only [singleton_subset_iff, mem_neighborFinset, huv]

lemma one_le_degree_of_adj' {u v : V} (huv : G.Adj v u) [Fintype (G.neighborSet u)] :
    1 ≤ G.degree u := by
  exact one_le_degree_of_adj huv.symm

lemma one_le_degree_of_mem_neighborFinset {u v : V} [Fintype (G.neighborSet u)]
    (huv : v ∈ G.neighborFinset u) :
    1 ≤ G.degree u := by
  rw [← card_singleton v]
  refine card_le_card ?_
  simp only [singleton_subset_iff, huv]

lemma one_le_degree_of_mem_neighborFinset' {u v : V}
    [Fintype (G.neighborSet u)] [Fintype (G.neighborSet v)] (huv : u ∈ G.neighborFinset v) :
    1 ≤ G.degree u := by
  exact one_le_degree_of_mem_neighborFinset <| mem_neighborFinset_symm huv

lemma one_le_degree_of_mem_N2 [DecidableEq V] [G.LocallyFinite]
    {v : V} {F : Finset V} (hv : v ∈ G.N2_of_Finset F) [Fintype (G.neighborSet v)] :
    1 ≤ G.degree v := by
  obtain ⟨_, _, _, _, h, _⟩ := mem_N2_of_Finset_iff.mp hv |>.2.2
  exact one_le_degree_of_adj h

lemma one_le_degree_of_walk_begin {u v : V} (hunev : u ≠ v) (w : G.Walk u v)
    [Fintype (G.neighborSet u)] :
    1 ≤ G.degree u := by
  match w with
  | Walk.nil => grind only
  | Walk.cons h _ => exact one_le_degree_of_adj h

lemma one_le_degree_of_walk_end {u v : V} (hunev : u ≠ v) (w : G.Walk u v)
    [Fintype (G.neighborSet v)] :
    1 ≤ G.degree v := by
  exact one_le_degree_of_walk_begin hunev.symm w.reverse

lemma card_connectedComponent_at_least_deg_plus_one {v : V}
    [Fintype (G.neighborSet v)] [Fintype (G.connectedComponentMk v)] :
    G.degree v + 1 ≤ #(G.connectedComponentMk v).supp.toFinset := by
  classical
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
