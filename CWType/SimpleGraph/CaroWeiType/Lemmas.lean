import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

import CWType.SimpleGraph.CaroWeiType.Basic

open Finset

namespace CaroWeiType

lemma add_congr {a b c d : ℝ} (h₁ : a = c) (h₂ : b = d) :
    a + b = c + d := by
  have hobj1 := add_right_inj a |>.mpr h₂
  have hobj2 := add_left_inj d |>.mpr h₁
  exact hobj1.trans hobj2

lemma sum_const' {ι : Type*} {f : ι → ℝ} {c : ℝ} (X : Finset ι) (h : ∀ x ∈ X, f x = c) :
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

@[simp]
lemma le_add_one {x : ℝ} : x ≤ x + 1 :=
  le_of_lt <| lt_add_one _

@[simp]
lemma add_one_pos {n : ℕ} : 0 < n + (1 : ℝ) := by
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_pos]
  exact Nat.zero_lt_succ _

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
  exact Nat.pos_of_neZero _

lemma p_and_p_implies {p q : Prop} : (p → (p ∧ q)) ↔ (p → q) :=
  ⟨fun h hp ↦ h hp |>.2, fun hpq hp ↦ ⟨hp, hpq hp⟩⟩

lemma p_imp_q_imp_p {p q : Prop} : p → q → p :=
  fun h _ ↦ h

lemma not_p_of_p_imp_false {p : Prop} : (p → False) → ¬p :=
  fun h hp ↦ h hp

variable {α : Type*}

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
    · simp_all only [ne_eq, not_false_eq_true]
    · simp_all only [ne_eq, mem_sdiff, mem_singleton, not_false_eq_true]
    · intro this
      let contr := this ▸ (mem_sdiff.mp <| hf'₁ _ hif').2
      simp at contr
    · have hkn : k = n := by exact Nat.eq_of_lt_succ_of_not_lt hk hif
      have hk'n : k' = n := by exact Nat.eq_of_lt_succ_of_not_lt hk' hif'
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
  · refine hf₂ 0 1 (Nat.zero_lt_of_lt h) (Nat.lt_of_succ_le h) (by simp)

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

lemma singleton_inter_eq_empty_iff {s : Finset α} {x : α} :
    ({x} ∩ s) = ∅ ↔ x ∉ s := by
  constructor
  · exact fun h hxs ↦ notMem_empty _ <| h ▸ mem_inter.mpr ⟨mem_singleton.mpr rfl, hxs⟩
  · intro hx
    ext
    simp only [hx, not_false_eq_true, singleton_inter_of_notMem, notMem_empty]

lemma disjoint_of_sdiff {X Y Z : Finset α} (h : X ⊆ Y \ Z) :
    X ∩ Z = ∅ := by
  ext x
  simp only [mem_inter, notMem_empty, iff_false, not_and]
  exact fun hx ↦ mem_sdiff.mp (h hx) |>.2

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

lemma pair_subset_of_mem_of_mem {x y : α} {s : Finset α}
    (hx : x ∈ s) (hy : y ∈ s) : {x, y} ⊆ s := by
  refine subset_of_eq_of_subset ?_ <| triplet_subset_of_mem_of_mem_of_mem hx hx hy
  simp only [mem_insert, mem_singleton, true_or, insert_eq_of_mem]

lemma card_triplet {x y z : α}
    (hxy : x ≠ y) (hz : z ∉ ({x, y} : Finset _)) :
    #{x, y, z} = 3 := by
  have : ({z, x, y} : Finset _) = {x, y, z} := by grind
  rw [← this]
  rw [card_insert_of_notMem hz, card_insert_of_notMem (notMem_singleton.mpr hxy), card_singleton]

lemma card_triplet' {x y z : α}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    #{x, y, z} = 3 :=
  card_triplet hxy (by grind)

lemma triplet_eq (x y z : α) : ({x, y, z} : Finset α) = {x, z, y} := by
  grind

lemma one_lt_card_iff_exists_a_b {s : Finset α} :
    1 < #s ↔ ∃ x y, {x, y} ⊆ s ∧ x ≠ y := by
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := nonempty_def.mp <| card_pos.mp <| Nat.zero_lt_of_lt hs
    obtain ⟨y, hy⟩ := nonempty_def.mp <| sdiff_nonempty_of_card_lt_card ((card_singleton x) ▸ hs)
    refine ⟨x, y, ?_, ?_⟩
    · exact pair_subset_of_mem_of_mem hx (mem_sdiff.mp hy |>.1)
    · exact Ne.symm <| notMem_singleton |>.mp <| mem_sdiff.mp hy |>.2
  · intro ⟨x, y, hxy, hxney⟩
    exact lt_of_lt_of_le Nat.one_lt_two ((card_pair hxney) ▸ card_le_card hxy)

lemma pair_eq {a b x y : α} (hab : a ≠ b)
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

lemma sorted_pair {β : Type*} [LinearOrder β] (f : α → β) (x y : α) :
    ∃ a b, ({a, b} : Finset _) = {x, y} ∧ f a ≤ f b :=
  if h : f x ≤ f y then
    ⟨x, y, rfl, h⟩
  else
    ⟨y, x, pair_comm .., le_of_not_ge h⟩

private lemma sorted_finset {s : Finset α} (k : ℕ) [NeZero k]
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

lemma pairwise_ne_of_triplet {x y z : α}
    (h : #({x, y, z} : Finset _) = 3) : x ≠ y ∧ x ≠ z ∧ y ≠ z := by
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

lemma ne_of_mem_finset_empty_inter
    {x y : α} (s t : Finset α)
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

lemma card_setminus_singleton {s : Finset α} {x : α}
    (h : x ∈ s) : #(s \ {x}) = #s - 1 := by
  rw [card_sdiff, singleton_inter_of_mem h, card_singleton]

lemma card_setminus_singleton' {n : ℕ} {s : Finset α} {x : α}
    (hx : x ∈ s) (hcard : s.card = n + 1) : #(s \ {x}) = n := by
  rw [card_setminus_singleton hx, hcard]
  exact Nat.add_sub_self_right ..

end CaroWeiType

open SimpleGraph
open CaroWeiType

namespace SimpleGraph

private noncomputable instance {α : Type*} {s t : Set α} [Fintype s] [Fintype t] :
    Fintype ((s ∪ t) : Set _) := by
  classical
  exact Set.fintypeUnion s t

variable {V : Type*}

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

lemma mem_neighborFinset_symm
    {u v : V} [Fintype (G.neighborSet u)] [Fintype (G.neighborSet v)] :
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

theorem deleteIncidenceSet_notAdj {v w : V} :
    ¬(G.deleteIncidenceSet v).Adj v w := by
  simp only [deleteIncidenceSet, deleteEdges_adj, mem_incidenceSet, and_not_self, not_false_eq_true]

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

lemma closed_neighborFinset_of_singleton_eq [DecidableEq V] [G.LocallyFinite]
    {v : V} : G.closed_neighborFinset_of_Finset {v} = G.neighborFinset v ∪ {v} := by
  ext w
  simp only [closed_neighborFinset_of_Finset, singleton_biUnion, singleton_union, mem_insert,
    mem_neighborFinset, union_singleton]

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

lemma N2_inter_Nle1_empty [DecidableEq V] [G.LocallyFinite] {s : Finset V} :
    G.N2_of_Finset s ∩ G.closed_neighborFinset_of_Finset s = ∅ :=
  disjoint_of_sdiff (subset_refl _)

lemma Nle1_inter_N2_empty [DecidableEq V] [G.LocallyFinite] {s : Finset V} :
    G.closed_neighborFinset_of_Finset s ∩ G.N2_of_Finset s = ∅ :=
  inter_comm (G.closed_neighborFinset_of_Finset s) _ ▸ N2_inter_Nle1_empty

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

lemma deleteIncidencesOf_degree_le {s : Finset V} {v : V}
    [Fintype ((G.deleteIncidencesOf s).neighborSet v)] [Fintype (G.neighborSet v)] :
    (G.deleteIncidencesOf s).degree v ≤ G.degree v :=
  degree_le_of_le deleteIncidencesOf_le

lemma deleteIncidencesOf_singleton_eq_deleteIncidenceSet (v : V) :
    G.deleteIncidencesOf {v} = G.deleteIncidenceSet v := by
  simp [deleteIncidencesOf, deleteIncidenceSet_le]

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

lemma adj_of_deleteIncidencesOf_adj
    {u v : V} {s : Finset V} (huv : (G.deleteIncidencesOf s).Adj u v) :
    G.Adj u v :=
  deleteIncidencesOf_le huv

lemma deleteIncidencesOf_adj_iff_of_notMem
    {u v : V} {s : Finset V} (hu : u ∉ s) (hv : v ∉ s) :
    G.Adj u v ↔ (G.deleteIncidencesOf s).Adj u v :=
  ⟨deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj hu hv, adj_of_deleteIncidencesOf_adj⟩

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

lemma deleteIncidencesOf_support_subset {s : Finset V} :
    (G.deleteIncidencesOf s).support ⊆ G.support \ s := by
  intro u hu
  obtain ⟨v, hv⟩ := mem_support _ |>.mp hu
  refine (Set.mem_diff u).mpr ⟨?_, ?_⟩
  · exact (mem_support G).mpr ⟨v, adj_of_deleteIncidencesOf_adj hv⟩
  · exact deleteIncidencesOf_notadj |>.mt <| not_not.mpr hv

lemma deleteIncidencesOf_le_mono {V : Type*} {G₁ G₂ : SimpleGraph V} {s : Finset V}
    (hle : G₁ ≤ G₂) : G₁.deleteIncidencesOf s ≤ G₂.deleteIncidencesOf s := by
  intro u v
  simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, inf_adj, iInf_adj,
    deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq, and_imp]
  intro h₁uv h hne
  simp only [hle h₁uv, forall_const, true_and, hne, not_false_eq_true, and_true]
  exact fun _ hw ↦  h _ |>.1 hw |>.2 h₁uv

end SimpleGraph

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
  have Nv_subs_X : G.neighborFinset v ⊆ X :=
    subset_trans neighborFinset_subset_support (Set.toFinset_subset.mpr hX)
  suffices f (G.degree v)
      ≤ ∑ x ∈ G.neighborFinset v, (f ((G.deleteIncidenceSet v).degree x) - f (G.degree x)) by
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
          + ∑ x ∈ G.neighborFinset v, (f (G.degree x) - f ((G.deleteIncidenceSet v).degree x)) := by
        simp only [sum_sub_distrib, add_add_sub_cancel]
      _ = ∑ x ∈ (X \ G.neighborFinset v) \ {v}, f ((G.deleteIncidenceSet v).degree x)
          + ∑ x ∈ G.neighborFinset v, f ((G.deleteIncidenceSet v).degree x)
          + f (G.degree v)
          + ∑ x ∈ G.neighborFinset v, (f (G.degree x) - f ((G.deleteIncidenceSet v).degree x)) := by
        linarith
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
          | Or.inr h => exact ⟨mem_of_subset_of_adj hX h, h.ne'⟩
        have cap : ((X \ G.neighborFinset v) \ {v}) ∩ G.neighborFinset v = ∅ := by
          rw [sdiff_inter_right_comm]
          refine eq_empty_of_subset_empty <| sdiff_subset_of_subset
            <| subset_of_eq <| sdiff_inter_self ..
        let hobj := cup ▸ cap ▸
          @sum_union_inter _ ℝ ((X \ G.neighborFinset v) \ {v}) (G.neighborFinset v)
          _ (fun w ↦ f ((G.deleteIncidenceSet v).degree w)) _
        simp only [sum_empty, add_zero] at hobj
        exact hobj
      _ = (∑ x ∈ X \ {v}, f ((G.deleteIncidenceSet v).degree x))
          + (f (G.degree v)
          + ∑ x ∈ G.neighborFinset v,
            (f (G.degree x) - f ((G.deleteIncidenceSet v).degree x))) := by
        linarith
    refine (add_le_iff_nonpos_right
      <| ∑ x ∈ X \ {v}, f ((G.deleteIncidenceSet v).degree x)).mpr ?_
    exact le_neg_iff_add_nonpos_right.mp
      <| le_trans this (by simp only [sum_sub_distrib, neg_sub, le_refl])
  calc ∑ x ∈ G.neighborFinset v, (f ((G.deleteIncidenceSet v).degree x) - f (G.degree x))
    _ = ∑ x ∈ G.neighborFinset v, (f (G.degree x - 1) - f (G.degree x)) := by
      refine sum_congr rfl ?_
      intro x hx
      simp only [sub_left_inj]
      exact congrArg _ <| deleteIncidenceSet_degree hx
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
      suffices {w | x ≠ w}.toFinset = univ \ {x} by
        simp [this, card_sdiff, inter_univ, card_singleton, card_univ, Fintype.card_fin,
          add_tsub_cancel_right]
      ext w
      simp only [ne_eq, Set.toFinset_setOf, mem_filter, mem_univ, true_and, mem_sdiff,
        mem_singleton, ne_comm]
    _ = (n + 1) * f n := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

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
  rw [degree]
  refine congrArg _ ?_
  ext y
  constructor
  · intro hy
    simp_all only [mem_neighborFinset, mem_inter, true_and]
    exact hX <| G.mem_support.mpr ⟨_, hy.symm⟩
  · exact fun hy ↦ mem_inter.mp hy |>.1

lemma degree_eq' [DecidableEq V] (v : V) [G.LocallyFinite] [Fintype G.support] :
    G.degree v = (G.neighborFinset v ∩ G.support.toFinset).card := by
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

lemma degree_in_deleteIncidenceSet' [DecidableEq V] {v : V} (s t : Finset V)
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
