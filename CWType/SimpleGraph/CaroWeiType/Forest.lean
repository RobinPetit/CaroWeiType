import Mathlib

import Mathlib.Combinatorics.SimpleGraph.Acyclic

import CWType.SimpleGraph.CaroWeiType.Lemmas
import CWType.SimpleGraph.CaroWeiType.Degenerate

namespace SimpleGraph

open Finset

def InducesForest {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) : Prop :=
  G.IsDegenerateSet 1 s

def InducesLinearForest {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) : Prop :=
  G.InducesForest s ∧ ∀ x ∈ s, (G.neighborFinset x ∩ s).card ≤ 2

def InducesCaterpillar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) : Prop :=
  G.InducesLinearForest <| s \ {x ∈ s | (G.neighborFinset x ∩ s).card = 1}

def degree_in {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) (x : Fin n) : ℕ :=
  (G.neighborFinset x ∩ s).card

lemma InducesForest_mono {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n))
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (s : Finset (Fin n)) (hle : G₁ ≤ G₂) (h : G₂.InducesForest s) : G₁.InducesForest s := by
  simp only [InducesForest] at h ⊢
  exact IsDegenerateSet_mono G₁ G₂ hle 1 s h

lemma InducesForest_mono' {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s₁ s₂ : Finset (Fin n)) (hs : s₁ ∩ s₂ = ∅)
    (h : (G.deleteIncidencesOf s₂).InducesForest s₁) :
    G.InducesForest s₁ := by
  exact IsDegenerateSet_mono' G 1 s₁ s₂ hs h

namespace CaroWeiType

namespace ABC

@[ext]
structure Tripartition (n : ℕ) where
  A : Fin n → Prop
  B : Fin n → Prop
  C : Fin n → Prop
  sound : ∀ x, ¬(A x ∧ B x) ∧ ¬(A x ∧ C x) ∧ ¬(B x ∧ C x)
  -- cover : ∀ x, (A x ∨ B x ∨ C x)

namespace Tripartition

instance {n : ℕ} : Membership (Fin n) (Tripartition n) :=
  ⟨fun ABC x ↦ ABC.A x ∨ ABC.B x ∨ ABC.C x⟩

noncomputable def toFinset {n : ℕ} (ABC : Tripartition n) : Finset (Fin n) := by
  classical
  exact {x | x ∈ ABC}

@[simp 10]
lemma mem_tripartition_toFinset {n : ℕ} (ABC : Tripartition n) (x : Fin n) :
    x ∈ ABC ↔ x ∈ ABC.toFinset := by
  simp [toFinset]

@[simp]
lemma mem_tripartition_iff {n : ℕ} (ABC : Tripartition n) (x : Fin n) :
    x ∈ ABC ↔ ABC.A x ∨ ABC.B x ∨ ABC.C x := by
  rfl

def sdiff {n : ℕ} (ABC : Tripartition n) (s : Finset (Fin n)) : Tripartition n where
  A := fun v ↦ ABC.A v ∧ v ∉ s
  B := fun v ↦ ABC.B v ∧ v ∉ s
  C := fun v ↦ ABC.C v ∧ v ∉ s
  sound x := by
    obtain ⟨h₁, h₂, h₃⟩ := ABC.sound x
    simp_all

infixl:50 " \\ " => sdiff

@[simp 100]
lemma sdiff_empty {n : ℕ} (ABC : Tripartition n) : (ABC \ ∅) = ABC := by
  ext <;> simp [Tripartition.sdiff]

@[simp 10]
lemma sdiff_eq {n : ℕ} (ABC : Tripartition n) (W : Finset (Fin n)) :
    (ABC \ W) = (ABC \ (W ∩ ABC.toFinset)) := by
  ext w <;> { simp [sdiff, toFinset]; grind }

noncomputable def card {n : ℕ} (ABC : Tripartition n) : ℕ := ABC.toFinset.card

@[simp]
lemma Tripartition_sdiff_notMem {n : ℕ} (ABC : Tripartition n) (s : Finset (Fin n)) :
    ∀ x ∈ s, x ∉ ABC \ s := by
  intro x hx
  simp [sdiff, hx]

@[simp]
lemma toFinset_mono {n : ℕ} {ABC : Tripartition n} {s : Finset (Fin n)} :
    (ABC \ s).toFinset ⊆ ABC.toFinset := by
  simp only [toFinset, sdiff, mem_tripartition_iff]
  intro x hx
  simp only [mem_tripartition_iff, mem_filter, mem_univ, true_and] at hx ⊢
  grind

end Tripartition

def respects {n : ℕ} (s : Finset (Fin n)) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) : Prop :=
  ∀ w ∈ s,
    (ABC.A w → G.degree_in s w ≤ 2)
    ∧ (ABC.B w → G.degree_in s w ≤ 1)
    ∧ (ABC.C w → G.degree_in s w = 0)

@[simp]
noncomputable def fA (d : ℕ) : ℝ :=
  if d = 0 then 1
  else if d = 1 then 5 / (6 : ℝ)
  else 2 / (d + 1 : ℝ)

@[simp]
noncomputable def fB (d : ℕ) : ℝ :=
  if d = 0 then 1
  else if d = 1 then 5 / (6 : ℝ)
  else if d = 2 then 1 / (3 : ℝ)
  else 4 / (3 * (d + 1 : ℝ))

@[simp]
noncomputable def fC (d : ℕ) : ℝ :=
  if d = 0 then 1
  else if d = 1 ∨ d = 2 then 1 / (3 : ℝ)
  else 2 / (3 * (d + 1 : ℝ))

lemma fA_decreasing {d d' : ℕ} (h : d ≤ d') : fA d' ≤ fA d := by
  if heq : d = d' then exact le_of_eq (heq ▸ rfl) else ?_
  simp only [fA]
  split_ifs
  any_goals grind
  · ring_nf
    calc (1 + d' : ℝ)⁻¹ * 2
      _ ≤ (1 + 2 : ℝ)⁻¹ * 2 := by
        simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
        refine inv_anti₀ (by grind) ?_
        simp only [add_le_add_iff_left, Nat.ofNat_le_cast]
        grind
      _ ≤ 1 := by grind
  · ring_nf
    calc (1 + d' : ℝ)⁻¹ * 2
      _ ≤ (1 + 2 : ℝ)⁻¹ * 2 := by
        simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
        refine inv_anti₀ (by grind) ?_
        simp only [add_le_add_iff_left, Nat.ofNat_le_cast]
        grind
      _ ≤ 5 / 6 := by grind
  · ring_nf
    simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
    refine inv_anti₀ (by grind) (by simp [h])

lemma fB_decreasing {d d' : ℕ} (h : d ≤ d') : fB d' ≤ fB d := by
  have H : 3 ≤ d' → fB d' ≤ 1 / (3 : ℝ) := by
    simp only [fB, one_div]
    intro hd'
    split_ifs
    any_goals grind
    calc 4 / (3 * (d' + 1 : ℝ))
      _ = 4 / (3 : ℝ) / (d' + 1 : ℝ) := by grind
      _ ≤ 4 / (3 : ℝ) / (3 + 1 : ℝ) := by
        ring_nf
        have h : (1 + d' : ℝ)⁻¹ * (4 / 3) = (1 + d' : ℝ)⁻¹ * 4 * 3⁻¹ := by grind
        have _ : 3⁻¹ = 1 / (3 : ℝ) := by exact inv_eq_one_div 3
        rw [h, inv_eq_one_div 3]
        simp only [one_div, inv_pos, Nat.ofNat_pos, mul_le_iff_le_one_left, ge_iff_le]
        suffices (1 + d' : ℝ)⁻¹ ≤ 4⁻¹ by grind
        refine inv_anti₀ four_pos ?_
        calc (4 : ℝ)
          _ = (1 + 3 : ℝ) := by grind
          _ ≤ (1 + d' : ℝ) := by
            simp only [add_le_add_iff_left, Nat.ofNat_le_cast]
            exact Nat.succ_le_of_lt hd'
      _ ≤ (3 : ℝ)⁻¹ := by grind
  simp only [fB] at H ⊢
  split_ifs
  any_goals grind
  ring_nf
  simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀, ge_iff_le]
  refine inv_anti₀ (by grind) (by simp [h])

lemma fC_decreasing {d d' : ℕ} (h : d ≤ d') : fC d' ≤ fC d := by
  simp only [fC]
  split_ifs
  any_goals grind
  · ring_nf
    have h' : 3 ≤ d' := by grind
    calc (3 + d' * 3 : ℝ)⁻¹ * 2
      _ ≤ (3 + 3 * 3 : ℝ)⁻¹ * 2 := by
        simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
        refine inv_anti₀ (by grind) (by simp [h'])
      _ ≤ 1 := by grind
  · ring_nf
    simp only [one_div]
    have h' : 3 ≤ d' := by grind
    calc (3 + d' * 3 : ℝ)⁻¹ * 2
      _ ≤ (3 + 3 * 3 : ℝ)⁻¹ * 2 := by
        simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
        refine inv_anti₀ (by grind) (by simp [h'])
      _ ≤ 3⁻¹ := by grind
  · ring_nf
    simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
    refine inv_anti₀ (by grind) (by simp [h])

@[simp]
noncomputable def f {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    (v : Fin n) : ℝ := by
  classical
  if ABC.A v then
    exact fA (G.degree v)
  else if ABC.B v then
    exact fB (G.degree v)
  else if ABC.C v then
    exact fC (G.degree v)
  else
    exact 0

lemma f_eq_in_sdiff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    {v w : Fin n} (hne : v ≠ w) :
    f G (ABC \ {v}) w = f G ABC w := by
  have hw' : w ∉ ({v} : Finset _) := not_iff_not.mpr mem_singleton |>.mpr hne.symm
  have : ABC.A w ↔ (ABC \ {v}).A w := ⟨fun h ↦ ⟨h, hw'⟩, fun ⟨h, _⟩ ↦ h⟩
  have : ABC.B w ↔ (ABC \ {v}).B w := ⟨fun h ↦ ⟨h, hw'⟩, fun ⟨h, _⟩ ↦ h⟩
  have : ABC.C w ↔ (ABC \ {v}).C w := ⟨fun h ↦ ⟨h, hw'⟩, fun ⟨h, _⟩ ↦ h⟩
  simp only [f]
  split_ifs
  any_goals grind

lemma f_pos_of_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    (v : Fin n) : v ∈ ABC → 0 < f G ABC v := by
  have _ : (0 : ℝ) ≤ G.degree v := Nat.cast_nonneg' _
  intro h
  rcases ABC.mem_tripartition_iff _ |>.mp h with hA | hB | hC
  · simp only [f, hA, ↓reduceDIte, fA]
    split_ifs
    any_goals grind
    ring_nf
    simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_right, inv_pos]
    grind [Nat.pos_of_neZero]
  · have hA' : ¬ABC.A v := by grind [ABC.sound]
    simp only [f, hA', ↓reduceDIte, hB, fB, one_div, gt_iff_lt]
    split_ifs
    any_goals grind
    ring_nf
    simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_right, inv_pos]
    grind
  · have hA' : ¬ABC.A v := by grind [ABC.sound]
    have hB' : ¬ABC.B v := by grind [ABC.sound]
    simp only [f, hA', ↓reduceDIte, hB', hC, fC, one_div, gt_iff_lt]
    split_ifs
    any_goals grind
    ring_nf
    simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_right, inv_pos]
    grind

lemma f_eq_zero_of_notMem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n)
    (v : Fin n) : v ∉ ABC → 0 = f G ABC v := by
  intro hv
  simp only [Tripartition.mem_tripartition_iff, not_or] at hv
  obtain ⟨hvA, hvB, hvC⟩ := hv
  simp [f, hvA, hvB, hvC]

@[simp]
noncomputable def γ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    (v : Fin n) : ℝ := by
  classical
  if ABC.A v      then exact fA (G.degree v - 1) - fA (G.degree v)
  else if ABC.B v then exact fB (G.degree v - 1) - fB (G.degree v)
  else if ABC.C v then exact fC (G.degree v - 1) - fC (G.degree v)
  else                 exact 0

lemma γ_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    {v : Fin n} : 0 ≤ γ G ABC v := by
  have h : G.degree v - 1 ≤ G.degree v := Nat.sub_le ..
  simp only [γ, dite_eq_ite]
  split_ifs
  any_goals grind [fA_decreasing h, fB_decreasing h, fC_decreasing h]

lemma degree_deleteIncidencesOf_neighbor {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {v w : Fin n} (hw : G.Adj v w) :
    G.degree w = (G.deleteIncidencesOf {v}).degree w + 1 := by
  suffices G.neighborFinset w = (G.deleteIncidencesOf {v}).neighborFinset w ∪ {v} by
    simp only [degree, congrArg card this]
    calc #((G.deleteIncidencesOf {v}).neighborFinset w ∪ {v})
      _ = #((G.deleteIncidencesOf {v}).neighborFinset w ∪ {v})
        + #((G.deleteIncidencesOf {v}).neighborFinset w ∩ {v}) := by
        simp only [union_singleton, Nat.left_eq_add, card_eq_zero]
        ext x
        simp [deleteIncidencesOf, deleteIncidenceSet, incidenceSet]
      _ = #((G.deleteIncidencesOf {v}).neighborFinset w) + #({v} : Finset _) := by
        exact card_union_add_card_inter ..
      _ = #((G.deleteIncidencesOf {v}).neighborFinset w) + 1 := by
        simp
  ext x
  simp only [mem_neighborFinset, deleteIncidencesOf, deleteIncidenceSet, incidenceSet,
    union_singleton, mem_insert, mem_singleton, iInf_iInf_eq_left, inf_adj, deleteEdges_adj,
    Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, and_self_left]
  constructor
  · intro hwx
    cases Classical.em <| x = v with
    | inl h => exact Or.inl h
    | inr h =>
        refine Or.inr ?_
        simp only [hwx, hw.ne, not_false_eq_true, Ne.symm h, and_self, imp_self]
  · intro h
    cases h with
    | inl h => exact h ▸ hw.symm
    | inr h => exact h.1

lemma f_deleteIncidencesOf_singleton {n : ℕ} (ABC : Tripartition n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {v w : Fin n} (hw : G.Adj v w) :
    f (G.deleteIncidencesOf {v}) (ABC \ {v}) w = f G ABC w + γ G ABC w := by
  simp only [f, Tripartition.sdiff_eq, inter_assoc, inter_self, fA, fB, one_div, fC, dite_eq_ite, γ,
    Nat.pred_eq_succ_iff, zero_add, Nat.reduceAdd]
  rw [degree_deleteIncidencesOf_neighbor G hw]
  if hA : (ABC \ {v}).A w then
    simp_all only [Tripartition.sdiff_eq, inter_assoc, inter_self, ↓reduceIte, hA.left,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.add_eq_right, Nat.cast_add, Nat.cast_one,
      add_tsub_cancel_right, Nat.reduceEqDiff, add_sub_cancel]
  else if hB : (ABC \ {v}).B w then
    have hB' : ABC.B w := hB.left
    have hA' : ¬ABC.A w := fun h ↦ ABC.sound w |>.1 ⟨h, hB'⟩
    simp_all
  else if hC : (ABC \ {v}).C w then
    have hC' : ABC.C w := hC.left
    have hB' : ¬ABC.B w := fun h ↦ ABC.sound w |>.2.2 ⟨h, hC'⟩
    have hA' : ¬ABC.A w := fun h ↦ ABC.sound w |>.2.1 ⟨h, hC'⟩
    simp_all
  else
    have hA' : ¬ABC.A w := fun this ↦ hA <| by simp [Tripartition.sdiff, this, hw.ne']
    have hB' : ¬ABC.B w := fun this ↦ hB <| by simp [Tripartition.sdiff, this, hw.ne']
    have hC' : ¬ABC.C w := fun this ↦ hC <| by simp [Tripartition.sdiff, this, hw.ne']
    simp_all

@[simp]
noncomputable def eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) : ℝ :=
  ∑ v ∈ ABC.toFinset, f G ABC v

private lemma eval_mono {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n))
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hle : G₁ ≤ G₂)
    (ABC : Tripartition n) :
    eval G₂ ABC ≤ eval G₁ ABC := by
  unfold eval
  refine sum_le_sum ?_
  intro w hw
  simp only [Tripartition.toFinset, Tripartition.mem_tripartition_iff, mem_filter, mem_univ,
    true_and] at hw
  rcases hw with hA | hB | hC
  · simp only [f, hA, ↓reduceDIte, fA]
    exact fA_decreasing <| degree_le_of_le hle
  · have hnA : ¬ABC.A w := by grind [ABC.sound]
    simp only [f, hnA, ↓reduceDIte, hB, fB, one_div, ge_iff_le]
    let hobj := @fB_decreasing (G₁.degree w) (G₂.degree w) <| degree_le_of_le hle
    simp only [fB, one_div] at hobj
    exact hobj
  · have hnA : ¬ABC.A w := by grind [ABC.sound]
    have hnB : ¬ABC.B w := by grind [ABC.sound]
    have hC : ABC.C w := by grind
    simp only [f, hnA, ↓reduceDIte, hnB, hC, fC, one_div, ge_iff_le]
    let hobj := @fC_decreasing (G₁.degree w) (G₂.degree w) <| degree_le_of_le hle
    simp only [fC, one_div] at hobj
    exact hobj

lemma eval_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (W : Finset (Fin n)) (hW : W ∩ ABC.toFinset ≠ ∅) :
    eval G (ABC \ W) < eval G ABC := by
  unfold eval
  calc ∑ v ∈ (ABC \ W).toFinset, f G (ABC \ W) v
    _ = ∑ v ∈ (ABC \ W).toFinset, f G ABC v := by
      refine sum_congr rfl ?_
      intro x hx
      simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_tripartition_iff,
        mem_filter, mem_univ, true_and, f, fA, fB, one_div, fC, dite_eq_ite] at hx ⊢
      if hA : ABC.A x then
        have hA' : (ABC \ W).A x := by simp [Tripartition.sdiff]; grind
        simp only [hA, true_and, ite_not, ↓reduceIte, ite_eq_right_iff]
        grind
      else if hB : ABC.B x then
        have hB' : (ABC \ W).B x := by simp [Tripartition.sdiff]; grind
        simp only [hA, false_and, ↓reduceIte, hB, true_and, ite_not, ite_eq_right_iff]
        grind
      else grind
    _ < ∑ v ∈ (ABC \ W).toFinset, f G ABC v + ∑ v ∈ (W ∩ ABC.toFinset), f G ABC v := by
      simp only [Tripartition.sdiff_eq, inter_assoc, inter_self, lt_add_iff_pos_right]
      suffices ∃ w, w ∈ W ∩ ABC.toFinset by
        obtain ⟨w, hw⟩ := this
        calc 0
          _ < f G ABC w :=
            f_pos_of_mem G ABC w <| (ABC.mem_tripartition_toFinset w).mpr (mem_inter.mp hw).2
          _ = ∑ v ∈ ((W ∩ ABC.toFinset) ∩ {w}), f G ABC v := by
            have this : ((W ∩ ABC.toFinset) ∩ {w}) = {w} := by grind
            rw [this]
            exact Eq.symm <| sum_singleton _ _
          _ ≤ ∑ v ∈ ((W ∩ ABC.toFinset) ∩ {w}), f G ABC v
            + ∑ v ∈ (W ∩ ABC.toFinset) \ {w}, f G ABC v := by
            simp only [inter_assoc, le_add_iff_nonneg_right]
            refine sum_nonneg' ?_
            intro v
            if hv : v ∈ ABC then
              exact le_of_lt <| f_pos_of_mem G ABC v hv
            else
              exact le_of_eq <| f_eq_zero_of_notMem G ABC v hv
          _ = ∑ v ∈ (W ∩ ABC.toFinset), f G ABC v := sum_inter_add_sum_diff ..
      grind
    _ = ∑ v ∈ ABC.toFinset, f G ABC v := by
      have _ {s t : Finset (Fin n)} : s ∩ t = t ∩ s := by exact inter_comm s t
      have h' : (ABC \ W).toFinset = ABC.toFinset \ W := by
        ext
        simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_tripartition_iff,
          mem_filter, mem_univ, true_and, mem_sdiff]
        grind
      rw [add_comm, inter_comm, h']
      exact Finset.sum_inter_add_sum_diff ..


@[simp, reducible]
private def Objective {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) : Prop :=
  ∃ s : Finset (Fin n),
    s ⊆ ABC.toFinset ∧ G.InducesLinearForest s ∧ respects s G ABC ∧ eval G ABC ≤ #s

private lemma Claim0 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (W : Finset (Fin n)) (hWABC' : W ∩ ABC.toFinset ≠ ∅)
    (h : eval G ABC ≤ eval (G.deleteIncidencesOf W) (ABC \ W))
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  have h' : (ABC \ W).card < ABC.card := by
    simp only [Tripartition.card, Tripartition.toFinset, Tripartition.mem_tripartition_iff]
    refine Finset.card_lt_card ⟨?_, ?_⟩
    · intro x
      simp only [Tripartition.sdiff, Tripartition.mem_tripartition_iff, mem_filter,
        mem_univ, true_and]
      grind
    · intro h
      obtain ⟨w, hw⟩ := @Classical.choice ↑(W ∩ ABC.toFinset) (Nonempty.to_subtype (by grind))
      simp only [mem_inter] at hw
      let hobj := h hw.2
      simp [Tripartition.sdiff] at hobj
      grind
  obtain ⟨s, ⟨hs1, hs2, hs3, hs4⟩⟩ := ih (G.deleteIncidencesOf W) (ABC \ W) h'
  have hsW : s ∩ W = ∅ := by
    simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_tripartition_iff] at hs1
    ext x
    simp only [mem_inter, notMem_empty, iff_false, not_and]
    intro hx
    let hobj := hs1 hx
    simp only [Tripartition.mem_tripartition_iff, mem_filter, mem_univ, true_and] at hobj
    grind
  refine ⟨s, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [Tripartition.toFinset, Tripartition.mem_tripartition_iff] at hs1 ⊢
    exact subset_trans hs1 Tripartition.toFinset_mono
  · exact InducesForest_mono' _ _ _ hsW hs2.1
  · intro x hx
    suffices #((G.deleteIncidencesOf W).neighborFinset x ∩ s) = #(G.neighborFinset x ∩ s) by
      exact this ▸ (hs2.2 x hx)
    refine congrArg _ ?_
    ext y
    simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_inter, mem_neighborFinset,
      inf_adj, iInf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and,
      not_or, ne_eq, and_congr_left_iff, and_iff_left_iff_imp]
    intro hy hxy
    refine ⟨fun z ↦ ⟨fun hz ↦ ⟨hxy, fun _ ↦ ?_⟩, hxy.ne⟩, hxy.ne⟩
    constructor <;> exact ne_of_mem_finset_empty_inter _ _ hsW (by simp [hx, hy]) hz |>.symm
  · simp only [respects] at hs3 ⊢
    intro w hw
    have heq : #((G.deleteIncidencesOf W).neighborFinset w ∩ s) = #(G.neighborFinset w ∩ s) := by
      refine congrArg _ ?_
      ext u
      constructor
      · intro hu
        simp only [deleteIncidencesOf, mem_inter, mem_neighborFinset, inf_adj, iInf_adj,
          ne_eq] at hu ⊢
        exact ⟨hu.1.1,  hu.2⟩
      · intro hu
        simp only [mem_inter, mem_neighborFinset, deleteIncidencesOf, deleteIncidenceSet,
          incidenceSet, inf_adj, iInf_adj, deleteEdges_adj, ne_eq] at hu ⊢
        refine ⟨⟨hu.1, ⟨fun v ↦ ⟨fun hv ↦ ⟨hu.1, ?_⟩, hu.1.ne⟩, hu.1.ne⟩⟩, hu.2⟩
        intro this
        simp only [Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff] at this
        rcases this.2 <;>
          { rename_i hv';
            have _ : v ∈ s ∩ W := by { subst hv'; simp [mem_inter, hv, hw, hu.2]; }; grind }
    have hwW : w ∉ W := by
      let hobj := hs1 hw
      simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_tripartition_iff,
        mem_filter, mem_univ, true_and] at hobj
      grind
    simp only [degree_in]
    refine ⟨?_, ?_, ?_⟩
    · exact fun hAw ↦ heq.symm ▸ (hs3 w hw).1   ⟨hAw, hwW⟩
    · exact fun hBw ↦ heq.symm ▸ (hs3 w hw).2.1 ⟨hBw, hwW⟩
    · exact fun hCw ↦ heq.symm ▸ (hs3 w hw).2.2 ⟨hCw, hwW⟩
  · exact le_trans h hs4

private lemma Claim1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (v : Fin n) (hv : v ∈ ABC) (hNv : G.neighborFinset v ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    f G ABC v ≤ ∑ w ∈ G.neighborFinset v, γ G ABC w → Objective G ABC := by
  intro h
  refine Claim0 G ABC {v} ?_ ?_ ih
  · suffices {v} ∩ ABC.toFinset = {v} by
      rw [this]
      exact singleton_ne_empty _
    simp [hv, Tripartition.toFinset]
  · calc eval G ABC
      _ = ∑ x ∈ (ABC \ {v}).toFinset, f G ABC x + f G ABC v := by
        have h : (ABC \ {v}).toFinset = ABC.toFinset \ {v} := by
          ext x
          simp [Tripartition.sdiff, Tripartition.toFinset]
          grind
        rw [h]
        have _ : f G ABC v = ∑ x ∈ {v}, f G ABC x := by
          exact Eq.symm (sum_singleton (f G ABC) v)
        rw [← sum_singleton (f G ABC) v]
        refine Eq.symm <| sum_sdiff ?_
        refine singleton_subset_iff.mpr ?_
        exact Tripartition.mem_tripartition_toFinset .. |>.mp hv
      _ = ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v, f G ABC x
        + ∑ x ∈ G.neighborFinset v, f G ABC x + f G ABC v := by
        simp only [add_left_inj]
        refine Eq.symm <| sum_sdiff ?_
        intro x hx
        have hxnev : x ≠ v := G.mem_neighborFinset .. |>.mp hx |>.ne'
        have hxABC : x ∈ ABC := Tripartition.mem_tripartition_toFinset .. |>.mpr <| hNv hx
        refine Tripartition.mem_tripartition_toFinset .. |>.mp ?_
        simp only [Tripartition.sdiff, mem_singleton, Tripartition.mem_tripartition_iff, hxnev,
          not_false_eq_true, and_true]
        exact Tripartition.mem_tripartition_iff .. |>.mpr hxABC
      _ = ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v, f G ABC x
        + (∑ x ∈ G.neighborFinset v, f G ABC x + f G ABC v) := by
          grind
      _ ≤ ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v, f G ABC x
        + (∑ x ∈ G.neighborFinset v, f G ABC x
        + ∑ x ∈ G.neighborFinset v, γ G ABC x) := by
          exact add_le_add_right (add_le_add_right h _) _
      _ = ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v, f G ABC x
        + ∑ x ∈ G.neighborFinset v, (f G ABC x + γ G ABC x) := by
          simp only [add_right_inj]
          exact Eq.symm <| sum_add_distrib
      _ = ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v, f G ABC x
        + ∑ x ∈ G.neighborFinset v, f (G.deleteIncidencesOf {v}) (ABC \ {v}) x := by
          simp only [add_right_inj]
          refine sum_congr rfl ?_
          intro x hx
          exact Eq.symm <| f_deleteIncidencesOf_singleton ABC G (G.mem_neighborFinset .. |>.mp hx)
      _ = ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v, f G (ABC \ {v}) x
        + ∑ x ∈ G.neighborFinset v, f (G.deleteIncidencesOf {v}) (ABC \ {v}) x := by
          simp only [add_left_inj]
          refine sum_congr rfl ?_
          intro x hx
          refine Eq.symm <| f_eq_in_sdiff G ABC ?_
          let hobj := mem_sdiff.mp hx |>.1
          simp [Tripartition.sdiff, Tripartition.toFinset] at hobj
          grind
      _ = ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v,
            f (G.deleteIncidencesOf {v}) (ABC \ {v}) x
        + ∑ x ∈ G.neighborFinset v, f (G.deleteIncidencesOf {v}) (ABC \ {v}) x := by
        simp only [add_left_inj]
        refine sum_congr rfl ?_
        intro x hx
        suffices (G.deleteIncidencesOf {v}).degree x = G.degree x by
          simp only [f, Tripartition.sdiff_eq, inter_assoc, inter_self, fA, fB, one_div, fC,
            dite_eq_ite, this]
        unfold degree
        refine congrArg _ ?_
        ext w
        simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_neighborFinset,
          mem_singleton, iInf_iInf_eq_left, inf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet,
          Sym2.mem_iff, not_and, not_or, and_self_left, and_iff_left_iff_imp, forall_self_imp]
        intro hxw
        constructor
        · simp [Tripartition.sdiff, Tripartition.toFinset] at hx
          grind
        · intro this
          subst this
          let hnotvx := (not_iff_not.mpr (G.mem_neighborFinset _ _)).mp <| mem_sdiff.mp hx |>.2
          exact hnotvx hxw.symm |>.elim
      _ = ∑ x ∈ (ABC \ {v}).toFinset, f (G.deleteIncidencesOf {v}) (ABC \ {v}) x := by
        rw [add_comm]
        let hobj := @sum_inter_add_sum_diff
          (Fin n) ℝ _ _ (ABC \ {v}).toFinset (G.neighborFinset v)
          (fun x ↦ f (G.deleteIncidencesOf {v}) (ABC \ {v}) x)
        have this : (ABC \ {v}).toFinset ∩ G.neighborFinset v = G.neighborFinset v := by
          ext w
          constructor
          · exact mem_of_mem_inter_right
          · intro hw
            simp only [Tripartition.toFinset, Tripartition.mem_tripartition_iff, mem_inter,
              mem_filter, mem_univ, true_and, hw, and_true, Tripartition.sdiff]
            have _ : w ∉ ({v} : Finset _) := by
              simp only [mem_neighborFinset, mem_singleton] at hw ⊢
              exact hw.ne'
            have _ : ABC.A w ∨ ABC.B w ∨ ABC.C w := by
              refine ABC.mem_tripartition_iff w |>.mp ?_
              exact ABC.mem_tripartition_toFinset w |>.mpr <| hNv hw
            grind
        rw [this] at hobj
        exact hobj

private lemma tmplemma (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (s : Finset ℕ) (x : s) :
    0 ≤ ∑ n ∈ s, f n := by exact sum_nonneg fun i a ↦ hf i

private lemma Corollary1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (v w : Fin n) (hv : v ∈ ABC) (hNv : G.neighborFinset v ⊆ ABC.toFinset)
    (hw : G.Adj v w)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    f G ABC v ≤ γ G ABC w → Objective G ABC := by
  intro h
  refine Claim1 G ABC v hv hNv ih ?_
  refine le_trans h ?_
  calc γ G ABC w
    _ = ∑ x ∈ {w}, γ G ABC x := Eq.symm <| sum_singleton ..
    _ = 0 + ∑ x ∈ {w}, γ G ABC x := by simp only [zero_add, sum_singleton]
    _ ≤ ∑ x ∈ G.neighborFinset v \ {w}, γ G ABC x + ∑ x ∈ {w}, γ G ABC x := by
      refine add_le_add_left ?_ _
      refine sum_nonneg (fun _ _ ↦ γ_nonneg G ABC)
    _ = ∑ x ∈ G.neighborFinset v, γ G ABC x := by
      refine sum_sdiff ?_
      simp [hw]

theorem ABCLemma {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n) :
    Objective G ABC := by
  induction hcard : ABC.card using Nat.strong_induction_on generalizing G ABC with | h k ih
  if hk : k = 0 then
    refine ⟨∅, ?_, ?_, ?_, ?_⟩ <;>
    simp [respects, card_eq_zero.mp <| hk ▸ hcard,
      InducesLinearForest, InducesForest, IsDegenerateSet]
  else
  have ih : ∀ (G' : SimpleGraph (Fin n)) [inst : DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC' := by
    intro G' _ ABC' hcardABC'
    exact ih ABC'.card (hcard ▸ hcardABC') G' ABC' rfl

  sorry

end ABC

end CaroWeiType
end SimpleGraph
