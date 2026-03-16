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
lemma coe_mem_toFinset {n : ℕ} (ABC : Tripartition n) (x : Fin n) :
    x ∈ ABC ↔ x ∈ ABC.toFinset := by
  simp [toFinset]

@[simp]
lemma mem_iff {n : ℕ} (ABC : Tripartition n) (x : Fin n) :
    x ∈ ABC ↔ ABC.A x ∨ ABC.B x ∨ ABC.C x := by
  rfl

@[simp]
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
  simp only [toFinset, sdiff, mem_iff]
  intro x hx
  simp only [mem_iff, mem_filter, mem_univ, true_and] at hx ⊢
  grind

@[simp]
lemma toFinset_eq {n : ℕ} {ABC : Tripartition n} {s : Finset (Fin n)} :
    (ABC \ s).toFinset = ABC.toFinset \ s := by
  ext w
  simp only [toFinset, sdiff, mem_iff, mem_filter, mem_univ, true_and, mem_sdiff]
  grind

lemma sdiff_card {n : ℕ} (ABC : Tripartition n) {s : Finset (Fin n)}
    (hs : s ∩ ABC.toFinset ≠ ∅) : (ABC \ s).card < ABC.card := by
  simp only [card, toFinset, sdiff]
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro z hz
    simp only [mem_iff, mem_filter, mem_univ, true_and] at hz ⊢
    grind
  · intro this
    obtain ⟨z, hz⟩ := nonempty_def.mp <| nonempty_iff_ne_empty.mpr hs
    have hzABC : z ∈ ABC.toFinset := by exact mem_of_mem_inter_right hz
    let hobj := this hzABC
    simp only [mem_iff, mem_filter, mem_univ, true_and] at hobj
    rcases hobj with ⟨_, h⟩ | ⟨⟨_, h⟩ | ⟨_, h⟩⟩ <;> exact h <| mem_of_mem_filter z hz

end Tripartition

def respects {n : ℕ} (s : Finset (Fin n)) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) : Prop :=
  ∀ w ∈ s,
    (ABC.A w → G.degree_in s w ≤ 2)
    ∧ (ABC.B w → G.degree_in s w ≤ 1)
    ∧ (ABC.C w → G.degree_in s w = 0)

lemma respects_union {n : ℕ} {s t : Finset (Fin n)} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (hs : respects s G ABC) (ht : respects t G ABC)
    (hst' : ∀ y ∈ s, ∀ z ∈ t, ¬G.Adj y z) :
    respects (s ∪ t) G ABC := by
  intro w hw
  rcases mem_union.mp hw with hw | hw
  · have heq : G.degree_in (s ∪ t) w = G.degree_in s w := by
      refine congrArg card ?_
      ext y
      simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff, or_iff_left_iff_imp]
      exact fun hwy hy ↦ hst' w hw y hy hwy |>.elim
    obtain ⟨hs1, hs2, hs3⟩ := hs w hw
    refine ⟨?_, ?_, ?_⟩ <;> { intro _; rw [heq]; grind }
  · have heq : G.degree_in (s ∪ t) w = G.degree_in t w := by
      refine congrArg card ?_
      ext y
      simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff,
        or_iff_right_iff_imp]
      refine fun hwy hy ↦ hst' y hy w hw hwy.symm |>.elim
    obtain ⟨hs1, hs2, hs3⟩ := ht w hw
    refine ⟨?_, ?_, ?_⟩ <;> { intro _; rw [heq]; grind }

lemma respects_mono {n : ℕ} {s t : Finset (Fin n)} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (hs : s ⊆ (ABC \ t).toFinset)
    (hresp : respects s (G.deleteIncidencesOf t) (ABC \ t)) :
    respects s G ABC := by
  intro w hw
  have mem_s_implies_notMem_t {z : Fin n} : z ∈ s → z ∉ t := by
    intro hz
    simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff] at hs
    let hobj := hs hz
    simp only [Tripartition.mem_iff, mem_filter, mem_univ, true_and] at hobj
    grind
  have hwt : w ∉ t := mem_s_implies_notMem_t hw
  have heqGNw : ((G.deleteIncidencesOf t).neighborFinset w ∩ s) = G.neighborFinset w ∩ s := by
    ext x
    simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_inter, mem_neighborFinset,
      inf_adj, iInf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and,
      not_or, ne_eq, and_congr_left_iff, and_iff_left_iff_imp]
    intro hx hwx
    simp only [hwx, forall_const, true_and, hwx.ne, not_false_eq_true, and_true]
    exact fun _ hu ↦ ⟨fun heq ↦ hwt <| heq ▸ hu, fun heq ↦ mem_s_implies_notMem_t (heq ▸ hx) <| hu⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hAw
    let hobj := hresp w hw |>.1 ⟨hAw, hwt⟩
    simp only [degree_in] at hobj ⊢
    exact heqGNw ▸ hobj
  · intro hBw
    let hobj := hresp w hw |>.2.1 ⟨hBw, hwt⟩
    simp only [degree_in] at hobj ⊢
    exact heqGNw ▸ hobj
  · intro hCw
    let hobj := hresp w hw |>.2.2 ⟨hCw, hwt⟩
    simp only [degree_in] at hobj ⊢
    exact heqGNw ▸ hobj

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
  if ABC.A v      then exact fA (G.degree v)
  else if ABC.B v then exact fB (G.degree v)
  else if ABC.C v then exact fC (G.degree v)
  else                 exact 0

lemma f_eq_in_sdiff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    {s : Finset (Fin n)} {w : Fin n} (hw : w ∉ s) :
    f G (ABC \ s) w = f G ABC w := by
  have : ABC.A w ↔ (ABC \ s).A w := ⟨fun h ↦ ⟨h, hw⟩, fun ⟨h, _⟩ ↦ h⟩
  have : ABC.B w ↔ (ABC \ s).B w := ⟨fun h ↦ ⟨h, hw⟩, fun ⟨h, _⟩ ↦ h⟩
  have : ABC.C w ↔ (ABC \ s).C w := ⟨fun h ↦ ⟨h, hw⟩, fun ⟨h, _⟩ ↦ h⟩
  simp only [f]
  split_ifs
  any_goals grind

lemma f_mono_degree {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n))
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (ABC : Tripartition n)
    {v : Fin n} : G₁.degree v = G₂.degree v → f G₁ ABC v = f G₂ ABC v := by
  intro heq
  simp only [f, fA, fB, one_div, fC, dite_eq_ite, heq]

lemma f_pos_of_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    (v : Fin n) : v ∈ ABC → 0 < f G ABC v := by
  have _ : (0 : ℝ) ≤ G.degree v := Nat.cast_nonneg' _
  intro h
  rcases ABC.mem_iff _ |>.mp h with hA | hB | hC
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
  simp only [Tripartition.mem_iff, not_or] at hv
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
        simp only [card_neighborFinset_eq_degree, card_singleton]
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
  simp only [Tripartition.toFinset, Tripartition.mem_iff, mem_filter, mem_univ,
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
      simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff,
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
            f_pos_of_mem G ABC w <| (ABC.coe_mem_toFinset w).mpr (mem_inter.mp hw).2
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
        simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff,
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
    simp only [Tripartition.card, Tripartition.toFinset, Tripartition.mem_iff]
    refine Finset.card_lt_card ⟨?_, ?_⟩
    · intro x
      simp only [Tripartition.sdiff, Tripartition.mem_iff, mem_filter,
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
    simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff] at hs1
    ext x
    simp only [mem_inter, notMem_empty, iff_false, not_and]
    intro hx
    let hobj := hs1 hx
    simp only [Tripartition.mem_iff, mem_filter, mem_univ, true_and] at hobj
    grind
  refine ⟨s, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [Tripartition.toFinset, Tripartition.mem_iff] at hs1 ⊢
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
      simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff,
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
        exact Tripartition.coe_mem_toFinset .. |>.mp hv
      _ = ∑ x ∈ (ABC \ {v}).toFinset \ G.neighborFinset v, f G ABC x
        + ∑ x ∈ G.neighborFinset v, f G ABC x + f G ABC v := by
        simp only [add_left_inj]
        refine Eq.symm <| sum_sdiff ?_
        intro x hx
        have hxnev : x ≠ v := G.mem_neighborFinset .. |>.mp hx |>.ne'
        have hxABC : x ∈ ABC := Tripartition.coe_mem_toFinset .. |>.mpr <| hNv hx
        refine Tripartition.coe_mem_toFinset .. |>.mp ?_
        simp only [Tripartition.sdiff, mem_singleton, Tripartition.mem_iff, hxnev,
          not_false_eq_true, and_true]
        exact Tripartition.mem_iff .. |>.mpr hxABC
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
            simp only [Tripartition.toFinset, Tripartition.mem_iff, mem_inter,
              mem_filter, mem_univ, true_and, hw, and_true, Tripartition.sdiff]
            have _ : w ∉ ({v} : Finset _) := by
              simp only [mem_neighborFinset, mem_singleton] at hw ⊢
              exact hw.ne'
            have _ : ABC.A w ∨ ABC.B w ∨ ABC.C w := by
              refine ABC.mem_iff w |>.mp ?_
              exact ABC.coe_mem_toFinset w |>.mpr <| hNv hw
            grind
        rw [this] at hobj
        exact hobj

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

private lemma Claim2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (F : Finset (Fin n)) (hFne : F.Nonempty)
    (hF : F ⊆ ABC.toFinset) (hF' : respects F G ABC)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    G.InducesLinearForest F →
      #F ≥ eval G ABC - eval (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
                             (ABC \ G.closed_neighborFinset_of_Finset F) →
        Objective G ABC := by
  intro h h'
  have hcap : G.closed_neighborFinset_of_Finset F ∩ ABC.toFinset ≠ ∅ := by
    refine Nonempty.ne_empty <| nonempty_def.mpr ?_
    obtain ⟨x, hx⟩ := nonempty_def.mp hFne
    refine ⟨x, mem_inter.mpr ⟨closed_neighborFinset_contains_Finset G F <| hx, hF hx⟩⟩
  obtain ⟨s', hs', hlf', hresp, hcard'⟩ :=
    ih (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
      (ABC \ (G.closed_neighborFinset_of_Finset F)) (Tripartition.sdiff_card ABC hcap)
  have hresp : respects (s' ∪ F) G ABC := by
    refine respects_union G ABC (respects_mono G ABC hs' hresp) hF' ?_
    intro y hy z hz this
    have _ : y ∈ G.closed_neighborFinset_of_Finset F := by
      simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
      refine Or.inr ⟨z, hz, this⟩
    let hobj := hs' hy
    simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff,
      mem_filter, mem_univ, true_and] at hobj
    have _ : y ∉ G.closed_neighborFinset_of_Finset F := by grind
    contradiction
  refine ⟨s' ∪ F, fun _ _ ↦ by grind [Tripartition.toFinset_mono], ?_, hresp, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro t ht htne
      have H : s' ⊆ s' ∪ F := by exact subset_union_left
      have _ : (t ∩ s') ⊆ s' := by exact inter_subset_right
      if hcap : t ∩ s' = ∅ then exact h.1 t (by grind) htne
      else ?_
      let bla := hlf'.1 (t ∩ s') (inter_subset_right) hcap
      obtain ⟨x, hx, hx'⟩ := bla
      refine ⟨x, mem_of_mem_filter x hx, ?_⟩
      refine le_trans ?_ hx'
      refine Finset.card_le_card ?_
      intro y
      simp only [mem_filter, mem_inter, and_imp, deleteIncidencesOf, deleteIncidenceSet]
      intro hy hxy
      simp only [hy, true_and, closed_neighborFinset_of_Finset, mem_filter, mem_univ,
        incidenceSet, inf_adj, hxy, iInf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet,
        Sym2.mem_iff, not_or, ne_eq, hxy.ne, not_false_eq_true, and_true]
      have hnotinF {z} (hz : z ∈ s') : z ∉ G.closed_neighborFinset_of_Finset F := by
        let hobj := hs' hz
        simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff,
          mem_filter, mem_univ, true_and] at hobj
        grind
      refine ⟨?_, ?_⟩
      · rcases mem_union.mp <| ht hy with hy | hy
        · exact hy
        · refine (hnotinF <| (mem_inter.mp hx).2) ?_ |>.elim
          simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
          exact Or.inr ⟨y, hy, hxy⟩
      · intro w h
        have hw : w ∈ G.closed_neighborFinset_of_Finset F := by
          simp [h, closed_neighborFinset_of_Finset]
        constructor
        · exact fun heq ↦ (hnotinF (mem_inter.mp hx).2) (heq ▸ hw)
        · suffices y ∉ G.closed_neighborFinset_of_Finset F by
            exact fun heq ↦ this (heq ▸ hw)
          rcases mem_union.mp <| ht hy with hy | hy
          · exact hnotinF hy
          · refine (hnotinF (mem_inter.mp hx).2) ?_ |>.elim
            simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
            exact Or.inr ⟨y, hy, hxy⟩
    · intro x hx
      simp only [respects, degree_in] at hresp
      let bla := hresp x hx
      have hxABC : x ∈ ABC := by
        rcases mem_union.mp hx with hx | hx
        · let bla := hs' hx
          simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff,
            mem_filter, mem_univ, true_and] at bla
          grind [Tripartition.mem_iff]
        · exact ABC.coe_mem_toFinset x |>.mpr <| hF hx
      simp only [Tripartition.mem_iff] at hxABC
      grind
  · simp only [ge_iff_le, tsub_le_iff_right] at h'
    calc eval G ABC
      _ = eval G ABC - eval (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
                             (ABC \ G.closed_neighborFinset_of_Finset F)
                     + eval (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
                             (ABC \ G.closed_neighborFinset_of_Finset F) := by
        simp only [sub_add_cancel]
      _ ≤ #F + eval (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
                             (ABC \ G.closed_neighborFinset_of_Finset F) := by
        simp only [sub_add_cancel, h']
      _ ≤ #F + #s' := by
        simp only [add_le_add_iff_left, hcard']
      _ = #s' + #F := add_comm ..
      _ = #(s' ∪ F) + #(s' ∩ F) := by
        simp only [← Nat.cast_add]
        refine Nat.cast_inj.mpr ?_
        exact Eq.symm <| card_union_add_card_inter ..
      _ = #(s' ∪ F) := by
        simp only [add_eq_left, Nat.cast_eq_zero, card_eq_zero]
        ext x
        simp only [mem_inter, notMem_empty, iff_false, not_and]
        intro hx
        let hobj := hs' hx
        simp [Tripartition.sdiff, Tripartition.toFinset] at hobj
        have hfinal : x ∉ G.closed_neighborFinset_of_Finset F := by grind
        exact fun hx ↦ hfinal <| closed_neighborFinset_contains_Finset G F hx

private lemma _γ_on_N2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (F : Finset (Fin n)) :
    ∑ w ∈ G.N2_of_Finset F, γ G ABC w ≤ ∑ w ∈ G.N2_of_Finset F,
        (f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
          (ABC \ G.closed_neighborFinset_of_Finset F) w - f G ABC w) := by
  refine sum_le_sum ?_
  intro w hw
  have hwNF : w ∉ G.closed_neighborFinset_of_Finset F := by
    exact fun _ ↦ by grind [closed_neighborFinset_of_Finset, N2_of_Finset]
  have hdeg : (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F).degree w + 1
      ≤ G.degree w := by
    refine Order.add_one_le_iff.mpr ?_
    repeat rw [degree]
    refine Finset.card_lt_card ⟨?_, ?_⟩
    · intro x hx
      simp only [closed_neighborFinset_of_Finset, deleteIncidencesOf, deleteIncidenceSet,
        incidenceSet, mem_neighborFinset, mem_filter, mem_univ, true_and, inf_adj, iInf_adj,
        deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq,
        N2_of_Finset] at hx hw
      exact (G.mem_neighborFinset ..).mpr hx.1
    · refine sdiff_nonempty.mp ?_
      simp only [N2_of_Finset, mem_filter, mem_univ, true_and] at hw
      obtain ⟨x, hx, y, hy, hwy, hyx⟩ := hw.2.2
      refine ⟨y, ?_⟩
      refine mem_sdiff.mpr ⟨(G.mem_neighborFinset w y).mpr hwy, ?_⟩
      have hy' : y ∈ G.closed_neighborFinset_of_Finset F := by
        simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
        exact Or.inr ⟨x, hx, hyx⟩
      simp only [mem_neighborFinset]
      exact Adj.symm.mt <| deleteIncidencesOf_notadj G hy'
  have hdegw : 1 ≤ G.degree w := by exact Nat.one_le_of_lt hdeg
  have h1 : ((((G.degree w- 1) : ℕ) : ℝ) + 1) = (G.degree w : ℝ) := by
    simp only [Nat.cast_one, sub_add_cancel, Nat.cast_sub hdegw]
  rw [γ, f]
  have hAiff : ABC.A w ↔ (ABC \ G.closed_neighborFinset_of_Finset F).A w := by
    exact ⟨fun h ↦ by simp [Tripartition.sdiff, h, hwNF], fun h ↦ h.1⟩
  have hBiff : ABC.B w ↔ (ABC \ G.closed_neighborFinset_of_Finset F).B w := by
    exact ⟨fun h ↦ by simp [Tripartition.sdiff, h, hwNF], fun h ↦ h.1⟩
  have hCiff : ABC.C w ↔ (ABC \ G.closed_neighborFinset_of_Finset F).C w := by
    exact ⟨fun h ↦ by simp [Tripartition.sdiff, h, hwNF], fun h ↦ h.1⟩
  if hA : ABC.A w then
    simp only [hA, ↓reduceDIte, f, tsub_le_iff_right, sub_add_cancel,
      ge_iff_le, hAiff.mp hA, fA, Nat.pred_eq_succ_iff, zero_add]
    split_ifs
    any_goals grind
    · rw [h1]
      exact mul_le_one (Nat.cast_pos'.mpr hdegw) (Nat.ofNat_le_cast.mpr (by grind))
    · rw [h1]
      ring_nf
      calc ((G.degree w) : ℝ)⁻¹ * 2
        _ ≤ (3 : ℝ)⁻¹ * 2 := by
          simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
          exact inv_anti₀ three_pos (Nat.cast_le.mpr (by grind))
      grind
    · ring_nf
      simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
      refine inv_anti₀ (by grind) ?_
      simp only [add_le_add_iff_left, Nat.cast_le]
      grind
  else if hB : ABC.B w then
    simp only [hA, ↓reduceDIte, hB, fB, Nat.pred_eq_succ_iff, zero_add, Nat.reduceAdd, one_div,
      Tripartition.sdiff, false_and, true_and, fC, dite_eq_ite, ite_not, f, tsub_le_iff_right,
      sub_add_cancel, ge_iff_le, h1]
    split_ifs
    any_goals grind
    · ring_nf
      calc (G.degree w : ℝ)⁻¹ * (4 / (3 : ℝ))
        _ ≤ (2 : ℝ)⁻¹ * (4 / (3 : ℝ)) := by
          simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀]
          exact inv_anti₀ two_pos (Nat.cast_le.mpr (by grind))
        _ ≤ 1 := by grind
    · ring_nf
      calc (G.degree w : ℝ)⁻¹ * (4 / (3 : ℝ))
        _ ≤ (2 : ℝ)⁻¹ * (4 / (3 : ℝ)) := by
          simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀]
          exact inv_anti₀ two_pos (Nat.cast_le.mpr (by grind))
        _ ≤ 5 / (6 : ℝ) := by grind
    · ring_nf
      suffices (4 : ℝ) ≤ G.degree w by
        calc (G.degree w : ℝ)⁻¹ * (4 / (3 : ℝ))
          _ ≤ (4 : ℝ)⁻¹ * (4 / (3 : ℝ)) := by
            simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀]
            exact inv_anti₀ four_pos this
          _ ≤ 1 / (3 : ℝ) := by grind
      exact Nat.cast_le.mpr <| by grind
    · refine div_le_div_iff_of_pos_left four_pos (by grind) (by grind) |>.mpr ?_
      simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
      have _ : ((1 : ℕ) : ℝ) = 1 := by exact Nat.cast_one
      rw [← Nat.cast_one, ← Nat.cast_add _ 1]
      exact Nat.cast_le.mpr hdeg
 else if hC : ABC.C w then
    simp only [hA, ↓reduceDIte, hB, hC, fC, Nat.pred_eq_succ_iff, zero_add, Nat.reduceAdd, one_div,
      h1, Tripartition.sdiff, false_and, true_and, dite_eq_ite, ite_not, f, tsub_le_iff_right,
      sub_add_cancel, ge_iff_le]
    split_ifs
    any_goals grind
    · ring_nf
      calc (G.degree w : ℝ)⁻¹ * (2 / (3 : ℝ))
        _ ≤ 1⁻¹ * (2 / (3 : ℝ)) := by
          simp only [inv_one, one_mul, Nat.ofNat_pos, div_pos_iff_of_pos_left,
            mul_le_iff_le_one_left]
          rw [← inv_one]
          refine inv_anti₀ one_pos ?_
          exact @Nat.cast_one ℝ _ ▸ Nat.cast_le.mpr hdegw
        _ ≤ 1 := by grind
    · ring_nf
      calc (G.degree w : ℝ)⁻¹ * (2 / (3 : ℝ))
        _ ≤ (2 : ℝ)⁻¹ * (2 / (3 : ℝ)) := by
          simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀]
          refine inv_anti₀ two_pos ?_
          exact @Nat.cast_two ℝ _ ▸ Nat.cast_le.mpr (by grind)
        _ ≤ (1 / (3 : ℝ)) := by grind
    · refine div_le_div_iff_of_pos_left two_pos (by grind) (by grind) |>.mpr ?_
      simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
      rw [← Nat.cast_one, ← Nat.cast_add]
      exact Nat.cast_le.mpr hdeg
  else
    simp [hA, hB, hC]

private lemma Claim2' {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (F : Finset (Fin n)) (hFne : F.Nonempty)
    (hG : G.support.toFinset ⊆ ABC.toFinset)
    (hF : G.closed_neighborFinset_of_Finset F ⊆ ABC.toFinset) (hF' : respects F G ABC)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    G.InducesLinearForest F →
      #F ≥ ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G ABC v
        - ∑ w ∈ G.N2_of_Finset F, γ G ABC w →
        Objective G ABC := by
  intro h h'
  refine Claim2 G ABC F hFne
    (subset_trans (closed_neighborFinset_contains_Finset G F) hF) hF' ih h ?_
  simp_all only [ge_iff_le]
  simp only [eval]
  calc ∑ v ∈ ABC.toFinset, f G ABC v
       - ∑ v ∈ (ABC \ G.closed_neighborFinset_of_Finset F).toFinset,
          f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
            (ABC \ G.closed_neighborFinset_of_Finset F) v
    _ = ∑ v ∈ ABC.toFinset \ (G.closed_neighborFinset_of_Finset F), f G ABC v
        + ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G ABC v
        - ∑ v ∈ (ABC \ G.closed_neighborFinset_of_Finset F).toFinset,
            f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
              (ABC \ G.closed_neighborFinset_of_Finset F) v := by
      simp only [sub_left_inj]
      refine Eq.symm <| sum_sdiff hF
    _ = (∑ v ∈ ABC.toFinset \ (G.closed_neighborFinset_of_Finset F), f G ABC v
        - ∑ v ∈ (ABC \ G.closed_neighborFinset_of_Finset F).toFinset,
          f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
            (ABC \ G.closed_neighborFinset_of_Finset F) v)
        + ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G ABC v := by
      grind
    _ = (∑ v ∈ ABC.toFinset \ (G.closed_neighborFinset_of_Finset F), f G ABC v
        - ∑ v ∈ ABC.toFinset \ (G.closed_neighborFinset_of_Finset F),
          f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
            (ABC \ G.closed_neighborFinset_of_Finset F) v)
        + ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G ABC v := by
      simp only [Tripartition.toFinset_eq]
    _ = ∑ v ∈ ABC.toFinset \ (G.closed_neighborFinset_of_Finset F), (f G ABC v
          - f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
            (ABC \ G.closed_neighborFinset_of_Finset F) v)
        + ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G ABC v := by
      simp only [sum_sub_distrib]
  refine le_trans ?_ h'
  rw [add_comm ..]
  refine add_le_add_iff_left _ |>.mpr ?_
  refine neg_le_neg_iff.mp ?_
  simp only [neg_neg]
  rw [← sum_neg_distrib]
  calc ∑ w ∈ G.N2_of_Finset F, γ G ABC w
    _ ≤ ∑ w ∈ G.N2_of_Finset F,
        (f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
          (ABC \ G.closed_neighborFinset_of_Finset F) w - f G ABC w) := by
      exact _γ_on_N2 G ABC F
    _ = 0 + ∑ w ∈ G.N2_of_Finset F,
        (f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
          (ABC \ G.closed_neighborFinset_of_Finset F) w - f G ABC w) := by
      simp only [zero_add]
    _ = ∑ w ∈ (ABC.toFinset \ G.closed_neighborFinset_of_Finset F) \ G.N2_of_Finset F,
          (f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
            (ABC \ G.closed_neighborFinset_of_Finset F) w - f G ABC w)
        + ∑ w ∈ G.N2_of_Finset F,
        (f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
          (ABC \ G.closed_neighborFinset_of_Finset F) w - f G ABC w) := by
      simp only [add_left_inj]
      refine Eq.symm <| sum_eq_zero ?_
      intro z hz
      have hz' : z ∉ G.closed_neighborFinset_of_Finset F :=
        mem_sdiff.mp (mem_sdiff.mp hz |>.1) |>.2
      rw [f_eq_in_sdiff _ ABC hz']
      rw [sub_eq_zero]
      refine f_mono_degree _ _ ABC ?_
      repeat rw [degree]
      refine congrArg _ ?_
      ext y
      simp only [closed_neighborFinset_of_Finset, deleteIncidencesOf, deleteIncidenceSet,
        incidenceSet, mem_neighborFinset, mem_filter, mem_univ, true_and, inf_adj, iInf_adj,
        deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq,
        and_iff_left_iff_imp]
      refine fun h ↦ ⟨fun x ↦ ⟨fun h' ↦ ⟨h, fun _ ↦ ?_⟩, h.ne⟩, h.ne⟩
      rcases h' with hx | hx
      · constructor
        · exact fun heq ↦ hz' <| closed_neighborFinset_contains_Finset G F <| heq ▸ hx
        · refine fun heq ↦ hz' ?_
          simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
          exact Or.inr ⟨x, hx, heq ▸ h⟩
      · constructor
        · have hx : x ∈ G.closed_neighborFinset_of_Finset F := by
            simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and]
            exact Or.inr hx
          exact fun heq ↦ hz' <| heq ▸ hx
        · intro heq
          subst heq
          refine mem_sdiff.mp hz |>.2 ?_
          simp only [N2_of_Finset, mem_filter, mem_univ, true_and]
          simp only [closed_neighborFinset_of_Finset, mem_filter, mem_univ, true_and, not_or,
            not_exists, not_and] at hz'
          refine ⟨hz'.1, hz'.2, ?_⟩
          · obtain ⟨y, hy, hxy⟩ := hx
            exact ⟨y, hy, x, by grind, h, hxy⟩
    _ = ∑ w ∈ ABC.toFinset \ G.closed_neighborFinset_of_Finset F,
          (f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
            (ABC \ G.closed_neighborFinset_of_Finset F) w - f G ABC w) := by
      refine Finset.sum_sdiff ?_
      intro w
      simp only [N2_of_Finset, mem_filter, mem_univ, true_and, closed_neighborFinset_of_Finset,
        mem_sdiff, not_or, not_exists, not_and, and_imp, forall_exists_index]
      intro hw H x hx y hy hwy hyx
      refine ⟨hG ?_, ⟨hw, H⟩⟩
      simp only [Set.mem_toFinset]
      exact G.degree_pos_iff_mem_support w |>.mp hwy.degree_pos_left
    _ = ∑ w ∈ ABC.toFinset \ G.closed_neighborFinset_of_Finset F,
        -(f G ABC w - f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
              (ABC \ G.closed_neighborFinset_of_Finset F) w) := by
      refine sum_congr rfl ?_
      intro w hw
      exact Eq.symm <| neg_sub ..

private lemma Corollary2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (F : Finset (Fin n)) (hFne : F.Nonempty)
    (hG : G.support.toFinset ⊆ ABC.toFinset)
    (hF : G.closed_neighborFinset_of_Finset F ⊆ ABC.toFinset) (hF' : respects F G ABC)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    G.InducesLinearForest F →
      #F ≥ ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G ABC v →
        Objective G ABC := by
  intro h h'
  refine Claim2' G ABC F hFne hG hF hF' ih h ?_
  simp only [ge_iff_le, tsub_le_iff_right] at h' ⊢
  refine le_trans h' ?_
  simp only [le_add_iff_nonneg_right]
  refine sum_nonneg <| fun _ _ ↦ γ_nonneg G ABC

theorem ABCLemma {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n) :
    Objective G ABC := by
  induction hcard : ABC.card using Nat.strong_induction_on generalizing G ABC with | h k ih
  if hk : k = 0 then
    refine ⟨∅, ?_, ?_, ?_, ?_⟩ <;>
    simp [respects, card_eq_zero.mp <| hk ▸ hcard,
      InducesLinearForest, InducesForest, IsDegenerateSet]
  else
  have ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC' :=
    fun G' _ ABC' hcardABC' ↦ ih ABC'.card (hcard ▸ hcardABC') G' ABC' rfl
  sorry

end ABC

end CaroWeiType
end SimpleGraph
