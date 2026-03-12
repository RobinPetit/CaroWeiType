import Mathlib

import Mathlib.Combinatorics.SimpleGraph.Acyclic

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

@[simp]
noncomputable def γ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    (v : Fin n) : ℝ := by
  classical
  if ABC.A v      then exact fA (G.degree v - 1) - fA (G.degree v)
  else if ABC.B v then exact fB (G.degree v - 1) - fB (G.degree v)
  else if ABC.C v then exact fC (G.degree v - 1) - fC (G.degree v)
  else                 exact 0

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

@[simp, reducible]
private def Objective {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) : Prop :=
  ∃ s : Finset (Fin n),
    s ⊆ ABC.toFinset ∧ G.InducesLinearForest s ∧ respects s G ABC ∧ s.card ≤ eval G ABC

private lemma Claim0 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (W : Finset (Fin n)) (hWABC' : W ∩ ABC.toFinset ≠ ∅)
    (h : eval (G.deleteIncidencesOf W) (ABC \ W) < eval G ABC)
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
  · exact le_trans hs4 (le_of_lt h)

-- private lemma Claim1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
--     (ABC : Tripartition n) (v : Fin n)
--     (ih : ∀ m < k, ∀ (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj]
--       (X : Finset (Fin n)), G.support ⊆ ↑X → #X = m → Objective G ABC) :
--     f G ABC v > ∑ w ∈ G.neighborFinset v, γ G ABC w → Objective G ABC := by
--   sorry

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
