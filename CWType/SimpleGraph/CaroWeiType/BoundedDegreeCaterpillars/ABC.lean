import Mathlib.Combinatorics.SimpleGraph.Basic

import CWType.SimpleGraph.CaroWeiType.Basic
import CWType.SimpleGraph.CaroWeiType.Forests.Basic

namespace CaroWeiType
namespace ABC

open Finset

@[ext]
structure Tripartition (n : ℕ) where
  A : Fin n → Prop
  B : Fin n → Prop
  C : Fin n → Prop
  sound : ∀ x, ¬(A x ∧ B x) ∧ ¬(A x ∧ C x) ∧ ¬(B x ∧ C x)

def promote_B {n : ℕ} {ABC : Tripartition n} {v : Fin n} (hv : ABC.B v) : Tripartition n where
  A w := ABC.A w ∨ w = v
  B w := ABC.B w ∧ w ≠ v
  C w := ABC.C w
  sound := by grind [ABC.sound]

def promote_C {n : ℕ} {ABC : Tripartition n} {v : Fin n} (hv : ABC.C v) : Tripartition n where
  A w := ABC.A w
  B w := ABC.B w ∨ w = v
  C w := ABC.C w ∧ w ≠ v
  sound := by grind [ABC.sound]

namespace Tripartition

def demote_finset {n : ℕ} (ABC : Tripartition n) (s : Finset (Fin n)) : Tripartition n where
  A w := ABC.A w ∧ w ∉ s
  B w := ABC.B w ∧ w ∉ s ∨ ABC.A w ∧ w ∈ s
  C w := ABC.C w ∨ ABC.B w ∧ w ∈ s
  sound := by grind [ABC.sound]

def demote {n : ℕ} (ABC : Tripartition n) (v : Fin n) : Tripartition n :=
  ABC.demote_finset {v}

noncomputable def promote {n : ℕ} (ABC : Tripartition n) (v : Fin n) : Tripartition n := by
  if      hB : ABC.B v then exact CaroWeiType.ABC.promote_B hB
  else if hC : ABC.C v then exact CaroWeiType.ABC.promote_C hC
  else                      exact ABC

instance {n : ℕ} : Membership (Fin n) (Tripartition n) :=
  ⟨fun ABC x ↦ ABC.A x ∨ ABC.B x ∨ ABC.C x⟩

noncomputable def toFinset {n : ℕ} (ABC : Tripartition n) : Finset (Fin n) := by
  classical
  exact {x | x ∈ ABC}

@[simp]
def sdiff {n : ℕ} (ABC : Tripartition n) (s : Finset (Fin n)) : Tripartition n where
  A := fun v ↦ ABC.A v ∧ v ∉ s
  B := fun v ↦ ABC.B v ∧ v ∉ s
  C := fun v ↦ ABC.C v ∧ v ∉ s
  sound x := by
    obtain ⟨h₁, h₂, h₃⟩ := ABC.sound x
    simp_all

infixl:50 " \\ " => sdiff

noncomputable def card {n : ℕ} (ABC : Tripartition n) : ℕ := ABC.toFinset.card

open SimpleGraph

def respects {n : ℕ} (s : Finset (Fin n)) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) : Prop :=
  ∀ w ∈ s,
    (ABC.A w → G.degree_in s w ≤ 2)
    ∧ (ABC.B w → G.degree_in s w ≤ 1)
    ∧ (ABC.C w → G.degree_in s w = 0)

end Tripartition

@[simp, reducible]
noncomputable def fA (d : ℕ) : ℝ :=
  if d = 0 then 1
  else if d = 1 then 5 / (6 : ℝ)
  else 2 / (d + 1 : ℝ)

@[simp, reducible]
noncomputable def fB (d : ℕ) : ℝ :=
  if d = 0 then 1
  else if d = 1 then 5 / (6 : ℝ)
  else if d = 2 then 1 / (3 : ℝ)
  else (4 / 3) / (d + 1 : ℝ)

@[simp, reducible]
noncomputable def fC (d : ℕ) : ℝ :=
  if d = 0 then 1
  else if d = 1 ∨ d = 2 then 1 / (6 : ℝ)
  else (2 / 3) / (d + 1 : ℝ)

@[simp]
noncomputable def f {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    (v : Fin n) : ℝ := by
  classical
  if ABC.A v      then exact fA (G.degree v)
  else if ABC.B v then exact fB (G.degree v)
  else if ABC.C v then exact fC (G.degree v)
  else                 exact 0

@[simp]
noncomputable def γ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    (v : Fin n) : ℝ := by
  classical
  if ABC.A v      then exact fA (G.degree v - 1) - fA (G.degree v)
  else if ABC.B v then exact fB (G.degree v - 1) - fB (G.degree v)
  else if ABC.C v then exact fC (G.degree v - 1) - fC (G.degree v)
  else                 exact 0

@[simp]
noncomputable def ℓ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    (v : Fin n) : ℝ := by
  classical
  if ABC.A v      then exact fA (G.degree v) - fA (G.degree v + 1)
  else if ABC.B v then exact fB (G.degree v) - fB (G.degree v + 1)
  else if ABC.C v then exact fC (G.degree v) - fC (G.degree v + 1)
  else                 exact 0

@[simp]
noncomputable def eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) : ℝ :=
  ∑ v ∈ ABC.toFinset, f G ABC v

@[simp, reducible]
def Objective {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) : Prop :=
  ∃ s : Finset (Fin n),
    s ⊆ ABC.toFinset ∧ G.InducesForest s ∧ ABC.respects s G ∧ eval G ABC ≤ #s

@[simp, reducible]
noncomputable def key {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) : Fin n → ℝ ×ₗ ℤ :=
  fun v ↦ ⟨γ G ABC v, -G.degree v⟩

def IsVstar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    (v : Fin n) : Prop :=
  MinimalFor (fun u ↦ u ∈ ABC.toFinset ∧ γ G ABC u ≠ 0) (key G ABC) v

end ABC
end CaroWeiType
