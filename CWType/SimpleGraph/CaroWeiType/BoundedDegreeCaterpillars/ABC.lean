import CWType.SimpleGraph.CaroWeiType.Basic
import CWType.SimpleGraph.CaroWeiType.Forests.Basic

open Finset

namespace CaroWeiType
namespace ABC

@[ext]
structure Tripartition (V : Type) [Fintype V] where
  A : V → Prop
  B : V → Prop
  C : V → Prop
  sound : ∀ x, ¬(A x ∧ B x) ∧ ¬(A x ∧ C x) ∧ ¬(B x ∧ C x)

namespace Tripartition

variable {V : Type} [Fintype V]

class Decidable (ABC : Tripartition V) where
  A : DecidablePred ABC.A
  B : DecidablePred ABC.B
  C : DecidablePred ABC.C

def promote_finset (ABC : Tripartition V) (s : Finset V) : Tripartition V where
  A w := ABC.A w ∨ ABC.B w ∧ w ∈ s
  B w := ABC.B w ∧ w ∉ s ∨ ABC.C w ∧ w ∈ s
  C w := ABC.C w ∧ w ∉ s
  sound := by grind only [ABC.sound]

abbrev promote (ABC : Tripartition V) (v : V) :
    Tripartition V :=
  ABC.promote_finset {v}

def demote_finset (ABC : Tripartition V) (s : Finset V) : Tripartition V where
  A w := ABC.A w ∧ w ∉ s
  B w := ABC.B w ∧ w ∉ s ∨ ABC.A w ∧ w ∈ s
  C w := ABC.C w ∨ ABC.B w ∧ w ∈ s
  sound := by grind only [ABC.sound]

abbrev demote (ABC : Tripartition V) (v : V) : Tripartition V :=
  ABC.demote_finset {v}

instance : Membership V (Tripartition V) :=
  ⟨fun ABC x ↦ ABC.A x ∨ ABC.B x ∨ ABC.C x⟩

@[simp]
lemma mem_iff (ABC : Tripartition V) {x : V} :
    x ∈ ABC ↔ ABC.A x ∨ ABC.B x ∨ ABC.C x := by
  rfl

instance {ABC : Tripartition V} [inst : ABC.Decidable] : DecidablePred (· ∈ ABC) := by
  simp only [mem_iff]
  intro x
  match inst.A x, inst.B x, inst.C x with
  | isFalse hA, isFalse hB, isFalse hC => exact isFalse <| by simp [hA, hB, hC]
  | isTrue h, _, _ => exact isTrue <| by grind
  | _, isTrue h, _ => exact isTrue <| by grind
  | _, _, isTrue h => exact isTrue <| by grind

def toSet (ABC : Tripartition V) : Set V :=
  {x | x ∈ ABC}

instance {ABC : Tripartition V} [ABC.Decidable] : Fintype (ABC.toSet) :=
  @Subtype.fintype _ (· ∈ ABC) _ _

def toFinset (ABC : Tripartition V) [Fintype ABC.toSet] : Finset V :=
  ABC.toSet.toFinset

@[simp]
def sdiff (ABC : Tripartition V) (s : Finset V) : Tripartition V where
  A v := ABC.A v ∧ v ∉ s
  B v := ABC.B v ∧ v ∉ s
  C v := ABC.C v ∧ v ∉ s
  sound x := by
    if hxs : x ∈ s then
      simp only [hxs, not_true_eq_false, and_false, not_false_eq_true, true_and]
    else
      simp only [hxs, not_false_eq_true, and_true, ABC.sound x]

infixl:50 " \\ " => sdiff

instance [DecidableEq V] {ABC : Tripartition V} [inst : ABC.Decidable] {s : Finset V} :
    (ABC \ s).Decidable where
  A x := by simp only [sdiff]; have := inst.A; infer_instance
  B x := by simp only [sdiff]; have := inst.B; infer_instance
  C x := by simp only [sdiff]; have := inst.C; infer_instance

instance [DecidableEq V] {ABC : Tripartition V} [inst : ABC.Decidable] {s : Finset V} :
    (ABC.promote_finset s).Decidable where
  A x := by simp only [promote_finset]; have := inst.A; have := inst.B; infer_instance
  B x := by simp only [promote_finset]; have := inst.B; have := inst.C; infer_instance
  C x := by simp only [promote_finset]; have := inst.C; infer_instance

instance [DecidableEq V] {ABC : Tripartition V} [inst : ABC.Decidable] {s : Finset V} :
    (ABC.demote_finset s).Decidable where
  A x := by simp only [demote_finset]; have := inst.A; infer_instance
  B x := by simp only [demote_finset]; have := inst.A; have := inst.B; infer_instance
  C x := by simp only [demote_finset]; have := inst.B; have := inst.C; infer_instance

def card (ABC : Tripartition V) [ABC.Decidable] : ℕ :=
  ABC.toFinset.card

open SimpleGraph

def respects [DecidableEq V] (s : Finset V) (G : SimpleGraph V) [G.LocallyFinite]
    (ABC : Tripartition V) : Prop :=
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

variable {V : Type} [Fintype V]

@[simp]
noncomputable def f (G : SimpleGraph V) (ABC : Tripartition V)
    (v : V) [Fintype (G.neighborSet v)] : ℝ := by
  if ABC.A v      then exact fA (G.degree v)
  else if ABC.B v then exact fB (G.degree v)
  else if ABC.C v then exact fC (G.degree v)
  else                 exact 0

@[simp]
noncomputable def γ (G : SimpleGraph V) (ABC : Tripartition V)
    (v : V) [Fintype (G.neighborSet v)] : ℝ := by
  if ABC.A v      then exact fA (G.degree v - 1) - fA (G.degree v)
  else if ABC.B v then exact fB (G.degree v - 1) - fB (G.degree v)
  else if ABC.C v then exact fC (G.degree v - 1) - fC (G.degree v)
  else                 exact 0

@[simp]
noncomputable def ℓ (G : SimpleGraph V) (ABC : Tripartition V)
    (v : V) [Fintype (G.neighborSet v)] : ℝ := by
  if ABC.A v      then exact fA (G.degree v) - fA (G.degree v + 1)
  else if ABC.B v then exact fB (G.degree v) - fB (G.degree v + 1)
  else if ABC.C v then exact fC (G.degree v) - fC (G.degree v + 1)
  else                 exact 0

@[simp]
noncomputable def eval (G : SimpleGraph V) [G.LocallyFinite]
    (ABC : Tripartition V) [ABC.Decidable] : ℝ :=
  ∑ v ∈ ABC.toFinset, f G ABC v

open Finset

@[simp, reducible]
def Objective [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ABC : Tripartition V) [ABC.Decidable] : Prop :=
  ∃ s : Finset V, s ⊆ ABC.toFinset ∧ G.InducesForest s ∧ ABC.respects s G ∧ eval G ABC ≤ s.card

@[simp, reducible]
noncomputable def key (G : SimpleGraph V) [G.LocallyFinite] (ABC : Tripartition V) :
    V → ℝ ×ₗ ℤ :=
  fun v ↦ ⟨γ G ABC v, -G.degree v⟩

def IsVstar (G : SimpleGraph V) [G.LocallyFinite] (ABC : Tripartition V) [ABC.Decidable] (v : V) :
    Prop :=
  MinimalFor (fun u ↦ u ∈ ABC.toFinset ∧ γ G ABC u ≠ 0) (key G ABC) v

end ABC
end CaroWeiType
