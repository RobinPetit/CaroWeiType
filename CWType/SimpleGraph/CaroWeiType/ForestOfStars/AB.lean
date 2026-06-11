import CWType.SimpleGraph.CaroWeiType.Basic
import CWType.SimpleGraph.CaroWeiType.Forests.Basic

open Finset

namespace CaroWeiType
namespace AB

@[ext]
structure Bipartition (V : Type) [Fintype V] where
  A : V → Prop
  B : V → Prop
  sound : ∀ x, ¬(A x ∧ B x)

namespace Bipartition

variable {V : Type} [Fintype V]

class Decidable (AB : Bipartition V) where
  A : DecidablePred AB.A
  B : DecidablePred AB.B

def promote_finset (AB : Bipartition V) (s : Finset V) : Bipartition V where
  A w := AB.A w ∨ AB.B w ∧ w ∈ s
  B w := AB.B w ∧ w ∉ s
  sound := by grind only [AB.sound]

abbrev promote (AB : Bipartition V) (v : V) : Bipartition V :=
  AB.promote_finset {v}

def demote_finset (AB : Bipartition V) (s : Finset V) : Bipartition V where
  A w := AB.A w ∧ w ∉ s
  B w := AB.B w ∨ AB.A w ∧ w ∈ s
  sound := by grind only [AB.sound]

abbrev demote (AB : Bipartition V) (v : V) : Bipartition V :=
  AB.demote_finset {v}

instance : Membership V (Bipartition V) :=
  ⟨fun AB x ↦ AB.A x ∨ AB.B x⟩

@[simp]
lemma mem_iff (AB : Bipartition V) {x : V} :
    x ∈ AB ↔ AB.A x ∨ AB.B x := by
  rfl

instance {AB : Bipartition V} [inst : AB.Decidable] : DecidablePred (· ∈ AB) := by
  simp only [mem_iff]
  intro x
  match inst.A x, inst.B x with
  | isFalse hA, isFalse hB => exact isFalse <| by simp [hA, hB]
  | isTrue h, _ => exact isTrue <| by grind
  | _, isTrue h => exact isTrue <| by grind

instance {AB : Bipartition V} [inst : AB.Decidable] : DecidablePred (AB.A ·) :=
  inst.A

instance {AB : Bipartition V} [inst : AB.Decidable] : DecidablePred (AB.B ·) :=
  inst.B

def toSet (AB : Bipartition V) : Set V :=
  {x | x ∈ AB}

instance {AB : Bipartition V} [AB.Decidable] : Fintype (AB.toSet) :=
  @Subtype.fintype _ (· ∈ AB) _ _

def toFinset (AB : Bipartition V) [Fintype AB.toSet] : Finset V :=
  AB.toSet.toFinset

@[simp]
def sdiff (AB : Bipartition V) (s : Finset V) : Bipartition V where
  A v := AB.A v ∧ v ∉ s
  B v := AB.B v ∧ v ∉ s
  sound x := by
    if hxs : x ∈ s then
      simp only [hxs, not_true_eq_false, and_false, not_false_eq_true]
    else
      simp only [hxs, not_false_eq_true, and_true, AB.sound x]

infixl:50 " \\ " => sdiff

instance [DecidableEq V] {AB : Bipartition V} [inst : AB.Decidable] {s : Finset V} :
    (AB \ s).Decidable where
  A x := by simp only [sdiff]; have := inst.A; infer_instance
  B x := by simp only [sdiff]; have := inst.B; infer_instance

instance [DecidableEq V] {AB : Bipartition V} [inst : AB.Decidable] {s : Finset V} :
    (AB.promote_finset s).Decidable where
  A x := by simp only [promote_finset]; infer_instance
  B x := by simp only [promote_finset]; infer_instance

instance [DecidableEq V] {AB : Bipartition V} [inst : AB.Decidable] {s : Finset V} :
    (AB.demote_finset s).Decidable where
  A x := by simp only [demote_finset]; infer_instance
  B x := by simp only [demote_finset]; infer_instance

def card (AB : Bipartition V) [AB.Decidable] : ℕ :=
  AB.toFinset.card

open SimpleGraph

def respects [DecidableEq V] (s : Finset V) (G : SimpleGraph V) [G.LocallyFinite]
    (AB : Bipartition V) : Prop :=
  ∀ w ∈ s, (AB.B w → ∀ u ∈ s, G.Adj u w → AB.A u ∧ G.degree_in s u ≤ 1)

end Bipartition

noncomputable def fA (d : ℕ) : ℝ :=
  if d = 0 then 1
  else if d = 1 then 5 / (6 : ℝ)
  else if d = 2 then 3 / (5 : ℝ)
  else 2 / (d + 1 : ℝ)

noncomputable def fB (d : ℕ) : ℝ :=
  1 / (d + 1 : ℝ)

variable {V : Type} [Fintype V]

noncomputable def f (G : SimpleGraph V) (AB : Bipartition V)
    (v : V) [Fintype (G.neighborSet v)] : ℝ := by
  if AB.A v then exact fA (G.degree v)
  else if AB.B v then exact fB (G.degree v)
  else exact 0

noncomputable def γ (G : SimpleGraph V) (AB : Bipartition V)
    (v : V) [Fintype (G.neighborSet v)] : ℝ := by
  if AB.A v      then exact fA (G.degree v - 1) - fA (G.degree v)
  else if AB.B v then exact fB (G.degree v - 1) - fB (G.degree v)
  else                 exact 0

noncomputable def ℓ (G : SimpleGraph V) (AB : Bipartition V)
    (v : V) [Fintype (G.neighborSet v)] : ℝ := by
  if AB.A v      then exact fA (G.degree v) - fA (G.degree v + 1)
  else if AB.B v then exact fB (G.degree v) - fB (G.degree v + 1)
  else                 exact 0

noncomputable def eval (G : SimpleGraph V) [G.LocallyFinite]
    (AB : Bipartition V) [AB.Decidable] : ℝ :=
  ∑ v ∈ AB.toFinset, f G AB v

@[simp, reducible]
def Objective [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (AB : Bipartition V) [AB.Decidable] : Prop :=
  ∃ s : Finset V, s ⊆ AB.toFinset ∧ G.InducesForestOfStars s ∧ AB.respects s G ∧ eval G AB ≤ s.card

end AB
end CaroWeiType
