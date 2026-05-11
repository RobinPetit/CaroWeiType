import CWType.SimpleGraph.CaroWeiType.Basic
import CWType.SimpleGraph.CaroWeiType.Forests.Basic

open Finset

namespace CaroWeiType
namespace ABC

@[ext]
structure Tripartition (n : ℕ) where
  A : Fin n → Prop
  B : Fin n → Prop
  C : Fin n → Prop
  sound : ∀ x, ¬(A x ∧ B x) ∧ ¬(A x ∧ C x) ∧ ¬(B x ∧ C x)

namespace Tripartition

class Decidable {n : ℕ} (ABC : Tripartition n) where
  A : DecidablePred ABC.A
  B : DecidablePred ABC.B
  C : DecidablePred ABC.C

def promote_finset {n : ℕ} (ABC : Tripartition n) (s : Finset (Fin n)) : Tripartition n where
  A w := ABC.A w ∨ ABC.B w ∧ w ∈ s
  B w := ABC.B w ∧ w ∉ s ∨ ABC.C w ∧ w ∈ s
  C w := ABC.C w ∧ w ∉ s
  sound := by grind only [ABC.sound]

abbrev promote {n : ℕ} (ABC : Tripartition n) (v : Fin n) : Tripartition n :=
  ABC.promote_finset {v}

def demote_finset {n : ℕ} (ABC : Tripartition n) (s : Finset (Fin n)) : Tripartition n where
  A w := ABC.A w ∧ w ∉ s
  B w := ABC.B w ∧ w ∉ s ∨ ABC.A w ∧ w ∈ s
  C w := ABC.C w ∨ ABC.B w ∧ w ∈ s
  sound := by grind only [ABC.sound]

abbrev demote {n : ℕ} (ABC : Tripartition n) (v : Fin n) : Tripartition n :=
  ABC.demote_finset {v}

instance {n : ℕ} : Membership (Fin n) (Tripartition n) :=
  ⟨fun ABC x ↦ ABC.A x ∨ ABC.B x ∨ ABC.C x⟩

@[simp]
lemma mem_iff {n : ℕ} (ABC : Tripartition n) {x : Fin n} :
    x ∈ ABC ↔ ABC.A x ∨ ABC.B x ∨ ABC.C x := by
  rfl

instance {n : ℕ} {ABC : Tripartition n} [inst : ABC.Decidable] : DecidablePred (· ∈ ABC) := by
  simp only [mem_iff]
  intro x
  match inst.A x, inst.B x, inst.C x with
  | isFalse hA, isFalse hB, isFalse hC => exact isFalse <| by simp [hA, hB, hC]
  | isTrue h, _, _ => exact isTrue <| by grind
  | _, isTrue h, _ => exact isTrue <| by grind
  | _, _, isTrue h => exact isTrue <| by grind

def toSet {n : ℕ} (ABC : Tripartition n) : Set (Fin n) :=
  {x | x ∈ ABC}

instance {n : ℕ} {ABC : Tripartition n} [ABC.Decidable] : Fintype (ABC.toSet) :=
  @Subtype.fintype _ (· ∈ ABC) _ _

def toFinset {n : ℕ} (ABC : Tripartition n) [Fintype ABC.toSet] : Finset (Fin n) :=
  ABC.toSet.toFinset

@[simp]
def sdiff {n : ℕ} (ABC : Tripartition n) (s : Finset (Fin n)) : Tripartition n where
  A v := ABC.A v ∧ v ∉ s
  B v := ABC.B v ∧ v ∉ s
  C v := ABC.C v ∧ v ∉ s
  sound x := by
    if hxs : x ∈ s then
      simp only [hxs, not_true_eq_false, and_false, not_false_eq_true, true_and]
    else
      simp only [hxs, not_false_eq_true, and_true, ABC.sound x]

infixl:50 " \\ " => sdiff

instance {n : ℕ} {ABC : Tripartition n} [inst : ABC.Decidable] {s : Finset (Fin n)} :
    (ABC \ s).Decidable where
  A x := by simp only [sdiff]; have := inst.A; infer_instance
  B x := by simp only [sdiff]; have := inst.B; infer_instance
  C x := by simp only [sdiff]; have := inst.C; infer_instance

instance {n : ℕ} {ABC : Tripartition n} [inst : ABC.Decidable] {s : Finset (Fin n)} :
    (ABC.promote_finset s).Decidable where
  A x := by simp only [promote_finset]; have := inst.A; have := inst.B;infer_instance
  B x := by simp only [promote_finset]; have := inst.B; have := inst.C; infer_instance
  C x := by simp only [promote_finset]; have := inst.C; infer_instance

instance {n : ℕ} {ABC : Tripartition n} [inst : ABC.Decidable] {s : Finset (Fin n)} :
    (ABC.demote_finset s).Decidable where
  A x := by simp only [demote_finset]; have := inst.A; infer_instance
  B x := by simp only [demote_finset]; have := inst.A; have := inst.B; infer_instance
  C x := by simp only [demote_finset]; have := inst.B; have := inst.C; infer_instance

def card {n : ℕ} (ABC : Tripartition n) [ABC.Decidable] : ℕ :=
  ABC.toFinset.card

open SimpleGraph

def respects {n : ℕ} (s : Finset (Fin n)) (G : SimpleGraph (Fin n)) [G.LocallyFinite]
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
noncomputable def f {n : ℕ} (G : SimpleGraph (Fin n)) (ABC : Tripartition n)
    (v : Fin n) [Fintype (G.neighborSet v)] : ℝ := by
  if ABC.A v      then exact fA (G.degree v)
  else if ABC.B v then exact fB (G.degree v)
  else if ABC.C v then exact fC (G.degree v)
  else                 exact 0

@[simp]
noncomputable def γ {n : ℕ} (G : SimpleGraph (Fin n)) (ABC : Tripartition n)
    (v : Fin n) [Fintype (G.neighborSet v)] : ℝ := by
  if ABC.A v      then exact fA (G.degree v - 1) - fA (G.degree v)
  else if ABC.B v then exact fB (G.degree v - 1) - fB (G.degree v)
  else if ABC.C v then exact fC (G.degree v - 1) - fC (G.degree v)
  else                 exact 0

@[simp]
noncomputable def ℓ {n : ℕ} (G : SimpleGraph (Fin n)) (ABC : Tripartition n)
    (v : Fin n) [Fintype (G.neighborSet v)] : ℝ := by
  if ABC.A v      then exact fA (G.degree v) - fA (G.degree v + 1)
  else if ABC.B v then exact fB (G.degree v) - fB (G.degree v + 1)
  else if ABC.C v then exact fC (G.degree v) - fC (G.degree v + 1)
  else                 exact 0

@[simp]
noncomputable def eval {n : ℕ} (G : SimpleGraph (Fin n)) [G.LocallyFinite]
    (ABC : Tripartition n) [ABC.Decidable] : ℝ :=
  ∑ v ∈ ABC.toFinset, f G ABC v

open Finset

@[simp, reducible]
def Objective {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) [ABC.Decidable] : Prop :=
  ∃ s : Finset (Fin n),
    s ⊆ ABC.toFinset ∧ G.InducesForest s ∧ ABC.respects s G ∧ eval G ABC ≤ s.card

@[simp, reducible]
noncomputable def key {n : ℕ} (G : SimpleGraph (Fin n)) [G.LocallyFinite]
    (ABC : Tripartition n) : Fin n → ℝ ×ₗ ℤ :=
  fun v ↦ ⟨γ G ABC v, -G.degree v⟩

def IsVstar {n : ℕ} (G : SimpleGraph (Fin n)) [G.LocallyFinite]
    (ABC : Tripartition n) [ABC.Decidable] (v : Fin n) : Prop :=
  MinimalFor (fun u ↦ u ∈ ABC.toFinset ∧ γ G ABC u ≠ 0) (key G ABC) v

end ABC
end CaroWeiType
