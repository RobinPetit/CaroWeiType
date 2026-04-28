import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic

namespace SimpleGraph

@[simp, reducible]
def degree_in {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (x : V) : ℕ :=
  (G.neighborFinset x ∩ s).card

def closed_neighborFinset_of_Finset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : Finset V :=
  {v : V | v ∈ s ∨ ∃ x ∈ s, G.Adj v x}

def N2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  {u : V | u ≠ v ∧ ¬G.Adj u v ∧ ∃ w, G.Adj u w ∧ G.Adj w v}

def N2_of_Finset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : Finset V :=
  {u : V | u ∉ s ∧ (∀ x ∈ s, ¬G.Adj u x) ∧ ∃ x ∈ s, ∃ w ∉ s, G.Adj u w ∧ G.Adj w x}

def deleteIncidencesOf {V : Type*} (G : SimpleGraph V) (s : Finset V) :
    SimpleGraph V :=
  G ⊓ ⨅ x ∈ s, G.deleteIncidenceSet x

noncomputable instance instDecidableRel_deleteIncidencesOf {V : Type*} {W : Finset V}
    {G : SimpleGraph V} [DecidableRel G.Adj] : DecidableRel (G.deleteIncidencesOf W).Adj := by
  intro u v
  simp only [deleteIncidencesOf, inf_adj, iInf_adj, ne_eq]
  if huv : G.Adj u v then
    simp only [huv, deleteIncidenceSet, incidenceSet, deleteEdges_adj, Set.mem_setOf_eq,
      mem_edgeSet, Sym2.mem_iff, true_and, not_or]
    if hu : u ∈ W then
      refine .isFalse ?_
      simp_all only [huv.ne, not_false_eq_true, and_true, not_forall, not_and]
      refine ⟨u, hu, by simp⟩
    else if hv : v ∈ W then
      refine .isFalse ?_
      simp_all only [huv.ne, not_false_eq_true, and_true, not_forall, not_and]
      exact ⟨v, hv, by simp⟩
    else
      refine .isTrue ?_
      refine ⟨fun w ↦ ⟨fun hw ↦ ⟨?_, ?_⟩, huv.ne⟩, huv.ne⟩
      · exact fun this ↦ hu (this ▸ hw) |>.elim
      · exact fun this ↦ hv (this ▸ hw) |>.elim
  else
    refine .isFalse (by simp [huv])

namespace CaroWeiType

open Finset

structure FiniteSimpleGraph (n : ℕ) where
  graph : SimpleGraph (Fin n)
  decAdj : DecidableRel graph.Adj := by aesop_graph

instance {n : ℕ} {G : FiniteSimpleGraph n} : DecidableRel G.graph.Adj := G.decAdj

@[simp]
abbrev FiniteCompleteGraph (n : ℕ) : FiniteSimpleGraph n where
  graph := completeGraph (Fin n)
  decAdj u w := by
    simp only [completeGraph_eq_top, top_adj, ne_eq]
    if h : u = w then exact .isFalse (by simp [h])
    else exact .isTrue h

def IsCaroWeiTypeLowerBound (f : ℕ → ℝ)
  (π : {n : ℕ} → FiniteSimpleGraph n → Finset (Fin n) → Prop) :=
  ∀ {n : ℕ},
    ∀ G : FiniteSimpleGraph n,
      ∃ s : Finset (Fin n), π G s
        ∧ ∑ v, f (G.graph.degree v) ≤ #s

theorem CaroWeiTypeLowerBound_mono {π : {n : ℕ} → FiniteSimpleGraph n → Finset (Fin n) → Prop}
    {f₁ f₂ : ℕ → ℝ} (hle : f₁ ≤ f₂) :
    IsCaroWeiTypeLowerBound f₂ π → IsCaroWeiTypeLowerBound f₁ π := by
  intro hf₂ n G
  obtain ⟨s, hs⟩ := hf₂ G
  refine ⟨s, ⟨hs.1, ?_⟩⟩
  refine le_trans (sum_le_sum fun v _ ↦ hle (G.graph.degree v)) hs.2

end CaroWeiType

end SimpleGraph
