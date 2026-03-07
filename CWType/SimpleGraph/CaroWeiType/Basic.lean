-- import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic

namespace SimpleGraph
namespace CaroWeiType

open Finset

@[simp]
lemma p_and_p_implies {p q : Prop} : (p → (p ∧ q)) ↔ (p → q) :=
  ⟨fun h hp ↦ h hp |>.2, fun hpq hp ↦ ⟨hp, hpq hp⟩⟩

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
#min_imports
