-- import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic

namespace SimpleGraph

def deleteIncidencesOf {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n)) :
    SimpleGraph (Fin n) :=
  G ⊓ ⨅ x ∈ s, G.deleteIncidenceSet x

instance {n : ℕ} {W : Finset (Fin n)} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] :
    DecidableRel (G.deleteIncidencesOf W).Adj := by
  intro u v
  simp only [deleteIncidencesOf, inf_adj, iInf_adj, ne_eq]
  if huv : G.Adj u v then
    simp only [huv, deleteIncidenceSet, incidenceSet, deleteEdges_adj, Set.mem_setOf_eq,
      mem_edgeSet, Sym2.mem_iff, true_and, not_or]
    if hu : u ∈ W then
      refine .isFalse ?_
      simp_all only [huv.ne, not_false_eq_true, and_true, not_forall, not_and,
        Decidable.not_not]
      refine ⟨u, hu, by simp⟩
    else if hv : v ∈ W then
      refine .isFalse ?_
      simp_all only [huv.ne, not_false_eq_true, and_true, not_forall, not_and,
        Decidable.not_not]
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

@[simp]
lemma p_and_p_implies {p q : Prop} : (p → (p ∧ q)) ↔ (p → q) :=
  ⟨fun h hp ↦ h hp |>.2, fun hpq hp ↦ ⟨hp, hpq hp⟩⟩

structure FiniteSimpleGraph (n : ℕ) where
  graph : SimpleGraph (Fin n)
  decAdj : DecidableRel graph.Adj := by aesop_graph

instance {n : ℕ} {G : FiniteSimpleGraph n} : DecidableRel G.graph.Adj := G.decAdj

-- instance {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (s : Set (Fin n)) :
--     DecidableRel (G.induce s).Adj := by
--   intro ⟨v, hv⟩ ⟨w, hw⟩
--   simp only [comap_adj, Function.Embedding.subtype_apply]
--   infer_instance


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
