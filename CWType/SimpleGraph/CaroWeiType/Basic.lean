import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic

import Mathlib.Data.ULift

namespace SimpleGraph

@[simp, reducible]
def degree_in {V : Type*} [DecidableEq V] (G : SimpleGraph V) (s : Finset V) (x : V)
    [Fintype (G.neighborSet x)] : ℕ :=
  (G.neighborFinset x ∩ s).card

def closed_neighborFinset_of_Finset {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [G.LocallyFinite] (s : Finset V) : Finset V :=
  s ∪ s.biUnion (G.neighborFinset ·)

def N2_of_Finset {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (s : Finset V) : Finset V :=
  G.closed_neighborFinset_of_Finset (G.closed_neighborFinset_of_Finset s)
    \ (G.closed_neighborFinset_of_Finset s)

def deleteIncidencesOf {V : Type*} (G : SimpleGraph V) (s : Finset V) :
    SimpleGraph V :=
  G ⊓ ⨅ x ∈ s, G.deleteIncidenceSet x

lemma deleteIncidensOf_neighborSet_subset {V : Type*} (G : SimpleGraph V) (s : Finset V) {v : V} :
    (G.deleteIncidencesOf s).neighborSet v ⊆ G.neighborSet v := by
  intro u
  simp only [deleteIncidencesOf, mem_neighborSet, inf_adj, iInf_adj, ne_eq, and_imp]
  intro h
  simp only [h, implies_true]

instance instDecidableRel_deleteIncidencesOf {V : Type*} {W : Finset V} [DecidablePred (· ∈ W)]
    {G : SimpleGraph V} [DecidableRel G.Adj] : DecidableRel (G.deleteIncidencesOf W).Adj := by
  intro u v
  simp only [deleteIncidencesOf, inf_adj, iInf_adj, ne_eq]
  if huv : G.Adj u v then
    simp only [huv, deleteIncidenceSet, incidenceSet, deleteEdges_adj, Set.mem_setOf_eq,
      mem_edgeSet, Sym2.mem_iff, true_and, not_or]
    if hu : u ∈ W then
      refine .isFalse ?_
      simp only [huv.ne, not_false_eq_true, and_true, not_forall, not_and]
      refine ⟨u, hu, ?_⟩
      simp only [not_true_eq_false]
      exact False.elim
    else if hv : v ∈ W then
      refine .isFalse ?_
      simp_all only [huv.ne, not_false_eq_true, and_true, not_forall, not_and]
      exact ⟨v, hv, by simp only [Decidable.not_not, implies_true]⟩
    else
      refine .isTrue ?_
      refine ⟨fun w ↦ ⟨fun hw ↦ ⟨?_, ?_⟩, huv.ne⟩, huv.ne⟩
      · exact fun this ↦ hu (this ▸ hw) |>.elim
      · exact fun this ↦ hv (this ▸ hw) |>.elim
  else
    refine .isFalse (by simp only [huv, false_and, not_false_eq_true])

end SimpleGraph

def IsNonAdjacentUnionStableProp {V : Type*} [DecidableEq V]
    (π : (G : SimpleGraph V) → [DecidableRel G.Adj] → Finset V → Prop) : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (s s' : Finset V),
    (s ∩ s' = ∅) → (∀ x ∈ s, ∀ y ∈ s', ¬G.Adj x y) → π G s → π G s' → π G (s ∪ s')

namespace CaroWeiType

open Finset
open SimpleGraph

lemma CompleteGraph_degree {n : ℕ} {v : Fin (n + 1)}
    [DecidableRel (completeGraph (Fin (n + 1))).Adj] :
    (completeGraph (Fin (n + 1))).degree v = n := by
  have H : #(Finset.univ \ {v}) = n := by
    rw [card_sdiff]
    simp only [card_univ, Fintype.card_fin, inter_univ, card_singleton, add_tsub_cancel_right]
  refine Eq.trans ?_ H
  refine congrArg Finset.card ?_
  ext
  simp only [completeGraph, mem_neighborFinset, top_adj, mem_sdiff, mem_univ, true_and,
    mem_singleton, ne_comm]

structure GraphParameter where
  toFun : {V : Type} → [DecidableEq V] → [Fintype V] →
    (G : SimpleGraph V) → [DecidableRel G.Adj] → Finset V → Prop
  invariant : ∀ {V V' : Type} [DecidableEq V] [DecidableEq V'] [Fintype V] [Fintype V']
    (G : SimpleGraph V) [DecidableRel G.Adj] (G' : SimpleGraph V') [DecidableRel G'.Adj]
    (φ : G ≃g G') (s : Finset V), toFun G s ↔ toFun G' (s.image φ.toFun)

def IsCaroWeiTypeLowerBound (f : ℕ → ℝ) (π : GraphParameter) :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ∃ s : Finset V, π.toFun G s ∧ ∑ v, f (G.degree v) ≤ #s

lemma f_on_complete_graph {n : ℕ} {f : ℕ → ℝ} :
    ∑ v, f ((completeGraph (Fin (n + 1))).degree v) = (n + 1 : ℕ) * f n := by
  calc ∑ v, f ((completeGraph (Fin (n + 1))).degree v)
    _ = ∑ v : (Fin (n + 1)), f n :=
      sum_congr rfl (fun _ _ ↦ congrArg _ CompleteGraph_degree)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

lemma f_on_complete_graph' {n k : ℕ} {f : ℕ → ℝ} {π : GraphParameter}
    (hf : IsCaroWeiTypeLowerBound f π)
    (h : ∀ s, π.toFun (completeGraph (Fin (n + 1))) s → #s ≤ k) :
    f n ≤ k / (n + 1 : ℝ) := by
  obtain ⟨s, hs, hcard⟩ := hf <| completeGraph (Fin (n + 1))
  rw [f_on_complete_graph] at hcard
  rw [← Nat.cast_one, ← Nat.cast_add]
  refine (le_div_iff₀ (Nat.cast_pos'.mpr <| Nat.zero_lt_succ _)).mpr ?_
  exact le_of_eq_of_le (mul_comm ..) <| le_trans hcard (Nat.cast_le.mpr <| h s hs)

lemma f_le_1_of_IsCaroWeiTypeLowerBound {f π} (hf : IsCaroWeiTypeLowerBound f π) :
    ∀ d, f d ≤ 1 := by
  intro d
  suffices f d ≤ (d + 1 : ℕ) / (d + 1 : ℝ) by
    refine le_of_le_of_eq this <| ?_
    nth_rw 2 [← Nat.cast_one]
    rw [← Nat.cast_add]
    exact div_self_eq_one₀.mpr <| Ne.symm <| ne_of_lt <| Nat.cast_pos'.mpr <| Nat.zero_lt_succ _
  exact f_on_complete_graph' hf <| fun s _ ↦ card_finset_fin_le s

theorem CaroWeiTypeLowerBound_mono {π : GraphParameter} {f₁ f₂ : ℕ → ℝ} (hle : f₁ ≤ f₂)
    (hf₂ : IsCaroWeiTypeLowerBound f₂ π) : IsCaroWeiTypeLowerBound f₁ π := by
  intro _ _ _ G _
  obtain ⟨s, hs⟩ := hf₂ G
  exact ⟨s, ⟨hs.1, le_trans (sum_le_sum fun v _ ↦ hle (G.degree v)) hs.2⟩⟩

end CaroWeiType
