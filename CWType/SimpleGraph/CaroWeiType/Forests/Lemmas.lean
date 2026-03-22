import CWType.SimpleGraph.CaroWeiType.Forests.Basic

namespace SimpleGraph
open Finset

lemma InducesForest_singleton {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {v : Fin n} :
    G.InducesForest {v} := by
  simp only [InducesForest, IsDegenerateSet, subset_singleton_iff, ne_eq, forall_eq_or_imp,
    not_true_eq_false, notMem_empty, filter_empty, card_empty, zero_le, and_true, exists_false,
    imp_self, forall_eq, singleton_ne_empty, not_false_eq_true, mem_singleton, exists_eq_left,
    forall_const, true_and]
  refine le_trans ?_ <| le_of_eq <| card_singleton v
  refine Finset.card_le_card (by simp)

lemma InducesLinearForest_singleton {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {v : Fin n} : G.InducesLinearForest {v} := by
  simp [InducesLinearForest, InducesForest_singleton]

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


end SimpleGraph
