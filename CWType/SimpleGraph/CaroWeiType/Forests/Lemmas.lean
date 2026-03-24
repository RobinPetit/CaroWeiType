import CWType.SimpleGraph.CaroWeiType.Forests.Basic

namespace SimpleGraph
open Finset

lemma InducesForest_singleton {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {v : Fin n} :
    G.InducesForest {v} := by
  simp only [InducesForest, IsDegenerateSet, subset_singleton_iff, ne_eq, degree_in,
    forall_eq_or_imp, not_true_eq_false, notMem_empty, inter_empty, card_empty, zero_le, and_true,
    exists_false, imp_self, forall_eq, singleton_ne_empty, not_false_eq_true, mem_singleton,
    exists_eq_left, mem_neighborFinset, SimpleGraph.irrefl, inter_singleton_of_notMem, and_self]

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

lemma InducesForest_union_disjoint_neighborhoods {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {s₁ s₂ : Finset (Fin n)} (hs₁ : G.InducesForest s₁)
    (hs₂ : G.InducesForest s₂) (h : ∀ x ∈ s₁, ∀ y ∈ s₂, ¬G.Adj x y) :
    G.InducesForest (s₁ ∪ s₂) := by
  intro t ht htne
  if ht' : t ∩ s₁ ≠ ∅ then
    obtain ⟨x, hx, hdeg⟩ := hs₁ (t ∩ s₁) inter_subset_right ht'
    refine ⟨x, (mem_inter.mp hx).1, ?_⟩
    simp only [degree_in] at hdeg ⊢
    refine le_trans (le_of_eq ?_) hdeg
    refine congrArg card ?_
    ext y
    simp only [mem_inter, mem_neighborFinset, and_congr_right_iff, iff_self_and]
    grind
  else
    have ht' : t ∩ s₂ ≠ ∅ := by grind
    obtain ⟨x, hx, hdeg⟩ := hs₂ (t ∩ s₂) inter_subset_right ht'
    refine ⟨x, (mem_inter.mp hx).1, ?_⟩
    simp only [degree_in] at hdeg ⊢
    refine le_trans (le_of_eq ?_) hdeg
    refine congrArg card ?_
    ext y
    simp only [mem_inter, mem_neighborFinset, and_congr_right_iff, iff_self_and]
    grind [Adj.symm]

lemma no_induced_K3_of_InducesForest {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) {x y z : Fin n} (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) :
    G.InducesForest s → ¬{x, y, z} ⊆ s := by
  intro hf ht
  obtain ⟨w, hw, hwdeg⟩ := hf _ ht <| insert_ne_empty _ _
  simp only [mem_insert, mem_singleton] at hw
  simp only [degree_in] at hwdeg
  rcases hw with h | h | h <;> {
    suffices G.neighborFinset w ∩ {x, y, z} = ({x, y, z} : Finset _) \ {w} by
      grind [Adj.ne]
    subst h
    ext u
    simp only [mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true, inter_insert_of_notMem,
      mem_inter, mem_insert, mem_singleton, mem_sdiff]
    grind [Adj.ne, Adj.symm]
  }

end SimpleGraph
