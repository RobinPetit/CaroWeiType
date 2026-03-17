import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim2

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

lemma Claim3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) {v : Fin n} (hv : v ∈ ABC) (hG : G.support.toFinset ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    ∑ w ∈ G.neighborFinset v, f G ABC w ≤ 1 - f G ABC v → Objective G ABC := by
  intro h
  refine Corollary2 G ABC {v} (singleton_nonempty v) hG (by simp [ABC.coe_mem_toFinset.mp hv])
    respects_singleton ih InducesLinearForest_singleton ?_
  calc ∑ w ∈ G.closed_neighborFinset_of_Finset {v}, f G ABC w
    _ = ∑ w ∈ G.neighborFinset v ∪ {v}, f G ABC w := by
      rw [closed_neighborFinset_of_singleton_eq]
    _ = ∑ w ∈ G.neighborFinset v, f G ABC w + f G ABC v := by
      have _ : f G ABC v = ∑ w ∈ {v}, f G ABC w := by exact Eq.symm (sum_singleton (f G ABC) v)
      rw [← sum_singleton (f G ABC ·) v]
      rw [← sum_union_inter]
      suffices G.neighborFinset v ∩ {v} = ∅ by grind
      ext; simp
    _ ≤ 1 := by grind
    _ = (#{v} : ℝ) := by
      rw [← Nat.cast_one]
      refine Eq.symm <| Nat.cast_inj.mpr <| card_singleton _

lemma Corollary3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) {v : Fin n} (hv : v ∈ ABC) (hG : G.support.toFinset ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    (∀ w ∈ G.neighborFinset v, f G ABC w ≤ (1 - f G ABC v) / (G.degree v : ℝ))
      → Objective G ABC := by
  intro h
  refine Claim3 G ABC hv hG ih ?_
  calc ∑ w ∈ G.neighborFinset v, f G ABC w
    _ ≤ ∑ w ∈ G.neighborFinset v, (1 - f G ABC v) / (G.degree v : ℝ) := by
      exact sum_le_sum h
    _ = (G.degree v) * (1 - f G ABC v) / (G.degree v : ℝ) := by
      simp only [sum_const, card_neighborFinset_eq_degree, nsmul_eq_mul]
      grind
    _ = (G.degree v) * (1 - f G ABC v) * (G.degree v : ℝ)⁻¹ := by
      grind
    _ = ((G.degree v) * (G.degree v : ℝ)⁻¹) * (1 - f G ABC v) := by
      grind
    _ = 1 - f G ABC v := by
      if hdegv : G.degree v = 0 then
        have _ : 1 - f G ABC v = 0 := by
          simp [Tripartition.mem_iff] at hv
          simp only [f, fA, hdegv, ↓reduceIte, fB, fC, dite_eq_ite]
          split_ifs
          any_goals grind
        grind
      else
        have : (G.degree v) * (G.degree v : ℝ)⁻¹ = 1 := by
          exact mul_inv_cancel₀ <| Nat.cast_ne_zero.mpr hdegv
        grind

end Tripartition
end ABC
end CaroWeiType
