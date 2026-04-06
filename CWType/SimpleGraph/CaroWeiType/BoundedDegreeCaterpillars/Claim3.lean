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
      have _ : f G ABC v = ∑ w ∈ {v}, f G ABC w := Eq.symm (sum_singleton (f G ABC) v)
      rw [← sum_singleton (f G ABC ·) v]
      rw [← sum_union_inter]
      suffices G.neighborFinset v ∩ {v} = ∅ by
        simp only [union_singleton, mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true,
          sum_insert, inter_singleton_of_notMem, add_zero, sum_empty]
      ext
      simp only [mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true,
        inter_singleton_of_notMem, notMem_empty]
    _ ≤ 1 := le_sub_iff_add_le.mp h
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
      exact mul_div_assoc' ..
    _ = (G.degree v) * (1 - f G ABC v) * (G.degree v : ℝ)⁻¹ := div_eq_mul_inv ..
    _ = ((G.degree v) * (G.degree v : ℝ)⁻¹) * (1 - f G ABC v) := mul_right_comm ..
    _ = 1 - f G ABC v := by
      if hdegv : G.degree v = 0 then
        have f_eq_zero : 1 - f G ABC v = 0 := by
          rcases hv with hv | hv | hv <;>
            simp only [f, hv, ↓reduceDIte, if_pos hdegv, sub_self, dite_eq_ite, ite_self, sub_self]
        simp only [f_eq_zero, mul_zero]
      else
        have hdegv' : G.degree v ≠ (0 : ℝ) := by
          simp only [ne_eq, Nat.cast_eq_zero, hdegv, not_false_eq_true]
        rw [mul_inv_cancel₀ hdegv']
        exact one_mul (1 - f G ABC v)

end Tripartition
end ABC
end CaroWeiType
