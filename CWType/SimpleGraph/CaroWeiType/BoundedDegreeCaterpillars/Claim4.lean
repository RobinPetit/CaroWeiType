import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

lemma Claim4 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] {v : Fin n}
    (h : G.degree v = G'.degree v + 1) : f G ABC v - f G' (ABC.demote v) v ≤ 1 / (6 : ℝ) := by
  simp only [f, fA, h, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_eq_right,
    Nat.cast_add, Nat.cast_one, fB, Nat.reduceEqDiff, fC, dite_eq_ite, tsub_le_iff_right]
  have H : 2 / (G'.degree v + 1 + 1 : ℝ) ≤ 1 := by
    ring_nf
    calc ((2 : ℝ) + G'.degree v)⁻¹ * 2
      _ ≤ (2 : ℝ)⁻¹ * 2 := by
        refine mul_le_mul_iff_of_pos_right two_pos |>.mpr ?_
        refine inv_anti₀ two_pos (by simp)
      _ = 1 := by simp
  have H' : 3 ≤ G'.degree v → (2 / 3) / (G'.degree v + 1 : ℝ) ≤ 1 / 6 := by
    intro h
    calc (2 / 3) / (G'.degree v + 1 : ℝ)
      _ ≤ (2 / 3) / (4 : ℝ) := by
        refine div_le_div_iff_of_pos_left (by grind) (by grind) (by grind) |>.mpr ?_
        rw [← Nat.cast_one, ← Nat.cast_four, ← Nat.cast_add]
        refine Nat.cast_le.mpr (by grind)
      _ ≤ 1 / 6 := by grind
  if hA : ABC.A v then
    simp only [hA, ↓reduceIte, Tripartition.demote_from_A', Tripartition.demote_from_A, ge_iff_le]
    split_ifs
    any_goals grind
    · calc 2 / ((G'.degree v) + 1 + 1 : ℝ)
        _ = 2 / (4 : ℝ) := by
          refine congrArg (fun x ↦ 2 / x) ?_
          rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_four, Nat.cast_inj]
          grind
        _ ≤ 1 / 6 + 1 / 3 := by grind
    · calc 2 / (G'.degree v + 1 + 1 : ℝ)
        _ = 2 * (G'.degree v + 1 + 1 : ℝ)⁻¹ := by ring_nf
        _ ≤ 2 * (G'.degree v + 1 : ℝ)⁻¹ := by
          simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
          refine inv_anti₀ (Nat.cast_add_one_pos _) (by grind)
        _ = (2 / 3) * (G'.degree v + 1 : ℝ)⁻¹ + (4 / 3) * (G'.degree v + 1 : ℝ)⁻¹ := by
          grind
        _ ≤ 1 / 6 + (4 / 3) * (G'.degree v + 1 : ℝ)⁻¹ := by
          simp only [add_le_add_iff_right]
          exact H' (by grind)
  else if hB : ABC.B v then
    simp only [hA, ↓reduceIte, hB, Tripartition.demote_from_B', Tripartition.demote_from_B,
      ge_iff_le]
    split_ifs
    any_goals grind
    · calc (4 / 3) / (G'.degree v + 1 + 1 : ℝ)
        _ ≤ (4 / 3) / (G'.degree v + 1 : ℝ) := by
          refine div_le_div_iff_of_pos_left (by grind) (by grind) (by grind) |>.mpr ?_
          simp only [le_add_iff_nonneg_right, zero_le_one]
        _ ≤ 2 / (G'.degree v + 1 : ℝ) := by
          ring_nf
          refine mul_le_mul_iff_right₀ (inv_pos.mpr (by grind)) |>.mpr (by grind)
      grind
    · calc (4 / 3) / (G'.degree v + 1 + 1 : ℝ)
        _ ≤ (4 / 3) / (2 + 1 + 1) := by
          refine div_le_div_iff_of_pos_left (by grind) (by grind) (by grind) |>.mpr ?_
          simp only [add_le_add_iff_right, Nat.ofNat_le_cast]
          rename_i hor
          rcases hor <;> grind
      grind
    · calc (4 / 3) / (G'.degree v + 1 + 1 : ℝ)
        _ ≤ (4 / 3) / (G'.degree v + 1 : ℝ) := by
          refine div_le_div_iff_of_pos_left (by grind) (by grind) (by grind) |>.mpr (by grind)
        _ = (2 / 3) / (G'.degree v + 1 : ℝ) + (2 / 3) / (G'.degree v + 1 : ℝ) := by
          grind
        _ ≤ 1 / 6 + (2 / 3) / (G'.degree v + 1 : ℝ) := by
          simp only [add_le_add_iff_right]
          exact H' (by grind)
  else if hC : ABC.C v then
    simp only [hA, ↓reduceIte, hB, hC, one_div, Tripartition.demote_from_C, ge_iff_le]
    split_ifs
    any_goals grind
    · calc (2 / 3) / (G'.degree v + 1 + 1 : ℝ)
        _ ≤ (2 / 3) / (G'.degree v + 1 : ℝ) := by
          refine div_le_div_iff_of_pos_left (by grind) (by grind) (by grind) |>.mpr (by grind)
        _ ≤ 2 / (G'.degree v + 1 : ℝ) := by
          ring_nf
          refine mul_le_mul_iff_right₀ (inv_pos.mpr (by grind)) |>.mpr (by grind)
      grind
    · calc (2 / 3) / (G'.degree v + 1 + 1 : ℝ)
        _ ≤ (2 / 3) / (G'.degree v + 1 : ℝ) := by
          refine div_le_div_iff_of_pos_left (by grind) (by grind) (by grind) |>.mpr (by grind)
        _ ≤ (4 / 3) / (G'.degree v + 1 : ℝ) := by
          ring_nf
          refine mul_le_mul_iff_right₀ (inv_pos.mpr (by grind)) |>.mpr (by grind)
      grind
    · calc (2 / 3) / (G'.degree v + 1 + 1 : ℝ)
        _ ≤ (2 / 3) / (G'.degree v + 1 : ℝ) := by
          refine div_le_div_iff_of_pos_left (by grind) (by grind) (by grind) |>.mpr (by grind)
      grind
  else
    have this {c : ℝ} (hc : 0 ≤ c) : 0 ≤ c / (G'.degree v + 1 : ℝ) := by
      ring_nf
      exact Left.mul_nonneg hc <| inv_nonneg_of_nonneg (by grind)
    simp only [hA, ↓reduceIte, hB, hC, ge_iff_le]
    have H16 : 0 ≤ (6 : ℝ)⁻¹ := by grind
    have H56 : 0 ≤ 5 / (6 : ℝ) := by grind
    split_ifs
    all_goals simp only [H56, Left.add_nonneg H16, Nat.ofNat_nonneg, add_zero, ge_iff_le,
      inv_nonneg, one_div, this, zero_le_one]
    · refine Left.add_nonneg H16 <| this <| div_nonneg zero_le_four zero_le_three
    · refine Left.add_nonneg H16 <| this <| div_nonneg zero_le_two zero_le_three

-- lemma Corollary4 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
--     (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] {v : Fin n}
--     (h : G.degree v = G'.degree v + 1) : f G ABC v - f G' (ABC.demote v) v ≤ 1 / (6 : ℝ) := by
--   sorry

end Tripartition
end ABC
end CaroWeiType
