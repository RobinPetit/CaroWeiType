import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

private lemma f_le_16_of_deg_ge_3 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {v : Fin n} : 3 ≤ G.degree v → (2 / 3) / (G.degree v + 1 : ℝ) ≤ 1 / 6 := by
  intro h
  calc (2 / 3) / (G.degree v + 1 : ℝ)
    _ ≤ (2 / 3) / (4 : ℝ) := by
      refine div_le_div_iff_of_pos_left two_thirds_pos add_one_pos four_pos |>.mpr ?_
      rw [← Nat.cast_one, ← Nat.cast_four, ← Nat.cast_add]
      refine Nat.cast_le.mpr <| by lia
    _ ≤ 1 / 6 := by linarith

lemma Claim4_A {n : ℕ} (G : SimpleGraph (Fin n)) [G.LocallyFinite] (ABC : Tripartition n)
    (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] {v : Fin n} {s : Finset _} (hv : v ∈ s)
    (hAv : ABC.A v) (h : G.degree v ≥ G'.degree v + 1) :
    f G ABC v - f G' (ABC.demote_finset s) v ≤ 1 / (6 : ℝ) := by
  simp only [f, hAv, ↓reduceDIte, not_A_of_B, tsub_le_iff_right, ABC.demote_finset_from_A hAv hv]
  refine le_trans (fA_decreasing h) ?_
  simp only [fA, fB]
  have : 2 / (G'.degree v + 1 + 1 : ℝ) ≤ 1 := by
    ring_nf
    calc ((2 : ℝ) + G'.degree v)⁻¹ * 2
      _ ≤ (2 : ℝ)⁻¹ * 2 := by
        refine mul_le_mul_iff_of_pos_right two_pos |>.mpr
          <| inv_anti₀ two_pos <| by simp only [le_add_iff_nonneg_right, Nat.cast_nonneg]
      _ = 1 := inv_mul_cancel₀ <| NeZero.ne _
  split_ifs
  any_goals grind
  · calc 2 / ((((G'.degree v + 1) : ℕ) : ℝ) + 1)
      _ = 2 / (4 : ℝ) := by
        refine congrArg (fun x ↦ 2 / x) ?_
        rename_i h
        rw [h]
        lia
      _ ≤ 1 / 6 + 1 / 3 := by linarith
  · calc 2 / ((((G'.degree v + 1) : ℕ) : ℝ) + 1)
      _ = 2 * (G'.degree v + 1 + 1 : ℝ)⁻¹ := by lia
      _ ≤ 2 * (G'.degree v + 1 : ℝ)⁻¹ := by
        simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
        exact inv_anti₀ (Nat.cast_add_one_pos _) le_add_one
      _ = (2 / 3) * (G'.degree v + 1 : ℝ)⁻¹ + (4 / 3) * (G'.degree v + 1 : ℝ)⁻¹ := by
        linarith
      _ ≤ 1 / 6 + (4 / 3) * (G'.degree v + 1 : ℝ)⁻¹ := by
        simp only [add_le_add_iff_right]
        exact f_le_16_of_deg_ge_3 <| by lia

lemma Claim4_B {n : ℕ} (G : SimpleGraph (Fin n)) [G.LocallyFinite] (ABC : Tripartition n)
    (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] {v : Fin n} {s : Finset _} (hv : v ∈ s)
    (hBv : ABC.B v) (h : G.degree v ≥ G'.degree v + 1) :
    f G ABC v - f G' (ABC.demote_finset s) v ≤ 1 / (6 : ℝ) := by
  simp only [f, hBv, not_A_of_B, ↓reduceDIte, ABC.demote_finset_from_B hBv hv, not_A_of_C,
    not_B_of_C, tsub_le_iff_right]
  refine le_trans (fB_decreasing h) ?_
  simp only [fB, fC]
  split_ifs
  any_goals grind
  · calc (4 / 3) / ((((G'.degree v + 1) : ℕ) : ℝ) + 1)
      _ ≤ (4 / 3) / (2 + 1 + 1) := by
        refine div_le_div_iff_of_pos_left four_thirds_pos add_one_pos (by lia) |>.mpr ?_
        simp only [Nat.cast_add, Nat.cast_one, add_le_add_iff_right, Nat.ofNat_le_cast]
        grind
    linarith
  · calc (4 / 3) / ((((G'.degree v + 1) : ℕ) : ℝ) + 1)
      _ ≤ (4 / 3) / (G'.degree v + 1 : ℝ) :=
        div_le_div_iff_of_pos_left four_thirds_pos add_one_pos add_one_pos |>.mpr <| by lia
      _ = (2 / 3) / (G'.degree v + 1 : ℝ) + (2 / 3) / (G'.degree v + 1 : ℝ) := by
        rw [← two_mul, mul_div_assoc']
        refine congrArg (· / _) (by linarith)
      _ ≤ 1 / 6 + (2 / 3) / (G'.degree v + 1 : ℝ) := by
        simp only [add_le_add_iff_right]
        exact f_le_16_of_deg_ge_3 (by lia)

lemma Claim4_C {n : ℕ} (G : SimpleGraph (Fin n)) [G.LocallyFinite] (ABC : Tripartition n)
    (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] {v : Fin n} {s : Finset _}
    (hCv : ABC.C v) (h : G.degree v ≥ G'.degree v + 1) :
    f G ABC v - f G' (ABC.demote_finset s) v ≤ 1 / (6 : ℝ) := by
  simp only [f, hCv, not_A_of_C, ↓reduceDIte, not_B_of_C, ABC.demote_finset_from_C hCv]
  have H1 : fC (G.degree v) - fC (G'.degree v) ≤ fC (G'.degree v) - fC (G'.degree v) := by
    simp only [tsub_le_iff_right, sub_add_cancel]
    exact fC_decreasing <| Nat.le_of_succ_le h
  refine le_trans H1 ?_
  grind

lemma Claim4 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    {G' : SimpleGraph (Fin n)} [G'.LocallyFinite] {v : Fin n} {s : Finset _} (hv : v ∈ s)
    (h : G.degree v ≥ G'.degree v + 1) :
    f G ABC v - f G' (ABC.demote_finset s) v ≤ 1 / (6 : ℝ) := by
  if hA : ABC.A v then
    exact Claim4_A G ABC G' hv hA h
  else if hB : ABC.B v then
    exact Claim4_B G ABC G' hv hB h
  else if hC : ABC.C v then
    exact Claim4_C G ABC G' hC h
  else
    simp only [f, hA, ↓reduceDIte, hB, hC, fA, fB, one_div, fC, dite_eq_ite, zero_sub]
    have this {c : ℝ} (hc : 0 ≤ c) : 0 ≤ c / (G'.degree v + 1 : ℝ) := by
      ring_nf
      refine Left.mul_nonneg hc <| inv_nonneg_of_nonneg <| le_of_lt one_add_pos
    have H16 : 0 ≤ (6 : ℝ)⁻¹ := by
      rw [← one_div]
      exact le_of_lt one_sixth_pos
    split_ifs
    any_goals grind

lemma Claim4' {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    {G' : SimpleGraph (Fin n)} [G'.LocallyFinite] {v : Fin n}
    (h : G.degree v ≥ G'.degree v + 1) :
    f G ABC v - f G' (ABC.demote v) v ≤ 1 / (6 : ℝ) := by
  exact Claim4 (mem_singleton.mpr rfl) h

end Tripartition
end ABC
end CaroWeiType
