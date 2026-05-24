import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim1
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim5
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim6
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim7

open SimpleGraph
open Finset

namespace CaroWeiType
namespace ABC
namespace Tripartition

variable {V : Type} [Fintype V] [DecidableEq V]

private lemma solve_deg_le_2 {G : SimpleGraph V} [DecidableRel G.Adj]
    {ABC : Tripartition V} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC')
    {v w : V} (hBv : ABC.B v) (hdv : G.degree v = 3) (hvw : G.Adj v w)
    (hw : w ∈ ABC) (hdw : G.degree w ≤ 2) : Objective G ABC := by
  if hdw : G.degree w ≤ 1 then
    exact Claim5 hG ih ⟨_, hw, hdw⟩
  else if hAw : ABC.A w then
    exact Claim7 hG ih ⟨_, _, hdv, hBv, by grind, hAw, hvw⟩
  else
    exact Claim6 hG ih ⟨_, by grind, hAw⟩

private lemma _Claim8 {G : SimpleGraph V} [DecidableRel G.Adj]
    {ABC : Tripartition V} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC')
    {v x y : V} (hBv : ABC.B v) (hdegv : G.degree v = 3) (hx : G.Adj x v) (hy : G.Adj y v)
    (hne : x ≠ y) (hyx : f G ABC y ≤ f G ABC x) :
    ℓ G ABC x + ℓ G ABC y > 1 / 6 → Objective G ABC := by
  intro h
  have hv : v ∈ ABC := by grind [ABC.mem_iff]
  have hinABC {v₁ v₂} (h : G.Adj v₁ v₂) : v₁ ∈ ABC :=
    ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨v₂, h⟩
  if hdx : G.degree x ≤ 2 then
    exact solve_deg_le_2 hG ih hBv hdegv hx.symm (hinABC hx) hdx
  else if hdy : G.degree y ≤ 2 then
    exact solve_deg_le_2 hG ih hBv hdegv hy.symm (hinABC hy) hdy
  else
    have hγ : 1 / 3 ≤ γ G ABC x + γ G ABC y := by
      have hℓx : ℓ G ABC x ≤ 1 / 10 :=
        ℓ_le_1_over_10_of_3_le_degree <| Nat.succ_le_of_lt <| Nat.lt_of_not_le hdx
      have hℓy : ℓ G ABC y > 1 / 15 := by grind
      have hdy : G.degree y = 3 := by grind [ℓ_le_1_over_15_of_4_le_degree.mt (not_le.mpr hℓy)]
      rcases ABC.mem_iff.mp (hinABC hy) with hA | hB | hC
      · have hfy : f G ABC y = 1 / 2 := fA3 hA hdy
        have hfx : f G ABC x = 1 / 2 := by
          refine le_antisymm ?_ ?_
          · refine f_le_1_over_2_of_3_le_deg <| Nat.succ_le_of_lt <| not_le.mp hdx
          · exact le_trans (le_of_eq hfy.symm) hyx
        have hAx : ABC.A x := by
          rcases ABC.mem_iff.mp (hinABC hx) with h | h | h
          · exact h
          · have H : f G ABC x ≤ 1 / 3 := fB_le_13_if_2_le_deg h <| Nat.le_of_not_ge hdx
            rw [hfx] at H
            linarith
          · have H : f G ABC x ≤ 1 / 6 := fC_le_16_if_2_le_deg h <| Nat.le_of_not_ge hdx
            rw [hfx] at H
            linarith
        have hdx : G.degree x = 3 := by
          if hdx : 4 ≤ G.degree x then
            have hobj : f G ABC x ≤ fA 4 := by simp only [f, hAx, ↓reduceDIte, fA_decreasing hdx]
            rw [hfx] at hobj
            simp only [fA, four_ne_zero, ↓reduceIte, Nat.add_one_add_one_ne_one] at hobj
            linarith
          else
            grind
        rw [γA3 hA hdy, γA3 hAx hdx]
        linarith
      · simp [ℓ, hB, hdy] at hℓy
        grind
      · simp [ℓ, hC, hdy] at hℓy
        grind
    refine Claim1 hv hG ih ?_
    refine le_trans (fB3 hBv hdegv ▸ hγ) ?_
    have h' : ∑ w ∈ {x, y}, γ G ABC w ≤ ∑ w ∈ G.neighborFinset v, γ G ABC w := by
      refine sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with h | h <;> { subst h; simp [hx.symm, hy.symm] }
      · exact fun _ _ _ ↦ γ_nonneg
    grind

lemma Claim8 {G : SimpleGraph V} [DecidableRel G.Adj]
    {ABC : Tripartition V} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC')
    {v x y : V} (hBv : ABC.B v) (hdegv : G.degree v = 3) (hx : G.Adj x v) (hy : G.Adj y v)
    (hne : x ≠ y) :
    ℓ G ABC x + ℓ G ABC y > 1 / 6 → Objective G ABC := by
  if hyx : f G ABC y ≤ f G ABC x then
    exact _Claim8 hG ih hBv hdegv hx hy hne hyx
  else
    rw [add_comm (ℓ G ABC x) (ℓ G ABC y)]
    exact _Claim8 hG ih hBv hdegv hy hx hne.symm (le_of_lt <| not_le.mp hyx)

lemma Corollary8 {G : SimpleGraph V} [DecidableRel G.Adj]
    {ABC : Tripartition V} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC')
    {v x y : V} (hBv : ABC.B v) (hdegv : G.degree v = 3) (hx : G.Adj x v) (hy : G.Adj y v)
    (hne : x ≠ y) :
    Objective G ABC ∨ ℓ G ABC x + ℓ G ABC y ≤ 1 / 6 := by
  if hℓ : ℓ G ABC x + ℓ G ABC y ≤ 1 / 6 then
    exact Or.inr hℓ
  else
    exact Or.inl <| Claim8 hG ih hBv hdegv hx hy hne (not_le.mp hℓ)

lemma Corollary8' {G : SimpleGraph V} [DecidableRel G.Adj]
    {ABC : Tripartition V} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC')
    {v x : V} (hBv : ABC.B v) (hdegv : G.degree v = 3) (hx : G.Adj x v) :
    Objective G ABC ∨ ℓ G ABC x ≤ 1 / 10 := by
  if hℓx : ℓ G ABC x ≤ 1 / 10 then
    exact Or.inr hℓx
  else
    have := ℓ_le_1_over_10_of_3_le_degree.mt hℓx
    refine Or.inl <| solve_deg_le_2 hG ih hBv hdegv hx.symm ?_ (by linarith)
    exact ABC.mem_toFinset.mpr <| mem_def.mpr <| hG <| G.mem_support.mpr ⟨v, hx⟩

end Tripartition
end ABC
end CaroWeiType
