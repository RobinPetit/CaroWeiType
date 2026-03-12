import CWType.SimpleGraph.CaroWeiType.Degenerate

namespace SimpleGraph
namespace CaroWeiType

open FiniteSimpleGraph
open Finset

theorem Is0DegenerateSet_iff_IsIndepSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) :
    G.IsDegenerateSet 0 s ↔ G.IsIndepSet s := by
  constructor
  · intro h x hx y hy hne hxy
    obtain ⟨z, ⟨hz, h⟩⟩ := h {x, y} (by grind) (by simp)
    simp only [mem_insert, mem_singleton] at hz
    simp only [nonpos_iff_eq_zero, card_eq_zero, filter_eq_empty_iff, mem_insert, mem_singleton,
      forall_eq_or_imp, forall_eq] at h
    cases hz with
    | inl hz => exact h.2 (hz ▸ hxy)
    | inr hz => exact h.1 <| (hz ▸ hxy.symm)
  · intro h s' hs' hs'ne
    obtain x := @Classical.choice s' <| Nonempty.to_subtype (by grind)
    refine ⟨x.1, x.2, ?_⟩
    simp only [nonpos_iff_eq_zero, card_eq_zero, filter_eq_empty_iff]
    intro y hy
    if hxy : x = y then
      exact hxy.symm ▸ G.irrefl
    else
      exact h (hs' x.2) (hs' hy) hxy

theorem IndepSet_LowerBound_iff_1DegenerateSet_LowerBound (f : ℕ → ℝ) :
    IsCaroWeiTypeLowerBound f (fun G s ↦ G.graph.IsIndepSet s)
      ↔ IsCaroWeiTypeLowerBound f (fun G s ↦ G.graph.IsDegenerateSet 0 s) := by
  constructor <;> refine fun h n G ↦ ⟨h G |>.choose, ?_⟩
  · obtain ⟨hsprop, hscard⟩ := h G |>.choose_spec
    refine ⟨?_, hscard⟩
    exact Is0DegenerateSet_iff_IsIndepSet G.graph _ |>.mpr hsprop
  · obtain ⟨hsprop, hscard⟩ := h G |>.choose_spec
    refine ⟨?_, hscard⟩
    exact Is0DegenerateSet_iff_IsIndepSet G.graph _ |>.mp hsprop

noncomputable abbrev cw_bound := aks_bound 0

theorem IndepSet_LowerBound_iff (f : ℕ → ℝ) :
    IsCaroWeiTypeLowerBound f (fun {n : ℕ} (G : FiniteSimpleGraph n) s ↦ G.graph.IsIndepSet s)
      ↔ f ≤ cw_bound := by
  exact Iff.trans
    (IndepSet_LowerBound_iff_1DegenerateSet_LowerBound f)
    (kDegenerateSet_LowerBound_iff f 0)

end CaroWeiType
end SimpleGraph
#min_imports
