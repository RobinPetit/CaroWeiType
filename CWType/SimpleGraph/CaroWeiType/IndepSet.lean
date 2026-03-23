import CWType.SimpleGraph.CaroWeiType.Degenerate

namespace SimpleGraph
namespace CaroWeiType

open FiniteSimpleGraph
open Finset

private lemma notMem_of_empty_inter {n : ℕ} {s t : Finset (Fin n)} (h : s ∩ t = ∅) {x} :
    x ∈ t → x ∉ s := by
  intro ht hs
  suffices x ∈ (∅ : Finset _) by exact (List.mem_nil_iff x).mp this
  exact h ▸ mem_inter.mpr ⟨hs, ht⟩

theorem Is0DegenerateSet_iff_IsIndepSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) :
    G.IsDegenerateSet 0 s ↔ G.IsIndepSet s := by
  constructor
  · intro h x hx y hy hne
    obtain ⟨z, hz, hzdeg⟩ := h {x, y} (by grind) (by simp)
    simp only [mem_insert, mem_singleton] at hz
    simp only [degree_in, nonpos_iff_eq_zero, card_eq_zero] at hzdeg
    rcases hz with hz | hz
    · suffices y ∉ G.neighborFinset z by grind [mem_neighborFinset]
      refine notMem_of_empty_inter hzdeg (by grind)
    · subst hz
      suffices x ∉ G.neighborFinset z by grind [mem_neighborFinset, mem_neighborFinset_symm]
      refine notMem_of_empty_inter hzdeg (by grind)
  · intro h s' hs' hs'ne
    obtain ⟨x, hx⟩ := nonempty_def.mp <| nonempty_iff_ne_empty.mpr hs'ne
    refine ⟨x, hx, ?_⟩
    simp only [degree_in, nonpos_iff_eq_zero, card_eq_zero]
    ext y
    simp only [mem_inter, mem_neighborFinset, notMem_empty, iff_false, not_and]
    exact fun hxy hy ↦ h (hs' hx) (hs' hy) hxy.ne hxy

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
