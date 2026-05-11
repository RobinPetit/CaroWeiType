import CWType.SimpleGraph.CaroWeiType.Degenerate

namespace CaroWeiType

namespace GraphParameter

universe u u' in
private lemma IndepSet_of_graph_iso {V : Type u} {V' : Type u'} [DecidableEq V']
    {G : SimpleGraph V} {G' : SimpleGraph V'} {s : Finset V} (φ : G ≃g G') (h : G.IsIndepSet s) :
    G'.IsIndepSet (s.image φ) := by
  intro v hv w hw hne
  simp only [Finset.coe_image, Set.mem_image, SetLike.mem_coe] at hv hw
  obtain ⟨v', hv's, hv'⟩ := hv
  obtain ⟨w', hw's, hw'⟩ := hw
  suffices ¬G'.Adj (φ.toEquiv v') (φ.toEquiv w') by
    simp only [RelIso.coe_fn_toEquiv, hv', hw'] at this
    exact this
  refine not_iff_not.mpr φ.map_rel_iff' |>.mpr <| h hv's hw's ?_
  refine ne_of_ne_congr φ ?_
  rw [hv', hw']
  exact hne

def IndepSet : GraphParameter where
  toFun := fun G s ↦ G.graph.IsIndepSet s
  invariant := by
    intro _ _ _ _ _ _ G G' φ s
    refine ⟨IndepSet_of_graph_iso φ, ?_⟩
    suffices (s.image φ).image φ.symm = s by
      intro h
      exact this ▸ IndepSet_of_graph_iso φ.symm h
    ext
    simp only [Finset.mem_image, exists_exists_and_eq_and, RelIso.symm_apply_apply, exists_eq_right]

end GraphParameter
end CaroWeiType

namespace CaroWeiType

open SimpleGraph
open Finset

theorem Is0DegenerateSet_iff_IsIndepSet {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    G.IsDegenerateSet 0 s ↔ G.IsIndepSet s := by
  constructor
  · intro h x hx y hy hne
    obtain ⟨z, hz, hzdeg⟩ := h {x, y} (by grind) (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [degree_in, nonpos_iff_eq_zero, Finset.card_eq_zero] at hzdeg
    rcases hz with hz | hz
    · suffices y ∉ G.neighborFinset z by grind [mem_neighborFinset]
      refine notMem_of_empty_inter_of_mem hzdeg (by grind)
    · subst hz
      suffices x ∉ G.neighborFinset z by grind [mem_neighborFinset, mem_neighborFinset_symm]
      refine notMem_of_empty_inter_of_mem hzdeg (by grind)
  · intro h s' hs' hs'ne
    obtain ⟨x, hx⟩ := Finset.nonempty_def.mp <| Finset.nonempty_iff_ne_empty.mpr hs'ne
    refine ⟨x, hx, ?_⟩
    simp only [degree_in, nonpos_iff_eq_zero, Finset.card_eq_zero]
    ext y
    simp only [Finset.mem_inter, mem_neighborFinset, Finset.notMem_empty, iff_false, not_and]
    exact fun hxy hy ↦ h (hs' hx) (hs' hy) hxy.ne hxy

theorem IndepSet_LowerBound_iff_0DegenerateSet_LowerBound (f : ℕ → ℝ) :
    IsCaroWeiTypeLowerBound f GraphParameter.IndepSet
      ↔ IsCaroWeiTypeLowerBound f (GraphParameter.DegenerateSet 0) := by
  constructor
  · intro h _ _ _ G
    obtain ⟨s, hs, hcard⟩ := h G
    exact ⟨s, Is0DegenerateSet_iff_IsIndepSet G.graph s |>.mpr hs, hcard⟩
  · intro h _ _ _ G
    obtain ⟨s, hs, hcard⟩ := h G
    exact ⟨s, Is0DegenerateSet_iff_IsIndepSet G.graph s |>.mp hs, hcard⟩

noncomputable abbrev cw_bound := aks_bound 0

theorem IndepSet_LowerBound_iff (f : ℕ → ℝ) :
    IsCaroWeiTypeLowerBound f (GraphParameter.IndepSet) ↔ f ≤ cw_bound :=
  (IndepSet_LowerBound_iff_0DegenerateSet_LowerBound f).trans (kDegenerateSet_LowerBound_iff f 0)

end CaroWeiType
