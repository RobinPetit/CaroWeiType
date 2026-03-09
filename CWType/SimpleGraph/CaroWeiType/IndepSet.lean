import CWType.SimpleGraph.CaroWeiType.Degenerate

namespace SimpleGraph
namespace CaroWeiType

open FiniteSimpleGraph
open Finset

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
