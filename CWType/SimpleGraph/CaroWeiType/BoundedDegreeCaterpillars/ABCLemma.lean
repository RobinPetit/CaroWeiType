import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.ABC
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claims

namespace CaroWeiType
namespace ABC

open Tripartition
open Finset
open SimpleGraph

theorem ABCLemma {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n) :
    Objective G ABC := by
  induction hcard : ABC.card using Nat.strong_induction_on generalizing G ABC with | h k ih
  if hk : k = 0 then
    refine ⟨∅, ?_, ?_, ?_, ?_⟩ <;>
    simp [respects, card_eq_zero.mp <| hk ▸ hcard, InducesForest, IsDegenerateSet]
  else
  have ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC' :=
    fun G' _ ABC' hcardABC' ↦ ih ABC'.card (hcard ▸ hcardABC') G' ABC' rfl
  sorry

end ABC
end CaroWeiType
