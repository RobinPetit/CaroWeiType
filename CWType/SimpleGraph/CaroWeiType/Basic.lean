-- import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic

namespace SimpleGraph
namespace CaroWeiType

open Finset

def IsCaroWeiTypeLowerBound (f : ℕ → ℝ)
  (π : {n : ℕ} → SimpleGraph (Fin n) → Finset (Fin n) → Prop) :=
  ∀ {n : ℕ},
    ∀ G : SimpleGraph (Fin n),
      let _ := Classical.decRel G.Adj
      ∃ s : Finset (Fin n), π G s ∧ ∑ v, f (@SimpleGraph.degree _ G v (G.neighborSetFintype v)) ≤ #s

theorem CaroWeiTypeLowerBound_mono {π : {n : ℕ} → SimpleGraph (Fin n) → Finset (Fin n) → Prop}
    {f₁ f₂ : ℕ → ℝ} (hle : f₁ ≤ f₂) :
    IsCaroWeiTypeLowerBound f₂ π → IsCaroWeiTypeLowerBound f₁ π := by
  intro hf₂ n G
  obtain ⟨s, hs⟩ := hf₂ G
  refine ⟨s, ⟨hs.1, ?_⟩⟩
  let _ := Classical.decRel G.Adj
  refine le_trans (sum_le_sum fun v _ ↦ hle (G.degree v)) hs.2

end CaroWeiType
end SimpleGraph
#min_imports
