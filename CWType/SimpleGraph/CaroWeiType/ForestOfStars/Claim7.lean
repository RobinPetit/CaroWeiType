import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim6
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Lemmas

open SimpleGraph
open Finset

namespace CaroWeiType
namespace AB
namespace Bipartition

variable {V : Type} [Fintype V] [DecidableEq V]

lemma Claim7 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (hne : u ≠ w)
    (hdv : G.degree v = 3) (hdu : G.degree u = 2) (hdw : G.degree w = 2)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  obtain ⟨x, hx, hunex, hvnex⟩ := Finset_get_other_other (le_of_eq <| hdv.symm) u w
  match Corollary4 hG ih, Claim6' hG ih with
  | Or.inr h, _ => exact h
  | _, Or.inr h => exact h
  | Or.inl h, Or.inl h' => ?_
  have hv : v ∈ AB := AB.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨w, hvw⟩
  refine Claim1 hv hG ih ?_
  suffices f G AB v ≤ γ G AB u + γ G AB w + γ G AB x by
    refine this.trans ?_
    suffices γ G AB u + γ G AB w + γ G AB x = ∑ z ∈ ({u, w, x} : Finset _), γ G AB z by
      rw [this]
      refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ γ_nonneg
      grind [mem_neighborFinset, Adj.symm]
    grind
  have H : ∀ z ∈ AB.toFinset, AB.A z := by grind
  have hAv : AB.A v := H _ (hG <| G.mem_support.mpr ⟨w, hvw⟩)
  have hAu : AB.A u := H _ (hG <| G.mem_support.mpr ⟨v, huv⟩)
  have hAw : AB.A w := H _ (hG <| G.mem_support.mpr ⟨v, hvw.symm⟩)
  simp only [fA3 hAv hdv, γA2 hAu hdu, γA2 hAw hdw]
  have : x ∈ AB.toFinset := hG <| G.mem_support.mpr ⟨v, Adj.symm <| mem_neighborFinset .. |>.mp hx⟩
  grind

end Bipartition
end AB
end CaroWeiType
