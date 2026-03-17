import Mathlib.Combinatorics.SimpleGraph.Acyclic

import CWType.SimpleGraph.CaroWeiType.Degenerate

namespace SimpleGraph

open Finset

def InducesForest {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) : Prop :=
  G.IsDegenerateSet 1 s

def InducesLinearForest {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) : Prop :=
  G.InducesForest s ∧ ∀ x ∈ s, (G.neighborFinset x ∩ s).card ≤ 2

def InducesCaterpillar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) : Prop :=
  G.InducesLinearForest <| s \ {x ∈ s | (G.neighborFinset x ∩ s).card = 1}

end SimpleGraph
