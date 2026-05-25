import Mathlib.Combinatorics.SimpleGraph.Acyclic

import CWType.SimpleGraph.CaroWeiType.Degenerate

namespace SimpleGraph

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def InducesForest (s : Finset V) : Prop :=
  G.IsDegenerateSet 1 s

def InducesLinearForest (s : Finset V) : Prop :=
  G.InducesForest s ∧ ∀ x ∈ s, G.degree_in s x ≤ 2

def InducesCaterpillar (s : Finset V) : Prop :=
  G.InducesLinearForest <| s \ {x ∈ s | G.degree_in s x = 1}

end SimpleGraph
