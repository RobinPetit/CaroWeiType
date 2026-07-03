import Mathlib.Combinatorics.SimpleGraph.Acyclic

import CWType.SimpleGraph.CaroWeiType.Degenerate

namespace SimpleGraph

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (s : Finset V)

def InducesForest : Prop :=
  G.IsDegenerateSet 1 s

def InducesLinearForest : Prop :=
  G.InducesForest s ∧ ∀ x ∈ s, G.degree_in s x ≤ 2

def InducesForestOfCaterpillars : Prop :=
  G.InducesLinearForest <| s \ {x ∈ s | G.degree_in s x = 1}

def InducesForestOfStars : Prop :=
  G.IsIndepSet <| ↑(s \ {x ∈ s | G.degree_in s x = 1})

end SimpleGraph
