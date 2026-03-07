# Caro-Wei type lower bounds in Lean

Formalisation of Caro-Wei type lower bounds for graph parameters.

The general definition is as follows: a function $f : ℕ → ℝ$ is called a
_Caro-Wei type lower bound_ for the graph parameter $\pi$ whenever the following
inequality holds for every graph $G = (V, E)$:

$$\pi(G) \ge \sum_{v \in V} f(d_G(v)).$$

Conceptually, these bounds only depend on the degree distribution of the graph.

The Lean definition provided in this module is:
```lean4
def IsCaroWeiTypeLowerBound (f : ℕ → ℝ)
  (π : {n : ℕ} → FiniteSimpleGraph n → Finset (Fin n) → Prop) :=
  ∀ {n : ℕ},
    ∀ G : FiniteSimpleGraph n,
      ∃ s : Finset (Fin n), π G s
        ∧ ∑ v, f (G.graph.degree v) ≤ #s
```

where `FiniteSimpleGraph` is defined as:
```lean4
structure FiniteSimpleGraph (n : ℕ) where
  graph : SimpleGraph (Fin n)
  decAdj : DecidableRel graph.Adj := by aesop_graph
```

This structure is used instead of `SimpleGraph` so that `SimpleGraph.degree` can be used.
Recall that `SimpleGraph.degree` is defined by:
```lean4
SimpleGraph.degree.{u_1} {V : Type u_1} (G : SimpleGraph V) (v : V) [Fintype ↑(G.neighborSet v)] : ℕ
```
And `Fintype (G.neighborSet v)` can be automatically deduced by `Fintype V` and `DecidableRel G.Adj`.

Caro-Wei's theorem (1979, 1981) states that $\alpha(G) \ge \sum_{v \in V(G)} \frac {1}{d(v) + 1}$.
Furthermore this bound is tight (in the sense that any such lower bound must satisfy $f(d) \le \frac {1}{d(v) + 1}$ (as witnessed by the complete graphs $K_n$.

In Lean, this theorem is formalised by:
```lean4
noncomputable abbrev cw_bound : ℕ → ℝ := fun d ↦ (d + 1 : ℝ)⁻¹

theorem IndepSet_LowerBound_iff (f : ℕ → ℝ) :
    IsCaroWeiTypeLowerBound f (fun {n : ℕ} (G : FiniteSimpleGraph n) s ↦ G.graph.IsIndepSet s)
      ↔ f ≤ cw_bound := by
```

# License

See the [LICENSE](https://github.com/RobinPetit/graphs-in-lean/blob/main/LICENSE) (copied from `https://github.com/non-ai-licenses/non-ai-licenses/tree/main`)

# Features

# Done

- [x] Generic definition
- [x] proof of Caro-Wei's theorem (independent sets)
- [x] get rid of `Classical.propDecidable` (by defining `FiniteSimpleGraph`)

# TODO

- [ ] bound for $k$-degenerate induced subgraphs
- [ ] bound for degree-bounded induced caterpillars
