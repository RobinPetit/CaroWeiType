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
  (π : {n : ℕ} → SimpleGraph (Fin n) → Finset (Fin n) → Prop) :=
  ∀ {n : ℕ},
    ∀ G : SimpleGraph (Fin n),
      let _ := Classical.decRel G.Adj  -- FIXME: get rid of this
      ∃ s : Finset (Fin n), π G s ∧ ∑ v, f (@SimpleGraph.degree _ G v (G.neighborSetFintype v)) ≤ #s
```

Caro-Wei's theorem (1979, 1981) states that $\alpha(G) \ge \sum_{v \in V(G)} \frac {1}{d(v) + 1}$.
Furthermore this bound is tight (in the sense that any such lower bound must satisfy $f(d) \le \frac {1}{d(v) + 1}$ (as witnessed by the complete graphs $K_n$.

In Lean, this theorem is formalised by:
```lean4
noncomputable abbrev cw_bound : ℕ → ℝ := fun d ↦ (d + 1 : ℝ)⁻¹

theorem IndepSet_LowerBound_iff (f : ℕ → ℝ) :
    IsCaroWeiTypeLowerBound f (fun {n : ℕ} (G : SimpleGraph (Fin n)) s ↦ G.IsIndepSet s)
      ↔ f ≤ cw_bound
```

# License

See the [LICENSE](https://github.com/RobinPetit/graphs-in-lean/blob/main/LICENSE) (copied from `https://github.com/non-ai-licenses/non-ai-licenses/tree/main`)

# Features

# Done

- [x] Generic definition
- [x] proof of Caro-Wei's theorem (independent sets)

# TODO

- [ ] get rid of `Classical.propDecidable`
- [ ] bound for $k$-degenerate induced subgraphs
- [ ] bound for degree-bounded induced caterpillars
