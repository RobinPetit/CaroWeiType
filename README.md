# Caro-Wei type lower bounds in Lean

## Context

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

## Proved characterisations

### Caro-Wei's theorem for independent sets

Caro-Wei's theorem (1979, 1981) states that $\alpha(G) \ge \sum_{v \in V(G)} \frac {1}{d(v) + 1}$.
Furthermore this bound is tight (in the sense that any such lower bound must satisfy $f(d) \le \frac {1}{d(v) + 1}$ (as witnessed by the complete graphs $K_n$).

In Lean, this theorem is formalised by (see `IndepSet.lean`):
```lean4
namespace CaroWeiType

-- Conceptually: noncomputable abbrev cw_bound : ℕ → ℝ := fun d ↦ (d + 1 : ℝ)⁻¹
-- but cw_bound is actually definde as `aks_bound 0` (see below)

theorem IndepSet_LowerBound_iff (f : ℕ → ℝ) :
    IsCaroWeiTypeLowerBound f (fun {n : ℕ} (G : FiniteSimpleGraph n) s ↦ G.graph.IsIndepSet s)
      ↔ f ≤ cw_bound := by
```

The proof in itself just consists in (1) the equivalence of $0$-degenerate sets and independent sets, and (2) Alon-Kahn-Seymour's theorem (see below).

### Alon-Kahn-Seymour's theorem for $k$-degenerate induced subgraphs

Alon-Kahn-Seymour's theorem (1987) states that if $\alpha_k(G)$ denotes the maximal size of an induced $k$-degenerate subgraph,
then $\alpha_k(G) \ge \sum_{v \in V(G)} \min\{1, \frac {k + 1}{d(v) + 1}\}$,
and this bound is tight (as witnessed by by the complete graphs).

This is formalised as follows (see `Degenerate.lean`):
```lean4
namespace SimpleGraph

abbrev IsDegenerateSet {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (s : Finset V) :=
  ∀ t ⊆ s, t ≠ ∅ → ∃ x ∈ t, {y ∈ t | G.Adj x y}.card ≤ k

namespace CaroWeiType

noncomputable def aks_bound (k : ℕ) (d : ℕ) : ℝ :=
  min 1 ((k + 1) * (d + 1 : ℝ)⁻¹)

theorem kDegenerateSet_LowerBound_iff (f : ℕ → ℝ) :
    ∀ k : ℕ,
      IsCaroWeiTypeLowerBound f (fun G s ↦ G.graph.IsDegenerateSet k s)
        ↔ f ≤ aks_bound k := by
```


# License

See the [LICENSE](https://github.com/RobinPetit/graphs-in-lean/blob/main/LICENSE) (copied from `https://github.com/non-ai-licenses/non-ai-licenses/tree/main`)

# Features

## WIP

Complete characterization of CW-type lower bounds for induced bounded-degree caterpillars

- [ ] ABC Lemma
  - [x] Claim 0
  - [x] Claim 1
  - [x] Claim 2
  - [x] Claim 3
  - [x] Claim 4
  - [x] Claim 5
  - [x] Claim 6
  - [x] Claim 7
  - [x] Claim 8
  - [x] Claim 9
  - [x] Claim 10
  - [x] Claim 11
  - [ ] Claim 12
  - [ ] Claim 13
  - [ ] define `vstar`
  - [ ] Claim 14
  - [ ] Claim 15
  - [ ] Claim 16
  - [ ] Claim 17
  - [ ] Claim 18
  - [ ] Claim 19
  - [ ] Claim 20
  - [ ] Finish

## Done

- [x] Generic definition
- [x] get rid of `Classical.propDecidable` (by defining `FiniteSimpleGraph`)
- [x] proof for independent sets (Caro-Wei)
- [x] proof for $k$-degenerate induced subgraphs (Alon-Khhan-Seymour)

## TODO

- [ ] bound for induced caterpillars (5/6 on leaves)
- [ ] bound for degree-bounded induced caterpillars
- [ ] bound for degree-bounded induced forests of stars
