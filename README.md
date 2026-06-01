# Caro-Wei type lower bounds in Lean

## Context

Formalisation of Caro-Wei type lower bounds for graph parameters.

The general definition is as follows: a function $f : ℕ → ℝ$ is called a
_Caro-Wei type lower bound_ for the graph parameter $\pi$ whenever the following
inequality holds for every graph $G = (V, E)$:

```math
\pi(G) \ge \sum_{v \in V} f(d_G(v)).
```

Conceptually, they are the bounds that only depend on the degree distribution of the graph.

More specifically, we will only consider parameters of the form (where $\mathcal C$ is an arbitrary class of graphs):

```math
\alpha_{\mathcal C}(G) := \max \left\{|s| : s \subseteq V(G) \text{ and } G[s] \sqsubseteq \mathcal C\right\},
```

where $G \sqsubseteq \mathcal C$ denotes the fact that $G$ is isomorphic to some graph in $\mathcal C$.

For instance, if $\mathcal I = \{([n], \varnothing) : n \in \mathbb N\}$ is the class of finite empty graphs, then $\alpha_{\mathcal I} = \alpha$ is the independence number.

First of all, here is the definition of a _graph parameter_:
a function that associates to every (finite) graph $G$ a predicate that determines wether or not a given (finite) set of vertices satisfies the desired property.
That function must also be an invariant, i.e. if $\varphi$ is an isomorphism between two graphs $G$ and $G'$, then $s$ satisfies the property in $G$ if and only if $\varphi$(s)$ satisfies the property in $G'$.
```lean4
structure GraphParameter where
  toFun : {V : Type} → [DecidableEq V] → [Fintype V] →
    SimpleGraph V → [DecidableRel G.Adj] → Finset V → Prop
  invariant : ∀ {V V' : Type} [DecidableEq V] [DecidableEq V'] [Fintype V] [Fintype V']
    (G : SimpleGraph V) [DecidableRel G.Adj] (G' : SimpleGraph V') [DecidableRel G'.Adj]
    (φ : G.graph ≃g G'.graph) (s : Finset V), toFun G s ↔ toFun G' (s.image φ.toFun)
```

The Lean definition provided in this module is:
```lean4
def IsCaroWeiTypeLowerBound (f : ℕ → ℝ) (π : GraphParameter) :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ∃ s : Finset V, π.toFun G s ∧ ∑ v, f (G.graph.degree v) ≤ #s
```

This structure is used instead of `SimpleGraph` so that `SimpleGraph.degree` can be used.
Recall that `SimpleGraph.degree` is defined by:
```lean4
SimpleGraph.degree.{u} {V : Type u} (G : SimpleGraph V) (v : V) [Fintype ↑(G.neighborSet v)] : ℕ
```
And `Fintype ↑(G.neighborSet v)` can be automatically deduced by `Fintype V` and `DecidableRel G.Adj`.

## Proved characterisations

### Caro-Wei's theorem for independent sets

Caro-Wei's theorem (1979, 1981) states that $\alpha(G) \ge \sum_{v \in V(G)} \frac {1}{d(v) + 1}$.
Furthermore this bound is tight (in the sense that any such lower bound must satisfy $f(d) \le \frac {1}{d(v) + 1}$ (as witnessed by the complete graphs $K_n$).

In Lean, this theorem is formalised by (see `IndepSet.lean`):
```lean4
namespace CaroWeiType

def IndepSet : GraphParameter where
  toFun := fun G s ↦ G.graph.IsIndepSet s
  invariant := sorry  -- ...

-- Conceptually: noncomputable abbrev cw_bound : ℕ → ℝ := fun d ↦ (d + 1 : ℝ)⁻¹
-- but cw_bound is actually definde as `aks_bound 0` (see below)

theorem IndepSet_LowerBound_iff (f : ℕ → ℝ) :
    IsCaroWeiTypeLowerBound f (GraphParameter.IndepSet) ↔ f ≤ cw_bound :=
  sorry -- ...
```

The proof in itself just consists in (1) the equivalence of $0$-degenerate sets and independent sets, and (2) Alon-Kahn-Seymour's theorem (see below).

### Alon-Kahn-Seymour's theorem for $k$-degenerate induced subgraphs

Alon-Kahn-Seymour's theorem ([1987](https://www.tau.ac.il/~nogaa/PDFS/Publications/Large%20induced%20degenerate%20subgraphs%20in%20graphs.pdf)) states that if $\alpha_k(G)$ denotes the maximal size of an induced $k$-degenerate subgraph, then

```math
\alpha_k(G) \ge \sum_{v \in V(G)} \min\left(1, (k + 1) / (d(v) + 1)\right),
```

and this bound is tight (as witnessed by by the complete graphs).

This is formalised as follows (see `Degenerate.lean`):
```lean4
namespace SimpleGraph

abbrev IsDegenerateSet {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (s : Finset V) :=
  ∀ t ⊆ s, t ≠ ∅ → ∃ x ∈ t, {y ∈ t | G.Adj x y}.card ≤ k

namespace CaroWeiType

def DegenerateSet (k : ℕ) : GraphParameter where
  toFun := fun G s ↦ G.graph.IsDegenerateSet k s
  invariant := sorry -- ...

noncomputable def aks_bound (k : ℕ) (d : ℕ) : ℝ :=
  min 1 ((k + 1) * (d + 1 : ℝ)⁻¹)

theorem kDegenerateSet_LowerBound_iff (f : ℕ → ℝ) :
    ∀ k : ℕ,
      IsCaroWeiTypeLowerBound f (GraphParameter.DegenerateSet k)
        ↔ f ≤ aks_bound k :=
  sorry -- ...
```

### Joret-Petit's theorem for caterpillars of bounded degree

Joret-Petit's theorem ([2025](https://arxiv.org/abs/2403.17568)) states that if $\mathcal C_k$ is the class of forests of caterpillars of maximum degree at most $k$,
then for every $0 \le \varepsilon \le \frac{2}{(k+1)(k+2)}$, the following inequality holds

```math
\alpha_{\mathcal C_k}(G) \ge \sum_{v \in V(G)}f_{k,\varepsilon}(d(v)),
```

where

```math
\begin{aligned}
    f(0) &= 1, \\
    f(1) &= 1 - \varepsilon, \\
    f(d) &= \frac{2}{d+1} &&\text{if } 2 \le d \le k,\\
    f(d) &= \min\{(k+1)\varepsilon, 2 / (d+1)\} &&\text{if } k+1 \le d
\end{aligned}
```

Furthermore, all those functions are tight, and no other extremal function exists.

Definiing this in Lean requires the definition of a linear forest and of a caterpillar:
```lean4
variable {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def InducesForest (s : Finset V) : Prop :=
  G.IsDegenerateSet 1 s

def InducesLinearForest (s : Finset V) : Prop :=
  G.InducesForest s ∧ ∀ x ∈ s, G.degree_in s x ≤ 2

def InducesCaterpillar (s : Finset V) : Prop :=
  G.InducesLinearForest <| s \ {x ∈ s | G.degree_in s x = 1}
```

The theorem is therefore:
```lean4
def BoundedDegreeCaterpillar (k : ℕ) : GraphParameter where
  toFun := fun G s ↦ G.graph.InducesCaterpillar s ∧ ∀ v ∈ s, G.graph.degree_in s v ≤ k
  invariant := sorry -- ...

private noncomputable def φ (k : ℕ) (ε : ℝ) : ℕ → ℝ := by
  intro d
  if hd : d = 0 then exact 1
  else if d = 1 then exact 1 - ε
  else if 2 ≤ d ∧ d ≤ k then exact 2 / (d + 1 : ℝ)
  else exact min ((k + 1) * ε) (2 / (d + 1 : ℝ))

theorem BoundedDegreeCaterpillar_LowerBound_iff (f : ℕ → ℝ) :
    ∀ k : ℕ, 2 ≤ k →
      (IsCaroWeiTypeLowerBound f (GraphParameter.BoundedDegreeCaterpillar k)
      ↔ ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ 2 / ((k + 1) * (k + 2 : ℝ)) ∧ f ≤ φ k ε) :=
  sorry -- ...
```

# License

See the [LICENSE](https://github.com/RobinPetit/graphs-in-lean/blob/main/LICENSE) (copied from `https://github.com/non-ai-licenses/non-ai-licenses/tree/main`)

# Features

## Done

- [x] Generic definition
- [x] proof for independent sets (Caro-Wei)
- [x] proof for $k$-degenerate induced subgraphs (Alon-Khhan-Seymour)
- [x] Proof for caterpillars of max degree at most $k$ (Joret-Petit)

## TODO

- Bound for degree-bounded induced forests of stars
