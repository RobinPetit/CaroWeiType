import Mathlib.Tactic

import Mathlib.Data.Finset.Card

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph

namespace SimpleGraph

-- open Finset

section tests

universe u

variable {V W : Type u} {G : SimpleGraph V} {x y v : V} {e : Sym2 V}

-- G + e

abbrev AddEdge (G : SimpleGraph V) (e : Sym2 V) : SimpleGraph V :=
  fromEdgeSet (G.edgeSet ∪ {e})

abbrev AddEdge' (G : SimpleGraph V) (x y : V) : SimpleGraph V :=
  AddEdge G s(x, y)

scoped infixl:50 " + " => AddEdge

theorem AddEdge_edgeSet (h : ¬e.IsDiag) : (G + e).edgeSet = G.edgeSet ∪ {e} := by
  suffices (G + e).edgeSet = G.edgeSet \ Sym2.diagSet ∪ {e} \ Sym2.diagSet by aesop
  aesop

theorem AddEdge'_edgeSet (h : x ≠ y) : (G + s(x, y)).edgeSet = G.edgeSet ∪ {s(x, y)} := by
  exact AddEdge_edgeSet h

theorem AddEdge_has_edge (h : ¬e.IsDiag) : e ∈ (G+e).edgeSet := by simp_all

theorem AddEdge'_has_edge (h : x ≠ y) : (G + s(x, y)).Adj x y := by
  suffices s(x, y) ∈ (G + s(x, y)).edgeSet by exact this
  exact AddEdge_has_edge h

theorem graph_le_AddEdge : G ≤ (G + e) := by simp_all

theorem graph_le_AddEdge' : G ≤ (G + s(x, y)) := graph_le_AddEdge

@[simp]
theorem AddEdge_eq_iff : G = (G+e) ↔ (e.IsDiag ∨ e ∈ G.edgeSet) := by
  rw [← edgeSet_inj]
  constructor
  · intro eq
    by_contra
    obtain ⟨isdiag, isedge⟩ := not_or.mp this
    have this : e ∈ (G+e).edgeSet := AddEdge_has_edge isdiag
    rw [← eq] at this
    exact isedge this
  · intro h
    cases h with
    | inl isdiag =>
        suffices e ∈ Sym2.diagSet by aesop
        simp_all only [Sym2.mem_diagSet_iff_isDiag]
    | inr isedge =>
        suffices {e} \ Sym2.diagSet ⊆ G.edgeSet by
          by_contra
          simp_all
        exact fun ⦃edge⦄ p ↦ (Set.singleton_subset_iff.mpr isedge) (Set.diff_subset p)

theorem AddEdge'_eq_iff : G = (G + s(x, y)) ↔ (x = y ∨ G.Adj x y) := AddEdge_eq_iff

-- G - W

def _subtype_ {V : Type u} (s : Set V) : Type u :=
  Subtype fun w : V => w ∈ s
def Vmset (V : Type u) (s : Set V) : Type u :=
  _subtype_ (Set.univ \ s)
abbrev Vmv (V : Type u) (v : V) : Type u :=
  Vmset V {v}

scoped infixl:50 " - " => Vmv  -- use notation V - v for Type V without entry v
scoped infixl:50 " - " => Vmset  -- use notation V - s for Type V without entries s

def induce_exact (G : SimpleGraph V) (s : Set V) : SimpleGraph (_subtype_ s) where
  Adj w₁ w₂ := G.Adj w₁.val w₂.val
  symm w₁ w₂ := by
    intro G_adj_w1w2
    apply G.symm G_adj_w1w2

def RemoveVertices (G : SimpleGraph V) (s : Set V) : SimpleGraph (V - s) :=
  induce_exact G (Set.univ \ s)

def RemoveVtx (G : SimpleGraph V) (v : V) : SimpleGraph (V - v) :=
  RemoveVertices G {v}

alias RemoveVertex := RemoveVtx

scoped infixl:50 " - " => RemoveVertex
scoped infixl:50 " - " => RemoveVertices

abbrev CanonicalEmbedding (s : Set V) : Copy (G-s) G where
  toHom := by
    constructor
    · intro w₁ w₂ adj
      exact adj
  injective' := by
    intro ⟨w1, _⟩ ⟨w2, _⟩
    simp_all

@[simp]
theorem RemoveVtx_iff (G : SimpleGraph V) (v : V) : (G - v) = (G - {v}) := rfl

@[simp]
theorem RemoveVertices_is_contained (s : Set V) : (G - s) ⊑ G :=
  Nonempty.intro (CanonicalEmbedding s)

@[simp]
theorem RemoveVtx_is_contained (v : V) : (G - v) ⊑ G := RemoveVertices_is_contained {v}

-- wtf is happening over here?
instance {v : V} : Fintype (V - v) := by
  sorry
instance {s : Set V} : Fintype (V - s) := by
  sorry

instance {s : Set V} [hdec : DecidableRel G.Adj] : DecidableRel (G-s).Adj := by
  exact fun ⟨v₁, _⟩ ⟨v₂, _⟩ => hdec v₁ v₂

instance {v : V} [hdec : DecidableRel G.Adj] : DecidableRel (G-v).Adj := by
  exact fun ⟨v₁, _⟩ ⟨v₂, _⟩ => hdec v₁ v₂

abbrev coerce {V : Type u} (s : Set V) (x : Finset (V - s)) [DecidableEq V] : Finset V :=
  Finset.image (fun y : (V-s) => y.val) x

@[simp]
private lemma split_into_inter_and_diff [hdec : DecidableEq V] (s1 s2 : Finset V) :
    s1 = (s1 ∩ s2) ∪ (s1 \ s2) := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro x x_in_s1
    simp_all only [Finset.mem_union, Finset.mem_inter, true_and, Finset.mem_sdiff]
    exact Decidable.em (x ∈ s2)
  · intro x x_in_union
    simp_all only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    cases x_in_union with
    | inl h => exact h.left
    | inr h => exact h.left

variable [hfin : Fintype V] [hdec : DecidableRel G.Adj]

@[simp]
private theorem RemoveVertices_neighborhood_subset
    [DecidableEq V] (s : Set V) [Fintype ↑s] {w : (V - s)} :
    coerce s ((G-s).neighborFinset w) ⊆ ((G.neighborFinset w.val) \ (s.toFinset)) := by
  unfold coerce
  intro a h
  have this : ∃ b ∈ (G-s).neighborFinset w, b.val = a := by simp_all
  obtain ⟨b, b_preim_of_a⟩ := this
  simp_all only [Finset.mem_image, mem_neighborFinset]
  have G_adj_wb : (G-s).Adj w b := by simp_all
  have a_not_in_s : a ∉ s := by
    rw [←b_preim_of_a.right]
    exact Set.notMem_of_mem_diff b.property
  simp_all only [true_and, Finset.mem_sdiff, mem_neighborFinset, Set.mem_toFinset,
    not_false_eq_true, and_true]
  subst b_preim_of_a
  obtain ⟨w_1, h⟩ := h
  obtain ⟨left, right⟩ := h
  exact G_adj_wb

@[simp]
theorem RemoveVertices_neighbor_iff (s : Set V) {w x : (V - s)} :
    (x ∈ (G-s).neighborFinset w) ↔ (x.val ∈ (↑(G.neighborFinset w.val) \ s)) := by
  constructor
  · intro G'_adj_xw
    simp_all only [mem_neighborFinset, Set.mem_diff, SetLike.mem_coe]
    constructor
    · exact G'_adj_xw
    · exact Set.notMem_of_mem_diff (Subtype.coe_prop x)
  · intro G_adj_xw
    simp_all only [Set.mem_diff, SetLike.mem_coe, mem_neighborFinset]
    exact G_adj_xw.left

variable [DecidableEq V]

open Finset

@[simp]
theorem RemoveVertices_degree_iff (s : Finset V) {w x : (V - s)} :
    ((G-s).degree w + Finset.card (s ∩ (G.neighborFinset w.val))) = (G.degree w.val) := by
  suffices G.neighborFinset w.val = (G.neighborFinset w.val ∩ s) ∪ (G.neighborFinset w.val \ s) by
    apply Eq.symm
    let id : (V-s) → V := fun y => y.val
    have h1 : G.degree w.val = Finset.card (G.neighborFinset w.val) := by rfl
    have h2 : (G-s).degree w = #(G.neighborFinset w.val \ s) := by
      refine card_bijective id ?_ ?_
      · --
        sorry
      · --
        intro i
        constructor
        · intro G'_adj_iw
          sorry
        · intro this
          simp only [mem_sdiff, mem_neighborFinset] at this
          obtain ⟨G_adj_iw, i_notin_s⟩ := this
          sorry
    have h3 : #(s ∩ G.neighborFinset w.val) = #(G.neighborFinset w.val ∩ s) := by
      sorry
    rw [h1, h2, h3]
    simp [card_sdiff_add_card_inter]
  exact split_into_inter_and_diff (G.neighborFinset w.val) s

-- Caro-Wei

end tests

@[simp]
private lemma _inv_increasing {x y : ℚ} {h1 : x > 0} {h2 : y > 0} :
    (x < y) ↔ ((Inv.inv y) < (Inv.inv x)) := by
  simp_all only [inv_lt_inv₀]

section CaroWei
open Finset

variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]

def _fCW (d : ℕ) : ℚ := Inv.inv ((1 + d) : ℚ)
def fCW (v : V) : ℚ := _fCW (G.degree v)

-- Useful for induction (on |S|)
private def _sub_CW_bound (S : Finset V) : ℚ := ∑ v ∈ S, _fCW (G.degree v)
def CaroWei_bound : ℚ := _sub_CW_bound G (Finset.univ)

private lemma fCW_pos {x : ℕ} : 0 < _fCW x := by
  unfold _fCW
  have h : 0 < ((1+x) : ℚ) := neg_lt_iff_pos_add'.mp rfl
  simp_all

private lemma _fCW_decreasing {x y : ℕ} : x < y → _fCW x > _fCW y := by
  intro x_le_y
  have _xp1_ge_0 : 0 < ((1+x) : ℚ) := neg_lt_iff_pos_add'.mp rfl
  have _yp1_ge_0 : 0 < ((1+y) : ℚ) := neg_lt_iff_pos_add'.mp rfl
  unfold _fCW
  simp_all

private lemma _card_gt_0_non_empty {n : ℕ} {V : Type*} [Fintype V]
    (h : Fintype.card V = n) (h' : n > 0) : Nonempty V := by
  subst h
  by_contra
  simp_all only [gt_iff_lt, not_nonempty_iff, Fintype.card_eq_zero, lt_self_iff_false]

private theorem _CaroWei {n : ℕ} {V : Type*} (G : SimpleGraph V)
    [fin : Fintype V] [dec : DecidableRel G.Adj] (h : Fintype.card V = n) :
    ∃ s : Finset V, G.IsIndepSet s ∧ #s ≥ G.CaroWei_bound := by
  induction n using Nat.recAux with
  | zero =>
      use ∅
      unfold CaroWei_bound _sub_CW_bound
      simp_all only [coe_empty, Set.pairwise_empty, card_empty, CharP.cast_eq_zero, ge_iff_le,
        true_and]
      suffices Vempty : @Finset.univ V = {} by
        exact le_of_eq_of_le
            (congrFun (congrArg Finset.sum (congrFun Vempty fin)) fun v ↦ _fCW (G.degree v))
            rfl
      ext v
      simp_all only [univ_eq_empty, notMem_empty, Fintype.card_eq_zero_iff]
  | succ n ih =>
    have VNonempty : Nonempty V := _card_gt_0_non_empty h (Nat.zero_lt_succ n)
    obtain ⟨v, v_max_deg⟩ := exists_maximal_degree_vertex G
    -- TODO!
    simp_all
    sorry

theorem CaroWei {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    ∃ s : Finset V, G.IsIndepSet s ∧ #s ≥ G.CaroWei_bound := by
  exact _CaroWei G rfl

end CaroWei
end SimpleGraph
