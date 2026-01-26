import Mathlib.Tactic

import Init.Data.Rat.Basic
import Init.Data.Rat.Lemmas

import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph

import GraphsExt.Rat.Lemmas

noncomputable instance instFinsubset {V : Type*} {s : Set V} [Fintype V] : Fintype s := by
  exact Fintype.ofFinite s

noncomputable instance {V : Type*} {G : SimpleGraph V} {H : G.Subgraph} [DecidableRel G.Adj] :
      DecidableRel H.Adj :=
  fun a b ↦ Classical.propDecidable (H.Adj a b)

section CaroWei
open SimpleGraph
open Rat
open Finset

def f : ℕ → ℚ := fun d : ℕ ↦ 1 /. (d+1)

def g : ℕ → ℚ := fun d ↦ 1 /. (d * (d+1))

def φ : ℕ → ℚ := fun d ↦ (↑d * (1 /. (↑d * (↑d + 1))))

@[simp]
private lemma φ_eq (d : ℕ) {h : d ≠ 0} : φ d = 1 /. (↑d + 1) := by
  let q := φ d
  let num := q.num
  let den := q.den
  have coprime : num.natAbs.Coprime den := q.reduced
  rw [φ]
  let a : ℚ := d
  let b : ℚ := (1 /. (↑d * (↑d + 1)))
  have d_gt_0 : (d : ℤ) > 0 := Int.natCast_pos.mpr <| Nat.zero_lt_of_ne_zero h
  have dp1_gt_0 : (d : ℤ)+1 > 0 := Int.natCast_pos.mpr <| Nat.zero_lt_succ d
  have ddp1_gt_0 : (d : ℤ) * ((d : ℤ)+1) > 0 := Int.mul_pos d_gt_0 dp1_gt_0
  have ⟨b_num_eq_1, b_den_eq_prod⟩ := @rat_inv_num_den_eq (d * (d+1)) ddp1_gt_0
  let ddp1 := (d : ℤ) * ((d : ℤ) + 1)
  have toNat : ddp1.toNat = d * (d+1) := by exact Nat.add_zero ((d.mul d).add d)
  apply Rat.ext
  · rw [Rat.num_mul]
    simp only [num_natCast, den_natCast, one_mul, gt_iff_lt, Order.lt_add_one_iff, Nat.cast_nonneg,
      rat_inv_num_den_eq]
    rw [(rat_inv_num_den_eq ddp1_gt_0).left, (rat_inv_num_den_eq ddp1_gt_0).right, toNat]
    simp only [mul_one, Int.natAbs_natCast, Nat.gcd_mul_right_right]
    exact Int.ediv_self <| Int.ofNat_ne_zero.mpr h
  · rw [Rat.den_mul]
    simp only [den_natCast, one_mul, num_natCast, gt_iff_lt, Order.lt_add_one_iff, Nat.cast_nonneg,
      rat_inv_num_den_eq, Int.toNat_natCast_add_one]
    rw [(rat_inv_num_den_eq ddp1_gt_0).left, (rat_inv_num_den_eq ddp1_gt_0).right, toNat]
    simp only [mul_one, Int.natAbs_natCast, Nat.gcd_mul_right_right]
    exact Eq.symm (Nat.eq_div_of_mul_eq_right h toNat)

@[simp]
private lemma diff_f {d : ℕ} {h : d > 0} : f (d-1) - f d = 1 /. (d * (d+1)) := by
  have dp1_gt_0 : d+1 > (0 : ℤ) := Int.succ_ofNat_pos d
  obtain ⟨num_eq_1, den_eq_dp1⟩ := @rat_inv_num_den_eq (d+1) dp1_gt_0
  obtain ⟨num_eq_1', den_eq_d⟩ := @rat_inv_num_den_eq d (Int.natCast_pos.mpr h)
  have mkRat_to_divInt {n : ℤ} {d : ℕ} : mkRat n d = n /. d := rfl
  rw [Rat.sub_def' (f (d-1)) (f d)]
  simp only [mkRat_to_divInt, f]
  refine Eq.symm (Rat.ext ?_ ?_) <;> grind

private lemma _prop_monotone {a b c d : ℤ} {ha : a > 0} {hc : b > 0} (h1 : a ≤ c) (h2 : b ≤ d) :
    a*b ≤ c*d := by
  have hd : d > 0 := Int.lt_of_lt_of_le hc h2
  have hc : c > 0 := Int.lt_of_lt_of_le ha h1
  calc
    a*b ≤ a*d := (Int.mul_le_mul_left ha).mpr h2
    a*d ≤ c*d := (Int.mul_le_mul_iff_of_pos_right hd).mpr h1

private lemma g_decreasing {x y : ℕ} {_hx : x > 0} {_hy : y > 0} : x ≤ y → g y ≤ g x := by
  intro _x_le_y
  apply (Rat.le_iff (g y) (g x)).mpr
  simp only [g]
  simp_all only [gt_iff_lt, Int.natCast_pos, mul_pos_iff_of_pos_left, Int.succ_ofNat_pos,
    rat_inv_num_den_eq, one_mul]
  have x_le_y : (x : ℤ) ≤ (y : ℤ) := Int.ofNat_le.mpr _x_le_y
  have xp1_le_yp1 : (x : ℤ) + 1 ≤ (y : ℤ) + 1 := (Int.add_le_add_iff_right 1).mpr x_le_y
  have hx : (x : ℤ) > 0 := Int.natCast_pos.mpr _hx
  have hx' : (x : ℤ) + 1 > 0 := Int.succ_ofNat_pos x
  exact @_prop_monotone _ _ _ _ hx hx' x_le_y xp1_le_yp1

variable {V : Type*} [Fintype V]

namespace SimpleGraph
namespace Subgraph
@[simp]
private abbrev vertsF {G : SimpleGraph V} (G' : G.Subgraph) [Fintype G'.verts] : Finset V :=
  G'.verts.toFinset

abbrev IsIndepSet {G : SimpleGraph V} (G' : G.Subgraph) (s : Set V) (h : s ⊆ G'.verts) : Prop :=
  G'.coe.IsIndepSet {⟨x, h mem⟩ | (x : V) (mem : x ∈ s)}

end Subgraph
end SimpleGraph

def caroWei_bound {G : SimpleGraph V} (G' : G.Subgraph) [Fintype G'.verts] [DecidableRel G'.Adj] :
    ℚ := ∑ v ∈ G'.verts, (f <| G'.degree v)

noncomputable def CaroWeiBound (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  caroWei_bound (G.toSubgraph G (le_refl _))

private structure _CaroWeiSolution {G : SimpleGraph V} (G' : G.Subgraph) [DecidableRel G'.Adj] where
  mk ::
  s : Set V
  s_subset : s ⊆ G'.verts
  is_indep : G'.IsIndepSet s s_subset
  lower_bound : #s.toFinset ≥ caroWei_bound G'

set_option linter.unusedFintypeInType false in
private lemma indep_set_of_induced {G : SimpleGraph V} (G' : G.Subgraph) (hind : G'.IsInduced)
    (s : Set V) (hs : s ⊆ G'.verts) : G'.IsIndepSet s hs → G.IsIndepSet s := by
  intro s_indepset v v_in_s w w_in_s v_ne_w
  let v' : G'.verts := ⟨v, hs v_in_s⟩
  let w' : G'.verts := ⟨w, hs w_in_s⟩
  have v'_ne_w' : v' ≠ w' := Subtype.coe_ne_coe.mp v_ne_w
  suffices ¬G'.coe.Adj v' w' by
    intro G_adj_vw
    exact this <| hind (hs v_in_s) (hs w_in_s) G_adj_vw
  refine s_indepset ?_ ?_ ?_
  · simp only [Set.mem_setOf_eq]
    use v, Set.mem_toFinset.mp (Set.mem_toFinset.mpr v_in_s)
  · simp only [Set.mem_setOf_eq]
    use w, Set.mem_toFinset.mp (Set.mem_toFinset.mpr w_in_s)
  · exact v'_ne_w'

private lemma _is_induced {V : Type*} (s : Set V) {G : SimpleGraph V} (G' : G.Subgraph)
      (h : G'.IsInduced) (hs : s ⊆ G'.verts) :
    (G'.induce s).IsInduced := by
  intro v v_in_s w w_in_s G_adj_vw
  constructor
  · exact v_in_s
  · constructor
    · exact w_in_s
    · exact h (hs v_in_s) (hs w_in_s) G_adj_vw

private lemma _equal_neighbourhoods_ {V : Type*} {v w : V} {G : SimpleGraph V} (G' : G.Subgraph)
    (h : w ≠ v) (hnonadj : ¬G'.Adj v w) :
    G'.neighborSet w = (G'.induce (G'.verts \ {v})).neighborSet w := by
  ext x
  constructor
  · intro G'_adj_xw
    constructor
    · exact ⟨G'.edge_vert G'_adj_xw, h⟩
    · constructor
      · constructor
        · exact Subgraph.Adj.snd_mem G'_adj_xw
        · intro x_in_v
          have x_eq_v : x = v := x_in_v
          have G'_adj_wv : G'.Adj w v := by
            rw [←x_eq_v]
            exact G'_adj_xw
          exact hnonadj (Subgraph.adj_symm G' G'_adj_wv)
      · exact G'_adj_xw
  · intro H_adj_xw
    simp_all only [ne_eq, Subgraph.mem_neighborSet, Subgraph.induce_adj, Set.mem_diff,
      Set.mem_singleton_iff, not_false_eq_true, and_true]

private lemma split_sum {V R : Type*} [DecidableEq V] [Ring R] {s t : Finset V} {f : V → R}
    (h1 : t ⊆ s) : ∑ v ∈ s, f v = ∑ v ∈ t, f v + ∑ v ∈ (s \ t), f v := by
  simp_all only [sum_sdiff_eq_sub, add_sub_cancel]

private lemma card_union_singleton_plus_1 {s : Set V} {v : V} (h : v ∉ s) [DecidableEq V] :
    Finset.card (s ∪ {v}).toFinset = Finset.card s.toFinset + 1 := by
  let s₁ := s.toFinset
  let s₂ := ({v} : Set V).toFinset
  have cap_empty : s₁ ∩ s₂ = ∅ := by grind
  have obj : #(s₁ ∪ s₂) + #(s₁ ∩ s₂) = #s₁ + #s₂ := card_union_add_card_inter _ _
  rw [cap_empty] at obj
  simp_all

private theorem _CaroWei_on_empty_subgraph {G : SimpleGraph V} {G' : G.Subgraph}
    {hempty : G'.verts = ∅} [DecidableRel G.Adj] : Nonempty (_CaroWeiSolution G') := by
  have bound_eq_0 : caroWei_bound G' = 0 := by
    simp only [caroWei_bound, Set.toFinset_empty, sum_empty, hempty]
  have _ : (∅ : Set V) ⊆ G'.verts := Set.empty_subset G'.verts
  let s : Set V := ∅
  let s_subset : s ⊆ G'.verts := Set.empty_subset G'.verts
  let is_indep : G'.IsIndepSet s s_subset := by
    intro x x_in_s
    simp only [Set.mem_empty_iff_false, IsEmpty.exists_iff, exists_false, Set.setOf_false, s]
      at x_in_s
  let lower_bound : #(@Set.toFinset V s instFinsubset) ≥ caroWei_bound G' := by
    rw [bound_eq_0]
    exact natCast_nonneg
  refine Nonempty.intro <| _CaroWeiSolution.mk s s_subset is_indep lower_bound

private theorem _CaroWei_on_empty_subgraph' {G : SimpleGraph V} [DecidableRel G.Adj]
    {G' : G.Subgraph} {hempty : ∀ w ∈ G'.verts, G'.degree w = 0} :
    Nonempty (_CaroWeiSolution G') := by
  -- For some reason, Lean switches between two instances of Fintype
  -- so it is forced here. That's not pretty but it seems to work
  let _fintype_inst (w : V) := G'.instFintypeElemNeighborSetOfVertsOfDecidablePredMemSet w
  let deg : G'.verts → ℕ := fun w ↦ @Subgraph.degree V G G' w (_fintype_inst w)
  refine Nonempty.intro <| _CaroWeiSolution.mk G'.verts (fun _ _in ↦ _in) ?_ ?_
  · intro x' x'_in y' y'_in x'_ne_y'
    simp_all only [exists_subtype_mk_eq_iff, exists_eq, Set.setOf_true, Set.mem_univ, ne_eq,
      Subgraph.coe_adj]
    let degx_eq_0 : deg x' = 0 := by
      simp only [deg]
      exact hempty x' x'.prop
    intro G'_adj_xy
    have degx_gt_0 : deg x' > 0 := by
      exact (@Subgraph.degree_pos_iff_exists_adj
        V G G' x'.val (_fintype_inst x'.val)).mpr (by use y')
    have degx_ne_0 : @Subgraph.degree V G G' x'.val (_fintype_inst x'.val) ≠ 0 := by
      exact Nat.ne_zero_of_lt degx_gt_0
    refine degx_ne_0 ?_
    exact degx_eq_0
  · rw [caroWei_bound]
    have f_le_1 : ∀ x ∈ G'.verts.toFinset, f (G'.degree x) ≤ 1 := by
      intro x x_in_G'
      unfold f
      simp_all
    have obj : ∑ x ∈ G'.verts.toFinset, f (G'.degree x) ≤ ∑ x ∈ G'.verts.toFinset, 1 :=
      sum_le_sum f_le_1
    simp_all only [Set.mem_toFinset, sum_const, Set.toFinset_card, nsmul_eq_mul, mul_one]

private lemma lift_sol_is_indep {G : SimpleGraph V} [DecidableRel G.Adj] (v : V)
    (G' : G.Subgraph) (sol_H : _CaroWeiSolution (G'.induce (G'.verts \ {v})))
    (s_subset : sol_H.s ⊆ G'.verts) : G'.IsIndepSet sol_H.s s_subset := by
  let H := (G'.induce (G'.verts \ {v}))
  intro x' x'_in y' y'_in x'_ne_y'
  obtain ⟨x, ⟨memx, liftx⟩⟩ := x'_in
  obtain ⟨y, ⟨memy, lifty⟩⟩ := y'_in
  have not_H_adj_xy : ¬H.Adj x y := by
    let is_indep := sol_H.is_indep
    simp only [Set.Pairwise, Set.mem_setOf_eq, ne_eq, Subgraph.coe_adj, forall_exists_index,
      Subtype.forall, Subtype.mk.injEq] at is_indep
    exact is_indep x (sol_H.s_subset memx) x memx rfl y (sol_H.s_subset memy)
      y memy rfl (by grind)
  intro this
  have this : G'.Adj x y := by
    rw [←liftx, ←lifty] at this
    exact this
  have in_H_implies_ne_v : ∀ w ∈ H.verts, w ≠ v := by
    intro w w_in_H
    simp_all only [ne_eq, Subgraph.induce_adj, Set.mem_diff, Set.mem_singleton_iff, and_true,
      not_and, not_not, and_imp, Subgraph.coe_adj, Subgraph.induce_verts, not_false_eq_true, H]
  have _ : H.Adj x y := by
    constructor
    · exact ⟨s_subset memx, in_H_implies_ne_v x <| sol_H.s_subset memx⟩
    · exact ⟨⟨s_subset memy, in_H_implies_ne_v y <| sol_H.s_subset memy⟩, this⟩
  contradiction

set_option linter.unusedDecidableInType false in
private lemma CW_lb_can_only_increase {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    (G' : G.Subgraph) (v : V) (hv : v ∈ G'.verts.toFinset) (Δ_ne_0 : G'.degree v ≠ 0)
    (h : ∀ w ∈ G'.verts, G'.degree w ≤ G'.degree v) :
    caroWei_bound (G'.induce (G'.verts \ {v})) ≥ caroWei_bound G' := by
  let Δ : ℕ := G'.degree v
  let H := G'.induce (G'.verts \ {v})
  have in_H_implies_ne_v : ∀ w ∈ H.verts, w ≠ v := by
    intro w w_in_H
    simp_all only [Set.mem_toFinset, Subgraph.induce_verts, Set.mem_diff, Set.mem_singleton_iff,
      ne_eq, not_false_eq_true, H]
  let Nv := Set.toFinset <| G'.neighborSet v
  have in_Nv_implies_ne_v : ∀ w ∈ Nv, w ≠ v := by
    intro w w_in_Nv w_eq_v
    simp only [w_eq_v, Nv] at w_in_Nv
    have G'_adj_vv : v ∈ G'.neighborSet v := Set.mem_toFinset.mp w_in_Nv
    exact G.loopless v <| G'.adj_sub G'_adj_vv
  suffices ∑ w ∈ Nv, f (H.degree w) ≥ ∑ w ∈ Nv, f (G'.degree w) + f (G'.degree v) by
    unfold caroWei_bound
    have G'_H_verts : G'.verts.toFinset = H.verts.toFinset ∪ {v} := by simp_all only [
      Set.mem_toFinset, Subgraph.induce_verts, Set.toFinset_diff, Set.toFinset_singleton,
      union_singleton, insert_sdiff_self_of_mem, H]
    rw [G'_H_verts]
    have split_sum_H : ∑ v ∈ H.verts.toFinset ∪ {v}, f (G'.degree v)
      = ∑ v ∈ H.verts.toFinset, f (G'.degree v) + f (G'.degree v) := by grind
    rw [split_sum_H]
    have Nv_in_H : Nv ⊆ H.verts.toFinset := by
      intro x x_in_Nv
      have x_ne_v : x ≠ v := in_Nv_implies_ne_v x x_in_Nv
      refine Set.mem_toFinset.mpr ?_
      have _x_in_Nv : x ∈ G'.neighborSet v := Set.mem_toFinset.mp x_in_Nv
      exact ⟨Subgraph.Adj.snd_mem _x_in_Nv, x_ne_v⟩
    rw [@split_sum V ℚ _ _ _ _ _ Nv_in_H]
    rw [@split_sum V ℚ _ _ _ _ _ Nv_in_H]
    have eq_on_Nv_compl : ∀ w, w ∈ (H.vertsF \ Nv) → f (G'.degree w) = f (H.degree w) := by
      intro w w_in_H_minus_Nv
      simp only [Subgraph.vertsF, mem_sdiff, Set.mem_toFinset] at w_in_H_minus_Nv
      have w_ne_v : w ≠ v := in_H_implies_ne_v w w_in_H_minus_Nv.left
      have not_G'_adj_vw : ¬G'.Adj v w := by
        let tmp := w_in_H_minus_Nv.right
        intro G'_adj_vw
        exact (Iff.not Set.mem_toFinset).mp w_in_H_minus_Nv.right <| G'_adj_vw
      simp only [Subgraph.degree]
      exact congrArg f <| Fintype.card_congr' <| congrArg Set.Elem <|
        _equal_neighbourhoods_ G' w_ne_v not_G'_adj_vw
    simp only [Subgraph.induce_verts, ge_iff_le]
    rw [Eq.symm <| sum_congr rfl eq_on_Nv_compl]
    grind
  have charac_neighborhoods_of_Nv : ∀ w ∈ Nv, H.neighborSet w ∪ {v} = G'.neighborSet w := by
    intro w w_in_Nv
    have _w_in_Nv : w ∈ G'.neighborSet v := Set.mem_toFinset.mp w_in_Nv
    have G'_adj_wv : G'.Adj w v := Subgraph.adj_symm G' _w_in_Nv
    have w_ne_v : w ≠ v := in_Nv_implies_ne_v w w_in_Nv
    ext x
    constructor
    · intro x_in_NHw_cup_v
      simp only [Set.union_singleton, Set.mem_insert_iff,
        Subgraph.mem_neighborSet] at x_in_NHw_cup_v
      cases x_in_NHw_cup_v with
      | inl h =>
          rw [h]
          exact G'_adj_wv
      | inr h =>
          obtain ⟨_, ⟨_, G'_adj_wx⟩⟩ := h
          exact G'_adj_wx
    · intro x_in_NG'w
      simp_all only [Set.mem_toFinset, ne_eq, Subgraph.mem_neighborSet,
        Set.union_singleton, Set.mem_insert_iff]
      cases Classical.em (x = v) with
      | inl h => exact Or.inl h
      | inr h =>
          have H_adj_wx : H.Adj w x := by
            constructor
            · exact ⟨G'.edge_vert x_in_NG'w, in_Nv_implies_ne_v w w_in_Nv⟩
            · exact ⟨⟨G'.edge_vert (Subgraph.adj_symm G' x_in_NG'w), h⟩, x_in_NG'w⟩
          exact Or.inr H_adj_wx
  have deg_diff_in_Nv : ∀ w ∈ Nv, H.degree w + 1 = G'.degree w := by
    intro w w_in_Nv
    have w_ne_v : w ≠ v := in_Nv_implies_ne_v w w_in_Nv
    simp only [Subgraph.degree, ←Set.toFinset_card]
    have not_G'_adj_vw : G'.Adj v w := by
      have _w_in_Nv : w ∈ G'.neighborSet v := Set.mem_toFinset.mp w_in_Nv
      exact _w_in_Nv
    let s₁ := H.neighborSet w
    let s₂ := ({v} : Set V)
    have tmp : (H.neighborSet w ∪ {v}).toFinset.card = (G'.neighborSet w).toFinset.card := by
      have union : s₁ ∪ s₂ = G'.neighborSet w := by grind
      exact congrArg card <| Set.toFinset_inj.mpr union
    rw [←tmp]
    have v_notin_NHw : v ∉ H.neighborSet w := by
      intro v_in_NHw
      exact (in_H_implies_ne_v v <| Subgraph.Adj.snd_mem v_in_NHw) rfl
    have cap_empty : s₁ ∩ s₂ = ∅ := Set.inter_singleton_of_notMem v_notin_NHw
    simp only [Set.toFinset_card, Eq.symm, Set.union_singleton, Set.toFinset_insert,
      Set.mem_toFinset, v_notin_NHw, not_false_eq_true, card_insert_of_notMem]
    --
  have f_congr_in_Nv : ∀ w ∈ Nv, f (H.degree w) = f (G'.degree w - 1) := by
    grind
  have tmp : ∑ w ∈ Nv, f (H.degree w) = ∑ w ∈ Nv, f (G'.degree w - 1) := by
    exact sum_congr rfl f_congr_in_Nv
  rw [tmp]
  suffices ∑ w ∈ Nv, (f (G'.degree w - 1) - f (G'.degree w)) ≥ f (G'.degree v) by
    simp only [ge_iff_le]
    have symbolic_manipulation {a b c : ℚ} (h : b ≤ c - a) : a + b ≤ c := by grind
    refine symbolic_manipulation ?_
    rw [←sum_sub_distrib]
    grind
  have diff_consec_f : ∀ w ∈ Nv, f (G'.degree w - 1) - f (G'.degree w)
      = divInt 1 (G'.degree w * (G'.degree w + 1)) := by
    intro w w_in_Nv
    simp only [f]
    have degw_gt_0 : G'.degree w > 0 := by
      refine Subgraph.degree_pos_iff_exists_adj.mpr ?_
      use v
      have _w_in_Nv : w ∈ G'.neighborSet v := by
        exact Set.mem_toFinset.mp w_in_Nv
      exact Subgraph.adj_symm G' _w_in_Nv
    exact @diff_f (G'.degree w) degw_gt_0
  rw [sum_congr rfl diff_consec_f]
  have deg_bounds : ∀ w ∈ Nv, 0 < G'.degree w ∧ G'.degree w ≤ Δ := by
    intro w w_in_Nv
    have _w_in_Nv : w ∈ G'.neighborSet v := Set.mem_toFinset.mp w_in_Nv
    constructor
    · have G'_adj_vw : G'.Adj v w := _w_in_Nv
      have Nv_nonempty : (G'.neighborSet w).Nonempty := by
        exact Set.nonempty_of_mem (Subgraph.adj_symm G' G'_adj_vw)
      exact Subgraph.degree_pos_iff_exists_adj.mpr Nv_nonempty
    · exact h w <| Subgraph.Adj.snd_mem _w_in_Nv
  have bla3 : ∀ w ∈ Nv, g (G'.degree w) ≥ g Δ := by
    intro w w_in_Nv
    obtain ⟨degw_gt_0, degw_le_Δ⟩ := deg_bounds w w_in_Nv
    have Δ_gt_0 : Δ > 0 := Nat.lt_of_lt_of_le degw_gt_0 degw_le_Δ
    exact @g_decreasing (G'.degree w) Δ degw_gt_0 Δ_gt_0 degw_le_Δ
  have obj : ∑ w ∈ Nv, g (G'.degree w) ≥ ∑ w ∈ Nv, g Δ := by exact sum_le_sum bla3
  rw [@sum_const V ℚ Nv _ (g Δ)] at obj
  have card_Nv_eq_Δ : #Nv = Δ := by exact Subgraph.finset_card_neighborSet_eq_degree
  rw [card_Nv_eq_Δ] at obj
  simp only [g, nsmul_eq_mul] at obj
  suffices Δ * (1 /. (Δ * (Δ + 1))) = f (Δ) by
    grind
  rw [f]
  apply Rat.eq_iff_mul_eq_mul.mpr
  simp only [gt_iff_lt, Int.succ_ofNat_pos, rat_inv_num_den_eq, one_mul]
  let tmp := @rat_divInt_num_den_eq (G'.degree v) 1 (G'.degree v+1) Δ_ne_0
  rw [←φ, φ_eq]
  -- why does there need to be a `·` here?
  -- WHere does the 2nd goal appear?
  · grind only [!rat_inv_num_den_eq]
  exact Δ_ne_0

set_option linter.unusedDecidableInType false in
theorem _CaroWei : ∀ {n : ℕ} {G : SimpleGraph V} (G' : G.Subgraph) {_ : Finset.card G'.vertsF = n}
    [DecidableRel G.Adj] [DecidableEq V], Nonempty (_CaroWeiSolution G') := by
  intro n
  induction n with
  | zero =>
      intro G G' h _ _
      have empty : G'.verts = ∅ := Set.toFinset_eq_empty.mp <| card_eq_zero.mp h
      exact @_CaroWei_on_empty_subgraph V _ G G' empty _
  | succ n ih =>
      intro G G' h _ _
      have G'verts_nonempty : Nonempty G'.verts := by
        have G'verts_nonempty : Finset.card G'.verts.toFinset > 0 := Nat.lt_of_sub_eq_succ h
        simp only [Set.toFinset_card, gt_iff_lt] at G'verts_nonempty
        exact Fintype.card_pos_iff.mp G'verts_nonempty
      have G'vertsF_nonempty : G'.verts.toFinset.Nonempty :=
        Set.toFinset_nonempty.mpr <| Set.nonempty_coe_sort.mp G'verts_nonempty
      let deg : V → ℕ := fun v ↦ G'.degree v
      let degrees : Finset ℕ := Finset.image deg G'.verts.toFinset
      have degrees_nonempty : degrees.Nonempty := image_nonempty.mpr G'vertsF_nonempty
      let Δ : ℕ := Finset.max' degrees (image_nonempty.mpr G'vertsF_nonempty)
      obtain ⟨v, ⟨v_in_verts, deg_v_eq_Δ⟩⟩ :=
        mem_image.mp <| max'_mem degrees (image_nonempty.mpr G'vertsF_nonempty)
      have Δ_is_max_deg : ∀ w ∈ G'.verts, @Subgraph.degree V G G' w _ ≤ Δ := by
        intro w w_in_G'
        have Δ_le_Δ : degrees.max' degrees_nonempty ≤ Δ :=
          max'_subset degrees_nonempty <| fun _ x ↦ x
        refine (@max'_le_iff ℕ _ degrees degrees_nonempty Δ).mp Δ_le_Δ (G'.degree w) ?_
        exact mem_image_of_mem deg <| Set.mem_toFinset.mpr w_in_G'
      cases Classical.em (Δ = 0) with
      | inl Δ_eq_0 =>
          have hempty : ∀ w ∈ G'.verts, G'.degree w = 0 := by
            intro w w_inG'
            have obj := Δ_is_max_deg w w_inG'
            rw [Δ_eq_0] at obj
            exact Nat.eq_zero_of_le_zero obj
          exact @_CaroWei_on_empty_subgraph' V _ G _ G' hempty
      | inr Δ_ne_0 =>
      suffices sol_G' : _CaroWeiSolution G' by
        exact Nonempty.intro sol_G'
      let H := G'.induce (G'.verts \ {v})
      have in_H_implies_ne_v : ∀ w ∈ H.verts, w ≠ v := by
        intro w w_in_H
        simp_all only [Subgraph.vertsF, Set.toFinset_card, forall_const, nonempty_subtype,
          Set.mem_toFinset, Subgraph.induce_verts, Set.mem_diff, Set.mem_singleton_iff, ne_eq,
          not_false_eq_true, H]
      have H_vertsF : H.vertsF = G'.vertsF \ {v} := by
        simp only [Subgraph.vertsF]
        have tmp : G'.verts.toFinset \ {v} = (G'.verts \ {v}).toFinset :=
          Eq.symm <| Set.toFinset_diff _ _
        rw [tmp, Set.toFinset_inj]
        rfl
      have Hcard : #H.vertsF = n := by
        rw [H_vertsF]
        grind
      let sol_H := Nonempty.some <| @ih G H Hcard _ _
      let s : Set V := sol_H.s
      let s_subset : s ⊆ G'.verts :=
        le_trans sol_H.s_subset <| fun _ _in ↦ Set.mem_of_mem_inter_left _in
      refine _CaroWeiSolution.mk s s_subset ?_ ?_
      · exact lift_sol_is_indep v G' sol_H s_subset
      · -- and now for the fun part:
        -- show that the Caro-Wei bound can only increase when removing a degree-max vertex
        suffices caroWei_bound H ≥ caroWei_bound G' by
          exact le_trans this sol_H.lower_bound
        simp only [Δ] at Δ_ne_0
        rw [←deg_v_eq_Δ] at Δ_ne_0
        have Δ_max_deg : ∀ w ∈ G'.verts, G'.degree w ≤ G'.degree v := by
          intro w w_in_G'
          grind
        exact CW_lb_can_only_increase G' v v_in_verts Δ_ne_0 Δ_max_deg

set_option linter.unusedDecidableInType false in
theorem CaroWei (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V] :
    ∃ s : Finset V, G.IsIndepSet s ∧ #s ≥ CaroWeiBound G := by
  let n : ℕ := Fintype.card V
  let G' := G.toSubgraph G (le_refl _ )
  have tmp1 : G'.vertsF = Finset.univ := by
    rw [←Set.toFinset_univ, SimpleGraph.Subgraph.vertsF]
    exact Set.toFinset_inj.mpr rfl
  have tmp2 : #G'.vertsF = n := by
    exact congrArg card tmp1
  let sol : _CaroWeiSolution G' :=
    Classical.choice (@_CaroWei V _ n G (G.toSubgraph G (le_refl _)) tmp2 _ _)
  use sol.s.toFinset
  constructor
  · have G'_induced : G'.IsInduced := fun v _ w _ adj ↦ adj
    rw [Set.coe_toFinset sol.s]
    exact indep_set_of_induced G' G'_induced sol.s sol.s_subset sol.is_indep
  · suffices CaroWeiBound G = caroWei_bound G' by
      rw [this]
      exact sol.lower_bound
    exact rfl

end CaroWei
