import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim6
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim9
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim10
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim11
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Lemmas

open SimpleGraph
open Finset

namespace CaroWeiType
namespace AB
namespace Bipartition

syntax "member_of" : tactic
macro_rules
| `(tactic| member_of) =>
    `(tactic| repeat first
      | exact mem_insert_self _ _
      | exact mem_singleton.mpr rfl
      | refine mem_insert_of_mem ?_
      | exact mem_union.mpr <| Or.inl <| by member_of
      | exact mem_union.mpr <| Or.inr <| by member_of)

variable {V : Type} [Fintype V] [DecidableEq V]

private lemma twonethree : 2 ≠ 3 := by linarith

lemma _card_N2_of_adj {x u v w : V} {G : SimpleGraph V} [DecidableRel G.Adj]
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj x w) (hux : G.Adj u x)
    (hunew : u ≠ w) (hvnex : v ≠ x)
    (hdu : G.degree u = 3) (hdv : G.degree v = 2) (hdw : G.degree w = 3) :
    #(G.N2_of_Finset {v}) < 4 := by
  have hNv : G.neighborFinset v = {u, w} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [card_pair hunew, ← degree, hdv]
  have : G.closed_neighborFinset_of_Finset {v} = {u, v, w} := by
    rw [closed_neighborFinset_of_singleton_eq, hNv]
    grind
  obtain ⟨u', hu', hvneu', hxneu'⟩ := Finset_get_other_other (le_of_eq hdu.symm) v x
  obtain ⟨w', hw', hvnew', hxnew'⟩ := Finset_get_other_other (le_of_eq hdw.symm) v x
  have hNu : G.neighborFinset u = {v, x, u'} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [← degree, hdu, card_triplet' hvnex hvneu' hxneu']
  have hNw : G.neighborFinset w = {v, x, w'} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [← degree, hdw, card_triplet' hvnex hvnew' hxnew']
  rw [N2_of_Finset, this, closed_neighborFinset_of_triplet_eq, hNu, hNv, hNw]; clear this
  have : ({v, x, u'} ∪ {u, w} ∪ {v, x, w'} ∪ {u, v, w}) = ({u, v, x, w, u', w'} : Finset _) := by
    have : {v, x, u'} ∪ {u, w} ∪ {v, x, w'} = ({u, v, x, w, u', w'} : Finset _) := by
      grind
    grind
  rw [this]; clear this
  grind

private lemma _card_N2_of_triangle {u v w : V} {G : SimpleGraph V} [DecidableRel G.Adj]
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hdu : G.degree u = 3) (hdv : G.degree v = 2) (hdw : G.degree w = 3) :
    #(G.N2_of_Finset {v}) < 4 := by
  obtain ⟨u', hu', hvneu', hwneu'⟩ := Finset_get_other_other (le_of_eq hdu.symm) v w
  obtain ⟨w', hw', hvnew', hunew'⟩ := Finset_get_other_other (le_of_eq hdw.symm) v u
  have hNv : G.neighborFinset v = {u, w} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [← degree, hdv, card_pair huw.ne]
  have hNu : G.neighborFinset u = {v, w, u'} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [← degree, hdu, card_triplet' hvw.ne hvneu' hwneu']
  have hNw : G.neighborFinset w = {u, v, w'} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [← degree, hdw, card_triplet' huv.ne hunew' hvnew']
  have : G.closed_neighborFinset_of_Finset {v} = {u, v, w} := by
    rw [closed_neighborFinset_of_singleton_eq, hNv]
    grind
  rw [N2_of_Finset, this, closed_neighborFinset_of_triplet_eq, hNu, hNv, hNw]; clear this
  have : {v, w, u'} ∪ {u, w} ∪ {u, v, w'} ∪ {u, v, w} = ({u, v, w, u', w'} : Finset _) := by
    have : {v, w, u'} ∪ {u, w} ∪ {u, v, w'} = ({u, v, w, u', w'} : Finset _) := by grind
    rw [this]; clear this
    grind
  rw [this]; clear this
  grind

private lemma _union_eq {α : Type*} [DecidableEq α] {x y x' v w v' w' : α} :
    {v, x', y} ∪ {w, v', x'} ∪ {x, w'} = ({x, w', v, y, x', w, v'} : Finset _) := by
  ext z
  simp only [union_insert, insert_union, singleton_union, mem_insert, mem_singleton]
  grind

private lemma _Claim12_of_v'w'_of_x'_eq_w'
    {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {v w x y v' w' x' : V}
    (hdv : G.degree v = 2) (hdw : G.degree w = 2) (hdv' : G.degree v' = 3) (hdw' : G.degree w' = 3)
    (hdx : G.degree x = 3) (hdy : G.degree y = 3) (hdx' : G.degree x' = 3)
    (hvx : G.Adj v x) (hxy : G.Adj x y) (hyw : G.Adj y w) (hvv' : G.Adj v v') (hww' : G.Adj w w')
    (hxx' : G.Adj x x') (hw'x' : G.Adj w' x') (hv'w' : G.Adj v' w')
    (hvnew : v ≠ w) (hxney : x ≠ y) (hvney : v ≠ y) (hwnex : w ≠ x) (hynex' : y ≠ x')
    (hvnex' : v ≠ x') (hwnex' : w ≠ x') (hv'nex' : v' ≠ x') (hv'eqw' : v' ≠ w') (hv'eqy : v' ≠ y)
    (hw'eqx : w' ≠ x) (hxnev' : x ≠ v') (hynew' : y ≠ w')
    (hAx : AB.A x) (hAy : AB.A y) (hAv' : AB.A v') (hAw' : AB.A w') (hAx' : AB.A x') (hAv : AB.A v)
    (hAw : AB.A w)
    (hNw' : G.neighborFinset w' = {w, v', x'})
    (h : ∀ u ∈ AB.toFinset, AB.A u ∧ (G.degree u = 2 ∨ G.degree u = 3))
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB')
    : Objective G AB := by
  obtain ⟨s, hs, hsf, hsresp, hscard⟩ := by
    refine ih (G.deleteIncidencesOf {x, w'}) (AB \ {x, w'}) (hsupp_mono hG) ?_
    refine sdiff_card AB (nonempty_iff_ne_empty.mp ⟨x, by grind [mem_iff, AB.mem_toFinset.mp]⟩)
  rw [AB.sdiff_toFinset] at hs
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · exact hs.trans sdiff_subset
  · exact InducesForestOfStars_graph_mono' (disjoint_of_sdiff hs) hsf
  · exact respects_of_A fun x hx ↦ h _ (mem_sdiff.mp (hs hx) |>.1) |>.1
  · have hs' : {x, w'} ⊆ AB.toFinset := by grind [AB.mem_iff, AB.mem_toFinset.mp]
    rw [eval_eq hs' hG]
    have hNx : G.neighborFinset x = {v, x', y} := by
      refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
      · grind [mem_neighborFinset, Adj.symm]
      · rw [← degree, hdx, card_triplet' hvnex' hvney hynex'.symm]
    suffices ∑ z ∈ G.closed_neighborFinset_of_Finset {x, w'} \ {x, w'},
        (f G AB z - f (G.deleteIncidencesOf {x, w'}) (AB \ {x, w'}) z)
        + ∑ z ∈ {x, w'}, f G AB z ≤ 0 by linarith
    have : ({x, w', v, y, x', w, v'} \ ({x, w'} : Finset _)) = {x', y, v, v', w} := by
      ext; grind [Adj.ne, Adj.symm]
    rw [closed_neighborFinset_of_pair_eq, hNx, hNw', _union_eq, this]; clear this
    have : ({x', y, v, v', w} : Finset _) = {v, w} ∪ {x', y, v'} := by grind
    have hdisj : ({v, w} : Finset _) ∩ {x', y, v'} = ∅ := by
      grind [Adj.ne, Adj.symm, degree]
    rw [this, sum_union (disjoint_iff_inter_eq_empty.mpr hdisj)]; clear this hdisj
    rw [sum_pair hvnew, sum_pair hw'eqx.symm]
    rw [sum_triplet hynex'.symm hv'nex'.symm hv'eqy.symm]
    simp only [fA2 hAv hdv, fA2 hAw hdw, fA3 hAx hdx, fA3 hAy hdy, fA3 hAw' hdw',
      fA3 hAv' hdv', fA3 hAx' hdx']
    suffices 37 / 10 ≤ f (G.deleteIncidencesOf {x, w'}) (AB \ {x, w'}) v
        + f (G.deleteIncidencesOf {x, w'}) (AB \ {x, w'}) w
        + f (G.deleteIncidencesOf {x, w'}) (AB \ {x, w'}) x'
        + f (G.deleteIncidencesOf {x, w'}) (AB \ {x, w'}) y
        + f (G.deleteIncidencesOf {x, w'}) (AB \ {x, w'}) v' by linarith
    have hA'v : (AB \ {x, w'}).A v   :=  ⟨hAv, by grind⟩
    have hA'w : (AB \ {x, w'}).A w   :=  ⟨hAw, by grind⟩
    have hA'x' : (AB \ {x, w'}).A x' :=  ⟨hAx', by grind [Adj.ne]⟩
    have hA'y : (AB \ {x, w'}).A y   :=  ⟨hAy, by grind⟩
    have hA'v' : (AB \ {x, w'}).A v' :=  ⟨hAv', by grind⟩
    have H {z : V} (hz : G.Adj z x) : (G.deleteIncidencesOf {x, w'}).degree z < G.degree z :=
      deleteIncidencesOf_degree_lt hz mem_pair
    have H' {z : V} (hz : G.Adj z w') : (G.deleteIncidencesOf {x, w'}).degree z < G.degree z :=
      deleteIncidencesOf_degree_lt hz mem_pair'
    have : 5 / 6 ≤ f (G.deleteIncidencesOf {x, w'}) (AB \ {x, w'}) v :=
      fAlt2 hA'v (hdv ▸ H hvx)
    have : 5 / 6 ≤ f (G.deleteIncidencesOf {x, w'}) (AB \ {x, w'}) w :=
      fAlt2 hA'w (hdw ▸ H' hww')
    have : 3 / 5 ≤ f (G.deleteIncidencesOf {x, w'}) (AB \ {x, w'}) y :=
      fAlt3 hA'y (hdy ▸ H hxy.symm)
    have : 3 / 5 ≤ f (G.deleteIncidencesOf {x, w'}) (AB \ {x, w'}) v' :=
      fAlt3 hA'v' (hdv' ▸ H' hv'w')
    suffices 5 / 6 ≤ f (G.deleteIncidencesOf {x, w'}) (AB \ {x, w'}) x' by
      linarith
    refine fAle1 hA'x' ?_
    have : (G.deleteIncidencesOf {x, w'}).neighborFinset x' = G.neighborFinset x' \ {x, w'} := by
      refine deleteIncidencesOf_neighborFinset_eq ?_
      simp only [mem_insert, hxx'.ne', mem_singleton, hw'x'.ne', or_self, not_false_eq_true]
    rw [degree, this, card_sdiff, ← degree, hdx']
    suffices {x, w'} ⊆ G.neighborFinset x' by grind
    grind [mem_neighborFinset, Adj.symm]

private lemma _Claim12_of_v'w'
    {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {v w x y v' w' : V}
    (hdv : G.degree v = 2) (hdw : G.degree w = 2) (hdv' : G.degree v' = 3) (hdw' : G.degree w' = 3)
    (hdx : G.degree x = 3) (hdy : G.degree y = 3)
    (hvx : G.Adj v x) (hxy : G.Adj x y) (hyw : G.Adj y w) (hvv' : G.Adj v v') (hww' : G.Adj w w')
    (hv'w' : G.Adj v' w')
    (hv'x : ¬G.Adj v' x) (hw'y : ¬G.Adj w' y) (hxw' : ¬G.Adj x w') (hyv' : ¬G.Adj y v')
    (hvnew : v ≠ w) (hxney : x ≠ y) (hvney : v ≠ y) (hwnex : w ≠ x)
    (hv'eqw' : v' ≠ w') (hv'eqy : v' ≠ y) (hw'eqx : w' ≠ x) (hxnev' : x ≠ v') (hynew' : y ≠ w')
    (hAx : AB.A x) (hAy : AB.A y) (hAv' : AB.A v') (hAw' : AB.A w') (hAv : AB.A v) (hAw : AB.A w)
    (hNv : G.neighborFinset v = {x, v'})
    (h : ∀ u ∈ AB.toFinset, AB.A u ∧ (G.degree u = 2 ∨ G.degree u = 3))
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB')
    : Objective G AB := by
  obtain ⟨x', hxx', hynex', hvnex'⟩ := Finset_get_other_other (le_of_eq hdx.symm) y v
  obtain ⟨y', hyy', hxney', hwney'⟩ := Finset_get_other_other (le_of_eq hdy.symm) x w
  obtain ⟨v'', hv'v'', hvnev'', hw'nev''⟩ := Finset_get_other_other (le_of_eq hdv'.symm) v w'
  obtain ⟨w'', hw'w'', hwnew'', hv'new''⟩ := Finset_get_other_other (le_of_eq hdw'.symm) w v'
  have hNx : G.neighborFinset x = {v, y, x'} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [← degree, hdx, card_triplet' hvney hvnex' hynex']
  obtain ⟨hAx', hdx'⟩ :=
    h x' (hG <| G.mem_support.mpr ⟨x, Adj.symm <| mem_neighborFinset .. |>.mp hxx'⟩)
  obtain ⟨hAy', hdy'⟩ :=
    h y' (hG <| G.mem_support.mpr ⟨y, Adj.symm <| mem_neighborFinset .. |>.mp hyy'⟩)
  match hdx', hdy' with
  | Or.inl hdx', _ =>
      exact Claim7 hG hvx (mem_neighborFinset .. |>.mp hxx') hvnex' hdx hdv hdx' ih
  | _, Or.inl hdy' =>
      exact Claim7 hG hyw.symm (mem_neighborFinset .. |>.mp hyy') hwney' hdy hdw hdy' ih
  | Or.inr hdx', Or.inr hdy' => ?_
  obtain ⟨hwnev', hvnew'⟩ : w ≠ v' ∧ v ≠ w':= by
    refine ⟨?_, ?_⟩ <;> refine ne_of_ne_congr (G.degree ·) (by simp [hdw, hdv', hdv, hdw'])
  simp only [mem_neighborFinset] at hxx' hyy' hv'v'' hw'w''
  have hNw : G.neighborFinset w = {y, w'} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [← degree, hdw, card_pair hynew']
  have hNw' : G.neighborFinset w' = {w, v', w''} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [← degree, hdw', card_triplet' hwnev' hwnew'' hv'new'']
  if hx'eqy' : x' = y' then
    cases Claim10 hG hxy hyy' (hx'eqy' ▸ hxx') ih with
    | inr h => exact h
    | inl h => ?_
    refine hvnew (h.2.2.2 v w ?_ ?_ hdv hdw) |>.elim
    · exact mem_closed_neighborFinset_iff.mpr <| Or.inr ⟨x, mem_insert_self .., hvx.symm⟩
    · exact mem_closed_neighborFinset_iff.mpr <| Or.inr ⟨y, by member_of, hyw⟩
  else if hv''eqw'' : v'' = w'' then
    cases Claim10 hG hv'v'' (hv''eqw'' ▸ hw'w''.symm) hv'w' ih with
    | inr h => exact h
    | inl h => ?_
    refine hvnew (h.2.2.2 v w ?_ ?_ hdv hdw) |>.elim
    · exact mem_closed_neighborFinset_iff.mpr <| Or.inr ⟨v', mem_insert_self .., hvv'.symm⟩
    · exact mem_closed_neighborFinset_iff.mpr <| Or.inr ⟨w', by member_of, hww'.symm⟩
  else if hx'eqw'' : x' = w'' then
    subst hx'eqw''
    refine _Claim12_of_v'w'_of_x'_eq_w' hG hdv hdw hdv' hdw' hdx hdy hdx' hvx hxy hyw hvv' hww' hxx'
      hw'w'' hv'w' hvnew hxney hvney hwnex hynex' hvnex' hwnew'' hv'new'' hv'eqw' hv'eqy hw'eqx
      hxnev' hynew' hAx hAy hAv' hAw' hAx' hAv hAw ?_ h ih
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [← degree, hdw', card_triplet' hwnev' hwnew'' hv'new'']
  else if hy'eqv'' : y' = v'' then
    subst hy'eqv''
    refine _Claim12_of_v'w'_of_x'_eq_w' hG  hdw hdv hdw' hdv' hdy hdx hdy' hyw.symm hxy.symm
      hvx.symm hww' hvv' hyy' hv'v'' hv'w'.symm hvnew.symm hxney.symm hwnex hvney hxney' hwney'
      hvnev'' hw'nev'' (Ne.symm hv'eqw') hw'eqx hv'eqy hynew' hxnev' hAy hAx hAw' hAv' hAy' hAw
      hAv ?_ h ih
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [← degree, hdv', card_triplet' hvnew' hvnev'' hw'nev'']
  else if hx'eqv'' : x' = v'' then
    subst hx'eqv''
    refine Claim11 hG hdv ?_ ih
    exact _card_N2_of_adj hvx.symm hvv' hv'v''.symm hxx' hxnev' hvnex' hdx hdv hdv'
  else if hy'eqw'' : y' = w'' then
    subst hy'eqw''
    refine Claim11 hG hdw ?_ ih
    exact _card_N2_of_adj hyw hww' hw'w''.symm hyy' hynew' hwney' hdy hdw hdw'
  else
    obtain ⟨hAw'', hdw''⟩ := h w'' (hG <| G.mem_support.mpr ⟨w', hw'w''.symm⟩)
    cases hdw'' with
    | inl hdw'' => exact Claim7 hG hww' hw'w'' hwnew'' hdw' hdw hdw'' ih
    | inr hdw'' => ?_
    obtain ⟨hAv'', hdv''⟩ := h v'' (hG <| G.mem_support.mpr ⟨v', hv'v''.symm⟩)
    cases hdv'' with
    | inl hdv'' => exact Claim7 hG hvv' hv'v'' hvnev'' hdv' hdv hdv'' ih
    | inr hdv'' => ?_
    obtain ⟨hvnew'', hwnew''⟩ : v ≠ w'' ∧ w ≠ w'' := by
      refine ⟨?_, ?_⟩ <;> refine ne_of_ne_congr (G.degree ·) (by simp [hdv, hdw, hdw''])
    refine Claim2' ({v, x} ∪ {w, w'}) (Nonempty.inr pair_nonempty) ?_ ?_ hG ih ?_ ?_
    · grind [AB.mem_iff, AB.mem_toFinset.mp]
    · refine respects_of_A (by grind [AB.mem_iff, AB.mem_toFinset.mp])
    · refine InducesForestOfStars_union_disjoint_neighborhoods ?_ ?_ ?_
      · exact InducesForestOfStars_pair
      · exact InducesForestOfStars_pair
      · intro v₁ hv₁ v₂ hv₂
        suffices v₁ ∉ G.neighborFinset v₂ by
          exact not_iff_not.mpr (mem_neighborFinset ..) |>.mp <| not_mem_neighborFinset_symm this
        grind [Adj.ne, Adj.symm]
    · have : #({v, x} ∪ {w, w'}) = 4 := by grind
      rw [this, Nat.cast_four]; clear this
      have : G.closed_neighborFinset_of_Finset ({v, x} ∪ {w, w'})
          = {v, x, w, w', x', y, w'', v'} := by
        rw [closed_neighborFinset_of_union, closed_neighborFinset_of_pair_eq,
          closed_neighborFinset_of_pair_eq, hNv, hNw, hNx, hNw']
        ext
        simp only [union_insert, insert_union, singleton_union, ne_eq,
          singleton_inter_eq_empty_iff, mem_insert, mem_singleton, or_true, not_true_eq_false,
          not_false_eq_true, mem_of_singleton_inter_ne_emty, insert_eq_of_mem, true_or]
        grind
      rw [this]; clear this
      have : ∑ z ∈ {v, x, w, w', x', y, w'', v'}, f G AB z
          = f G AB v + f G AB x + f G AB w + f G AB w' + f G AB x' + f G AB y
            + f G AB w'' + f G AB v' := by
        repeat rw [sum_insert]
        · rw [sum_singleton]
          linarith
        any_goals grind [Adj.ne, Adj.symm]
      rw [this, fA2 hAv hdv, fA2 hAw hdw, fA3 hAx hdx, fA3 hAw' hdw', fA3 hAx' hdx',
        fA3 hAy hdy, fA3 hAw'' hdw'', fA3 hAv' hdv']; clear this
      suffices 2 / 10 ≤ ∑ z ∈ G.N2_of_Finset ({v, x} ∪ {w, w'}), γ G AB z by linarith
      have : ∑ z ∈ G.N2_of_Finset ({v, x} ∪ {w, w'}), 1 / 10
          ≤ ∑ z ∈ G.N2_of_Finset ({v, x} ∪ {w, w'}), γ G AB z := by
        refine sum_le_sum fun z hz ↦ ?_
        obtain ⟨hAz, hdz⟩ :=
          h _ (hG <| G.degree_pos_iff_mem_support _ |>.mp <| one_le_degree_of_mem_N2 hz)
        rcases hdz with hdz | hdz
        · rw [γA2 hAz hdz]
          linarith
        · rw [γA3 hAz hdz]
      refine le_trans ?_ this; clear this
      suffices {y', v''} ⊆ G.N2_of_Finset ({v, x} ∪ {w, w'}) by
        refine le_trans (by linarith : 2 / 10 ≤ 2 * (1 / (10 : ℝ))) ?_
        simp only [sum_const', one_div, inv_pos, Nat.ofNat_pos, mul_le_mul_iff_left₀,
          Nat.ofNat_le_cast, ← card_pair hy'eqv'']
        exact card_le_card this
      intro z hz
      refine mem_N2_of_Finset_iff.mpr ?_
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with hz | hz
      · subst hz
        have : z ≠ w' := by
          refine ne_of_ne_congr (G.Adj y ·) ?_
          simp only [hyy', ne_eq, eq_iff_iff, true_iff]
          suffices y ∉ G.neighborFinset w' by
            exact not_adj_symm <| not_iff_not.mpr (mem_neighborFinset ..) |>.mp this
          grind
        refine ⟨by grind, ?_, ⟨x, by member_of, y, by grind, hyy'.symm, hxy.symm⟩⟩
        intro z' hz'
        suffices z ∉ G.neighborFinset z' by
          exact not_adj_symm <| not_iff_not.mpr (mem_neighborFinset ..) |>.mp this
        grind [Adj.ne]
      · subst hz
        refine ⟨by grind, ?_, ⟨v, by member_of, v', by grind, hv'v''.symm, hvv'.symm⟩⟩
        intro z' hz'
        suffices z ∉ G.neighborFinset z' by
          exact not_adj_symm <| not_iff_not.mpr (mem_neighborFinset ..) |>.mp this
        grind [Adj.ne, Adj.symm]

set_option maxHeartbeats 1000000 in  -- woopsie it's a bit long
private lemma _Claim12_of_not_v'w'
    {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset)
    {v w x y v' w' : V}
    (hdv : G.degree v = 2) (hdw : G.degree w = 2) (hdx : G.degree x = 3) (hdy : G.degree y = 3)
    (hdv' : G.degree v' = 3) (hdw' : G.degree w' = 3)
    (hvnew : v ≠ w) (hxney : x ≠ y) (hvney : v ≠ y) (hwnex : w ≠ x) (hxnev' : x ≠ v')
    (hynew' : y ≠ w') (hv'eqw' : v' ≠ w') (hv'eqy : v' ≠ y) (hw'eqx : w' ≠ x)
    (hvx : G.Adj v x) (hxy : G.Adj x y) (hyw : G.Adj y w) (hvv' : G.Adj v v') (hww' : G.Adj w w')
    (hv'x : ¬G.Adj v' x) (hyw' : ¬G.Adj y w') (hxw' : ¬G.Adj x w') (hyv' : ¬G.Adj y v')
    (hv'w' : ¬G.Adj v' w')
    (hAv : AB.A v) (hAw : AB.A w) (hAx : AB.A x) (hAy : AB.A y) (hAv' : AB.A v') (hAw' : AB.A w')
    (hNv : G.neighborFinset v = {x, v'}) (hNw : G.neighborFinset w = {y, w'})
    (h : ∀ u ∈ AB.toFinset, AB.A u ∧ (G.degree u = 2 ∨ G.degree u = 3))
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V) [AB'.Decidable],
      G'.support ⊆ ↑AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  obtain ⟨x', hxx', hvnex', hynex'⟩ := Finset_get_other_other (le_of_eq hdx.symm) v y
  obtain ⟨y', hyy', hwney', hxney'⟩ := Finset_get_other_other (le_of_eq hdy.symm) w x
  have hNx : G.neighborFinset x = {v, y, x'} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind only [= subset_iff, Adj.symm, = mem_insert, mem_neighborFinset, = mem_singleton]
    · rw [← degree, hdx, card_triplet' hvney hvnex' hynex']
  have hNy : G.neighborFinset y = {w, x, y'} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind only [= subset_iff, Adj.symm, = mem_insert, mem_neighborFinset, = mem_singleton]
    · rw [← degree, hdy, card_triplet' hwnex hwney' hxney']
  simp only [mem_neighborFinset] at hxx' hyy'
  obtain ⟨hAx', hdx'⟩ := h x' <| hG <| G.mem_support.mpr ⟨x, hxx'.symm⟩
  cases hdx' with
  | inl hdx' => exact Claim7 hG hvx hxx' hvnex' hdx hdv hdx' ih
  | inr hdx' => ?_
  obtain ⟨hAy', hdy'⟩ := h y' <| hG <| G.mem_support.mpr ⟨y, hyy'.symm⟩
  cases hdy' with
  | inl hdy' => exact Claim7 hG hyw.symm hyy' hwney' hdy hdw hdy' ih
  | inr hdy' => ?_
  if hx'ney' : x' = y' then
    cases Claim10 hG hxy hyy' (hx'ney' ▸ hxx') ih with
    | inr h => exact h
    | inl h => ?_
    refine hvnew (h.2.2.2 v w ?_ ?_ hdv hdw) |>.elim
    · exact mem_closed_neighborFinset_iff.mpr <| Or.inr ⟨x, mem_insert_self .., hvx.symm⟩
    · exact mem_closed_neighborFinset_iff.mpr <| Or.inr ⟨y, by member_of, hyw⟩
  else if hv'x' : G.Adj v' x' then
    refine Claim11 hG hdv ?_ ih
    exact _card_N2_of_adj hvv'.symm hvx hxx'.symm hv'x' hxnev'.symm hvnex' hdv' hdv hdx
  else if hv'nex' : v' = x' then
    have := Claim10 hG hvx hxx' (hv'nex' ▸ hvv') ih
    simp only [hdv, twonethree, false_and, false_or] at this
    exact this
  else if hv'w : G.Adj v' w then
    exact Claim7 hG hvv' hv'w hvnew hdv' hdv hdw ih
  else
    have : Objective G AB ∨ ∀ z, G.Adj v' z → z ≠ v → (AB.A z ∧ G.degree z = 3) := by
      by_contra
      simp only [not_or, not_forall] at this
      obtain ⟨hobj, ⟨z, hv'z, hznev, hdzne3⟩⟩ := this
      refine hobj ?_
      obtain ⟨hAz, hdz⟩ := h z (hG <| G.mem_support.mpr ⟨v', hv'z.symm⟩)
      simp only [hAz, true_and] at hdzne3
      simp only [hdzne3, or_false] at hdz
      exact Claim7 hG hvv' hv'z hznev.symm hdv' hdv hdz ih
    cases this with
    | inl h => exact h
    | inr HNv => ?_
    obtain ⟨hx'new, hx'nev, hy'nev, h'new⟩ : x' ≠ w ∧ x' ≠ v ∧ y' ≠ v ∧ y' ≠ w := by
      refine ⟨?_, ?_, ?_, ?_⟩
      <;> refine ne_of_ne_congr (G.degree ·) (by simp [hdx', hdy', hdv, hdw])
    have hx'v : ¬G.Adj x' v := by
      refine not_adj_symm <| not_iff_not.mpr (mem_neighborFinset ..) |>.mp <| hNv ▸ ?_
      simp only [mem_insert, mem_singleton, hxx'.ne', Ne.symm hv'nex', false_or, not_false_eq_true]
    have hx'y : ¬G.Adj x' y := by
      refine not_adj_symm <| not_iff_not.mpr (mem_neighborFinset ..) |>.mp <| hNy ▸ ?_
      simp only [mem_insert, mem_singleton, hx'new, hxx'.ne', hx'ney', false_or, not_false_eq_true]
    have hx'w : ¬G.Adj x' w := by
      intro hx'w
      have := hNw ▸ mem_neighborFinset .. |>.mpr hx'w.symm
      simp only [mem_insert, hynex'.symm, mem_singleton, false_or] at this
      exact hxw' (this ▸ hxx')
    obtain ⟨v'', hv'v'', hvnev'', hy'nev''⟩ := Finset_get_other_other (le_of_eq hdv'.symm) v y'
    simp only [mem_neighborFinset] at hv'v''
    obtain ⟨hAv'', hdv''⟩ := h v'' (hG <| G.mem_support.mpr ⟨v', hv'v''.symm⟩)
    cases hdv'' with
    | inl hdv'' => exact Claim7 hG hv'v''.symm hvv'.symm hvnev''.symm hdv' hdv'' hdv ih
    | inr hdv'' => ?_
    obtain ⟨s, hs, hsf, hsresp, hscard⟩ := by
      refine ih (G.deleteIncidencesOf {v, w, x, y, x', v'}) (AB \ {v, w, x, y, x', v'} |>.demote w')
        ?_ ?_
      · rw [← demote_toFinset_eq]
        exact hsupp_mono hG
      · rw [← card_demote_eq_card]
        refine (AB.sdiff_card <| nonempty_iff_ne_empty.mp ?_)
        exact ⟨v, mem_inter.mpr ⟨mem_insert_self .., AB.mem_toFinset.mp <| Or.inl hAv⟩⟩
    rw [← demote_toFinset_eq, sdiff_toFinset] at hs
    have hsresp' : respects s G (AB.demote w') := by
      intro v₁ hv₁ hB'v₁ v₂ hv₂s hv₂v₁
      have hAv₁ : AB.A v₁ := h _ (hG <| G.mem_support.mpr ⟨v₂, hv₂v₁.symm⟩) |>.1
      have : w' = v₁ := by
        simp only [demote, demote_finset, hAv₁, not_B_of_A, true_and, false_or,
          mem_singleton] at hB'v₁
        exact hB'v₁.symm
      subst this
      refine ⟨?_, ?_⟩
      · simp only [demote, demote_finset, mem_singleton, hv₂v₁.ne, not_false_eq_true,
          and_true]
        exact h _ (hG <| G.mem_support.mpr ⟨w', hv₂v₁⟩) |>.1
      · have := by
          refine hsresp w' hv₁ ?_ v₂ hv₂s ?_
          · simp only [demote, demote_finset, mem_singleton, and_true]
            refine Or.inr ⟨hAv₁, by grind⟩
          · refine deleteIncidencesOf_adj_iff_of_notMem ?_ ?_ |>.mp hv₂v₁
            <;>  grind only [= subset_iff, = mem_sdiff]
        refine le_trans ?_ this.2
        refine card_le_card ?_
        intro z hz
        simp only [mem_inter, mem_neighborFinset] at hz ⊢
        obtain ⟨hz, hzs⟩ := hz
        refine ⟨?_, hzs⟩
        refine deleteIncidencesOf_adj_iff_of_notMem ?_ ?_ |>.mp hz
        <;> grind only [= subset_iff, = mem_sdiff]
    refine ⟨(s ∪ {w}) ∪ {v, x}, ?_, ?_, ?_, ?_⟩
    · grind only [AB.mem_iff, AB.mem_toFinset.mp, = subset_iff, = insert_eq_of_mem, = mem_union,
        = mem_insert, = mem_singleton, = Set.mem_singleton_iff, = mem_sdiff]
    · refine InducesForestOfStars_union_disjoint_neighborhoods ?_ ?_ ?_
      · if hw's : w' ∈ s then
          have : G.degree_in s w = 1 := by grind
          have hN'w : G.neighborFinset w ∩ s = {w'} := by
            rw [hNw]
            grind only [= subset_iff, usr card_union_add_card_inter, = inter_insert, = insert_union,
              = card_insert_of_notMem, = mem_sdiff, = mem_insert, = singleton_inter]
          refine InducesForestOfStars_union_leaf_to_B hsresp' hN'w (AB.demote_from_A hAw') ?_
          refine InducesForestOfStars_graph_mono' ?_ hsf
          grind only [= subset_iff, = insert_inter, = mem_sdiff, = mem_insert, = mem_inter,
            ← notMem_empty]
        else
          have : G.degree_in s w = 0 := by grind
          refine InducesForestOfStars_union_isolated this ?_
          exact InducesForestOfStars_graph_mono' (by grind) hsf
      · exact InducesForestOfStars_pair
      · exact fun _ _ _ _ ↦ not_adj_symm <| not_iff_not.mpr (mem_neighborFinset ..) |>.mp (by grind)
    · refine respects_of_union_disjoint_neighborhood ?_ ?_ ?_
      · refine respects_of_A ?_
        intro z hz
        simp only [union_singleton, mem_insert] at hz
        rcases hz with hz | hz
        · exact hz ▸ hAw
        · exact h _ (mem_sdiff.mp (hs hz) |>.1) |>.1
      · exact respects_pair' hAx
      · intro v₁ hv₁ v₂ hv₂
        suffices v₁ ∉ G.neighborFinset v₂ by
          exact not_adj_symm <| not_iff_not.mpr (mem_neighborFinset ..) |>.mp this
        grind
    · suffices eval G AB ≤ #s + 3 by
        refine this.trans ?_
        rw [← Nat.cast_three, ← Nat.cast_add, Nat.cast_le, card_union, card_union, card_singleton,
          card_pair hvx.ne]
        have : (s ∩ {w}) = ∅ := disjoint_of_sdiff' hs <| singleton_subset_iff.mpr <| by member_of
        rw [this, card_empty, tsub_zero]; clear this
        have : ((s ∪ {w}) ∩ {v, x}) = ∅ := by
          grind only [= subset_iff, = insert_eq_of_mem, = insert_inter, = union_singleton,
            = inter_insert, = mem_insert, = mem_singleton, = mem_sdiff, = mem_inter, ← notMem_empty]
        rw [this, card_empty, tsub_zero]
      calc _
        _ = ∑ z ∈ AB.toFinset \ {v, w, x, y, x', v'}, f G AB z
            + ∑ z ∈ {v, w, x, y, x', v'}, f G AB z := by
          refine Eq.symm <| sum_sdiff ?_
          grind only [= subset_iff, = insert_eq_of_mem, = mem_insert, = mem_singleton,
            AB.mem_iff, AB.mem_toFinset.mp]
        _ = (∑ z ∈ (AB.toFinset \ {v, w, x, y, x', v'}) \ {w'}, f G AB z
              + ∑ z ∈ {w'}, f G AB z)
            + ∑ z ∈ {v, w, x, y, x', v'}, f G AB z := by
          simp only [add_left_inj]
          refine Eq.symm <| sum_sdiff <| singleton_subset_iff.mpr ?_
          refine mem_sdiff.mpr ⟨AB.mem_toFinset.mp <| Or.inl hAw', ?_⟩
          grind only [= insert_eq_of_mem, = mem_insert, = mem_singleton]
        _ = (∑ z ∈ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset \ {w'},
                f G ((AB \ {v, w, x, y, x', v'}).demote w') z
              + f G AB w')
            + ∑ z ∈ {v, w, x, y, x', v'}, f G AB z := by
          simp only [sum_singleton, add_left_inj]
          refine sum_congr ?_ ?_
          · rw [← demote_toFinset_eq, ← sdiff_toFinset]
          · intro z hz
            rw [← demote_toFinset_eq, sdiff_toFinset] at hz
            have hAz : AB.A z := by
              refine h _ ?_ |>.1
              exact mem_sdiff.mp (mem_sdiff.mp hz |>.1) |>.1
            have hznew' : z ≠ w' := notMem_singleton.mp <| mem_sdiff.mp hz |>.2
            have hA'z : (AB \ {v, w, x, y, x', v'}).demote w' |>.A z := by
              simp only [demote, demote_finset, mem_singleton, hznew', not_false_eq_true, and_true,
                sdiff, hAz, true_and]
              grind only [= mem_sdiff]
            refine Eq.symm <| f_congr rfl ⟨fun _ ↦ hAz, ?_, ?_⟩
            · intro h'z
              simp only [demote, demote_finset, sdiff, hAz, not_B_of_A, false_and, true_and,
                mem_singleton, false_or, hznew', and_false] at h'z
            · simp only [Bipartition.mem_iff, hAz, true_or, not_true_eq_false, hA'z, imp_self]
        _ = (∑ z ∈ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset,
                f G ((AB \ {v, w, x, y, x', v'}).demote w') z
              - f G ((AB \ {v, w, x, y, x', v'}).demote w') w'
              + f G AB w')
            + ∑ z ∈ {v, w, x, y, x', v'}, f G AB z := by
          suffices ∑ z ∈ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset \ {w'},
                f G ((AB \ {v, w, x, y, x', v'}).demote w') z
                + f G ((AB \ {v, w, x, y, x', v'}).demote w') w'
              = ∑ z ∈ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset,
                f G ((AB \ {v, w, x, y, x', v'}).demote w') z by
            linarith
          rw [← sum_singleton (f G ((AB \ {v, w, x, y, x', v'}).demote w') ·) w']
          refine sum_sdiff <| singleton_subset_iff.mpr ?_
          rw [← demote_toFinset_eq, sdiff_toFinset]
          grind [AB.mem_iff, AB.mem_toFinset.mp]
        _ = ∑ z ∈ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset,
                f G ((AB \ {v, w, x, y, x', v'}).demote w') z
            + 3 + 9 / 20 := by
          have : ∑ z ∈ {v, w, x, y, x', v'}, f G AB z
              = f G AB v + f G AB w + ∑ z ∈ {x, y, x', v'}, f G AB z := by
            grind
          rw [this]; clear this
          have : ∑ z ∈ {x, y, x', v'}, f G AB z = f G AB x + f G AB y + f G AB x' + f G AB v' := by
            grind [mem_neighborFinset, Adj.symm, Adj.ne]
          rw [this, fA2 hAv hdv, fA2 hAw hdw, fA3 hAx hdx, fA3 hAy hdy, fA3 hAx' hdx',
            fA3 hAv' hdv', fA3 hAw' hdw', fB3]
          · linarith
          · exact demote_from_A _ ⟨hAw', by grind⟩
          · exact hdw'
      suffices ∑ z ∈ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset,
              f G ((AB \ {v, w, x, y, x', v'}).demote w') z
              + 9 / 20
          ≤ eval (G.deleteIncidencesOf {v, w, x, y, x', v'})
              ((AB \ {v, w, x, y, x', v'}).demote w') by
        linarith
      suffices 9 / 20
          ≤ ∑ z ∈ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset,
              (f (G.deleteIncidencesOf {v, w, x, y, x', v'})
                  ((AB \ {v, w, x, y, x', v'}).demote w') z
                - f G ((AB \ {v, w, x, y, x', v'}).demote w') z) by
        rw [eval]
        rw [sum_sub_distrib] at this
        linarith
      have : v'' ∉ ({v, w, x, y, x', w'} : Finset _) := by
        grind [Adj.ne, Adj.symm, mem_neighborFinset]
      let g := fun z ↦
          (f (G.deleteIncidencesOf {v, w, x, y, x', v'})
              ((AB \ {v, w, x, y, x', v'}).demote w') z
            - f G ((AB \ {v, w, x, y, x', v'}).demote w') z)
      have hg {z z' : V} (hzz' : G.Adj z z') (hz : z ∉ ({v, w, x, y, x', v', w'} : Finset _))
          (hz' : z' ∈ ({v, w, x, y, x', v'} : Finset _)) : 1/ 10 ≤ g z := by
        obtain ⟨hAz, hdz⟩ := h z (hG <| G.mem_support.mpr ⟨_, hzz'⟩)
        have hA'z : ((AB \ {v, w, x, y, x', v'}).demote w').A z :=
          demote_A_of_ne _ (by grind) ⟨hAz, by grind⟩
        rcases hdz with hdz | hdz
        · simp only [g, fA2 hA'z hdz]
          linarith [fAlt2 hA'z (hdz ▸ deleteIncidencesOf_degree_lt hzz' hz')]
        · simp only [g, fA3 hA'z hdz]
          linarith [fAlt3 hA'z (hdz ▸ deleteIncidencesOf_degree_lt hzz' hz')]
      have hA'v'' : ((AB \ {v, w, x, y, x', v'}).demote w').A v'' := by
        refine demote_A_of_ne _ ?_ ⟨hAv'', ?_⟩ <;> grind [mem_neighborFinset, Adj.ne, Adj.symm]
      have hA'y' : ((AB \ {v, w, x, y, x', v'}).demote w').A y' := by
        refine demote_A_of_ne _ ?_ ⟨hAy', ?_⟩ <;> grind [mem_neighborFinset, Adj.ne, Adj.symm]
      have hf'v'': 3 / 5 ≤ f (G.deleteIncidencesOf {v, w, x, y, x', v'})
          ((AB \ {v, w, x, y, x', v'}).demote w') v'' := by
        refine fAlt3 hA'v'' ?_
        rw [← hdv'']
        refine deleteIncidencesOf_degree_lt hv'v''.symm <| by member_of
      have hfv'': f G ((AB \ {v, w, x, y, x', v'}).demote w') v'' = 1 / 2 := by
        refine fA3 hA'v'' hdv''
      have hfw' : f G ((AB \ {v, w, x, y, x', v'}).demote w') w' = 1 / 4 :=
        fB3 (demote_from_A _ ⟨hAw', by grind⟩) hdw'
      have hfy': f G ((AB \ {v, w, x, y, x', v'}).demote w') y' = 1 / 2 := by
        refine fA3 hA'y' hdy'
      have Hw'v''y' : {w', v'', y'} ⊆ AB.toFinset \ {v, w, x, y, x', v'} := by
        refine subset_sdiff.mpr ⟨?_, disjoint_iff_inter_eq_empty.mpr ?_⟩
        · intro z hz
          simp only [mem_insert, mem_singleton] at hz
          refine hG <| G.mem_support.mpr ?_
          rcases hz with hz | hz | hz
          · exact ⟨w, hz ▸ hww'.symm⟩
          · exact ⟨v', hz ▸ hv'v''.symm⟩
          · exact ⟨y, hz ▸ hyy'.symm⟩
        · grind only [= mem_insert, Adj.symm, = insert_inter, = inter_insert, Adj.ne,
            = mem_singleton, = mem_inter, ← notMem_empty]
      if hx'w' : G.Adj x' w' then
        suffices {w', v'', y'} ⊆ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset by
          have : ∑ z ∈ {w', v'', y'}, g z ≤ ∑ z ∈ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset,
              g z := by
            refine sum_le_sum_of_subset_of_nonneg this fun z hz h'z ↦ ?_
            simp only [sub_nonneg, g, f_le_f']
          refine le_trans ?_ this; clear this
          have : ∑ z ∈ {w', v'', y'}, g z = g w' + g v'' + g y' := by
            rw [sum_triplet]
            <;> grind only
          rw [this]; clear this
          have hf'w': 1 / 2 ≤ f (G.deleteIncidencesOf {v, w, x, y, x', v'})
              ((AB \ {v, w, x, y, x', v'}).demote w') w' := by
            refine fBle1 (demote_from_A _ ⟨hAw', by grind⟩) ?_
            rw [degree, deleteIncidencesOf_neighborFinset_eq (by grind), card_sdiff, ← degree, hdw']
            suffices 2 ≤ #({v, w, x, y, x', v'} ∩ G.neighborFinset w') by grind
            rw [← card_pair hx'new]
            refine card_le_card ?_
            grind only [= subset_iff, Adj.symm, = inter_insert, = mem_insert, = mem_inter,
              = mem_singleton, mem_neighborFinset]
          have hf'y': 3 / 5 ≤ f (G.deleteIncidencesOf {v, w, x, y, x', v'})
              ((AB \ {v, w, x, y, x', v'}).demote w') y' := by
            refine fAlt3 hA'y' ?_
            rw [← hdy']
            refine deleteIncidencesOf_degree_lt hyy'.symm <| by member_of
          have hfy': f G ((AB \ {v, w, x, y, x', v'}).demote w') y' = 1 / 2 := by
            refine fA3 hA'y' hdy'
          simp only [g, hfw', hfv'', hfy']
          linarith
        rw [← demote_toFinset_eq, sdiff_toFinset]
        exact Hw'v''y'
      else
      have hf'w': 1 / 3 ≤ f (G.deleteIncidencesOf {v, w, x, y, x', v'})
          ((AB \ {v, w, x, y, x', v'}).demote w') w' := by
        refine fBlt3 (demote_from_A _ ⟨hAw', by grind⟩) ?_
        rw [← hdw']
        exact deleteIncidencesOf_degree_lt hww'.symm <| by member_of
      have : 1 / 12 ≤ g w' := by linarith
      if hv'y' : G.Adj v' y' then
        suffices {v'', w', y'} ⊆ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset by
          have : ∑ z ∈ {v'', w', y'}, g z ≤ ∑ z ∈ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset,
              g z := by
            refine sum_le_sum_of_subset_of_nonneg this fun z hz h'z ↦ ?_
            simp only [sub_nonneg, g, f_le_f']
          refine le_trans ?_ this; clear this
          have hf'y': 5 / 6 ≤ f (G.deleteIncidencesOf {v, w, x, y, x', v'})
              ((AB \ {v, w, x, y, x', v'}).demote w') y' := by
            refine fAle1 hA'y' ?_
            rw [degree, deleteIncidencesOf_neighborFinset_eq (by grind [Adj.ne, Adj.symm]),
              card_sdiff, ← degree, hdy']
            suffices 2 ≤ #({v, w, x, y, x', v'} ∩ G.neighborFinset y') by grind
            rw [← card_pair hv'eqy]
            refine card_le_card <| subset_inter ?_ ?_
            · grind
            · intro z hz
              simp only [mem_insert, mem_singleton, mem_neighborFinset] at hz ⊢
              refine Adj.symm <| by grind only
          have : ∑ z ∈ {v'', w', y'}, g z = g v'' + g w' + g y' := by grind
          linarith
        rw [← demote_toFinset_eq, sdiff_toFinset]
        refine subset_of_eq_of_subset ?_ Hw'v''y'
        clear * - w' v'' y'
        grind only [= mem_insert]
      else if H : G.neighborFinset x' ∩ G.neighborFinset v' = ∅ then
        have H : #((G.neighborFinset x' ∪ G.neighborFinset v') \ {v, w, x, y, x', v'}) = 4 := by
          rw [union_sdiff_distrib, card_union, ← inter_sdiff_distrib, H, empty_sdiff, card_empty,
            tsub_zero, card_sdiff, ← degree, card_sdiff, ← degree, hdx', hdv']
          suffices #(G.neighborFinset x' ∩ {v, w, x, y, x', v'}) = 1
              ∧ #(G.neighborFinset v' ∩ {v, w, x, y, x', v'}) = 1 by
            obtain ⟨h, h'⟩ := this
            rw [inter_comm, h, inter_comm, h']
          refine ⟨(card_singleton x) ▸ le_antisymm ?_ ?_, (card_singleton v) ▸ le_antisymm ?_ ?_⟩
          <;> refine card_le_card <| by grind [mem_neighborFinset, Adj.symm, Adj.ne]
        suffices (((G.neighborFinset x' ∪ G.neighborFinset v') \ {v, w, x, y, x', v'}) ∪ {w'})
            ⊆ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset by
          have : ∑ z ∈ ((G.neighborFinset x' ∪ G.neighborFinset v') \ {v, w, x, y, x', v'}) ∪ {w'},
                  g z
              ≤ ∑ z ∈ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset, g z := by
            refine sum_le_sum_of_subset_of_nonneg this fun z hz h'z ↦ ?_
            simp only [sub_nonneg, g, f_le_f']
          refine le_trans ?_ this; clear this
          suffices 11 / 30
              ≤ ∑ z ∈ (G.neighborFinset x' ∪ G.neighborFinset v') \ {v, w, x, y, x', v'}, g z by
            rw [sum_union, sum_singleton]
            · linarith
            · refine disjoint_iff_inter_eq_empty.mpr <| inter_singleton_of_notMem ?_
              grind [mem_neighborFinset, Adj.symm, Adj.ne]
          have : ∑ z ∈ (G.neighborFinset x' ∪ G.neighborFinset v') \ {v, w, x, y, x', v'}, 1 / 10
              ≤ ∑ z ∈ (G.neighborFinset x' ∪ G.neighborFinset v') \ {v, w, x, y, x', v'}, g z := by
            refine sum_le_sum fun z hz ↦ ?_
            simp only [mem_sdiff, mem_union, mem_neighborFinset] at hz
            obtain ⟨hz, h'z⟩ := hz
            have : z ∉ ({v, w, x, y, x', v', w'} : Finset _) := by
              grind
            clear * - hz hg this
            rcases hz with hz | hz
            <;> refine hg hz.symm this (by member_of)
          refine le_trans ?_ this; clear this
          simp only [sum_const', H, Nat.cast_four]
          linarith
        rw [← demote_toFinset_eq, sdiff_toFinset]
        refine Finset.union_subset ?_ ?_
        · refine sdiff_subset_sdiff ?_ (subset_refl _)
          intro u hu
          refine hG <| G.mem_support.mpr ?_
          simp only [mem_union, mem_neighborFinset] at hu
          rcases hu with hu | hu <;> exact ⟨_, hu.symm⟩
        · grind [AB.mem_iff, AB.mem_toFinset.mp]
      else
        obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.mpr H
        obtain ⟨u', hx'u', huneu', hxneu'⟩ := Finset_get_other_other (le_of_eq hdx'.symm) u x
        simp only [mem_neighborFinset, mem_inter] at hu hx'u'
        obtain ⟨hx'u, hv'u⟩ := hu
        obtain ⟨hAu, hdu⟩ := HNv u hv'u (by grind)
        have hunotinvwx : u ∉ ({v, w, x} : Finset _) := by
          grind [mem_neighborFinset, Adj.symm, Adj.ne]
        have huney : u ≠ y := by
          grind [mem_neighborFinset, Adj.symm, Adj.ne]
        have Hu : u ∉ ({v, w, x, y, x', v'} : Finset _) := by
          grind [mem_neighborFinset, Adj.symm, Adj.ne]
        obtain ⟨hunew', hu'new'⟩ : u ≠ w' ∧ u' ≠ w' := by
          refine ⟨?_, ?_⟩ <;> exact ne_of_ne_congr (G.Adj x' ·) (by simp [hx'u, hx'u', hx'w'])
        suffices {u, u', w'} ⊆ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset by
          have : ∑ z ∈ {u, u', w'}, g z
              ≤ ∑ z ∈ ((AB \ {v, w, x, y, x', v'}).demote w').toFinset, g z := by
            refine sum_le_sum_of_subset_of_nonneg this fun _ _ _ ↦ ?_
            simp only [sub_nonneg, f_le_f', g]
          refine le_trans ?_ this; clear this
          rw [sum_triplet huneu' hunew' hu'new']
          have : 1 / 10 ≤ g u'  := by
            refine hg hx'u'.symm ?_ (by member_of)
            have : u' ∉ ({v, w, x, y} : Finset _) := by grind [mem_neighborFinset, Adj.symm, Adj.ne]
            have : u' ∉ ({x', v', w'} : Finset _) := by grind [mem_neighborFinset, Adj.symm, Adj.ne]
            grind
          have : 1 / 3 ≤ g u := by
            have hA'u : ((AB \ {v, w, x, y, x', v'}).demote w').A u := by
              refine demote_A_of_ne _ ?_ ⟨hAu, ?_⟩ <;> grind [mem_neighborFinset, Adj.ne, Adj.symm]
            simp only [g, fA3 hA'u hdu]
            suffices 5 / 6 ≤ f (G.deleteIncidencesOf {v, w, x, y, x', v'})
                  ((AB \ {v, w, x, y, x', v'}).demote w') u by linarith
            refine fAle1 hA'u ?_
            rw [degree, deleteIncidencesOf_neighborFinset_eq Hu, card_sdiff, ← degree, hdu]
            suffices 2 ≤ #({v, w, x, y, x', v'} ∩ G.neighborFinset u) by lia
            rw [← card_pair hv'nex']
            refine card_le_card fun z ↦ ?_
            simp only [mem_insert, mem_singleton, mem_inter, mem_neighborFinset]
            grind only [Adj.symm]
          linarith
        rw [← demote_toFinset_eq, sdiff_toFinset]
        intro z hz
        simp only [mem_insert, mem_singleton, mem_sdiff, not_or] at hz ⊢
        refine ⟨?_, by grind [Adj.ne, Adj.symm]⟩
        refine hG <| G.mem_support.mpr ?_
        rcases hz with hz | hz | hz
        · exact ⟨_, hz ▸ hx'u.symm⟩
        · exact ⟨_, hz ▸ hx'u'.symm⟩
        · exact ⟨_, hz ▸ hww'.symm⟩

lemma Claim12_of_dist_3 {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} [AB.Decidable]
    (hG : G.support ⊆ AB.toFinset) {v w x y : V} (hdv : G.degree v = 2) (hdw : G.degree w = 2)
    (hvnew : v ≠ w) (hvx : G.Adj v x) (hxy : G.Adj x y) (hyw : G.Adj y w)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    Objective G AB := by
  match Claim6' hG ih with
  | Or.inr h => exact h
  | Or.inl h => ?_
  have h : ∀ u ∈ AB.toFinset, AB.A u ∧ (G.degree u = 2 ∨ G.degree u = 3) := by grind
  have hAv : AB.A v := h v (hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith) |>.1
  have hAw : AB.A w := h w (hG <| G.degree_pos_iff_mem_support _ |>.mp <| by linarith) |>.1
  obtain ⟨hAx, hdx⟩ := h x (hG <| G.mem_support.mpr ⟨y, hxy⟩)
  obtain ⟨hAy, hdy⟩ := h y (hG <| G.mem_support.mpr ⟨x, hxy.symm⟩)
  match hdx, hdy with
  | Or.inl hdx, _ => exact Claim9 hG hvx hdv hdx ih
  | _, Or.inl hdy => exact Claim9 hG hyw hdy hdw ih
  | Or.inr hdx, Or.inr hdy => ?_
  obtain ⟨hvney, hwnex⟩ : v ≠ y ∧ w ≠ x := by
    refine ⟨?_, ?_⟩ <;> refine ne_of_ne_congr (G.degree ·) (by simp [hdv, hdw, hdx, hdy])
  obtain ⟨v', hv', hxnev'⟩ := Finset_get_other (le_of_eq <| hdv.symm) x
  obtain ⟨w', hw', hynew'⟩ := Finset_get_other (le_of_eq <| hdw.symm) y
  have hNv : G.neighborFinset v = {x, v'} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset]
    · rw [← degree, hdv, card_pair hxnev']
  have hNw : G.neighborFinset w = {y, w'} := by
    refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
    · grind [mem_neighborFinset, Adj.symm]
    · rw [← degree, hdw, card_pair hynew']
  simp only [mem_neighborFinset] at hv' hw'
  obtain ⟨hAv', hdv'⟩ := h v' (hG <| G.mem_support.mpr ⟨v, hv'.symm⟩)
  obtain ⟨hAw', hdw'⟩ := h w' (hG <| G.mem_support.mpr ⟨w, hw'.symm⟩)
  match hdv', hdw' with
  | Or.inl hdv', _ => exact Claim9 hG hv' hdv hdv' ih
  | _, Or.inl hdw' => exact Claim9 hG hw' hdw hdw' ih
  | Or.inr hdv', Or.inr hdw' => ?_
  if hv'eqw' : v' = w' then
    exact Claim7 hG hv' (hv'eqw' ▸ hw'.symm) hvnew hdv' hdv hdw ih
  else if hv'eqy : v' = y then
    exact Claim7 hG (hv'eqy ▸ hv') hyw hvnew hdy hdv hdw ih
  else if hw'eqx : w' = x then
    exact Claim7 hG hvx (hw'eqx ▸ hw'.symm) hvnew hdx hdv hdw ih
  else if hv'x : G.Adj v' x then
    have := Claim10 hG hv' hv'x hvx ih
    simp only [hdv, twonethree, false_and, false_or] at this
    exact this
  else if hyw' : G.Adj y w' then
    have := Claim10 hG hyw hw' hyw' ih
    simp only [hdw, twonethree, false_and, and_false, false_or] at this
    exact this
  else if hxw' : G.Adj x w' then
    exact Claim11 hG hdw (_card_N2_of_adj hyw hw' hxw' hxy.symm hynew' hwnex hdy hdw hdw') ih
  else if hyv' : G.Adj y v' then
    exact Claim11 hG hdv (_card_N2_of_adj hvx.symm hv' hyv' hxy hxnev' hvney hdx hdv hdv') ih
  else if hv'w' : G.Adj v' w' then
    exact _Claim12_of_v'w' hG hdv hdw hdv' hdw' hdx hdy hvx hxy hyw hv' hw' hv'w' hv'x
      (not_adj_symm hyw') hxw' hyv' hvnew hxy.ne hvney hwnex hv'eqw' hv'eqy hw'eqx hxnev'
      hynew' hAx hAy  hAv' hAw' hAv hAw hNv h ih
  else
    exact _Claim12_of_not_v'w' hG hdv hdw hdx hdy hdv' hdw' hvnew hxy.ne hvney hwnex hxnev' hynew'
      hv'eqw' hv'eqy hw'eqx hvx hxy hyw hv' hw' hv'x hyw' hxw' hyv' hv'w' hAv hAw hAx hAy hAv' hAw'
      hNv hNw h ih

end Bipartition
end AB
end CaroWeiType
