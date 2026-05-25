import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim1
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim4

open SimpleGraph
open Finset

namespace CaroWeiType
namespace ABC
namespace Tripartition

variable {V : Type} [Fintype V] [DecidableEq V]

@[reducible]
private def _op_g (G : SimpleGraph V) [DecidableRel G.Adj] (v x y : V) :
    SimpleGraph V :=
  (fromEdgeSet <| G.edgeSet ∪ {s(x, y)}).deleteIncidencesOf {v}

private lemma _op_g_Nv (G : SimpleGraph V) [DecidableRel G.Adj] {v x y : V} :
    (_op_g G v x y).neighborFinset v = ∅ := by
  simp only [_op_g]
  exact deleteIncidencesOf_neighborFinset_empty (mem_singleton.mpr rfl)

private lemma _op_g_Nxy (G : SimpleGraph V) [DecidableRel G.Adj] {v w x y z : V}
    (hNv : G.neighborFinset v = {x, y, z}) (hw : w ∈ ({x, y} : Finset _)) :
    (_op_g G v x y).neighborFinset w = (G.neighborFinset w ∪ {x, y}) \ {v, w} := by
  ext u
  constructor
  · intro hu
    have hunev : ¬u = v :=
      ne_of_mem_of_not_mem hu (not_mem_neighborFinset_symm <| _op_g_Nv G ▸ notMem_empty w)
    refine mem_sdiff.mpr ⟨?_, ?_⟩
    · have := mem_neighborFinset_of_deleteIncidencesOf_mem_neighborFinset hu
      rcases mem_fromEdgeSet_union_neighborFinset_iff.mp this with hu | hu
      · exact mem_union_left _ hu
      · exact mem_union_right _ (by grind)
    · simp only [mem_insert, mem_singleton, not_or, ne_of_mem_neighborFinset hu,
        not_false_eq_true, and_true, hunev]
  · intro hu
    have Huv : u ≠ v := by grind only [= mem_sdiff, = mem_insert]
    have Hwv : w ≠ v := by
      refine ne_of_mem_of_not_mem (hNv ▸ ?_) (G.notMem_neighborFinset_self _)
      grind only [= mem_insert, = mem_singleton]
    refine mem_neighborFinset_deleteIncidencesOf_of_notMem_of_notMem_of_mem_neighborFinset
      (notMem_singleton.mpr Huv) (notMem_singleton.mpr Hwv) ?_
    rcases mem_union.mp <| mem_sdiff.mp hu |>.1 with hu | hu
    · exact le_fromEdgeSet_union' hu
    · exact mem_fromEdgeSet_union_neighborFinset_iff.mpr <| Or.inr <| by grind

private lemma _op_g_Nx (G : SimpleGraph V) [DecidableRel G.Adj] {v x y z : V}
    (hNv : G.neighborFinset v = {x, y, z}) (hxy : x ≠ y) :
    (_op_g G v x y).neighborFinset x = (G.neighborFinset x ∪ {y}) \ {v} := by
  rw [_op_g_Nxy G hNv (mem_insert_self x _)]
  ext u
  simp only [union_insert, union_singleton, mem_sdiff, mem_insert, mem_neighborFinset,
    mem_singleton, not_or]
  constructor
  · refine fun ⟨h, huv, hux⟩ ↦ ⟨?_, huv⟩
    simp only [hux, false_or] at h
    exact h
  · intro ⟨h, huv⟩
    exact ⟨Or.inr h, huv, by grind only [Adj.ne]⟩

private lemma _op_g_degx (G : SimpleGraph V) [DecidableRel G.Adj] {v x y z : V}
    (hNv : G.neighborFinset v = {x, y, z}) (hxy : x ≠ y) :
    (_op_g G v x y).degree x ≤ G.degree x := by
  let hobj := congrArg Finset.card <| _op_g_Nx G hNv hxy
  simp only [degree, hobj]
  have hsdiff : #((G.neighborFinset x ∪ {y}) \ {v}) = #((G.neighborFinset x ∪ {y})) - 1 := by
    refine card_sdiff_of_subset ?_
    simp only [union_singleton, singleton_subset_iff, mem_insert]
    exact Or.inr <| mem_neighborFinset_symm (by simp only [hNv, mem_insert, mem_singleton, true_or])
  rw [hsdiff]
  calc #(G.neighborFinset x ∪ {y}) - 1
    _ ≤ #(G.neighborFinset x) + 1 - 1 := by
      have hcup : #(G.neighborFinset x ∪ {y}) ≤ (#(G.neighborFinset x) + 1) := by
        exact card_union_le ..
      grind only [= card_sdiff_of_subset, usr card_sdiff_add_card_inter, = card_singleton]
    _ = #(G.neighborFinset x) := Nat.add_sub_self_right ..

private lemma _op_g_Ny (G : SimpleGraph V) [DecidableRel G.Adj] {v x y z : V}
    (hNv : G.neighborFinset v = {x, y, z}) (hxy : x ≠ y) :
    (_op_g G v x y).neighborFinset y = (G.neighborFinset y ∪ {x}) \ {v} := by
  have hy : y ∈ ({x, y} : Finset _) := by
    simp only [mem_insert, mem_singleton, or_true]
  rw [_op_g_Nxy G hNv hy]
  ext u
  simp only [union_insert, union_singleton, mem_sdiff, mem_insert, mem_neighborFinset,
    mem_singleton, not_or]
  constructor
  · refine fun ⟨h, huv, hux⟩ ↦ ⟨?_, huv⟩
    simp only [hux, false_or] at h
    exact h
  · intro ⟨h, huv⟩
    refine ⟨by grind only, huv, by grind only [Adj.ne]⟩

private lemma _op_g_degy (G : SimpleGraph V) [DecidableRel G.Adj] {v x y z : V}
    (hNv : G.neighborFinset v = {x, y, z}) (hxy : x ≠ y) :
    (_op_g G v x y).degree y ≤ G.degree y := by
  let hobj := congrArg Finset.card <| _op_g_Ny G hNv hxy
  simp only [degree, hobj]
  have hsdiff : #((G.neighborFinset y ∪ {x}) \ {v}) = #((G.neighborFinset y ∪ {x})) - 1 := by
    refine card_sdiff_of_subset ?_
    simp only [union_singleton, singleton_subset_iff, mem_insert]
    exact Or.inr <| mem_neighborFinset_symm
      <| by simp only [hNv, mem_insert, mem_singleton, true_or, or_true]
  rw [hsdiff]
  calc #(G.neighborFinset y ∪ {x}) - 1
    _ ≤ #(G.neighborFinset y) + 1 - 1 := by
      have hcup : #(G.neighborFinset y ∪ {x}) ≤ (#(G.neighborFinset y) + 1) := by
        exact card_union_le ..
      grind only [= card_sdiff_of_subset, usr card_sdiff_add_card_inter, = card_singleton]
    _ = #(G.neighborFinset y) := Nat.add_sub_self_right ..

@[reducible]
private def _op_t (ABC : Tripartition V) (v x y z : V) : Tripartition V :=
  ABC \ {v} |>.demote_finset {x, y, z}

private lemma _op_t_toFinset_subset {ABC : Tripartition V} [ABC.Decidable]
    {v x y z : V} :
    (_op_t ABC v x y z).toFinset ⊆ ABC.toFinset := by
  intro u hu
  simp only [_op_t, ← demote_finset_toFinset_eq, sdiff_toFinset] at hu
  exact mem_sdiff.mp hu |>.1

private lemma _op_t_B (ABC : Tripartition V) {v w x y z : V} (hwv : w ≠ v)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hw : w ∈ ({x, y, z} : Finset _)) :
    ABC.A w → (_op_t ABC v x y z).B w := by
  intro hAw
  simp only [mem_insert, mem_singleton] at hw
  rcases hw with h | h | h <;> {
    subst h
    refine Or.inr ⟨⟨hAw, not_iff_not.mpr mem_singleton |>.mpr hwv⟩, ?_⟩
    simp only [mem_insert, mem_singleton, true_or, or_true]
  }

private lemma _op_t_C (ABC : Tripartition V) {v w x y z : V} (hwv : w ≠ v)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hw : w ∈ ({x, y, z} : Finset _)) :
    ABC.B w → (_op_t ABC v x y z).C w := by
  intro hBw
  simp only [mem_insert, mem_singleton] at hw
  rcases hw with h | h | h <;> {
    subst h
    refine Or.inr ⟨⟨hBw, not_iff_not.mpr mem_singleton |>.mpr hwv⟩, ?_⟩
    simp only [mem_insert, mem_singleton, true_or, or_true]
  }

private lemma _degG_eq_degG'_out_Nv {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v x y z : V} (hu : u ∉ ({v, x, y, z} : Finset _))
    (hNv : G.neighborFinset v = {x, y, z}) :
    G.degree u = (_op_g G v x y).degree u := by
  refine congrArg Finset.card ?_
  ext w
  constructor
  · intro hwu
    have : w ≠ v := by
      have huNv : u ∉ G.neighborFinset v := by grind only [= mem_sdiff, = mem_insert]
      exact fun heq ↦ huNv <| mem_neighborFinset_symm (heq ▸ hwu)
    simp only [_op_g]
    refine mem_neighborFinset_deleteIncidencesOf_of_notMem_of_notMem_of_mem_neighborFinset ?_ ?_ ?_
    · exact notMem_singleton.mpr this
    · grind only [= mem_sdiff, = mem_singleton, = mem_insert]
    · exact le_fromEdgeSet_union' hwu
  · intro hwu
    have := mem_neighborFinset_of_deleteIncidencesOf_mem_neighborFinset hwu
    rcases mem_fromEdgeSet_union_neighborFinset_iff.mp this with hw | hw
    · exact hw
    · have := eq_or_eq_of_eq_Sym2 hw.1
      grind only [= mem_sdiff, = mem_insert]

private lemma _degGz_eq_degG'z_plusone {G : SimpleGraph V} [DecidableRel G.Adj]
    {v x y z : V} (hNv : G.neighborFinset v = {x, y, z})
    (hxnez : x ≠ z) (hynez : y ≠ z) :
    G.degree z = (_op_g G v x y).degree z + 1 := by
  simp_rw [degree, ← card_singleton v]
  suffices G.neighborFinset z = (_op_g G v x y).neighborFinset z ∪ {v} by
    rw [this]
    refine card_union_of_disjoint <| disjoint_iff_inter_eq_empty.mpr ?_
    refine inter_singleton_of_notMem <| not_mem_neighborFinset_symm ?_
    simp only [_op_g_Nv, notMem_empty, not_false_eq_true]
  ext u
  constructor
  · intro huz
    if hueqv : u = v then
      simp only [union_singleton, hueqv, mem_insert, mem_neighborFinset, true_or]
    else
      refine mem_union_left _ ?_
      have hvnez : v ≠ z := by
        refine Adj.ne <| G.mem_neighborFinset .. |>.mp <| hNv ▸ ?_
        simp only [mem_insert, mem_singleton, or_true]
      exact mem_neighborFinset_deleteIncidencesOf_of_notMem_of_notMem_of_mem_neighborFinset
        (notMem_singleton.mpr hueqv) (notMem_singleton.mpr hvnez.symm)
        (le_fromEdgeSet_union' huz)
  · intro hu'
    rcases mem_union.mp hu' with huz | huv
    · have := mem_neighborFinset_of_deleteIncidencesOf_mem_neighborFinset huz
      rcases mem_fromEdgeSet_union_neighborFinset_iff |>.mp this with hu | hu
      · exact hu
      · simp only [Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
          Prod.swap_prod_mk, ne_eq, Ne.symm hxnez, Ne.symm hynez, false_and, false_or] at hu
    · refine mem_neighborFinset_symm <| (mem_singleton.mp huv) ▸ (by simp [hNv])

private lemma _eval_ok (G : SimpleGraph V) [DecidableRel G.Adj] (ABC : Tripartition V)
    [ABC.Decidable] {v x y z : V} (hG : G.support ⊆ ABC.toFinset)
    (hAv : ABC.A v) (hBx : ABC.B x) (hBy : ABC.B y) (hCz : ¬ABC.C z)
    (hNv : G.neighborFinset v = {x, y, z})
    (hdv : G.degree v = 3) (hdx : G.degree x = 3) (hdy : G.degree y = 3) :
    eval G ABC ≤ eval (_op_g G v x y) (ABC._op_t v x y z) + 1 := by
  rw [degree] at hdv
  obtain ⟨hxney, hxnez, hynez⟩ := pairwise_ne_of_triplet (hNv ▸ hdv)
  have Hne : v ≠ x ∧ v ≠ y ∧ v ≠ z := by
    suffices v ∉ G.neighborFinset v by
      simp only [hNv, mem_insert, mem_singleton, not_or] at this
      exact this
    exact G.notMem_neighborFinset_self _
  obtain ⟨hvnex, hvney, hvnez⟩ := Hne
  calc eval G ABC
    _ = ∑ w ∈ ABC.toFinset \ {v, x, y, z}, f G ABC w + ∑ w ∈ {v, x, y, z}, f G ABC w := by
      rw [eval]
      refine Eq.symm <| ?_
      refine sum_sdiff ?_
      refine fun u hu ↦ hG ?_
      if hu' : u = v then
        refine G.mem_support |>.mpr ⟨x, ?_⟩
        exact G.mem_neighborFinset .. |>.mp <| hu' ▸ hNv ▸ mem_insert_self ..
      else
      simp only [hu', mem_insert, mem_singleton, false_or] at hu
      rcases hu with h | h | h <;> {
        refine G.mem_support |>.mpr ⟨v, ?_⟩
        refine Adj.symm <| G.mem_neighborFinset .. |>.mp <| ?_
        simp only [h, hNv, mem_insert, mem_singleton, true_or, or_true]
      }
    _ = ∑ w ∈ ABC.toFinset \ {v, x, y, z}, f (_op_g G v x y) (_op_t ABC v x y z) w
        + ∑ w ∈ {v, x, y, z}, f G ABC w := by
      simp only [add_left_inj]
      refine sum_congr rfl ?_
      intro u hu
      obtain ⟨hunex, huney, hunez, hunev⟩ : u ≠ x ∧ u ≠ y ∧ u ≠ z ∧ u ≠ v := by
        simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hu
        grind
      rcases ABC.mem_toFinset.mpr <| mem_sdiff.mp hu |>.1 with hA | hB | hC
      · have hA' : (_op_t ABC v x y z).A u := by refine ⟨⟨hA, ?_⟩, ?_⟩ <;> grind
        simp only [f, hA, ↓reduceDIte, hA']
        exact congrArg _ <| _degG_eq_degG'_out_Nv (mem_sdiff.mp hu |>.2) hNv
      · have hB' : (_op_t ABC v x y z).B u :=
          B_of_demote_finset_notin _ (by grind) ⟨hB, not_iff_not.mpr mem_singleton |>.mpr hunev⟩
        simp only [f, hB, hB', not_A_of_B, ↓reduceDIte]
        exact congrArg _ <| _degG_eq_degG'_out_Nv (mem_sdiff.mp hu |>.2) hNv
      · have hC' : (_op_t ABC v x y z).C u :=
          C_of_demote_finset_notin _ ⟨hC, not_iff_not.mpr mem_singleton |>.mpr hunev⟩
        simp only [f, hC, hC', not_A_of_C, not_B_of_C, ↓reduceDIte]
        exact congrArg _ <| _degG_eq_degG'_out_Nv (mem_sdiff.mp hu |>.2) hNv
    _ = ∑ w ∈ (_op_t ABC v x y z).toFinset \ {x, y, z}, f (_op_g G v x y) (_op_t ABC v x y z) w
        + ∑ w ∈ {v, x, y, z}, f G ABC w := by
      simp only [add_left_inj]
      refine sum_congr ?_ (fun _ _ ↦ rfl)
      simp only [_op_t, ← demote_finset_toFinset_eq, sdiff_toFinset]
      grind
    _ = ∑ w ∈ (_op_t ABC v x y z).toFinset \ {x, y, z}, f (_op_g G v x y) (_op_t ABC v x y z) w
         + ∑ w ∈ {x, y, z}, f (_op_g G v x y) (_op_t ABC v x y z) w
         - ∑ w ∈ {x, y, z}, f (_op_g G v x y) (_op_t ABC v x y z) w
        + ∑ w ∈ {v, x, y, z}, f G ABC w := by
      lia
    _ = ∑ w ∈ (_op_t ABC v x y z).toFinset, f (_op_g G v x y) (_op_t ABC v x y z) w
        - ∑ w ∈ {x, y, z}, f (_op_g G v x y) (_op_t ABC v x y z) w
        + ∑ w ∈ {v, x, y, z}, f G ABC w := by
      simp only [add_left_inj, sub_left_inj]
      refine sum_sdiff ?_
      intro u hu
      simp only [_op_t, ← demote_finset_toFinset_eq, sdiff_toFinset]
      simp only [mem_insert, mem_singleton] at hu
      rcases hu with h | h | h <;> {
        refine mem_sdiff.mpr ⟨?_, ?_⟩
        · refine hG <| G.mem_support.mpr ⟨v, Adj.symm <| G.mem_neighborFinset .. |>.mp ?_⟩
          simp only [hNv, h, mem_insert, mem_singleton, true_or, or_true]
        · simp only [mem_singleton]
          refine Adj.ne <| Adj.symm <| G.mem_neighborFinset .. |>.mp ?_
          simp [hNv, h]
      }
    _ = ∑ w ∈ (_op_t ABC v x y z).toFinset, f (_op_g G v x y) (_op_t ABC v x y z) w
        + (∑ w ∈ {v, x, y, z}, f G ABC w
        - ∑ w ∈ {x, y, z}, f (_op_g G v x y) (_op_t ABC v x y z) w) := by
      lia
  refine add_le_add_right ?_ _
  calc ∑ w ∈ {v, x, y, z}, f G ABC w - ∑ w ∈ {x, y, z}, f (_op_g G v x y) (_op_t ABC v x y z) w
    _ = f G ABC v + f G ABC x + f G ABC y + f G ABC z
        - f (_op_g G v x y) (_op_t ABC v x y z) x
        - f (_op_g G v x y) (_op_t ABC v x y z) y
        - f (_op_g G v x y) (_op_t ABC v x y z) z := by
      grind
    _ = 7 / 6 + f G ABC z
        - f (_op_g G v x y) (_op_t ABC v x y z) x
        - f (_op_g G v x y) (_op_t ABC v x y z) y
        - f (_op_g G v x y) (_op_t ABC v x y z) z := by
      simp only [sub_left_inj, add_left_inj, fA3 hAv hdv, fB3 hBx hdx, fB3 hBy hdy]
      linarith
    _ ≤ 7 / 6 + f G ABC z
        - f (_op_g G v x y) (_op_t ABC v x y z) x
        - 1 / 6
        - f (_op_g G v x y) (_op_t ABC v x y z) z := by
      refine sub_le_sub_right ?_ _
      refine sub_le_sub_left ?_ _
      have hCy' : (_op_t ABC v x y z).C y := by
        refine demote_finset_from_B _ ?_ ?_
        · exact ⟨hBy, by simp only [mem_singleton, Ne.symm hvney, not_false_eq_true]⟩
        · simp only [mem_insert, mem_singleton, true_or, or_true]
      simp only [f, hCy', not_A_of_C, not_B_of_C, ↓reduceDIte]
      suffices (_op_g G v x y).degree y ≤ 3 by
        have H : fC 3 = 1 / 6 := by grind only
        exact H ▸ fC_decreasing this
      refine le_trans (_op_g_degy G hNv hxney) (le_of_eq hdy)
    _ ≤ 7 / 6 + f G ABC z
        - 1 / 6
        - 1 / 6
        - f (_op_g G v x y) (_op_t ABC v x y z) z := by
      refine sub_le_sub_right ?_ _
      refine sub_le_sub_right ?_ _
      refine sub_le_sub_left ?_ _
      have hCx' : (_op_t ABC v x y z).C x := by
        refine demote_finset_from_B (ABC \ {v}) ?_ ?_
        · exact ⟨hBx, by simp only [mem_singleton, Ne.symm hvnex, not_false_eq_true]⟩
        · simp only [mem_insert, mem_singleton, true_or]
      simp only [f, hCx', not_A_of_C, not_B_of_C, ↓reduceDIte]
      suffices (_op_g G v x y).degree x ≤ 3 by
        have H : fC 3 = 1 / 6 := by grind only
        exact H ▸ fC_decreasing this
      refine le_trans (_op_g_degx G hNv hxney) (le_of_eq hdx)
    _ ≤ 5 / 6 + f G ABC z
        - f (_op_g G v x y) (_op_t ABC v x y z) z := by
      linarith
  suffices f G ABC z - f (_op_g G v x y) (ABC._op_t v x y z) z ≤ 1 / 6 by
    linarith
  have Hz : z ∈ ({x, y, z} : Finset _) := by simp only [mem_insert, mem_singleton, or_true]
  have H : f (_op_g G v x y) (ABC._op_t v x y z) z
      = f (_op_g G v x y) (ABC.demote_finset {x, y, z}) z := by
    simp only [_op_t]
    have hz : ABC.A z ∨ ABC.B z := by
      suffices z ∈ ABC by grind [ABC.mem_iff]
      refine ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨v, ?_⟩
      refine Adj.symm <| G.mem_neighborFinset .. |>.mp (hNv ▸ Hz)
    rcases hz with hz | hz
    · have hBz' : ABC.demote_finset {x, y, z} |>.B z := Or.inr ⟨hz, Hz⟩
      have hBz'' : (ABC \ {v}).demote_finset {x, y, z} |>.B z := by
        refine Or.inr ⟨⟨hz, ?_⟩, Hz⟩
        simp [Ne.symm, hvnez]
      simp only [f, hBz', hBz'', not_A_of_B, ↓reduceDIte]
    · have hCz' : ABC.demote_finset {x, y, z} |>.C z := Or.inr ⟨hz, Hz⟩
      have hCz'' : (ABC \ {v}).demote_finset {x, y, z} |>.C z := by
        refine Or.inr ⟨⟨hz, ?_⟩, Hz⟩
        simp [Ne.symm, hvnez]
      simp only [f, hCz', hCz'', not_A_of_C, not_B_of_C]
  rw [H]
  exact Claim4 (mem_def.mpr Hz) (ge_of_eq <| _degGz_eq_degG'z_plusone hNv hxnez hynez)

lemma _forest {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V}
    {v x y z : V} {s : Finset V}
    (hNv : G.neighborFinset v = {x, y, z}) (hdv : G.degree v = 3) (hBx : ABC.B x) (hBy : ABC.B y)
    (hsf : (_op_g G v x y).InducesForest s) (hxy_not_both_in_s : ¬{x, y} ⊆ s) (hvnotins : v ∉ s)
    (hsresp : respects s (_op_g G v x y) (ABC._op_t v x y z)) :
    G.InducesForest (s ∪ {v}) := by
  rw [degree] at hdv
  obtain ⟨hxney, hxnez, hynez⟩ := pairwise_ne_of_triplet (hNv ▸ hdv)
  obtain ⟨hvx, hvy, hvz⟩ : G.Adj v x ∧ G.Adj v y ∧ G.Adj v z := by
    refine ⟨?_, ?_, ?_⟩ <;> exact G.mem_neighborFinset .. |>.mp <| by simp [hNv]
  simp only [_op_g] at hsf
  intro t ht htne
  if hvt : v ∈ t then
    if hinter : {x, y} ∩ t = ∅ then
      refine ⟨v, hvt, ?_⟩
      rw [← card_singleton z]
      refine card_le_card ?_
      intro u
      simp only [hNv, mem_inter, mem_insert, mem_singleton, and_imp]
      intro hu hut
      rw [inter_comm] at hinter
      rcases hu with hu | hu | hu
      · refine (ne_of_mem_of_not_mem hut ?_) hu |>.elim
        refine notMem_of_empty_inter_of_mem hinter <| by simp
      · refine (ne_of_mem_of_not_mem hut ?_) hu |>.elim
        refine notMem_of_empty_inter_of_mem hinter <| by simp
      · exact hu
    else
      obtain ⟨u, hu⟩ := nonempty_def.mp <| nonempty_iff_ne_empty.mpr hinter
      refine ⟨u, mem_inter.mp hu |>.2, ?_⟩
      refine le_trans (degree_in_mono ht) ?_
      refine le_trans degree_in_union_le ?_
      simp only [card_singleton, add_le_iff_nonpos_left]
      have hobj := by
        refine hsresp u (by grind [Adj.ne]) |>.2.2 ?_
        have H : u = x ∨ u = y := by grind
        rcases H with H | H <;> {
          rw [H]
          refine _op_t_C ABC ?_ hxney hxnez hynez ?_ ?_
          · simp [hvx.ne', hvy.ne']
          · simp only [mem_insert, mem_singleton, true_or, or_true]
          · simp only [hBx, hBy]
        }
      refine le_of_le_of_eq ?_ hobj
      refine card_le_card ?_
      intro w hw
      simp only [mem_inter] at hw ⊢
      refine ⟨?_, hw.2⟩
      have hw' : w ∉ ({v} : Finset _) := by grind only [= mem_singleton]
      have hu' : u ∉ ({v} : Finset _) := by
        simp only [mem_inter, mem_insert, mem_singleton] at hu
        exact notMem_singleton.mpr <| hu.1.elim (fun hu ↦ hu ▸ hvx.ne') (fun hu ↦ hu ▸ hvy.ne')
      refine mem_neighborFinset .. |>.mpr <| ?_
      simp only [_op_g]
      refine deleteIncidencesOf_adj_iff_of_notMem hu' hw' |>.mp ?_
      refine mem_neighborFinset .. |>.mp <| ?_
      refine mem_fromEdgeSet_union_neighborFinset_iff.mpr <| Or.inl hw.1
  else
    obtain ⟨u, hu, hudeg⟩ := hsf t (by grind) htne
    refine ⟨u, hu, ?_⟩
    refine le_trans (card_le_card ?_) hudeg
    intro w hw
    simp only [mem_inter, mem_neighborFinset] at hw ⊢
    refine ⟨?_, hw.2⟩
    refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ ?_
    · exact notMem_singleton.mpr <| ne_of_mem_of_not_mem hu hvt
    · exact notMem_singleton.mpr <| ne_of_mem_of_not_mem hw.2 hvt
    · exact le_fromEdgeSet_union hw.1

private lemma _respects {G : SimpleGraph V} [DecidableRel G.Adj]
    {ABC : Tripartition V} [ABC.Decidable] {s : Finset V} {v x y z : V} (hAv : ABC.A v)
    (hdv : #(G.neighborFinset v) = 3) (hNv : G.neighborFinset v = {x, y, z})
    (hBx : ABC.B x) (hBy : ABC.B y) (hCz : ¬ABC.C z) (hvz : G.Adj v z)
    (hs : s ⊆ (ABC._op_t v x y z).toFinset) (hxy_not_both_in_s : ¬{x, y} ⊆ s)
    (hvnotins : v ∉ s) (hsresp : respects s (_op_g G v x y) (ABC._op_t v x y z)) :
    respects (s ∪ {v}) G ABC := by
  obtain ⟨hxney, hxnez, hynez⟩ := pairwise_ne_of_triplet (hNv ▸ hdv)
  intro w hw
  simp only [union_singleton, mem_insert] at hw
  rcases hw with hw | hw
  · subst hw
    simp only [hAv, not_B_of_A, not_C_of_A, IsEmpty.forall_iff, and_true, forall_const]
    simp only [degree_in, union_singleton, mem_neighborFinset, SimpleGraph.irrefl,
      not_false_eq_true, inter_insert_of_notMem]
    suffices G.neighborFinset w ∩ s ⊂ G.neighborFinset w by
      have := hdv ▸ card_lt_card this
      exact Nat.le_of_lt_succ this
    refine (ssubset_iff_of_subset inter_subset_left).mpr ?_
    if hxs : x ∈ s then
      have hy : y ∈ G.neighborFinset w := by
        simp only [hNv, mem_insert, mem_singleton, true_or, or_true]
      refine ⟨y, ?_⟩
      simp only [hy, true_and, mem_inter]
      exact pair_subset_of_mem_of_mem hxs |>.mt hxy_not_both_in_s
    else
      have hx : x ∈ G.neighborFinset w := by
        simp only [hNv, mem_insert, mem_singleton, true_or]
      refine ⟨x, ?_⟩
      simp only [hx, true_and, mem_inter, hxs, not_false_eq_true]
  · if hvw : w ∈ G.neighborFinset v then
      have hwABC : w ∈ ABC := by
        have hobj := hs hw
        simp only [_op_t, ← demote_finset_toFinset_eq, sdiff_toFinset, mem_sdiff] at hobj
        exact ABC.mem_toFinset.mpr hobj.1
      obtain ⟨h₁, h₂, h₃⟩ := hsresp w hw
      have hdeg : G.degree_in (s ∪ {v}) w ≤ (_op_g G v x y).degree_in s w + 1 := by
        have H : G.neighborFinset w ∩ (s ∪ {v}) ⊆ (_op_g G v x y).neighborFinset w ∩ s ∪ {v} := by
          intro u hu
          refine mem_union.mpr ?_
          if huv : u = v then
            simp only [mem_inter, mem_neighborFinset, mem_singleton, or_true, huv]
          else
            simp only [mem_inter, mem_union] at hu ⊢
            obtain ⟨hu, hu'⟩ := hu
            rcases hu' with hu' | hu'
            · simp only [hu', and_true, mem_singleton, huv, or_false]
              exact mem_neighborFinset_deleteIncidencesOf_of_notMem_of_notMem_of_mem_neighborFinset
                (notMem_singleton.mpr huv)
                (notMem_singleton.mpr <| ne_of_mem_of_not_mem hvw (G.notMem_neighborFinset_self _))
                (le_fromEdgeSet_union' hu)
            · simp only [mem_singleton, huv] at hu'
        rw [← card_singleton v]
        refine le_trans (card_le_card H) (le_of_eq ?_)
        refine card_union_of_disjoint <| disjoint_singleton_right.mpr <| mem_inter.mp.mt ?_
        simp only [mem_neighborFinset, hvnotins, and_false, not_false_eq_true]
      refine ⟨?_, ?_, ?_⟩
      · intro hAw
        have hw : w = z := by grind only [= mem_insert, not_A_of_B, = mem_singleton]
        exact le_trans hdeg
          <| Nat.succ_le_succ <| h₂ <| _op_t_B ABC (hw ▸ hvz.ne') hxney hxnez hynez (hNv ▸ hvw) hAw
      · intro hBw
        refine le_trans hdeg ?_
        simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero]
        exact h₃ <| _op_t_C ABC (by grind) hxney hxnez hynez (hNv ▸ hvw) hBw
      · exact fun hCw ↦ by grind only [= subset_iff, = mem_insert, not_C_of_B, = mem_singleton]
    else
      have hwABC : w ∈ ABC.toFinset := by
        let hobj := hs hw
        simp only [_op_t, ← demote_finset_toFinset_eq, sdiff_toFinset] at hobj
        exact mem_sdiff.mp hobj |>.1
      rw [degree_in_union_eq <| singleton_inter_of_notMem <| mem_neighborFinset_symm.mt hvw]
      have Hw : w ∉ ({v} : Finset _) :=
        notMem_singleton.mpr <| ne_of_mem_of_not_mem hw hvnotins
      have hdegree_in : G.degree_in s w ≤ (_op_g G v x y).degree_in s w := by
        refine card_le_card ?_
        intro u
        simp only [mem_inter]
        refine fun ⟨hu, hu'⟩ ↦ ⟨?_, hu'⟩
        exact mem_neighborFinset_deleteIncidencesOf_of_notMem_of_notMem_of_mem_neighborFinset
          (notMem_singleton.mpr <| ne_of_mem_of_not_mem hu' hvnotins) Hw
          (le_fromEdgeSet_union' hu)
      rcases ABC.mem_iff.mp <| ABC.mem_toFinset.mpr hwABC with h | h | h
      · simp only [h, forall_const, not_B_of_A, IsEmpty.forall_iff,
          not_C_of_A, card_eq_zero, and_self, and_true, ge_iff_le]
        have hA' : (_op_t ABC v x y z).A w := A_of_demote_finset_notin _ (hNv ▸ hvw) ⟨h, Hw⟩
        exact le_trans hdegree_in (hsresp w hw |>.1 hA')
      · simp only [h, not_A_of_B, IsEmpty.forall_iff, forall_const, not_C_of_B, card_eq_zero,
          and_true, true_and, ge_iff_le]
        have hB' : (_op_t ABC v x y z).B w := B_of_demote_finset_notin _ (hNv ▸ hvw) ⟨h, Hw⟩
        refine le_trans hdegree_in (hsresp w hw |>.2.1 hB')
      · simp only [h, not_A_of_C, IsEmpty.forall_iff, not_B_of_C, forall_const, true_and]
        have hC' : (_op_t ABC v x y z).C w := C_of_demote_finset_notin _ ⟨h, Hw⟩
        exact le_antisymm (le_trans hdegree_in (le_of_eq <| hsresp w hw |>.2.2 hC')) (zero_le _)

lemma Claim11 {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {v : V} (hAv : ABC.A v) (hdv : G.degree v = 3)
    {x y z : V} (hNv : G.neighborFinset v = {x, y, z}) (hBx : ABC.B x) (hBy : ABC.B y)
    (hdx : G.degree x = 3) (hdy : G.degree y = 3)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  rw [degree] at hdv
  obtain ⟨hxney, hxnez, hynez⟩ := pairwise_ne_of_triplet (hNv ▸ hdv)
  obtain ⟨hvx, hvy, hvz⟩ : G.Adj v x ∧ G.Adj v y ∧ G.Adj v z := by
    refine ⟨?_, ?_, ?_⟩ <;> exact G.mem_neighborFinset .. |>.mp <| by simp [hNv]
  have hvABC : v ∈ ABC := by simp only [mem_iff, hAv, true_or]
  if hfz : f G ABC z ≤ 1 / 6 then
    exact Corollary1 hG hvz.symm ih <| le_of_le_of_eq hfz <| symm <| γA3 hAv hdv
  else if hCz : ABC.C z then
    have hdz : ¬1 ≤ G.degree z := fC_le_16_if_1_le_deg hCz |>.mt hfz
    have _ : 0 < G.degree z := G.degree_pos_iff_exists_adj _|>.mpr ⟨v, hvz.symm⟩
    contradiction
  else
    obtain ⟨s, hs, hsf, hsresp, hscard⟩ := by
      refine ih (_op_g G v x y) (_op_t ABC v x y z) ?_ ?_
      · intro u hu
        obtain ⟨w, hw⟩ := mem_support _ |>.mp hu
        simp only [_op_t, ← demote_finset_toFinset_eq, SetLike.mem_coe, sdiff_toFinset]
        rcases adj_fromEdgeSet_union_iff.mp <| adj_of_deleteIncidencesOf_adj hw with hu' | hu'
        · refine mem_sdiff.mpr ⟨?_, notMem_of_mem_support_deleteIncidencesOf <| hu⟩
          refine mem_def.mpr <| hG <| G.mem_support.mp ⟨_, hu'⟩
        · rcases eq_or_eq_of_eq_Sym2 <| mem_singleton.mp <| mem_singleton.mpr hu'.1 with hu' | hu'
          · refine mem_sdiff.mpr ⟨?_, ?_⟩
            · exact mem_of_subset_of_adj hG (hu' ▸ hvx)
            · simp only [mem_singleton, hu' ▸ hvx.ne', not_false_eq_true]
          · refine mem_sdiff.mpr ⟨?_, ?_⟩
            · refine mem_of_subset_of_adj hG (hu' ▸ hvy)
            · simp only [mem_singleton, hu' ▸ hvy.ne', not_false_eq_true]
      · simp only [_op_t, ← card_demote_finset_eq_card]
        refine sdiff_card ABC <| nonempty_iff_ne_empty.mp <| nonempty_def.mpr ⟨v, ?_⟩
        refine mem_inter.mpr ⟨?_, ?_⟩
        · exact mem_singleton.mpr rfl
        · exact ABC.mem_toFinset.mp hvABC
    have hvnotins : v ∉ s := by
      intro hv
      simp only [_op_t, ← demote_finset_toFinset_eq, sdiff_toFinset] at hs
      let hobj := mem_sdiff.mp (hs hv) |>.2
      simp only [mem_singleton, not_true_eq_false] at hobj
    have hxy_not_both_in_s : ¬{x, y} ⊆ s := by
      intro this
      have hobj : 0 < (_op_g G v x y).degree_in s x := by
        suffices ((_op_g G v x y).neighborFinset x ∩ s).Nonempty by
          simp only [degree_in, card_pos, this]
        refine nonempty_def.mpr ⟨y, mem_inter.mpr ⟨?_, ?_⟩⟩
        · refine mem_neighborFinset_deleteIncidencesOf_of_notMem_of_notMem_of_mem_neighborFinset
            (notMem_singleton.mpr <| ne_of_mem_of_not_mem (this <| by simp) hvnotins)
            (notMem_singleton.mpr <| ne_of_mem_of_not_mem (this <| by simp) hvnotins)
            ?_
          refine mem_neighborFinset .. |>.mpr <| fromEdgeSet_adj _ |>.mpr ⟨?_, hxney⟩
          exact Set.mem_union_right _ <| Set.mem_singleton _
        · exact this <| by simp only [mem_insert, mem_singleton, or_true]
      refine (ne_of_lt hobj) <| symm ?_
      refine le_antisymm ?_ (zero_le _)
      refine le_of_le_of_eq (le_refl _) (hsresp x ?_ |>.2.2 ?_)
      · exact this <| mem_insert_self ..
      · simp only [_op_t]
        refine _op_t_C ABC hvx.ne' hxney hxnez hynez ?_ hBx
        simp only [mem_insert, mem_singleton, true_or]
    refine ⟨s ∪ {v}, ?_, ?_, ?_, ?_⟩
    · intro u hu
      simp only [union_singleton, mem_insert] at hu
      rcases hu with hu | hu
      · exact ABC.mem_toFinset.mp <| hu ▸ hvABC
      · exact _op_t_toFinset_subset <| hs hu
    · exact _forest hNv hdv hBx hBy hsf hxy_not_both_in_s hvnotins hsresp
    · exact _respects hAv hdv hNv hBx hBy hCz  hvz hs hxy_not_both_in_s hvnotins hsresp
    · refine le_trans (_eval_ok G ABC hG hAv hBx hBy hCz hNv hdv hdx hdy) ?_
      calc eval (_op_g G v x y) (ABC._op_t v x y z) + 1
        _ ≤ #s + 1 := add_le_add hscard (le_refl _)
        _ = #(s ∪ {v}) := by
          rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_inj, ← card_singleton v]
          exact Eq.symm <| card_union_of_disjoint <| disjoint_singleton_right.mpr hvnotins

end Tripartition
end ABC
end CaroWeiType
