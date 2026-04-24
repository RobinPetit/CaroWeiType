import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim1
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim4

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

@[reducible]
private def _op_g {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v x y : Fin n) :
    SimpleGraph (Fin n) :=
  (fromEdgeSet <| G.edgeSet ∪ {s(x, y)}).deleteIncidenceSet v

private lemma _op_g_Nv {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v x y : Fin n) :
    (_op_g G v x y).neighborFinset v = ∅ := by
  ext u
  simp only [mem_neighborFinset, notMem_empty, iff_false]
  exact deleteIncidenceSet_notAdj

private lemma _op_g_Nxy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {v w x y z : Fin n}
    (hNv : G.neighborFinset v = {x, y, z}) (hw : w ∈ ({x, y} : Finset _))
    (hxy : x ≠ y) :
    (_op_g G v x y).neighborFinset w = (G.neighborFinset w ∪ {x, y}) \ {v, w} := by
  ext u
  simp only [deleteIncidenceSet, incidenceSet, mem_neighborFinset, Set.union_singleton,
    edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff, Sym2.mem_diagSet,
    deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, sdiff_adj, fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff',
    Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, ne_eq, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq,
    Sym2.mem_iff, not_and, Decidable.not_not, and_imp, union_insert, union_singleton, mem_sdiff,
    mem_insert, mem_singleton, not_or]
  simp only [mem_insert, mem_singleton] at hw
  have hxv : x ≠ v :=
    ne_of_mem_neighborFinset G <| by simp only [hNv, mem_insert, mem_singleton, true_or]
  have hyv : y ≠ v :=
    ne_of_mem_neighborFinset G <| by simp only [hNv, mem_insert, mem_singleton, true_or, or_true]
  rcases hw with hw | hw <;> {
    constructor
    · exact fun ⟨⟨_, _⟩, _⟩ ↦ by grind only
    · intro ⟨h₁, ⟨huv, huw⟩⟩
      refine ⟨⟨by grind only, Ne.symm huw⟩, ?_⟩
      rcases h₁ with h | h | h
      · simp only [ne_eq, not_false_eq_true, Ne.symm, and_false, and_true, or_self, hw, ne_eq, hxy,
          Ne.symm, SimpleGraph.irrefl, not_true_eq_false, implies_true, h, hyv, hxv, and_self,
          not_false_eq_true, or_true, true_or, or_self, imp_self]
      · simp only [ne_eq, not_false_eq_true, Ne.symm, and_false, and_true, or_self, hw, ne_eq, hxy,
          Ne.symm, SimpleGraph.irrefl, not_true_eq_false, implies_true, h, hyv, hxv, and_self,
          not_false_eq_true, true_or, or_self, imp_self]
      · simp only [h, or_true, ne_eq, huw, not_false_eq_true, Ne.symm, huv, or_false, imp_false,
          forall_const]
        simp only [hw, Ne.symm hxv, Ne.symm hyv, not_false_eq_true]
  }

private lemma _op_g_Nx {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {v x y z : Fin n}
    (hNv : G.neighborFinset v = {x, y, z}) (hxy : x ≠ y) :
    (_op_g G v x y).neighborFinset x = (G.neighborFinset x ∪ {y}) \ {v} := by
  rw [_op_g_Nxy G hNv (mem_insert_self x _) hxy]
  ext u
  simp only [union_insert, union_singleton, mem_sdiff, mem_insert, mem_neighborFinset,
    mem_singleton, not_or]
  constructor
  · refine fun ⟨h, huv, hux⟩ ↦ ⟨?_, huv⟩
    simp only [hux, false_or] at h
    exact h
  · intro ⟨h, huv⟩
    exact ⟨Or.inr h, huv, by grind only [Adj.ne]⟩

private lemma _op_g_degx {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {v x y z : Fin n}
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
    _ ≤ #(G.neighborFinset x) := by lia

private lemma _op_g_Ny {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {v x y z : Fin n}
    (hNv : G.neighborFinset v = {x, y, z}) (hxy : x ≠ y) :
    (_op_g G v x y).neighborFinset y = (G.neighborFinset y ∪ {x}) \ {v} := by
  have hy : y ∈ ({x, y} : Finset _) := by
    simp only [mem_insert, mem_singleton, or_true]
  rw [_op_g_Nxy G hNv hy hxy]
  ext u
  simp only [union_insert, union_singleton, mem_sdiff, mem_insert, mem_neighborFinset,
    mem_singleton, not_or]
  constructor
  · refine fun ⟨h, huv, hux⟩ ↦ ⟨?_, huv⟩
    simp only [hux, false_or] at h
    exact h
  · intro ⟨h, huv⟩
    refine ⟨by grind, huv, by grind only [Adj.ne]⟩

private lemma _op_g_degy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {v x y z : Fin n}
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
    _ ≤ #(G.neighborFinset y) := by lia

@[reducible]
private noncomputable def _op_t {n : ℕ} (ABC : Tripartition n) (v x y z : Fin n) : Tripartition n :=
  ABC \ {v} |>.demote_finset {x, y, z}

private lemma _op_t_toFinset_subset {n : ℕ} (ABC : Tripartition n) (v x y z : Fin n) :
    (_op_t ABC v x y z).toFinset ⊆ ABC.toFinset := by
  intro u hu
  simp only [_op_t, ← demote_finset_toFinset_eq, sdiff_toFinset] at hu
  exact mem_sdiff.mp hu |>.1

private lemma _op_t_B {n : ℕ} (ABC : Tripartition n) {v w x y z : Fin n} (hwv : w ≠ v)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hw : w ∈ ({x, y, z} : Finset _)) :
    ABC.A w → (_op_t ABC v x y z).B w := by
  intro hAw
  simp only [mem_insert, mem_singleton] at hw
  rcases hw with h | h | h <;> {
    subst h
    refine Or.inr ⟨⟨hAw, not_iff_not.mpr mem_singleton |>.mpr hwv⟩, ?_⟩
    simp only [mem_insert, mem_singleton, true_or, or_true]
  }

private lemma _op_t_C {n : ℕ} (ABC : Tripartition n) {v w x y z : Fin n} (hwv : w ≠ v)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hw : w ∈ ({x, y, z} : Finset _)) :
    ABC.B w → (_op_t ABC v x y z).C w := by
  intro hBw
  simp only [mem_insert, mem_singleton] at hw
  rcases hw with h | h | h <;> {
    subst h
    refine Or.inr ⟨⟨hBw, not_iff_not.mpr mem_singleton |>.mpr hwv⟩, ?_⟩
    simp only [mem_insert, mem_singleton, true_or, or_true]
  }

private lemma _degG_eq_degG' {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v x y z : Fin n} {ABC : Tripartition n} (hu : u ∈ ABC.toFinset \ {v, x, y, z})
    (hNv : G.neighborFinset v = {x, y, z}) :
    G.degree u = (_op_g G v x y).degree u := by
  refine congrArg Finset.card ?_
  ext w
  simp only [mem_neighborFinset, deleteIncidenceSet, incidenceSet, Set.union_singleton,
    edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff, Sym2.mem_diagSet,
    deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, sdiff_adj, fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff',
    Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, ne_eq, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq,
    Sym2.mem_iff, not_and, Decidable.not_not, and_imp]
  constructor
  · intro huw
    simp only [huw, or_true, huw.ne, not_false_eq_true, and_self, imp_false, not_or, forall_const,
      true_and]
    constructor
    · intro heq
      let hobj := heq ▸ mem_sdiff.mp hu |>.2
      simp only [mem_insert, mem_singleton, true_or, not_true_eq_false] at hobj
    · intro heq
      let hin := hNv ▸ G.mem_neighborFinset .. |>.mpr <| Adj.symm <| heq ▸ huw
      grind
  · grind

private lemma _eval_ok {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    {v x y z : Fin n} (hG : G.support.toFinset ⊆ ABC.toFinset)
    (hAv : ABC.A v) (hBx : ABC.B x) (hBy : ABC.B y) (hCz : ¬ABC.C z)
    (hNv : G.neighborFinset v = {x, y, z})
    (hdv : G.degree v = 3) (hdx : G.degree x = 3) (hdy : G.degree y = 3) :
    eval G ABC ≤ eval (_op_g G v x y) (ABC._op_t v x y z) + 1 := by
  rw [degree] at hdv
  obtain ⟨hxney, hxnez, hynez⟩ := pairwise_ne_of_triplet (hNv ▸ hdv)
  have Hne : v ≠ x ∧ v ≠ y ∧ v ≠ z := by
    refine ⟨?_, ?_, ?_⟩ <;> {
      refine ne'_of_mem_neighborFinset G (hNv ▸ ?_)
      simp only [mem_insert, mem_singleton, true_or, or_true]
    }
  obtain ⟨hvnex, hvney, hvnez⟩ := Hne
  calc eval G ABC
    _ = ∑ w ∈ ABC.toFinset \ {v, x, y, z}, f G ABC w + ∑ w ∈ {v, x, y, z}, f G ABC w := by
      rw [eval]
      refine Eq.symm <| ?_
      refine sum_sdiff ?_
      intro u hu
      refine hG <| Set.mem_toFinset.mpr ?_
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
      have hunex : u ≠ x := by grind
      have huney : u ≠ y := by grind
      have hunez : u ≠ z := by grind
      have hunev : u ≠ v := by grind
      rcases ABC.coe_mem_toFinset.mpr <| mem_sdiff.mp hu |>.1 with hA | hB | hC
      · have hA' : (_op_t ABC v x y z).A u := by refine ⟨⟨hA, ?_⟩, ?_⟩ <;> grind
        simp only [f, hA, ↓reduceDIte, hA']
        exact congrArg _ <| _degG_eq_degG' hu hNv
      · have hB' : (_op_t ABC v x y z).B u :=
          B_of_demote_finset_notin _ (by grind) ⟨hB, not_iff_not.mpr mem_singleton |>.mpr hunev⟩
        simp only [f, hB, hB', not_A_of_B, ↓reduceDIte]
        exact congrArg _ <| _degG_eq_degG' hu hNv
      · have hC' : (_op_t ABC v x y z).C u :=
          C_of_demote_finset_notin _ ⟨hC, not_iff_not.mpr mem_singleton |>.mpr hunev⟩
        simp only [f, hC, hC', not_A_of_C, not_B_of_C, ↓reduceDIte]
        exact congrArg _ <| _degG_eq_degG' hu hNv
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
        · refine hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨v, ?_⟩
          refine Adj.symm <| G.mem_neighborFinset .. |>.mp ?_
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
      simp_rw [fA3 hAv hdv, fB3 hBx hdx, fB3 hBy hdy]
      linarith
    _ ≤ 7 / 6 + f G ABC z
        - f (_op_g G v x y) (_op_t ABC v x y z) x
        - 1 / 6
        - f (_op_g G v x y) (_op_t ABC v x y z) z := by
      refine sub_le_sub_right ?_ _
      refine sub_le_sub_left ?_ _
      have hCy' : (_op_t ABC v x y z).C y := by
        refine demote_finset_from_B (ABC \ {v}) ?_ ?_
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
      lia
  suffices f G ABC z - f (_op_g G v x y) (ABC._op_t v x y z) z ≤ 1 / 6 by
    linarith
  have Hz : z ∈ ({x, y, z} : Finset _) := by simp only [mem_insert, mem_singleton, or_true]
  have H : f (_op_g G v x y) (ABC._op_t v x y z) z
      = f (_op_g G v x y) (ABC.demote_finset {x, y, z}) z := by
    simp only [_op_t]
    have hz : ABC.A z ∨ ABC.B z := by
      suffices z ∈ ABC by grind [ABC.mem_iff]
      refine ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr ?_
      refine (mem_support G).mpr ⟨v, ?_⟩
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
  refine Claim4 ?_ ?_
  · simp only [mem_insert, mem_singleton, or_true]
  · refine ge_of_eq ?_
    simp_rw [degree, ← card_singleton v]
    suffices G.neighborFinset z = (_op_g G v x y).neighborFinset z ∪ {v} by
      rw [this]
      refine card_union_of_disjoint ?_
      refine disjoint_iff_inter_eq_empty.mpr ?_
      rw [inter_comm]
      ext u
      simp only [deleteIncidenceSet, incidenceSet, mem_neighborFinset, Set.union_singleton,
        edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff, Sym2.mem_diagSet,
        deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, sdiff_adj, fromEdgeSet_adj, Sym2.eq,
        Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, ne_eq, Set.mem_setOf_eq,
        Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, or_true, and_true, and_self_right, not_and,
        Decidable.not_not, Classical.not_imp, imp_self, singleton_inter_of_notMem, notMem_empty]
    ext u
    simp only [mem_neighborFinset, deleteIncidenceSet, incidenceSet, union_singleton, mem_insert,
      Set.union_singleton, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff, Sym2.mem_diagSet,
      deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, sdiff_adj, fromEdgeSet_adj, Sym2.eq,
      Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, ne_eq, Set.mem_setOf_eq,
      Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and, Decidable.not_not, and_imp, false_and,
      false_or, Ne.symm hxnez, Ne.symm hynez]
    constructor
    · intro hzu
      simp only [hzu, hzu.ne, not_false_eq_true, and_self, imp_false, not_or, forall_const,
        true_and]
      if huv : u = v then
        exact Or.inl huv
      else
        simp only [huv, Ne.symm huv, not_false_eq_true, and_true, false_or]
        refine Adj.ne <| (G.mem_neighborFinset ..).mp (hNv ▸ ?_)
        simp only [mem_insert, mem_singleton, or_true]
    · intro h
      rcases h with h | h
      · have hzv : G.Adj z v := by
          refine Adj.symm <| G.mem_neighborFinset .. |>.mp (hNv ▸ ?_)
          simp only [mem_insert, mem_singleton, or_true]
        exact h ▸ hzv
      · exact h.1.1

lemma Claim11 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) {v : Fin n} (hAv : ABC.A v) (hdv : G.degree v = 3)
    {x y z : Fin n} (hNv : G.neighborFinset v = {x, y, z}) (hBx : ABC.B x) (hBy : ABC.B y)
    (hdx : G.degree x = 3) (hdy : G.degree y = 3)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
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
      · intro u
        simp only [support, _op_g, deleteIncidenceSet, Set.union_singleton, incidenceSet,
          edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff, Sym2.mem_diagSet,
          deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, sdiff_adj, fromEdgeSet_adj, Prod.mk.eta,
          Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, ne_eq, Set.mem_setOf_eq,
          Sym2.isDiag_iff_proj_eq, not_and, Decidable.not_not, and_imp, Set.mem_toFinset,
          SetRel.mem_dom, Prod.mk.injEq, mem_edgeSet, Sym2.mem_iff, _op_t,
          ← demote_finset_toFinset_eq, toFinset_eq, mem_sdiff, mem_singleton, forall_exists_index]
        intro u' h₁ h₂ h₃
        simp only [h₁, h₂, not_false_eq_true, imp_false, not_or, forall_const] at h₃
        refine ⟨?_, Ne.symm h₃.1⟩
        refine hG <| Set.mem_toFinset.mpr <| ?_
        rcases h₁ with ⟨h | h⟩ | h
        · refine G.mem_support.mpr ⟨v, ?_⟩
          refine Adj.symm <| G.mem_neighborFinset .. |>.mp ?_
          simp only [hNv, h.1, mem_insert, mem_singleton, true_or]
        · refine G.mem_support.mpr ⟨v, ?_⟩
          refine Adj.symm <| G.mem_neighborFinset .. |>.mp ?_
          simp only [hNv, h.1, mem_insert, mem_singleton, true_or, or_true]
        · exact G.mem_support.mpr ⟨u', h⟩
      · simp only [_op_t, ← card_demote_finset_eq_card]
        refine sdiff_card ABC <| nonempty_iff_ne_empty.mp <| nonempty_def.mpr ⟨v, ?_⟩
        refine mem_inter.mpr ⟨?_, ?_⟩
        · exact mem_singleton.mpr rfl
        · exact ABC.coe_mem_toFinset.mp hvABC
    have hxy_not_both_in_s : ¬{x, y} ⊆ s := by
      intro this
      have hobj : 0 < (_op_g G v x y).degree_in s x := by
        suffices ((_op_g G v x y).neighborFinset x ∩ s).Nonempty by
          simp only [degree_in, card_pos, this]
        refine nonempty_def.mpr ⟨y, mem_inter.mpr ⟨?_, ?_⟩⟩
        · simp only [deleteIncidenceSet, incidenceSet, mem_neighborFinset, Set.union_singleton,
          edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff, Sym2.mem_diagSet,
          deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, sdiff_adj, fromEdgeSet_adj, mem_edgeSet,
          true_or, ne_eq, hxney, not_false_eq_true, and_self, Set.mem_setOf_eq,
          Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, hvx.ne, hvy.ne, or_self, and_false, and_true]
        · exact this <| by simp only [mem_insert, mem_singleton, or_true]
      refine (ne_of_lt hobj) <| symm ?_
      refine le_antisymm ?_ (zero_le _)
      refine le_of_le_of_eq ?_ (hsresp x ?_ |>.2.2 ?_)
      · refine card_le_card ?_
        intro u
        simp only [deleteIncidenceSet, incidenceSet, mem_inter, mem_neighborFinset,
          Set.union_singleton, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff,
          Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, sdiff_adj,
          fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk,
          hxney, false_and, or_false, mem_edgeSet, ne_eq, Set.mem_setOf_eq,
          Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and, Decidable.not_not, and_imp]
        grind
      · exact this <| mem_insert_self ..
      · simp only [_op_t]
        refine _op_t_C ABC hvx.ne' hxney hxnez hynez ?_ hBx
        simp only [mem_insert, mem_singleton, true_or]
    have hvnotins : v ∉ s := by
      intro hv
      simp only [_op_t, ← demote_finset_toFinset_eq, sdiff_toFinset] at hs
      let hobj := mem_sdiff.mp (hs hv) |>.2
      simp only [mem_singleton, not_true_eq_false] at hobj
    refine ⟨s ∪ {v}, ?_, ?_, ?_, ?_⟩
    · intro u hu
      simp only [union_singleton, mem_insert] at hu
      rcases hu with hu | hu
      · exact ABC.coe_mem_toFinset.mp <| hu ▸ hvABC
      · exact _op_t_toFinset_subset ABC v x y z <| hs hu
    · intro t ht htne
      if hvt : v ∈ t then
        if hinter : {x, y} ∩ t = ∅ then
          refine ⟨v, hvt, by grind⟩
        else
          obtain ⟨u, hu⟩ := nonempty_def.mp <| nonempty_iff_ne_empty.mpr hinter
          refine ⟨u, mem_inter.mp hu |>.2, ?_⟩
          refine le_trans (degree_in_mono ht) ?_
          refine le_trans degree_in_union_le ?_
          simp only [card_singleton, add_le_iff_nonpos_left]
          let hobj := by
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
          intro w
          simp only [mem_inter, mem_neighborFinset, deleteIncidenceSet, incidenceSet,
            Set.union_singleton, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff,
            Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, sdiff_adj,
            fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet,
            ne_eq, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and,
            Decidable.not_not, and_imp]
          grind [Adj.ne]
      else
        obtain ⟨u, hu, hudeg⟩ := hsf t (by grind) htne
        refine ⟨u, hu, ?_⟩
        refine le_of_eq_of_le ?_ hudeg
        refine congrArg Finset.card ?_
        ext w
        simp only [mem_inter, mem_neighborFinset, deleteIncidenceSet, incidenceSet,
          Set.union_singleton, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff,
          Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, sdiff_adj, fromEdgeSet_adj,
          Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, ne_eq,
          Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and, Decidable.not_not,
          and_imp, and_congr_left_iff]
        grind [Adj.ne]
    · intro w hw
      simp only [union_singleton, mem_insert] at hw
      rcases hw with hw | hw
      · subst hw
        simp only [hAv, not_B_of_A, not_C_of_A, IsEmpty.forall_iff, and_true, forall_const]
        simp only [degree_in, union_singleton, mem_neighborFinset, SimpleGraph.irrefl,
          not_false_eq_true, inter_insert_of_notMem]
        by_contra
        have H' : #(G.neighborFinset w ∩ s) = 3 := by
          refine le_antisymm ?_ ?_
          · exact le_trans (card_le_card inter_subset_left) (le_of_eq hdv)
          · exact Nat.succ_le_of_lt <| not_le.mp this
        have H' : {x, y, z} = (G.neighborFinset w ∩ s) := by
          refine Eq.symm <| eq_of_subset_and_eq_card ?_ (by grind)
          exact hNv ▸ inter_subset_left
        grind
      · if hvw : w ∈ G.neighborFinset v then
          rw [hNv] at hvw
          have hwABC : w ∈ ABC := by
            refine ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ?_
            exact ⟨v, G.mem_neighborFinset .. |>.mp <| mem_neighborFinset_symm <| hNv ▸ hvw⟩
          obtain ⟨h₁, h₂, h₃⟩ := hsresp w hw
          have hdeg : G.degree_in (s ∪ {v}) w ≤ (_op_g G v x y).degree_in s w + 1 := by
            have H : G.neighborFinset w ∩ (s ∪ {v})
                ⊆ (_op_g G v x y).neighborFinset w ∩ s ∪ {v} := by
              intro u hu
              refine mem_union.mpr ?_
              if huv : u = v then
                simp only [mem_inter, mem_neighborFinset, mem_singleton, or_true, huv]
              else
                simp_rw [mem_inter] at hu
                rcases mem_union.mp <| hu.2 with hu' | hu'
                · simp only [huv, mem_singleton, or_false, mem_inter, hu', and_true]
                  let hwu := G.mem_neighborFinset .. |>.mp <| hu.1
                  simp only [deleteIncidenceSet, incidenceSet, mem_neighborFinset, and_self, hwu,
                    Set.union_singleton, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff,
                    Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, sdiff_adj, hwu.ne,
                    fromEdgeSet_adj, mem_edgeSet, or_true, ne_eq, not_false_eq_true, and_true,
                    Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, Ne.symm huv, or_false,
                    true_and]
                  grind only
                · simp only [mem_singleton, huv] at hu'
            rw [← card_singleton v]
            refine le_trans (card_le_card H) (le_of_eq ?_)
            refine card_union_of_disjoint ?_
            refine disjoint_singleton_right.mpr ?_
            refine mem_inter.mp.mt ?_
            simp only [mem_neighborFinset, not_and]
            have hnotadj : ¬(_op_g G v x y).Adj w v := by
              simp only [_op_g, deleteIncidenceSet, Set.union_singleton, incidenceSet,
                edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff, Sym2.mem_diagSet,
                deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, sdiff_adj, fromEdgeSet_adj, Sym2.eq,
                mem_edgeSet, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, or_true,
                and_true, and_self_right, not_and, Decidable.not_not, Classical.not_imp, imp_self]
            exact fun h ↦ (hnotadj h).elim
          refine ⟨?_, ?_, ?_⟩
          · intro hAw
            refine le_trans hdeg ?_
            haveI := by
              refine h₂ ?_
              have heq : w = z := by grind only [not_B_of_A, mem_insert, mem_singleton]
              subst heq
              refine _op_t_B ABC ?_ hxney hxnez hynez ?_ hAw
              · exact Adj.ne' <| G.mem_neighborFinset .. |>.mp
                  <| by simp only [hNv, mem_insert, mem_singleton, or_true]
              · simp only [mem_insert, mem_singleton, or_true]
            grind
          · intro hBw
            refine le_trans hdeg ?_
            simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero]
            exact h₃ <| _op_t_C ABC (by grind) hxney hxnez hynez hvw hBw
          · exact fun hCw ↦ by grind [not_C_of_B]
        else
          have hwABC : w ∈ ABC.toFinset := by
            let hobj := hs hw
            simp only [_op_t, ← demote_finset_toFinset_eq, sdiff_toFinset] at hobj
            exact mem_sdiff.mp hobj |>.1
          rw [degree_in_union_eq <| singleton_inter_of_notMem <| mem_neighborFinset_symm.mt hvw]
          have hdegree_in : G.degree_in s w ≤ (_op_g G v x y).degree_in s w := by
            refine card_le_card ?_
            intro u
            simp only [mem_inter, mem_neighborFinset, deleteIncidenceSet, incidenceSet,
              Set.union_singleton, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff,
              Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, sdiff_adj,
              fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
              mem_edgeSet, ne_eq, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff, not_and,
              Decidable.not_not, and_imp]
            grind [Adj.ne]
          have H : w ∉ ({v} : Finset _) := by
            exact not_iff_not.mpr mem_singleton |>.mpr <| Ne.symm <| neq_of_notin hw hvnotins
          rcases ABC.mem_iff.mp <| ABC.coe_mem_toFinset.mpr hwABC with h | h | h
          · simp only [h, forall_const, not_B_of_A, IsEmpty.forall_iff,
              not_C_of_A, card_eq_zero, and_self, and_true, ge_iff_le]
            have hA' : (_op_t ABC v x y z).A w := A_of_demote_finset_notin _ (hNv ▸ hvw) ⟨h, H⟩
            exact le_trans hdegree_in (hsresp w hw |>.1 hA')
          · simp only [h, not_A_of_B, IsEmpty.forall_iff, forall_const, not_C_of_B, card_eq_zero,
              and_true, true_and, ge_iff_le]
            have hB' : (_op_t ABC v x y z).B w := B_of_demote_finset_notin _ (hNv ▸ hvw) ⟨h, H⟩
            refine le_trans hdegree_in (hsresp w hw |>.2.1 hB')
          · simp only [h, not_A_of_C, IsEmpty.forall_iff, not_B_of_C, forall_const, true_and]
            have hC' : (_op_t ABC v x y z).C w := C_of_demote_finset_notin _ ⟨h, H⟩
            exact le_antisymm (le_trans hdegree_in (le_of_eq <| hsresp w hw |>.2.2 hC')) (zero_le _)
    · refine le_trans (_eval_ok G ABC hG hAv hBx hBy hCz hNv hdv hdx hdy) ?_
      calc eval (_op_g G v x y) (ABC._op_t v x y z) + 1
        _ ≤ #s + 1 := add_le_add hscard (le_refl _)
        _ = #(s ∪ {v}) := by
          rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_inj, ← card_singleton v]
          exact Eq.symm <| card_union_of_disjoint <| disjoint_singleton_right.mpr hvnotins

end Tripartition
end ABC
end CaroWeiType
