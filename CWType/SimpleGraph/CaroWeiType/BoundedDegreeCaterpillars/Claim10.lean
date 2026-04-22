import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim2
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim5
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim6
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim7
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim9

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

private lemma deg3_neighborhood {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {v x y : Fin n} (hx : G.Adj v x) (hy : G.Adj v y) (hne : x ≠ y) (hdv : G.degree v = 3) :
    ∃ z, G.neighborFinset v = {x, y, z} := by
  have : ∃ z, z ∈ G.neighborFinset v \ {x, y} := by
    refine nonempty_def.mp ?_
    refine sdiff_nonempty_of_card_lt_card ?_
    simp only [card_neighborFinset_eq_degree, hdv]
    refine lt_of_le_of_lt card_le_two <| lt_add_one _
  obtain ⟨z, hz⟩ := this
  refine ⟨z, ?_⟩
  refine Eq.symm <| eq_of_subset_and_eq_card ?_ ?_
  · grind [mem_neighborFinset]
  · simp only [card_neighborFinset_eq_degree, hdv]
    grind

@[simp, reducible]
private def _op_g {n : ℕ} (G : SimpleGraph (Fin n)) (v x y z : Fin n) : SimpleGraph (Fin n) :=
  (fromEdgeSet <| G.edgeSet ∪ {s(x, y), s(x, z), s(y, z)}).deleteIncidencesOf {v}

private lemma _op_g_adj_xy {n : ℕ} (G : SimpleGraph (Fin n)) (v x y z : Fin n)
    (hxy : x ≠ y) (hvx : v ≠ x) (hvy : v ≠ y) :
    (_op_g G v x y z).Adj x y := by
  simp [hxy, hvx, hvy, deleteIncidencesOf, deleteIncidenceSet, incidenceSet]

private lemma _op_g_adj_xz {n : ℕ} (G : SimpleGraph (Fin n)) (v x y z : Fin n)
    (hxz : x ≠ z) (hvx : v ≠ x) (hvz : v ≠ z) :
    (_op_g G v x y z).Adj x z := by
  simp [hxz, hvx, hvz, deleteIncidencesOf, deleteIncidenceSet, incidenceSet]

private lemma _op_g_adj_yz {n : ℕ} (G : SimpleGraph (Fin n)) (v x y z : Fin n)
    (hyz : y ≠ z) (hvy : v ≠ y) (hvz : v ≠ z) :
    (_op_g G v x y z).Adj y z := by
  simp [hyz, hvy, hvz, deleteIncidencesOf, deleteIncidenceSet, incidenceSet]

private lemma _op_g_deg_xyz {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v x y z : Fin n} (hx : G.Adj v x) (hy : G.Adj v y) (hz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hu : u ∈ ({x, y, z} : Finset _)) : (_op_g G v x y z).degree u ≤ G.degree u + 1 := by
  simp only [mem_insert, mem_singleton] at hu
  rcases hu with h | h | h <;> {
    suffices (_op_g G v x y z).neighborFinset u
        ⊆ G.neighborFinset u \ {v} ∪ ({x, y, z} \ {u} : Finset _) by
      refine le_trans (card_le_card this) ?_
      refine le_trans (card_union_le ..) ?_
      have hv : {v} ⊆ G.neighborFinset u := by simp [hx, hy, hz, Adj.symm, h]
      rw [card_sdiff_of_subset hv]
      rw [← degree, card_singleton]
      have _ : 0 < G.degree u :=
        G.degree_pos_iff_exists_adj _ |>.mpr ⟨v, by simp [Adj.symm, h, hx, hy, hz]⟩
      grind
    intro w
    simp only [Set.union_singleton, mem_union, mem_neighborFinset, or_false, mem_singleton,
      sdiff_adj, deleteIncidenceSet, and_imp, Prod.swap_prod_mk, iInf_iInf_eq_left, Sym2.mem_iff,
      fromEdgeSet_adj, le_sup_right, sdiff_le_iff, mem_insert, deleteIncidencesOf, Set.union_insert,
      or_self, Sym2.mem_diagSet, fromEdgeSet_sdiff, Prod.mk.injEq, false_and, Set.mem_diff,
      incidenceSet, Sym2.eq, not_and, hxy, hxz, hyz, deleteEdges_fromEdgeSet, Sym2.rel_iff', ne_eq,
      true_and, mem_edgeSet, Set.mem_insert_iff, Decidable.not_not, false_or, inf_of_le_right,
      edgeSet_fromEdgeSet, Sym2.isDiag_iff_proj_eq, mem_sdiff, Set.mem_setOf_eq, h]
    grind
  }

@[simp, reducible]
private noncomputable def _op_t {n : ℕ} (ABC : Tripartition n) (v x y z : Fin n) : Tripartition n :=
  (ABC \ {v}) |>.demote_finset {x, y, z}

private lemma A'_of_ne {n : ℕ} (ABC : Tripartition n) {u v x y z : Fin n}
    (hu : u ∉ ({v, x, y, z} : Finset _)) (hAu : ABC.A u) :
    (_op_t ABC v x y z).A u :=
  A_of_demote_finset_notin _ (by grind) ⟨hAu, by grind⟩

private lemma B'_of_ne {n : ℕ} (ABC : Tripartition n) {u v x y z : Fin n}
    (hu : u ∉ ({v, x, y, z} : Finset _)) (hBu : ABC.B u) :
    (_op_t ABC v x y z).B u :=
  B_of_demote_finset_notin _ (by grind) ⟨hBu, by grind⟩

private lemma C'_of_ne {n : ℕ} (ABC : Tripartition n) {u v x y z : Fin n}
    (hu : u ∉ ({v, x, y, z} : Finset _)) (hCu : ABC.C u) :
    (_op_t ABC v x y z).C u :=
  C_of_demote_finset_notin _ ⟨hCu, by grind⟩

private lemma B'_of_demote {n : ℕ} (ABC : Tripartition n) {u v x y z : Fin n} (huv : u ≠ v)
    (hu : u ∈ ({x, y, z} : Finset _)) (hAu : ABC.A u) : (_op_t ABC v x y z).B u := by
  simp only [mem_insert, mem_singleton] at hu
  have hA' : (ABC \ {v}).A u := ⟨hAu, by simp [huv]⟩
  rcases hu with hx | hy | hz <;> exact demote_finset_from_A _ hA' (by grind)

private lemma C'_of_demote {n : ℕ} (ABC : Tripartition n) {u v x y z : Fin n} (huv : u ≠ v)
    (hu : u ∈ ({x, y, z} : Finset _)) (hBu : ABC.B u) : (_op_t ABC v x y z).C u := by
  simp only [mem_insert, mem_singleton] at hu
  have hB' : (ABC \ {v}).B u := ⟨hBu, by simp [huv]⟩
  rcases hu with hx | hy | hz <;> exact demote_finset_from_B _ hB' (by grind)

private lemma pairwise_ne {n : ℕ} {x y z : Fin n} {s : Finset (Fin n)} (hs : s = {x, y, z})
    (hs' : #s = 3) : x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  refine ⟨?_, ?_, ?_⟩ <;> {
    intro heq; subst heq
    suffices 3 ≤ 2 by grind
    rw [← hs', hs]
    simp only [mem_insert, mem_singleton, true_or, or_true, insert_eq_of_mem, card_le_two]
  }

private lemma neighborFinset_eq_outside {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v x y z : Fin n} (hu : u ∉ ({v, x, y, z} : Finset _)) (hv : G.neighborFinset v = {x, y, z}) :
    G.neighborFinset u = (_op_g G v x y z).neighborFinset u := by
  ext w
  have H : G.Adj u w → w ≠ v := by
    intro huw heq
    subst heq
    haveI := hv ▸ G.mem_neighborFinset .. |>.mpr huw.symm
    grind
  simp only [mem_neighborFinset, deleteIncidencesOf, deleteIncidenceSet, incidenceSet,
    Set.union_insert, Set.union_singleton, mem_singleton, edgeSet_fromEdgeSet, Set.mem_diff,
    Set.mem_insert_iff, Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff,
    iInf_iInf_eq_left, sdiff_le_iff, le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj,
    Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, Set.mem_setOf_eq]
  grind [Adj.ne]

private lemma degree_in_eq_outside {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v x y z : Fin n} (hu : u ∉ ({v, x, y, z} : Finset _)) (hv : G.neighborFinset v = {x, y, z})
    (s : Finset (Fin n)) :
    G.degree_in s u = (_op_g G v x y z).degree_in s u := by
  refine congrArg Finset.card ?_
  rw [neighborFinset_eq_outside hu hv]

private lemma f_eq_outside {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {u v x y z : Fin n}
    (hu : u ∉ ({v, x, y, z} : Finset _)) (hv : G.neighborFinset v = {x, y, z}) :
    f G ABC u = f (_op_g G v x y z) ((ABC \ {v}).demote_finset {x, y, z}) u := by
  if huABC : u ∈ ABC then
    simp only [mem_iff] at huABC
    rcases huABC with hA | hB | hC
    · simp only [f, hA, ABC.A'_of_ne hu hA, ↓reduceDIte]
      exact congrArg (fA ∘ Finset.card) <| neighborFinset_eq_outside hu hv
    · simp only [f, not_A_of_B, hB, ABC.B'_of_ne hu hB, ↓reduceDIte]
      exact congrArg (fB ∘ Finset.card) <| neighborFinset_eq_outside hu hv
    · simp only [f, not_A_of_C, not_B_of_C, hC, ABC.C'_of_ne hu hC, ↓reduceDIte]
      exact congrArg (fC ∘ Finset.card) <| neighborFinset_eq_outside hu hv
  else
    have huABC' : u ∉ (ABC \ {v}).demote_finset {x, y, z} := by
      simp only [← mem_iff_mem_demote_tofinset, huABC, mem_sdiff_iff, false_and, not_false_eq_true]
    rw [← f_eq_zero_of_notMem _ huABC]
    rw [← f_eq_zero_of_notMem _ huABC']

private lemma _diff {a x : ℝ} (hx : 0 < x + 1) (hx' : 0 < x + 2) :
    a / (x + 1) - (a - 2 / 3) / (x + 2) = (2 / 3) / (x + 2) + a / ((x + 1) * (x + 2)) := by
  calc a / (x + 1) - (a - 2 / 3) / (x + 2)
    _ = (a * (x + 2)) / ((x + 1) * (x + 2)) - (a - 2 / 3) / (x + 2) := by
      simp only [sub_left_inj]
      exact Eq.symm <| mul_div_mul_right _ _ ((ne_of_lt hx').symm)
    _ = (a * (x + 2)) / ((x + 1) * (x + 2)) - ((a - 2 / 3) * (x + 1)) / ((x + 2) * (x + 1)) := by
      simp only [sub_right_inj]
      exact Eq.symm <| mul_div_mul_right _ _ ((ne_of_lt hx).symm)
  grind

private lemma diff_f_AB {d d' : ℕ} (hd : 3 ≤ d) (hdd' : d' ≤ d + 1) :
    fA d - fB d' ≤ 7 / 30 := by
  have four_le_d_plus_one : 4 ≤ (d : ℝ) + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    refine Nat.cast_le.mpr <| by simp [hd]
  have five_le_d_plus_two : 5 ≤ (d : ℝ) + 2 := by
    rw [← Nat.cast_two, ← Nat.cast_add]
    refine Nat.cast_le.mpr <| by simp [hd]
  calc fA d - fB d'
    _ ≤ fA d - fB (d + 1) := by
      refine sub_le_sub_left ?_ _
      refine fB_decreasing hdd'
    _ = 2 / (d + 1 : ℝ) - (4 / 3) / (d + 1 + 1 : ℝ) := by
      simp only [fA, fB]
      grind
    _ = 2 / (d + 1 : ℝ) - (2 - 2 / 3) / (d + 2 : ℝ) := by grind
    _ = (2 / 3) / (d + 2 : ℝ) + 2 / ((d + 1 : ℝ) * (d + 2 : ℝ)) := _diff add_one_pos add_two_pos
    _ ≤ (2 / 3) / 5 + 2 / (4 * 5) := by
      refine add_le_add ?_ ?_
      · refine (div_le_div_iff₀ add_two_pos (by grind)).mpr ?_
        simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_right₀]
        exact five_le_d_plus_two
      · refine (div_le_div_iff₀ (mul_pos add_one_pos add_two_pos) (by grind)).mpr ?_
        simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
        refine mul_le_mul_of_nonneg ?_ ?_ zero_le_four (le_of_lt add_two_pos)
        · exact four_le_d_plus_one
        · exact five_le_d_plus_two
  grind

private lemma diff_f_BC {d d' : ℕ} (hd : 3 ≤ d) (hdd' : d' ≤ d + 1) :
    fB d - fC d' ≤ 7 / 30 := by
  have four_le_d_plus_one : 4 ≤ (d : ℝ) + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    refine Nat.cast_le.mpr <| by simp [hd]
  have five_le_d_plus_two : 5 ≤ (d : ℝ) + 2 := by
    rw [← Nat.cast_two, ← Nat.cast_add]
    refine Nat.cast_le.mpr <| by simp [hd]
  calc fB d - fC d'
    _ ≤ fB d - fC (d + 1) := by
      refine sub_le_sub_left ?_ _
      refine fC_decreasing hdd'
    _ = (4 / 3) / (d + 1 : ℝ) - (2 / 3) / (d + 1 + 1 : ℝ) := by
      simp only [fB, fC]
      grind
    _ = (4 / 3) / (d + 1 : ℝ) - (4 / 3 - 2 / 3) / (d + 2 : ℝ) := by grind
    _ = (2 / 3) / (d + 2 : ℝ) + (4 / 3) / ((d + 1 : ℝ) * (d + 2 : ℝ)) :=
        _diff add_one_pos add_two_pos
    _ ≤ (2 / 3) / 5 + (4 / 3) / (4 * 5) := by
      refine add_le_add ?_ ?_
      · refine (div_le_div_iff₀ add_two_pos (by grind)).mpr ?_
        simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_right₀]
        exact five_le_d_plus_two
      · refine (div_le_div_iff₀ (mul_pos add_one_pos add_two_pos) (by grind)).mpr ?_
        simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_right₀]
        refine mul_le_mul_of_nonneg ?_ ?_ zero_le_four (le_of_lt add_two_pos)
        · exact four_le_d_plus_one
        · exact five_le_d_plus_two
  linarith

lemma Claim10 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) {v : Fin n} (hBv : ABC.B v) (hdv : G.degree v = 3)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    (∃ x y, x ≠ y ∧ G.Adj v x ∧ G.Adj v y ∧ ABC.B x ∧ ABC.B y ∧ G.degree x = 3 ∧ G.degree y = 3)
      → Objective G ABC := by
  intro ⟨x, y, hne, hvx, hvy, hBx, hBy, hdx, hdy⟩
  obtain ⟨z, hNv⟩ := deg3_neighborhood hvx hvy hne hdv
  obtain ⟨hxney, hxnez, hynez⟩ := pairwise_ne hNv hdv
  have hvz : G.Adj v z :=
    G.mem_neighborFinset .. |>.mp <| by simp only [hNv, mem_insert, mem_singleton, or_true]
  have hzABC : z ∈ ABC :=
    ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨v, hvz.symm⟩
  if hCz : ABC.C z then
    refine Corollary9 hG hBv hdv ih ⟨z, ?_, hCz⟩
    simp only [← mem_neighborFinset, hNv, mem_insert, mem_singleton, or_true]
  else if hdz : G.degree z ≤ 2 then
    if hdz : G.degree z ≤ 1 then
      refine Claim5 hG ih ⟨z, hzABC, hdz⟩
    else
      have hz : ABC.A z ∨ ABC.B z := by grind [mem_iff]
      rcases hz with hAz | hBz
      · exact Claim7 hG ih ⟨v, z, hdv, hBv, by grind, hAz, hvz⟩
      · exact Claim6 hG ih ⟨z, by grind, not_A_of_B hBz⟩
  else
    have hdz : 3 ≤ G.degree z := by grind
    obtain ⟨s, hs, hsf, hsresp, hscard⟩ := by
      refine ih (_op_g G v x y z) (_op_t ABC v x y z) ?_ ?_
      · intro u hu
        simp only [support, _op_g, deleteIncidencesOf, Set.union_insert, Set.union_singleton,
          mem_singleton, deleteIncidenceSet, incidenceSet, edgeSet_fromEdgeSet, Set.mem_diff,
          Set.mem_insert_iff, Sym2.mem_diagSet, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff,
          iInf_iInf_eq_left, sdiff_le_iff, le_sup_right, inf_of_le_right, sdiff_adj,
          fromEdgeSet_adj, Prod.mk.eta, Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, ne_eq,
          Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, not_and, Decidable.not_not, and_imp,
          Set.mem_toFinset, SetRel.mem_dom, Prod.mk.injEq, mem_edgeSet, Sym2.mem_iff] at hu
        simp only [_op_t, ← demote_finset_toFinset_eq, sdiff_toFinset]
        obtain ⟨w, hu', hu''⟩ := hu
        simp only [hu'.2, not_false_eq_true, and_true, imp_false, not_or, forall_const] at hu' hu''
        refine mem_sdiff.mpr ⟨?_, ?_⟩
        · have H {u'} : u' ∈ G.neighborFinset v → u' ∈ ABC.toFinset :=
            fun hu' ↦ hG <| Set.mem_toFinset.mpr <|
              G.mem_support.mpr ⟨v, Adj.symm <| G.mem_neighborFinset .. |>.mp hu'⟩
          rcases hu' with ⟨hu' | hu'⟩ | ⟨⟨hu' | hu'⟩ | ⟨⟨hu' | hu'⟩ | hu'⟩⟩
          any_goals simp only [hu'.1, hNv, mem_insert, mem_singleton, true_or, or_true, H]
          exact hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨w, hu'⟩
        · grind only [= mem_singleton]
      · simp only [_op_t, ← card_demote_finset_eq_card]
        refine sdiff_card _ <| nonempty_iff_ne_empty.mp <| nonempty_def.mpr ⟨v, ?_⟩
        simp only [← ABC.coe_mem_toFinset, mem_iff, hBv, or_true, not_A_of_B, not_C_of_B,
          or_false, singleton_inter_of_mem, mem_singleton]
    have _ : x ∈ s → y ∉ s ∧ z ∉ s := by
      intro hx
      have hd'x : (_op_g G v x y z).degree_in s x = 0 := by
        refine hsresp x hx |>.2.2 <| ?_
        refine demote_finset_from_B _ ?_ ?_
        · refine ⟨hBx, ?_⟩
          simp only [mem_singleton, Adj.ne' hvx, not_false_eq_true]
        · simp only [mem_insert, mem_singleton, true_or]
      constructor
      · refine notMem_of_degree_in_eq_zero_of_adj hd'x  ?_
        refine _op_g_adj_xy _ _ _ _ _ hxney hvx.ne hvy.ne
      · refine notMem_of_degree_in_eq_zero_of_adj hd'x  ?_
        refine _op_g_adj_xz _ _ _ _ _ hxnez hvx.ne hvz.ne
    have _ : y ∈ s → z ∉ s ∧ x ∉ s := by
      intro hy
      have hd'y : (_op_g G v x y z).degree_in s y = 0 := by
        refine hsresp y hy |>.2.2 <| ?_  -- C'_of_demote _ hvy.ne' hne hxnez hynez (by simp) hBy
        refine demote_finset_from_B _ ?_ ?_
        · refine ⟨hBy, ?_⟩
          simp only [mem_singleton, Adj.ne' hvy, not_false_eq_true]
        · simp only [mem_insert, mem_singleton, true_or, or_true]
      constructor
      · refine notMem_of_degree_in_eq_zero_of_adj hd'y  ?_
        refine _op_g_adj_yz _ _ _ _ _ hynez hvy.ne hvz.ne
      · refine notMem_of_degree_in_eq_zero_of_adj hd'y (Adj.symm ?_)
        refine _op_g_adj_xy _ _ _ _ _ hxney hvx.ne hvy.ne
    have hdegsv : G.degree_in s v ≤ 1 := by grind
    have hvnotins : v ∉ s :=  by
      simp only [_op_t, ← demote_finset_toFinset_eq, sdiff_toFinset] at hs
      intro hvs
      let hobj := mem_sdiff.mp (hs hvs) |>.2
      simp at hobj
    refine ⟨s ∪ {v}, ?_, ?_, ?_, ?_⟩
    · intro u hu
      simp only [union_singleton, mem_insert] at hu
      rcases hu with hu | hu
      · simp [hu, hBv, ← ABC.coe_mem_toFinset]
      · simp only [_op_t, ← demote_finset_toFinset_eq, sdiff_toFinset] at hs
        exact mem_sdiff.mp (hs hu) |>.1
    · refine G.InducesForest_union_leaf s ?_ hdegsv
      refine @InducesForest_mono' _ _ _ _ {v} (by simp [hvnotins]) ?_
      refine InducesForest_mono ?_ hsf
      refine deleteIncidencesOf_le_mono ?_
      intro u u' huu'
      simp only [Set.union_insert, Set.union_singleton, fromEdgeSet_adj, Set.mem_insert_iff,
        Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet, huu', or_true,
        ne_eq, huu'.ne, not_false_eq_true, and_self]
    · intro u hu
      simp only [union_singleton, mem_insert] at hu
      rcases hu with hu | hu
      · simp [hu, hBv, hu ▸ hdegsv]
      · if huNv : u ∈ G.neighborFinset v then
          simp only [hNv, mem_insert, mem_singleton] at huNv
          have H_degree_in : G.degree_in s u = (_op_g G v x y z).degree_in s u := by
            refine congrArg Finset.card ?_
            ext w
            simp only [mem_inter, mem_neighborFinset, deleteIncidencesOf, deleteIncidenceSet,
              incidenceSet, Set.union_insert, Set.union_singleton, mem_singleton, sdiff_le_iff,
              Set.mem_insert_iff, deleteEdges_fromEdgeSet, fromEdgeSet_sdiff, iInf_iInf_eq_left,
              le_sup_right, inf_of_le_right, sdiff_adj, fromEdgeSet_adj, Sym2.eq, Sym2.rel_iff',
              mem_edgeSet, Set.mem_setOf_eq]
            grind [Adj.ne]
          if huz : u = z then
            subst huz
            simp only [hCz, card_eq_zero, IsEmpty.forall_iff, and_true]
            constructor
            · intro hAu
              refine le_trans degree_in_union_le ?_
              simp only [card_singleton, Order.add_one_le_iff]
              refine Nat.add_le_add_right ?_ 1
              refine H_degree_in ▸ hsresp u hu |>.2.1 ?_
              refine demote_finset_from_A (ABC \ {v}) ⟨hAu, ?_⟩ ?_
              · simp only [mem_singleton, hvz.ne', not_false_eq_true]
              · simp only [mem_insert, mem_singleton, or_true]
            · intro hBu
              refine le_trans degree_in_union_le ?_
              simp only [card_singleton, add_le_iff_nonpos_left]
              refine le_of_eq <| H_degree_in ▸ hsresp u hu |>.2.2 ?_
              refine demote_finset_from_B (ABC \ {v}) ⟨hBu, ?_⟩ ?_
              · simp only [mem_singleton, hvz.ne', not_false_eq_true]
              · simp only [mem_insert, mem_singleton, or_true]
          else
            simp only [huz, or_false] at huNv
            rcases huNv with heq | heq <;> {
              subst heq
              simp only [hBx, hBy, not_A_of_B, not_C_of_B, degree_in, IsEmpty.forall_iff,
                true_and, and_true, true_and, forall_const, IsEmpty.forall_iff]
              refine le_trans (@degree_in_union_le _ G _ _ _ _) ?_
              simp only [card_singleton, add_le_iff_nonpos_left]
              refine le_of_eq ?_
              refine Eq.trans H_degree_in <| hsresp u hu |>.2.2 ?_
              simp only [_op_t]
              refine demote_finset_from_B (ABC \ {v}) ⟨?_, ?_⟩ ?_
              · simp only [hBx, hBy]
              · simp [hvx.ne', hvy.ne']
              · simp only [mem_insert, mem_singleton, true_or, or_true]
            }
        else
          have hdegree_in_eq : G.degree_in (s ∪ {v}) u = G.degree_in s u := by
            refine degree_in_union_eq ?_
            ext w
            simp only [mem_inter, mem_singleton, mem_neighborFinset, notMem_empty, iff_false,
              not_and]
            intro heq; subst heq
            exact fun huw ↦ huNv <| G.mem_neighborFinset .. |>.mpr huw.symm
          rw [hdegree_in_eq, degree_in_eq_outside (by grind) hNv s]
          have hu' : u ∉ ({v, x, y, z} : Finset _) := by grind
          refine ⟨?_, ?_, ?_⟩
          · exact fun hAu ↦ hsresp u hu |>.1   <| ABC.A'_of_ne hu' hAu
          · exact fun hBu ↦ hsresp u hu |>.2.1 <| ABC.B'_of_ne hu' hBu
          · exact fun hCu ↦ hsresp u hu |>.2.2 <| ABC.C'_of_ne hu' hCu
    · calc eval G ABC
        _ = ∑ w ∈ ABC.toFinset \ {v, x, y, z}, f G ABC w + ∑ w ∈ {v, x, y, z}, f G ABC w := by
          refine Eq.symm <| sum_sdiff ?_
          intro w hw
          refine ABC.coe_mem_toFinset.mp ?_
          simp only [mem_insert, mem_singleton] at hw
          rcases hw with hw | hw | hw | hw
          any_goals grind [mem_iff]
        _ = ∑ w ∈ (_op_t ABC v x y z).toFinset \ {x, y, z},
              f (_op_g G v x y z) (_op_t ABC v x y z) w
            + ∑ w ∈ {v, x, y, z}, f G ABC w := by
          simp only [add_left_inj]
          simp only [← demote_finset_toFinset_eq, sdiff_toFinset]
          refine sum_congr ?_ ?_
          · grind
          · exact fun _ _ ↦ f_eq_outside (by grind) hNv
        _ = (∑ w ∈ (_op_t ABC v x y z).toFinset \ {x, y, z},
              f (_op_g G v x y z) (_op_t ABC v x y z) w
            + ∑ w ∈ {x, y, z}, f (_op_g G v x y z) (_op_t ABC v x y z) w)
            - ∑ w ∈ {x, y, z}, f (_op_g G v x y z) (_op_t ABC v x y z) w
            + ∑ w ∈ {v, x, y, z}, f G ABC w := by
          grind
        _ = eval (_op_g G v x y z) (_op_t ABC v x y z)
            - ∑ w ∈ {x, y, z}, f (_op_g G v x y z) (_op_t ABC v x y z) w
            + ∑ w ∈ {v, x, y, z}, f G ABC w := by
          simp only [add_left_inj, sub_left_inj]
          simp only [eval]
          refine sum_sdiff ?_
          simp only [_op_t, ← demote_finset_toFinset_eq, sdiff_toFinset]
          intro u hu
          simp only [mem_insert, mem_singleton] at hu
          refine mem_sdiff.mpr ⟨?_, ?_⟩
          · rcases hu with hu | hu | hu
            <;> simp only [hu, ← coe_mem_toFinset, mem_iff, hBx, hBy, hzABC, or_true,
                  not_A_of_B, not_C_of_B, or_false]
          · rcases hu with hu | hu | hu
            <;> simp only [hu, hvx.ne', hvy.ne', hvz.ne', mem_singleton, not_false_eq_true]
        _ = eval (_op_g G v x y z) (_op_t ABC v x y z)
            - (f (_op_g G v x y z) (_op_t ABC v x y z) x
               + f (_op_g G v x y z) (_op_t ABC v x y z) y
               + f (_op_g G v x y z) (_op_t ABC v x y z) z)
            + ∑ w ∈ {v, x, y, z}, f G ABC w := by
          simp only [add_left_inj, sub_right_inj]
          grind
        _ = eval (_op_g G v x y z) (_op_t ABC v x y z)
            - (f (_op_g G v x y z) (_op_t ABC v x y z) x
               + f (_op_g G v x y z) (_op_t ABC v x y z) y
               + f (_op_g G v x y z) (_op_t ABC v x y z) z)
            + (f G ABC v + f G ABC x + f G ABC y + f G ABC z) := by
          simp only [add_right_inj]
          grind [Adj.ne]
        _ = eval (_op_g G v x y z) (_op_t ABC v x y z)
            - (f (_op_g G v x y z) (_op_t ABC v x y z) x - f G ABC x)
            - (f (_op_g G v x y z) (_op_t ABC v x y z) y - f G ABC y)
            - (f (_op_g G v x y z) (_op_t ABC v x y z) z - f G ABC z)
            + f G ABC v := by
          ring
        _ = eval (_op_g G v x y z) (_op_t ABC v x y z)
            + (f G ABC x - f (_op_g G v x y z) (_op_t ABC v x y z) x)
            + (f G ABC y - f (_op_g G v x y z) (_op_t ABC v x y z) y)
            + (f G ABC z - f (_op_g G v x y z) (_op_t ABC v x y z) z)
            + f G ABC v := by
          ring
      have _fC4 : fC 4 = 2 / 15 := by
        simp only [fC, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.reduceEqDiff,
          or_self, Nat.cast_ofNat]
        grind
      have fdiff {u} (hu : u ∈ ({x, y} : Finset _)) :
          f G ABC u - f (_op_g G v x y z) (_op_t ABC v x y z) u ≤ 1 / 5 := by
        simp only [mem_insert, mem_singleton] at hu
        rcases hu with hu | hu <;> {
          simp only [fB3 hBx hdx, fB3 hBy hdy, hu]
          suffices 2 / 15 ≤ f (_op_g G v x y z) (_op_t ABC v x y z) u by grind
          let hC'u : (_op_t ABC v x y z).C u := by
            refine demote_finset_from_B _ ?_ ?_
            · refine ⟨?_, ?_⟩
              · simp only [hu, hBx, hBy]
              · simp only [mem_singleton, hu, hvx.ne', hvy.ne', not_false_eq_true]
            · simp only [hu, mem_insert, mem_singleton, true_or, or_true]
          subst hu
          simp only [f, hC'u, not_A_of_C, not_B_of_C, ↓reduceDIte]
          rw [← _fC4]
          refine fC_decreasing ?_
          refine le_trans (_op_g_deg_xyz G hvx hvy hvz hxney hxnez hynez (by simp)) ?_
          simp [hdx, hdy]
        }
      have fdiffz : f G ABC z - f (_op_g G v x y z) (_op_t ABC v x y z) z ≤ 7 / 30 := by
        have hz : ABC.A z ∨ ABC.B z := by grind [mem_iff]
        rcases hz with hAz | hBz
        · have hz' : ((ABC \ {v}).demote_finset {x, y, z}).B z := by
            refine demote_finset_from_A _ ?_ ?_
            · refine ⟨hAz, by simp only [mem_singleton, hvz.ne', not_false_eq_true]⟩
            · simp only [mem_insert, mem_singleton, or_true]
          simp only [f, hAz, hz', not_A_of_B, ↓reduceDIte]
          exact diff_f_AB hdz <| _op_g_deg_xyz G hvx hvy hvz hxney hxnez hynez (by simp)
        · have hz' : ((ABC \ {v}).demote_finset {x, y, z}).C z := by
            refine demote_finset_from_B _ ?_ ?_
            · refine ⟨hBz, by simp only [mem_singleton, hvz.ne', not_false_eq_true]⟩
            · simp only [mem_insert, mem_singleton, or_true]
          simp only [f, hBz, hz', not_A_of_B, not_A_of_C, not_B_of_C, ↓reduceDIte]
          exact diff_f_BC hdz <| _op_g_deg_xyz G hvx hvy hvz hxney hxnez hynez (by simp)
      calc eval (_op_g G v x y z) (_op_t ABC v x y z)
            + (f G ABC x - f (_op_g G v x y z) (_op_t ABC v x y z) x)
            + (f G ABC y - f (_op_g G v x y z) (_op_t ABC v x y z) y)
            + (f G ABC z - f (_op_g G v x y z) (_op_t ABC v x y z) z)
            + f G ABC v
        _ ≤ #s + 1 / 5 + 1 / 5 + 7 / 30 + 1 / 3 := by
          rw [fB3 hBv hdv]
          simp only [add_le_add_iff_right]
          refine add_le_add ?_ fdiffz
          refine add_le_add ?_ (@fdiff y (by simp))
          refine add_le_add ?_ (@fdiff x (by simp))
          exact hscard
        _ ≤ #s + 1 := by grind
        _ = #(s ∪ {v}) := by
          rw [← Nat.cast_one, ← Nat.cast_add, ← card_singleton v]
          refine Nat.cast_inj.mpr ?_
          refine Eq.symm <| card_union_of_disjoint (by simp [hvnotins])

end Tripartition
end ABC
end CaroWeiType
