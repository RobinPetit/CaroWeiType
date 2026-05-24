import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas

open SimpleGraph
open Finset

namespace CaroWeiType
namespace ABC
namespace Tripartition

variable {V : Type} [Fintype V] [DecidableEq V]

private lemma _ok_eval {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V}
    [ABC.Decidable] {s : Finset V} (hG : G.support ⊆ ABC.toFinset)
    {v x y z : V} (hNv : G.neighborFinset v = {x, y, z})
    (hdv : G.degree v = 3) (hBv : ABC.B v)
    (hscard : eval ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x})
        ((ABC \ {x}).promote v) ≤ #s)
    (hbound : f G ABC x - 1 / 3 + ∑ u ∈ {y, z},
        (f G ABC u - f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x})
          ((ABC \ {x}).promote v) u) ≤
      ∑ u ∈ G.neighborFinset x \ ({v} ∪ G.neighborFinset v), γ G ABC u) :
    eval G ABC ≤ #s := by
  refine le_trans ?_ hscard
  calc _
    _ = ∑ u ∈ (ABC.toFinset \ (G.neighborFinset x ∪ G.neighborFinset v)), f G ABC u
        + ∑ u ∈ (G.neighborFinset x ∪ G.neighborFinset v), f G ABC u := by
      refine Eq.symm <| sum_sdiff ?_
      intro u hu
      simp only [mem_union, mem_neighborFinset] at hu
      rcases hu with hu | hu <;> exact mem_def.mpr <| hG <| G.mem_support.mpr ⟨_, hu.symm⟩
    _ = ∑ u ∈ (ABC.toFinset \ (G.neighborFinset x ∪ G.neighborFinset v)),
          f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) u
        + ∑ u ∈ (G.neighborFinset x ∪ G.neighborFinset v), f G ABC u := by
      simp only [add_left_inj]
      refine sum_congr rfl ?_
      intro u hu
      simp only [mem_sdiff, mem_union, not_or] at hu
      have huv : u ∉ ({v} : Finset _) := by
        refine notMem_singleton.mpr ?_
        refine Ne.symm <| ne_of_mem_of_not_mem ?_ (hu.2.1)
        refine mem_neighborFinset_symm <| by simp [hNv]
      have hux : u ∉ ({x} : Finset _) := by
        refine notMem_singleton.mpr ?_
        refine Ne.symm <| ne_of_mem_of_not_mem ?_ (hu.2.2)
        refine by simp [hNv]
      have hdeg : G.degree u
          = ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}).degree u := by
        refine congrArg Finset.card ?_
        ext u'
        simp only [mem_neighborFinset]
        constructor
        · intro huu'
          refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj hux ?_ ?_
          · refine notMem_singleton.mpr ?_
            exact fun heq ↦ hu.2.1 <| G.mem_neighborFinset .. |>.mpr <| heq ▸ huu'.symm
          · exact le_fromEdgeSet_union huu'
        · intro h
          rcases adj_fromEdgeSet_union_iff.mp <| adj_of_deleteIncidencesOf_adj h with huu' | huu'
          · exact huu'
          · refine hu.2.2 (by grind) |>.elim
      rcases ABC.mem_toFinset.mpr hu.1 with hAu | hBu | hCu
      · have hA' : (ABC \ {x}).promote v |>.A u := Or.inl ⟨hAu, hux⟩
        simp only [f, hAu, hA', ↓reduceDIte]
        refine congrArg _ hdeg
      · have hB' : (ABC \ {x}).promote v |>.B u := Or.inl ⟨⟨hBu, hux⟩, huv⟩
        simp only [f, hBu, hB', not_A_of_B, ↓reduceDIte]
        refine congrArg _ hdeg
      · have hC' : (ABC \ {x}).promote v |>.C u := ⟨⟨hCu, hux⟩, huv⟩
        simp only [f, hCu, hC', not_A_of_C, not_B_of_C, ↓reduceDIte]
        refine congrArg _ hdeg
    _ = ∑ u ∈ ABC.toFinset \ (G.neighborFinset x ∪ G.neighborFinset v),
          f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) u
        + ∑ u ∈ (G.neighborFinset x ∪ G.neighborFinset v) \ {x},
          f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) u
        - ∑ u ∈ (G.neighborFinset x ∪ G.neighborFinset v) \ {x},
          f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) u
        + ∑ u ∈ G.neighborFinset x ∪ G.neighborFinset v, f G ABC u := by
      linarith
    _ = ∑ u ∈ ABC.toFinset \ {x},
          f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) u
        - ∑ u ∈ (G.neighborFinset x ∪ G.neighborFinset v) \ {x},
          f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) u
        + ∑ u ∈ G.neighborFinset x ∪ G.neighborFinset v, f G ABC u := by
      simp only [add_left_inj, sub_left_inj]
      have H : (ABC.toFinset \ {x}) = ABC.toFinset \ (G.neighborFinset x ∪ G.neighborFinset v)
          ∪ ((G.neighborFinset x ∪ G.neighborFinset v) \ {x}) := by
        ext u
        simp only [mem_sdiff, mem_singleton, mem_union, mem_neighborFinset, not_or]
        constructor
        · grind
        · intro h
          rcases h with h | h
          · obtain ⟨huABC, hxu, hvu⟩ := h
            simp only [huABC, true_and]
            refine Ne.symm <| ne_of_mem_of_not_mem (by grind : x ∈ G.neighborFinset v) ?_
            exact not_iff_not.mpr (G.mem_neighborFinset ..) |>.mpr hvu
          · obtain ⟨h, hunex⟩ := h
            simp only [hunex, not_false_eq_true, and_true]
            rcases h with h | h <;> exact mem_def.mpr <| hG <| G.mem_support.mpr ⟨_, h.symm⟩
      rw [H]
      refine Eq.symm <| sum_union ?_
      refine disjoint_iff_inter_eq_empty.mpr ?_
      ext u
      simp only [mem_inter, mem_sdiff, mem_union, mem_neighborFinset, not_or, mem_singleton,
        notMem_empty, iff_false, not_and, Decidable.not_not, and_imp]
      intro _ hxu hvu
      simp only [hxu, hvu, or_self, IsEmpty.forall_iff]
  have : (ABC.toFinset \ {x}) = ((ABC \ {x}).promote v).toFinset := by
    rw [← promote_toFinset_eq, sdiff_toFinset]
  rw [this, eval]
  suffices ∑ u ∈ G.neighborFinset x ∪ G.neighborFinset v, f G ABC u
      ≤ ∑ u ∈ (G.neighborFinset x ∪ G.neighborFinset v) \ {x},
        f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x})
          ((ABC \ {x}).promote v) u by
    linarith
  calc _
    _ = ∑ u ∈ ((G.neighborFinset x \ ({v} ∪ G.neighborFinset v)) ∪ ({v} ∪ G.neighborFinset v)),
        f G ABC u := by
      refine sum_congr ?_ fun _ _ ↦ rfl
      refine Eq.symm ?_
      ext u
      simp only [singleton_union, union_insert, mem_insert, mem_union, mem_sdiff,
        mem_neighborFinset, not_or]
      constructor
      · intro h
        rcases h with h | h | h
        · exact Or.inl <| Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
        · simp only [h, or_false]
        · simp only [h, or_true]
      · grind
    _ = ∑ u ∈ G.neighborFinset x \ ({v} ∪ G.neighborFinset v), f G ABC u
        + ∑ u ∈ {v} ∪ G.neighborFinset v, f G ABC u := by
      refine sum_union ?_
      refine disjoint_iff_inter_eq_empty.mpr ?_
      exact sdiff_inter_self ..
    _ = ∑ u ∈ (G.neighborFinset x \ ({v} ∪ G.neighborFinset v)), f G ABC u
        + (f G ABC v + f G ABC x + f G ABC y + f G ABC z) := by
      simp only [add_right_inj, hNv]
      grind [degree, notMem_singleton_of_mem_neighborFinset]
  refine ge_iff_le.mp ?_
  have hv' : v ∉ ({x, y, z} : Finset _) := hNv ▸ notMem_neighborFinset_self G v
  have hxv : G.Adj x v := Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
  calc _
    _ = ∑ u ∈ ((G.neighborFinset x \ ({v} ∪ G.neighborFinset v))
          ∪ (({v} ∪ G.neighborFinset v \ {x}))),
        f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x})
          ((ABC \ {x}).promote v) u := by
      refine sum_congr ?_ fun _ _ ↦ rfl
      ext u
      simp only [mem_sdiff, mem_union, mem_neighborFinset, mem_singleton]
      grind [Adj.ne]
    _ = ∑ u ∈ (G.neighborFinset x \ ({v} ∪ G.neighborFinset v)),
        f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) u
      + ∑ u ∈ ({v} ∪ G.neighborFinset v \ {x}),
        f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) u
        := by
      refine sum_union ?_
      refine disjoint_iff_inter_eq_empty.mpr ?_
      grind
    _ = ∑ u ∈ (G.neighborFinset x \ ({v} ∪ G.neighborFinset v)),
        f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) u
      + (f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) v
      + f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) y
      + f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) z)
        := by
      simp only [add_right_inj, hNv]
      have : ({v} ∪ ({x, y, z} : Finset _) \ {x}) = {v, y, z} := by grind [degree]
      grind [degree]
  refine ge_iff_le.mpr ?_
  have {a b c d : ℝ} (h : a - c ≥ d - b) : a + b ≥ c + d := by linarith
  refine this ?_
  have {f g : ℕ → ℝ} {s : Finset ℕ} : ∑ x ∈ s, f x - ∑ x ∈ s, g x = ∑ x ∈ s, (f x - g x) := by
    exact Eq.symm (sum_sub_distrib f g)
  rw [← sum_sub_distrib _ _]
  calc _
    _ = ∑ u ∈ G.neighborFinset x \ ({v} ∪ G.neighborFinset v), γ G ABC u := by
      refine sum_congr rfl ?_
      intro u hu
      simp only [mem_sdiff, mem_union, not_or] at hu
      have huABC : u ∈ ABC := by
        exact ABC.mem_toFinset.mpr <| mem_def.mpr <| hG
          <| G.mem_support.mpr ⟨x, Adj.symm <| G.mem_neighborFinset .. |>.mp hu.1⟩
      have hux : u ∉ ({x} : Finset _) := by
        refine notMem_singleton.mpr <| Ne.symm <| ne_of_mem_of_not_mem (by grind) (hu.2.2)
      have hdeg : ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}).degree u
          = G.degree u - 1 := by
        suffices ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}).neighborFinset u
            = G.neighborFinset u \ {x} by
          simp only [degree, this, ← card_singleton x]
          exact card_sdiff_of_subset <| singleton_subset_iff.mpr <| mem_neighborFinset_symm hu.1
        ext u'
        simp only [mem_neighborFinset, mem_sdiff]
        constructor
        · intro h
          refine ⟨?_, notMem_of_adj_deleteIncidencesOf' h⟩
          grind [adj_fromEdgeSet_union_iff.mp <| adj_of_deleteIncidencesOf_adj h]
        · intro ⟨huu', hu'nex⟩
          refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj hux hu'nex ?_
          refine adj_fromEdgeSet_union_iff.mpr <| Or.inl huu'
      rcases huABC with hAu | hBu | hCu
      · have hA' : ((ABC \ {x}).promote v).A u := Or.inl ⟨hAu, hux⟩
        simp only [f, γ, hAu, hA', ↓reduceDIte, sub_left_inj]
        refine congrArg _ hdeg
      · have hB' : ((ABC \ {x}).promote v).B u := Or.inl ⟨⟨hBu, hux⟩, hu.2.1⟩
        simp only [f, γ, hBu, hB', not_A_of_B, ↓reduceDIte, sub_left_inj]
        refine congrArg _ hdeg
      · have hC' : ((ABC \ {x}).promote v).C u := ⟨⟨hCu, hux⟩, hu.2.1⟩
        simp only [f, γ, hCu, hC', not_A_of_C, not_B_of_C, ↓reduceDIte, sub_left_inj]
        refine congrArg _ hdeg
  have hAv' : ((ABC \ {x}).promote v).A v := Or.inr ⟨⟨hBv, by grind⟩, mem_singleton.mpr rfl⟩
  have hdv' : ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}).degree v = 2 := by
    suffices ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}).neighborFinset v
        = G.neighborFinset v \ {x} by
      rw [degree, this, card_sdiff, ← degree, hdv]
      suffices {x} ∩ G.neighborFinset v = {x} by
        rw [this, card_singleton]
      refine singleton_inter_of_mem <| by simp [hNv]
    ext u
    simp only [mem_neighborFinset, mem_sdiff]
    constructor
    · intro h
      refine ⟨?_, notMem_of_adj_deleteIncidencesOf' h⟩
      grind [adj_fromEdgeSet_union_iff.mp <| adj_of_deleteIncidencesOf_adj h]
    · intro ⟨hvu, hux⟩
      refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj (by grind) hux ?_
      exact adj_fromEdgeSet_union_iff.mpr <| Or.inl hvu
  rw [fB3 hBv hdv, fA2 hAv' hdv']
  refine ge_iff_le.mpr ?_
  calc _
    _ = f G ABC x - 1 / 3 + (f G ABC y + f G ABC z) -
      (f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) y
      + f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) z)
        := by
      linarith
    _ = (f G ABC x - 1 / 3) + (∑ u ∈ {y, z}, f G ABC u
      - ∑ u ∈ {y, z},
        f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) u)
        := by
      grind [degree]
    _ = (f G ABC x - 1 / 3) + ∑ u ∈ {y, z}, (f G ABC u -
        f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x}) ((ABC \ {x}).promote v) u)
        := by
      simp only [add_right_inj]
      exact Eq.symm <| sum_sub_distrib ..
  exact hbound

lemma objective_of_B3 {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {v x y z : V} (hdv : G.degree v = 3)
    (hBv : ABC.B v) (hNv : G.neighborFinset v = {x, y, z})
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC')
    (hbound : f G ABC x - 1 / 3 + ∑ u ∈ {y, z},
        (f G ABC u - f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x})
          ((ABC \ {x}).promote v) u) ≤
      ∑ u ∈ G.neighborFinset x \ ({v} ∪ G.neighborFinset v), γ G ABC u) :
    Objective G ABC := by
  let G' := (fromEdgeSet <| G.edgeSet ∪ {s(y, z)}).deleteIncidencesOf {x}
  let ABC' := (ABC \ {x}).promote v
  obtain ⟨s, hs, hsf, hsresp, hscard⟩ := by
    refine ih ((fromEdgeSet <| G.edgeSet ∪ {s(y, z)}).deleteIncidencesOf {x})
      ((ABC \ {x}).promote v) ?_ ?_
    · intro u hu
      simp only [← promote_toFinset_eq, toFinset_eq, coe_sdiff, coe_singleton, Set.mem_diff,
        SetLike.mem_coe, Set.mem_singleton_iff]
      obtain ⟨w, hu⟩ := mem_support _ |>.mp hu
      refine ⟨?_, ?_⟩
      · have := adj_fromEdgeSet_union_iff.mp <| adj_of_deleteIncidencesOf_adj hu
        rcases this with hu | hu
        · exact mem_def.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp hu.degree_pos_left
        · have : u = y ∨ u = z := by grind
          refine mem_def.mpr <| hG <| G.mem_support.mpr ⟨v, ?_⟩
          exact Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
      · exact notMem_singleton.mp <| notMem_of_adj_deleteIncidencesOf hu
    · simp only [← card_promote_finset_eq_card]
      refine ABC.sdiff_card ?_
      suffices x ∈ ABC.toFinset by
        refine not_iff_not.mpr singleton_inter_eq_empty_iff |>.mpr ?_
        simp only [Decidable.not_not, this]
      refine mem_def.mpr <| hG <| G.mem_support.mpr ⟨v, ?_⟩
      exact Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNv]
  have hxs : x ∉ s := by
    simp only [← promote_toFinset_eq, sdiff_toFinset] at hs
    exact fun hx ↦ notMem_singleton.mp (mem_sdiff.mp (hs hx) |>.2) rfl
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have := hs hu
    simp only [← promote_toFinset_eq, toFinset_eq, mem_sdiff, mem_singleton] at this
    exact this.1
  · refine InducesForest_graph_mono le_fromEdgeSet_union (InducesForest_graph_mono' ?_ hsf)
    exact inter_singleton_of_notMem hxs
  · intro u hu
    have hux : u ∉ ({x} : Finset _) := notMem_singleton.mpr <| ne_of_mem_of_not_mem hu hxs
    refine ⟨?_, ?_, ?_⟩
    · intro hA
      have := hsresp u hu |>.1 <| Or.inl ⟨hA, hux⟩
      rw [degree_in_deleteIncidencesOf _ _ (singleton_inter_of_notMem hxs) hux] at this
      exact le_trans (degree_in_mono' le_fromEdgeSet_union) this
    · intro hB
      if huv : u = v then
        subst huv
        simp only [degree_in]
        have : ¬{u, y, z} ⊆ s := by
          refine no_induced_K3_of_InducesForest _ _ ?_ ?_ ?_ hsf
          · refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj hux (by grind [degree]) ?_
            refine adj_fromEdgeSet_union_iff.mpr <| Or.inl ?_
            exact G.mem_neighborFinset .. |>.mp <| by simp [hNv]
          · refine Adj.symm <| (deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ ?_)
            · grind [degree]
            · grind [degree]
            · refine adj_fromEdgeSet_union_iff.mpr <| by grind [degree]
          · refine Adj.symm
              <| deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj hux (by grind [degree]) ?_
            refine adj_fromEdgeSet_union_iff.mpr <| Or.inl ?_
            exact G.mem_neighborFinset .. |>.mp <| by simp [hNv]
        grind
      else
        have := hsresp u hu |>.2.1 <| Or.inl ⟨⟨hB, hux⟩, notMem_singleton.mpr huv⟩
        rw [degree_in_deleteIncidencesOf _ _ (singleton_inter_of_notMem hxs) hux] at this
        exact le_trans (degree_in_mono' le_fromEdgeSet_union) this
    · intro hC
      refine le_antisymm ?_ (zero_le _)
      have := by
        refine hsresp u hu |>.2.2 <| ⟨⟨hC, hux⟩, ?_⟩
        refine notMem_singleton.mpr ?_
        refine ne_of_ne_congr (ABC.C ·) ?_
        simp only [hC, not_C_of_B hBv]
        exact true_ne_false
      rw [degree_in_deleteIncidencesOf _ _ (singleton_inter_of_notMem hxs) hux] at this
      exact le_trans (degree_in_mono' le_fromEdgeSet_union) (le_of_eq this)
  · exact _ok_eval hG hNv hdv hBv hscard hbound

lemma objective_of_B3' {G : SimpleGraph V} [DecidableRel G.Adj] {ABC : Tripartition V}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {v x y z : V} (hdv : G.degree v = 3)
    (hBv : ABC.B v) (hNv : G.neighborFinset v = {x, y, z})
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (ABC' : Tripartition V)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨
      (∑ u ∈ G.neighborFinset x \ ({v} ∪ G.neighborFinset v), γ G ABC u
       < f G ABC x - 1 / 3 + ∑ u ∈ {y, z},
        (f G ABC u - f ((fromEdgeSet (G.edgeSet ∪ {s(y, z)})).deleteIncidencesOf {x})
        ((ABC \ {x}).promote v) u)) := by
  if h : Objective G ABC then
    exact Or.inl h
  else
    exact Or.inr <| not_le.mp <| objective_of_B3 hG hdv hBv hNv ih |>.mt h

end Tripartition
end ABC
end CaroWeiType
