import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim0
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Claim1
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.Lemmas

open SimpleGraph
open Finset

namespace CaroWeiType
namespace AB
namespace Bipartition

variable {V : Type} [Fintype V] [DecidableEq V]

lemma Claim2 {G : SimpleGraph V} [DecidableRel G.Adj]
    {AB : Bipartition V} [AB.Decidable] (F : Finset V) (hFne : F.Nonempty)
    (hF : F ⊆ AB.toFinset) (hF' : respects F G AB)
    (hG : G.support ⊆ AB.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    G.InducesForestOfStars F →
      #F ≥ eval G AB - eval (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
                             (AB \ G.closed_neighborFinset_of_Finset F) →
        Objective G AB := by
  intro h h'
  have hcap : G.closed_neighborFinset_of_Finset F ∩ AB.toFinset ≠ ∅ := by
    refine Nonempty.ne_empty <| nonempty_def.mpr ?_
    obtain ⟨x, hx⟩ := nonempty_def.mp hFne
    refine ⟨x, mem_inter.mpr ⟨closed_neighborFinset_contains_Finset hx, hF hx⟩⟩
  obtain ⟨s', hs', hsf, hresp, hcard'⟩ :=
    ih (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
      (AB \ (G.closed_neighborFinset_of_Finset F)) (hsupp_mono hG) (AB.sdiff_card hcap)
  rw [sdiff_toFinset] at hs'
  have hN : ∀ x ∈ s', ∀ y ∈ F, ¬G.Adj x y := by
    intro x hx y hy
    have := mem_sdiff.mp (hs' hx) |>.2
    simp only [mem_closed_neighborFinset_iff, not_or, not_exists, not_and] at this
    exact not_adj_symm <| this.2 y hy
  refine ⟨s' ∪ F, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact mem_sdiff.mp (hs' hx) |>.1
    · exact hF hx
  · refine InducesForestOfStars_union_disjoint_neighborhoods ?_ h hN
    refine InducesForestOfStars_graph_mono' ?_ hsf
    ext y
    simp only [mem_inter, notMem_empty, iff_false, not_and]
    exact fun hy ↦ mem_sdiff.mp (hs' hy) |>.2
  · refine respects_of_union_disjoint_neighborhood ?_ hF' hN
    intro x hx hBx u hu hux
    obtain ⟨hA'u, hd'u⟩ := by
      refine hresp x hx ⟨hBx, mem_sdiff.mp (hs' hx) |>.2⟩ u hu ?_
      refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ hux
      · exact mem_sdiff.mp (hs' hu) |>.2
      · exact mem_sdiff.mp (hs' hx) |>.2
    refine ⟨hA'u.1, le_of_eq_of_le ?_ hd'u⟩
    refine Eq.symm <| degree_in_deleteIncidencesOf _ _ ?_ ?_
    · rw [inter_comm]
      ext z
      simp only [mem_inter, notMem_empty, iff_false, not_and]
      exact fun hz ↦ mem_sdiff.mp (hs' hz) |>.2
    · exact mem_sdiff.mp (hs' hu) |>.2
  · calc _
      _ = eval G AB
            - eval (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
                (AB \ G.closed_neighborFinset_of_Finset F)
            + eval (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
                (AB \ G.closed_neighborFinset_of_Finset F) :=
        Eq.symm <| sub_add_cancel ..
      _ ≤ #F + #s' := by
        linarith
    rw [card_union, ← Nat.cast_add, Nat.cast_le]
    suffices #(s' ∩ F) = 0 by lia
    refine card_eq_zero.mpr ?_
    ext x
    simp only [mem_inter, notMem_empty, iff_false, not_and]
    intro hx
    have := mem_sdiff.mp (hs' hx) |>.2
    simp only [mem_closed_neighborFinset_iff, not_or, not_exists, not_and] at this
    exact this.1

lemma Claim2'' {G : SimpleGraph V} [DecidableRel G.Adj]
    {AB : Bipartition V} [AB.Decidable] (F : Finset V) (hFne : F.Nonempty)
    (hF : F ⊆ AB.toFinset) (hF' : respects F G AB)
    (hG : G.support ⊆ AB.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    G.InducesForestOfStars F →
      #F ≥ ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G AB v
        - ∑ w ∈ G.N2_of_Finset F,
            (f (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
                (AB \ G.closed_neighborFinset_of_Finset F) w - f G AB w) →
        Objective G AB := by
  intro h h'
  refine Claim2 F hFne hF hF' hG ih h ?_
  simp_all only [ge_iff_le]
  let X := G.closed_neighborFinset_of_Finset <| G.closed_neighborFinset_of_Finset F
  have : eval G AB = ∑ x ∈ AB.toFinset \ X, f G AB x + ∑ x ∈ X, f G AB x := by
    refine Eq.symm (sum_sdiff ?_)
    intro x hx
    simp only [X, mem_closed_neighborFinset_iff] at hx
    rcases hx with ⟨hx | hx⟩ | hx
    · exact hF hx
    · obtain ⟨_, _, hwx⟩ := hx
      exact mem_def.mpr <| hG <| G.mem_support.mpr ⟨_, hwx.symm⟩
    · obtain ⟨_, ⟨_, hwx⟩⟩ := hx
      exact mem_def.mpr <| hG <| G.mem_support.mpr ⟨_, hwx.symm⟩
  have : eval G AB = ∑ x ∈ AB.toFinset \ X,
        f (G.deleteIncidencesOf <| G.closed_neighborFinset_of_Finset F)
          (AB \ G.closed_neighborFinset_of_Finset F) x + ∑ x ∈ X, f G AB x := by
    simp only [this, add_left_inj]
    refine sum_congr rfl fun x hx ↦ ?_
    have hx' : x ∉ G.closed_neighborFinset_of_Finset F := by
      have := not_iff_not.mpr mem_closed_neighborFinset_iff |>.mp <| mem_sdiff.mp hx |>.2
      simp only [not_or, not_exists, not_and] at this
      exact this.1
    refine f_congr ?_ ⟨?_, ?_, ?_⟩
    · refine degree_eq_deleteIncidencesOf_degree_of_inter_neighborhood_empty ?_ ?_
      · exact notMem_mono closed_neighborFinset_contains_Finset (mem_sdiff.mp hx |>.2)
      · have := not_iff_not.mpr mem_closed_neighborFinset_iff |>.mp <| mem_sdiff.mp hx |>.2
        simp only [not_or, not_exists, not_and] at this
        ext u
        simp only [mem_inter, mem_neighborFinset, notMem_empty, iff_false, not_and]
        exact fun hu ↦ not_adj_symm <| this.2 _ hu
    · exact (⟨·, hx'⟩)
    · exact (⟨·, hx'⟩)
    · exact (· (AB.mem_toFinset.mpr <| mem_sdiff.mp hx |>.1) |>.elim)
  rw [this]; repeat clear this
  have : eval (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
          (AB \ G.closed_neighborFinset_of_Finset F)
         = ∑ x ∈ AB.toFinset \ X,
            f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
              (AB \ G.closed_neighborFinset_of_Finset F) x
           + ∑ x ∈ G.N2_of_Finset F,
              f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
              (AB \ G.closed_neighborFinset_of_Finset F) x := by
    refine Eq.symm <| sum_disjoint_union ?_ ?_
    · ext x
      simp only [toFinset_eq, mem_sdiff, N2_of_Finset, mem_union, X]
      constructor
      · intro hx
        simp only [hx.1, true_and, hx.2, not_false_eq_true, and_true]
        exact Or.comm.mp <| em _
      · intro hx
        rcases hx with hx | hx
        · exact ⟨hx.1, notMem_mono closed_neighborFinset_contains_Finset hx.2⟩
        · refine ⟨?_, hx.2⟩
          simp only [mem_closed_neighborFinset_iff] at hx
          obtain ⟨hx, hx'⟩ := hx
          simp only [hx', false_or] at hx
          obtain ⟨_, hx⟩ := hx
          exact mem_def.mpr <| hG <| G.mem_support.mpr ⟨_, hx.2.symm⟩
    · grind [N2_of_Finset]
  rw [this]; clear this
  suffices ∑ x ∈ X, f G AB x
      - ∑ x ∈ G.N2_of_Finset F,
        f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
        (AB \ G.closed_neighborFinset_of_Finset F) x
      ≤ #F by
    linarith
  have : ∑ x ∈ X, f G AB x
      = ∑ x ∈ G.closed_neighborFinset_of_Finset F, f G AB x + ∑ x ∈ G.N2_of_Finset F, f G AB x := by
    simp only [X, N2_of_Finset]
    refine Eq.symm <| sum_disjoint_union ?_ ?_
    · exact Eq.symm <| union_sdiff_of_subset closed_neighborFinset_contains_Finset
    · exact inter_sdiff_self ..
  rw [this]; clear this
  refine le_trans ?_ h'
  suffices ∑ x ∈ G.N2_of_Finset F, f G AB x
        ≤ ∑ w ∈ G.N2_of_Finset F, f G AB w by
    simp only [sum_sub_distrib]
    linarith
  exact le_refl _

lemma Claim2' {G : SimpleGraph V} [DecidableRel G.Adj]
    {AB : Bipartition V} [AB.Decidable] (F : Finset V) (hFne : F.Nonempty)
    (hF : F ⊆ AB.toFinset) (hF' : respects F G AB)
    (hG : G.support ⊆ AB.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    G.InducesForestOfStars F →
      #F ≥ ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G AB v
        - ∑ w ∈ G.N2_of_Finset F, γ G AB w →
        Objective G AB := by
  intro h h'
  refine Claim2'' F hFne hF hF' hG ih h ?_
  refine le_trans ?_ h'
  suffices∑ w ∈ G.N2_of_Finset F, γ G AB w
      ≤ ∑ w ∈ G.N2_of_Finset F,
          (f (G.deleteIncidencesOf (G.closed_neighborFinset_of_Finset F))
              (AB \ G.closed_neighborFinset_of_Finset F) w
            - f G AB w) by
    linarith
  refine sum_le_sum fun x hx ↦ ?_
  have : x ∈ AB := by
    refine AB.mem_toFinset.mpr ?_
    exact hG <| G.degree_pos_iff_mem_support _ |>.mp <| one_le_degree_of_mem_N2 hx
  rcases this with hAx | hBx
  · have hA'x : (AB \ G.closed_neighborFinset_of_Finset F).A x :=
      ⟨hAx, notMem_closed_neighborFinset_of_mem_N2 hx⟩
    simp only [γ, f, hAx, hA'x, ↓reduceDIte, tsub_le_iff_right, sub_add_cancel, ge_iff_le]
    obtain ⟨x', hx', hxx'⟩ := mem_N2_of_Finset_iff''.mp hx |>.2
    refine fA_decreasing <| Nat.le_sub_one_of_lt <| deleteIncidencesOf_degree_lt hxx' hx'
  · have hB'x : (AB \ G.closed_neighborFinset_of_Finset F).B x :=
      ⟨hBx, notMem_closed_neighborFinset_of_mem_N2 hx⟩
    simp only [γ, f, hBx, hB'x, not_A_of_B, ↓reduceDIte, tsub_le_iff_right, sub_add_cancel,
      ge_iff_le]
    obtain ⟨x', hx', hxx'⟩ := mem_N2_of_Finset_iff''.mp hx |>.2
    refine fB_decreasing <| Nat.le_sub_one_of_lt <| deleteIncidencesOf_degree_lt hxx' hx'

lemma Corollary2 {G : SimpleGraph V} [DecidableRel G.Adj]
    {AB : Bipartition V} [AB.Decidable] (F : Finset V) (hFne : F.Nonempty)
    (hF : F ⊆ AB.toFinset) (hF' : respects F G AB)
    (hG : G.support ⊆ AB.toFinset)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj] (AB' : Bipartition V)
      [AB'.Decidable], G'.support ⊆ AB'.toFinset → AB'.card < AB.card → Objective G' AB') :
    G.InducesForestOfStars F →
      #F ≥ ∑ v ∈ G.closed_neighborFinset_of_Finset F, f G AB v →
        Objective G AB := by
  intro h h'
  refine Claim2' F hFne hF hF' hG ih h ?_
  simp only [ge_iff_le, tsub_le_iff_right] at h' ⊢
  refine le_trans h' ?_
  simp only [le_add_iff_nonneg_right]
  refine sum_nonneg <| fun _ _ ↦ γ_nonneg

end Bipartition
end AB
end CaroWeiType
