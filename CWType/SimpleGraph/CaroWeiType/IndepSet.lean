-- import Mathlib
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Cast.Order.Field

import CWType.SimpleGraph.CaroWeiType.Basic
import CWType.SimpleGraph.CaroWeiType.Lemmas

namespace SimpleGraph
namespace CaroWeiType

open FiniteSimpleGraph
open Finset

theorem IndepNumberClique_eq_one {V : Type*} (s : Finset V) :
    (completeGraph V).IsIndepSet s ↔ #s ≤ 1 := by
  classical
  constructor
  · contrapose!
    intro hs
    obtain ⟨x, y, hx, hy, hxy⟩ := Finset_get_two s (Nat.succ_le_of_lt hs)
    simp only [IsIndepSet, Set.Pairwise, SetLike.mem_coe, ne_eq, completeGraph_eq_top, top_adj,
      Decidable.not_not, _root_.not_imp_self, not_forall]
    exact ⟨x, hx, y, hy, hxy⟩
  · intro hs
    simp_all only [IsIndepSet, Set.Pairwise, SetLike.mem_coe, ne_eq, completeGraph_eq_top, top_adj,
      not_false_eq_true, not_true_eq_false, imp_false, Decidable.not_not]
    intro x hx y hy
    by_contra
    suffices 2 ≤ 1 by simp_all only [Nat.not_ofNat_le_one]
    calc 2
      _ = ({x} : Finset V).card + ({y} : Finset V).card := by simp
      _ = ({x, y} : Finset V).card := by simp_all only [card_singleton, mem_singleton,
                                          not_false_eq_true, card_insert_of_notMem]
      _ ≤ s.card := card_le_card (by grind)
      _ ≤ 1 := hs

noncomputable abbrev cw_bound : ℕ → ℝ := fun d ↦ (d + 1 : ℝ)⁻¹

lemma cw_bound_prev (d : ℕ) (hd : 0 < d) : cw_bound (d-1) = (d : ℝ)⁻¹ := by
  simp only [cw_bound, inv_inj]
  refine add_eq_of_eq_sub <| Nat.cast_pred hd

noncomputable def cw_gain : ℕ → ℝ := fun d ↦ cw_bound (d - 1) - cw_bound (d)

lemma cw_gain_eq (d : ℕ) (hd_pos : 0 < d) : cw_gain d = ((d * (d + 1)) : ℝ)⁻¹ := by
  simp only [cw_bound, cw_gain]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [Nat.cast_pred hd_pos]
  simp only [sub_add_cancel]
  have hdR_pos : (d : ℝ) ≠ 0 := by exact Nat.cast_ne_zero.mpr <| Nat.ne_zero_of_lt hd_pos
  calc ((d : ℝ)⁻¹ - (d + 1 : ℝ)⁻¹) * ((d : ℝ) * (d + 1 : ℝ))
    _ = (d : ℝ)⁻¹ * ((d : ℝ) * (d + 1 : ℝ)) - (d + 1 : ℝ)⁻¹ * ((d : ℝ) * (d + 1 : ℝ)) := by
      exact sub_mul ..
    _ = ((d : ℝ)⁻¹ * (d : ℝ)) * (d + 1 : ℝ) - (d + 1 : ℝ)⁻¹ * ((d : ℝ) * (d + 1 : ℝ)) := by
      simp only [sub_left_inj]
      exact Eq.symm <| mul_assoc ..
    _ = (d + 1 : ℝ) - (d + 1 : ℝ)⁻¹ * ((d : ℝ) * (d + 1 : ℝ)) := by
      have h' : (d : ℝ)⁻¹ * (d : ℝ) = 1 := by grind
      simp only [h', one_mul]
    _ = 1 := by grind

theorem cw_bound_gain_decreasing {m n : ℕ} (hm : 0 < m) (h : m < n) : cw_gain n < cw_gain m := by
  have hn : 0 < n := lt_trans hm h
  rw [cw_gain_eq m hm, cw_gain_eq n hn]
  simp only [mul_inv_rev, gt_iff_lt]
  have h1 : (m : ℝ) < (n : ℝ) := by exact Nat.cast_lt.mpr h
  have h2 : (m + 1 : ℝ) < (n + 1 : ℝ) := by exact (add_lt_add_iff_right 1).mpr h1
  have hn' : 0 < (n : ℝ) := by exact Nat.cast_pos'.mpr hn
  have _ : 0 < (n : ℝ)⁻¹ := by exact Right.inv_pos.mpr hn'
  calc (n + 1 : ℝ)⁻¹ * (n : ℝ)⁻¹
    _ < (m + 1 : ℝ)⁻¹ * (n : ℝ)⁻¹ := by
      refine mul_lt_mul_of_pos_right ?_ (Right.inv_pos.mpr hn')
      refine (inv_lt_inv₀ ?_ ?_).mpr h2 <;> exact Nat.cast_add_one_pos _
    _ < (m + 1 : ℝ)⁻¹ * (m : ℝ)⁻¹ := by
      refine (mul_lt_mul_of_pos_left ?_ Nat.inv_pos_of_nat)
      refine (inv_lt_inv₀ ?_ ?_).mpr h1 <;> simp [hm, hn]

theorem CaroWeiIndepSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (X : Finset (Fin n))
    (hX : G.support ⊆ X) :
    ∃ s : Finset (Fin n), s ⊆ X ∧ G.IsIndepSet s ∧ ∑ v ∈ X, cw_bound (G.degree v) ≤ #s := by
  induction hcard : #X generalizing G X with
  | zero => exact ⟨∅, by simp, by simp, by simp_all⟩
  | succ m ih => ?_
  if hΔ : G.maxDegree = 0 then
    refine ⟨X, by simp, ?_, ?_⟩
    · intro x _ _ _ _ hadj
      suffices 0 < 0 by grind
      have _ : G.degree x > 0 := by exact Adj.degree_pos_left hadj
      calc 0
        _ < G.degree x := hadj.degree_pos_left
        _ ≤ 0 := hΔ ▸ G.degree_le_maxDegree _
    · refine le_of_eq <| mul_one (#X : ℝ) ▸ sum_const' X ?_
      intro x hx
      simp only [inv_eq_one, add_eq_right, Nat.cast_eq_zero]
      refine Nat.le_antisymm (hΔ ▸ G.degree_le_maxDegree _) (Nat.zero_le _)
  else
    have _ : Nonempty (Fin n) := by
      refine Nonempty.intro <| (@Classical.choice X ?_).1
      exact Nonempty.to_subtype <| card_pos.mp <| Nat.lt_of_sub_eq_succ hcard
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    let X' := X \ {v}
    have hX' : (G.deleteIncidenceSet v).support ⊆ X' := by
      intro x hx
      simp only [coe_sdiff, coe_singleton, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff, X']
      refine ⟨hX <| (support_mono (G.deleteIncidenceSet_le v)) hx, ?_⟩
      intro heq
      simp_all only [support, deleteIncidenceSet, deleteEdges, incidenceSet, sdiff_adj,
        fromEdgeSet_adj, Prod.mk.eta, Set.mem_setOf_eq, ne_eq, not_and, Decidable.not_not,
        and_imp, SetRel.mem_dom, mem_edgeSet, Sym2.mem_iff, true_or, forall_const]
      obtain ⟨u, ⟨hvu, h⟩⟩ := hx
      exact G.irrefl <| h hvu ▸ hvu
    have hcardX' : #(X \ {v}) = #X - 1 := by
      refine card_setminus_singleton <| hX <| (G.degree_pos_iff_mem_support v).mp ?_
      exact hv ▸ Nat.zero_lt_of_ne_zero hΔ
    obtain ⟨s', ⟨hs', hind', hcard'⟩⟩ :=
      ih (G.deleteIncidenceSet v) (X \ {v}) hX' (by simp_all only [add_tsub_cancel_right])
    refine ⟨s', ?_, ?_, ?_⟩
    · exact fun _ hx ↦ (@mem_sdiff _ _ X {v} |>.mp (hs' hx)).1
    · intro x hx y hy hne hadj
      let hnadj' := hind' hx hy hne
      simp only [deleteIncidenceSet, incidenceSet, deleteEdges_adj, hadj, Set.mem_setOf_eq,
        mem_edgeSet, Sym2.mem_iff, true_and, not_or, not_and, Decidable.not_not] at hnadj'
      grind
    · refine le_trans ?_ hcard'
      refine cw_bound_mono (fun d ↦ (d + 1 : ℝ)⁻¹) G hv.symm (Nat.zero_lt_of_ne_zero hΔ) X hX ?_ ?_
      · intro d hd_pos hdΔ
        simp only
        if hd_eq_Δ : d = G.maxDegree then rw [hd_eq_Δ]
        else ?_
        have hd_lt_Δ : d < G.maxDegree := Nat.lt_of_le_of_ne hdΔ hd_eq_Δ
        let hobj := cw_bound_gain_decreasing hd_pos hd_lt_Δ
        simp only [cw_gain, cw_bound] at hobj
        exact le_of_lt hobj
      · simp only [ge_iff_le]
        refine le_of_eq ?_
        have hΔ' : (G.maxDegree : ℝ) > 0 := by exact Nat.cast_pos'.mpr <| Nat.zero_lt_of_ne_zero hΔ
        calc (G.maxDegree + 1 : ℝ)⁻¹
          _ = (G.maxDegree : ℝ) * (G.maxDegree : ℝ)⁻¹ * (G.maxDegree + 1 : ℝ)⁻¹ := by
            have hΔΔinv : (G.maxDegree : ℝ) * (G.maxDegree : ℝ)⁻¹ = 1 := by
              exact mul_inv_cancel₀ <| Nat.cast_ne_zero.mpr hΔ
            simp only [hΔΔinv, one_mul]
          _ = (G.maxDegree : ℝ) * ((G.maxDegree : ℝ) * (G.maxDegree + 1 : ℝ))⁻¹ := by
            grind
        let hobj := cw_gain_eq G.maxDegree (Nat.zero_lt_of_ne_zero hΔ)
        simp only [← hobj, mul_eq_mul_left_iff, Nat.cast_eq_zero, hΔ, or_false]
        rfl

theorem IndepSet_LowerBound :
    IsCaroWeiTypeLowerBound (fun d ↦ (d + 1 : ℝ)⁻¹) (fun G s ↦ G.graph.IsIndepSet s) := by
  intro n G
  obtain ⟨s, ⟨_, ⟨hind, hcard⟩⟩⟩ := CaroWeiIndepSet G.graph (Finset.univ) (by simp)
  exact ⟨s, hind, hcard⟩

theorem IndepSet_LowerBound_iff (f : ℕ → ℝ) :
    IsCaroWeiTypeLowerBound f (fun {n : ℕ} (G : FiniteSimpleGraph n) s ↦ G.graph.IsIndepSet s)
      ↔ f ≤ cw_bound := by
  refine ⟨?_, fun hle ↦ CaroWeiTypeLowerBound_mono hle IndepSet_LowerBound⟩
  intro hf d
  unfold IsCaroWeiTypeLowerBound at hf
  let K' := FiniteCompleteGraph (d + 1)
  let _ := K'.decAdj
  obtain ⟨s, hind, hcard⟩ := hf <| K'
  simp only [K'] at hcard
  have hpos' : (d + 1 : ℝ)⁻¹ > 0 := Nat.inv_pos_of_nat
  suffices f d * (d + 1 : ℝ) ≤ 1 by
    calc f d
      _ = (f d * (d + 1 : ℝ)) * (d + 1 : ℝ)⁻¹ := by grind
      _ ≤ 1 * (d + 1 : ℝ)⁻¹ := by simp_all
      _ = (d + 1 : ℝ)⁻¹ := by simp
  calc f d * (d + 1)
    _ = ∑ v : Fin (d + 1), f d := by simp [CommMonoid.mul_comm]
    _ = ∑ v : Fin (d + 1), f (K'.graph.degree v) := by
        apply Eq.symm
        refine Fintype.sum_congr _ _ (fun v ↦ congrArg f ?_)
        simp only [degree, neighborFinset, completeGraph_eq_top, FiniteCompleteGraph,
          eq_mpr_eq_cast, cast_eq, Set.toFinset_card, Fintype.card_ofFinset, mem_neighborSet,
          top_adj, ne_eq, K']
        have h : ({x | ¬v = x} : Finset (Fin (d + 1))) = univ \ ({v} : Finset (Fin (d + 1))) := by
          ext x
          simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_singleton, ne_comm, ne_eq]
        simp [h, card_sdiff]
    _ ≤ 1 := hcard.trans <| Nat.cast_le_one.mpr <| IndepNumberClique_eq_one s |>.mp hind

end CaroWeiType
end SimpleGraph
#min_imports
