import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.ABCLemma

import CWType.SimpleGraph.CaroWeiType.Forests.Basic
import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas

open SimpleGraph
open Finset

namespace CaroWeiType

namespace GraphParameter

def BoundedDegreeCaterpillar (k : ℕ) : GraphParameter where
  toFun := fun G s ↦ G.graph.InducesCaterpillar s ∧ ∀ v, G.graph.degree_in s v ≤ k
  invariant := by
    intro V V' _ _ _ _ G G' φ s
    constructor
    · intro ⟨h, hdeg⟩
      refine ⟨InducesCaterpillar_of_iso φ h, ?_⟩
      refine fun φv ↦ le_of_eq_of_le (Eq.symm ?_) (hdeg <| φ.invFun φv)
      have H : (φ.toFun (φ.invFun φv)) = φv := by
        simp only [Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.apply_symm_apply]
      have hobj := @degree_in_eq_of_iso _ _ _ _ _ _ (φ.invFun φv) s φ _ _
      rw [H] at hobj
      exact hobj
    · intro ⟨h, hdeg⟩
      refine ⟨?_, ?_⟩
      · suffices (image φ.symm.toFun (image φ.toFun s)) = s by
          exact this ▸ (InducesCaterpillar_of_iso φ.symm h)
        ext
        simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, mem_image, exists_exists_and_eq_and,
          RelIso.symm_apply_apply, exists_eq_right]
      · exact fun v ↦ le_of_eq_of_le (degree_in_eq_of_iso v s φ) (hdeg <| φ.toFun v)

end GraphParameter

private noncomputable def φ (k : ℕ) (ε : ℝ) : ℕ → ℝ := by
  intro d
  if hd : d = 0 then exact 1
  else if d = 1 then exact 1 - ε
  else if 2 ≤ d ∧ d ≤ k then exact 2 / (d + 1 : ℝ)
  else exact min ((k + 1) * ε) (2 / (d + 1 : ℝ))

@[reducible]
private def _H (n k : ℕ) : SimpleGraph (Fin n × Fin (k + 2)) where
  Adj u v := u ≠ v ∧ ((u.2 = 0 ∧ v.2 = 0) ∨ (u.2 = 0 ∧ u.1 = v.1) ∨ (v.2 = 0 ∧ u.1 = v.1))

private def H (n k : ℕ) : FiniteSimpleGraph (Fin n × Fin (k + 2)) where
  graph := _H n k

private lemma _degree_bound_Hnk {n k : ℕ} (s : Finset (Fin n × Fin (k + 2)))
    (hsd : ∀ x, (_H n k).degree_in s x ≤ k) :
    #s ≤ n * (k + 1) := by
  have : ∀ u : Fin n, ∃ w : Fin (k + 2), ⟨u, w⟩ ∉ s := by
    by_contra
    simp only [not_forall, not_exists, Decidable.not_not] at this
    obtain ⟨x, hx⟩ := this
    suffices k + 1 ≤ (_H n k).degree_in s ⟨x, 0⟩ by grind only
    have : #(@univ (Fin (k + 2)) _ \ {0}) = k + 1 := by
      simp only [card_sdiff, card_univ, Fintype.card_fin, inter_univ, card_singleton,
        Nat.add_one_sub_one]
    rw [← this, degree_in]
    let f : ↥(@univ (Fin (k + 2)) _ \ {0}) → ↥(((_H n k).neighborFinset ⟨x, 0⟩) ∩ s) :=
      fun ⟨w, hw⟩ ↦ ⟨⟨x, w⟩, by grind [mem_neighborFinset]⟩
    suffices Function.Injective f by
      exact card_le_card_of_injective this
    intro ⟨x, hx⟩ ⟨y, hy⟩ hf
    simp only [ne_eq, Subtype.mk.injEq, Prod.mk.injEq, true_and, f] at hf ⊢
    exact hf
  let F : Fin n → (Fin n × Fin (k + 2)) := fun u ↦ ⟨u, this u |>.choose⟩
  have hs : s ⊆ univ \ (univ.image F) := by grind
  refine le_trans (card_le_card hs) ?_
  rw [card_sdiff, inter_univ, card_univ]
  suffices #(@univ (Fin n) _) = #(univ.image F)  by
    simp only [card_univ, Fintype.card_fin, Fintype.card_prod] at this ⊢
    grind
  refine Eq.symm <| card_image_of_injective univ ?_
  intro x y
  simp only [Prod.mk.injEq, and_imp, F]
  exact fun h _ ↦ h

private lemma _bound_fnpk_f1 (n k : ℕ) [NeZero n] (f : ℕ → ℝ)
      (hf : IsCaroWeiTypeLowerBound f (GraphParameter.BoundedDegreeCaterpillar k)) :
    f (n + k) + (k + 1) * f 1 ≤ k + 1 := by
  obtain ⟨s, hs, hcard⟩ := hf (H n k)
  have hcards := @_degree_bound_Hnk n k s hs.2
  have : ∑ v, f ((H n k).graph.degree v) = n * f (n + k) + n * (k + 1) * f 1 := by
    have hcard_ : #(univ.image (⟨·, 0⟩ : Fin n → Fin n × Fin (k + 2))) = n := by
      have : #(univ.image (⟨·, 0⟩ : Fin n → Fin n × Fin (k + 2))) = #(@univ (Fin n) _) := by
        refine card_image_iff.mpr ?_
        intro _ _ _ _ heq
        simp only [Prod.mk.injEq, and_true] at heq
        exact heq
      rw [this, card_univ, Fintype.card_fin]
    rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_mul]
    calc _
      _ = ∑ v ∈ univ \ ({⟨u, 0⟩ | u ∈ univ} : Finset (Fin n × Fin (k + 2))),
              f ((H n k).graph.degree v)
          + ∑ v ∈ ({⟨u, 0⟩ | u ∈ univ} : Finset (Fin n × Fin (k + 2))),
              f ((H n k).graph.degree v) := by
        refine Eq.symm (sum_sdiff ?_)
        intro u
        simp only [inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
          mem_of_singleton_inter_ne_emty, true_and, univ_filter_exists, mem_image, implies_true]
      _ = ∑ v ∈ univ \ ({⟨u, 0⟩ | u ∈ univ} : Finset (Fin n × Fin (k + 2))), f 1
          + ∑ v ∈ ({⟨u, 0⟩ | u ∈ univ} : Finset (Fin n × Fin (k + 2))),
            f ((H n k).graph.degree v) := by
        simp only [add_left_inj]
        refine sum_congr rfl ?_
        intro u
        simp only [inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
          mem_of_singleton_inter_ne_emty, true_and, univ_filter_exists, mem_sdiff, mem_image,
          not_exists]
        intro hu
        have : u.2 ≠ 0 := Ne.symm (fun heq ↦ hu u.1 (congrArg (Prod.mk u.1 ·) heq))
        refine congrArg _ ?_
        rw [← card_singleton (⟨u.1, 0⟩ : Fin n × Fin (k + 2))]
        refine congrArg Finset.card ?_
        ext w
        simp only [H, _H, ne_eq, mem_neighborFinset, mem_singleton]
        grind
      _ = ∑ v ∈ univ \ ({⟨u, 0⟩ | u ∈ univ} : Finset (Fin n × Fin (k + 2))), f 1
          + ∑ v ∈ ({⟨u, 0⟩ | u ∈ univ} : Finset (Fin n × Fin (k + 2))), f (n + k) := by
        simp only [add_right_inj]
        refine sum_congr rfl ?_
        intro u
        simp only [inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
          mem_of_singleton_inter_ne_emty, true_and, univ_filter_exists, mem_image,
          forall_exists_index]
        intro u' hu
        refine congrArg _ ?_
        subst hu
        let S1 := (@univ (Fin n) _ \ {u'}).image (⟨·, 0⟩ : Fin n → Fin n × Fin (k + 2))
        let S2 := (@univ (Fin (k + 2)) _ \ {0}).image (⟨u', ·⟩ : Fin (k + 2) → Fin n × Fin (k + 2))
        have hS12 : S1 ∩ S2 = ∅ := by
          ext
          simp only [mem_inter, notMem_empty, iff_false, not_and, S1, S2]
          grind only [= mem_image, = mem_sdiff, = mem_singleton]
        simp only [H, degree]
        have hNu : (_H n k).neighborFinset ⟨u', 0⟩ = S1 ∪ S2 := by
          ext
          simp only [S1, S2, mem_neighborFinset]
          grind only [= mem_union, = mem_image, = mem_sdiff, ← mem_univ, = mem_singleton]
        have hcardS1 : #S1 = n - 1 := by
          have : #S1 = #(@univ (Fin n) _ \ {u'}) := by
            simp only [S1]
            refine card_image_iff.mpr ?_
            intro _ _ _ _ heq
            simp only [Prod.mk.injEq, and_true] at heq
            exact heq
          rw [this, card_sdiff, inter_univ, card_singleton, card_univ, Fintype.card_fin]
        have hcardS2 : #S2 = k + 1 := by
          have : #S2 = #(@univ (Fin (k + 2)) _ \ {0}) := by
            simp only [S2]
            refine card_image_iff.mpr ?_
            intro _ _ _ _ heq
            simp only [Prod.mk.injEq, true_and] at heq
            exact heq
          rw [this, card_sdiff, inter_univ, card_singleton, card_univ,
            Fintype.card_fin, Nat.add_succ_sub_one]
        rw [hNu, card_union, hS12, card_empty, hcardS1, hcardS2]
        grind only [NeZero.ne n]
      _ = ((n * (k + 1)) : ℕ) * f 1
          + ∑ v ∈ ({⟨u, 0⟩ | u ∈ univ} : Finset (Fin n × Fin (k + 2))), f (n + k) := by
        simp only [add_left_inj]
        rw [sum_const, nsmul_eq_mul, mul_eq_mul_right_iff]
        refine Or.inl ?_
        rw [Nat.cast_inj, card_sdiff, inter_univ, card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_fin]
        suffices #{x : Fin n × Fin (k + 2) | ∃ u ∈ univ, (u, 0) = x} = n by lia
        simp only [inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
          mem_of_singleton_inter_ne_emty, true_and, univ_filter_exists, hcard_]
      _ = ((n * (k + 1)) : ℕ) * f 1
          + n * f (n + k) := by
        simp only [add_right_inj]
        rw [sum_const, nsmul_eq_mul, mul_eq_mul_right_iff]
        refine Or.inl ?_
        rw [Nat.cast_inj]
        simp only [inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
          mem_of_singleton_inter_ne_emty, true_and, univ_filter_exists, hcard_]
    exact add_comm ..
  have := this ▸ hcard.trans (Nat.cast_le.mpr hcards)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this
  have hn : (0 : ℝ) < n := by
    rw [← Nat.cast_zero, Nat.cast_lt]
    exact Nat.pos_of_neZero n
  refine le_of_mul_le_mul_left ?_ hn
  refine le_of_eq_of_le ?_ this
  linarith

universe u in
theorem BoundedDegreeCaterpillar_LowerBound_iff (f : ℕ → ℝ) :
    ∀ k : ℕ, 2 ≤ k →
      (IsCaroWeiTypeLowerBound f (GraphParameter.BoundedDegreeCaterpillar k)
      ↔ ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ 2 / ((k + 1) * (k + 2 : ℝ)) ∧ f ≤ φ k ε) := by
  intro k hk
  constructor
  · intro hf
    have hfle1 : ∀ d, f d ≤ 1 := f_le_1_of_IsCaroWeiTypeLowerBound hf
    have fKn : ∀ d ≥ 2, f d ≤ 2 / (d + 1 : ℝ) := by
      intro d hd
      rw [← Nat.cast_two]
      refine f_on_complete_graph' hf ?_
      intro s hs
      simp only [GraphParameter.BoundedDegreeCaterpillar] at hs
      have hf := InducesForest_of_InducesCaterpillar _ (hs.1)
      refine card_le_2_iff_no_triplet.mpr ?_
      intro x y z hne
      refine no_induced_K3_of_InducesForest _ _ ?_ ?_ ?_ hf
      <;> simp [hne, Ne.symm]
    let ε := 1 - f 1
    have hε_nonneg : 0 ≤ ε := by linarith [hfle1 1]
    if hkε : 2 / ((k + 1) * (k + 2 : ℝ)) ≤ ε then
      refine ⟨2 / ((k + 1) * (k + 2 : ℝ)), ?_, le_refl _, ?_⟩
      · refine div_nonneg zero_le_two <| Left.mul_nonneg ?_ ?_ <;> linarith
      · intro d
        simp only [φ]
        split_ifs
        · exact hfle1 _
        · rename_i hd
          subst hd
          linarith
        · exact fKn d (by linarith)
        · have hkd : k < d := by lia
          simp only [le_inf_iff]
          refine ⟨?_, fKn d (by linarith)⟩
          suffices f d ≤ 2 / (k + 2 : ℝ) by
            exact le_of_le_of_eq this (by grind)
          refine le_trans (fKn d (by linarith)) ?_
          refine (div_le_div_iff_of_pos_left zero_lt_two add_one_pos add_two_pos).mpr ?_
          rw [← Nat.cast_two, ← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.cast_le]
          linarith
    else
      refine ⟨ε, hε_nonneg, le_of_lt <| not_le.mp hkε, ?_⟩
      intro d
      simp only [φ]
      split_ifs
      · exact hfle1 _
      · rename_i hd
        subst hd
        linarith
      · exact fKn _ (by linarith)
      · simp only [le_inf_iff]
        refine ⟨?_, fKn _ (by lia)⟩
        have hkd : k < d := by lia
        have : NeZero (d - k) := NeZero.of_pos <| Nat.zero_lt_sub_of_lt hkd
        have hfs := _bound_fnpk_f1 (d - k) k f hf
        have : d - k + k = d := Nat.sub_add_cancel (le_of_lt hkd)
        rw [this] at hfs
        linarith
  · sorry

end CaroWeiType
