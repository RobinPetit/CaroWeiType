import CWType.SimpleGraph.CaroWeiType.Calc
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.ABLemma

import CWType.SimpleGraph.CaroWeiType.Forests.Basic
import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas

namespace SimpleGraph

private def Λ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  {v | G.degree v = 1}

end SimpleGraph

open SimpleGraph
open Finset

namespace CaroWeiType
open AB

-- @[grind! .]
-- private lemma hdΛ {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
--     v ∈ G.Λ ↔ G.degree v = 1 := by
--   simp only [Λ, mem_filter, mem_univ, true_and]

namespace GraphParameter

def ForestOfStars : GraphParameter where
  toFun := fun G _ s ↦ G.InducesForestOfStars s
  invariant := by
    intro V V' _ _ _ _ G _ G' _ φ s
    constructor
    · exact InducesForestOfStars_of_iso φ
    · intro h
      suffices (image φ.symm.toFun (image φ.toFun s)) = s by
        exact this ▸ (InducesForestOfStars_of_iso φ.symm h)
      ext
      simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, mem_image, exists_exists_and_eq_and,
        RelIso.symm_apply_apply, exists_eq_right]

end GraphParameter

private noncomputable def φ (ε : ℝ) : ℕ → ℝ := by
  intro d
  if hd : d = 0 then exact 1
  else if d = 1 then exact 1 - ε
  else if d = 2 then exact min (1 / (2 : ℝ) + ε) (3 / (5 : ℝ))
  else exact min (1 / (d : ℝ) + ε) (2 / (d + 1 : ℝ))

private lemma φ_le_1 {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) : φ ε d ≤ 1 := by
  if hd0 : d = 0 then
    simp only [φ, hd0, ↓reduceDIte, le_refl]
  else if hd1 : d = 1 then
    simp only [φ, hd1, one_ne_zero, ↓reduceDIte]
    exact sub_le_self 1 hε
  else if hd2 : d = 2 then
    simp only [φ, hd0, hd1]
    simp only [hd2, ↓reduceDIte]
    exact Std.min_le_right.trans (by linarith)
  else
    have : φ ε d ≤ 2 / (d + 1 : ℝ) := by grind [φ]
    refine le_trans this ?_
    refine (div_le_one₀ add_one_pos).mpr ?_
    rw [← Nat.cast_two, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    lia

end CaroWeiType

/-

private lemma φ_decreasing (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 6)
    {d d' : ℕ} (hdd' : d ≤ d') :
    φ ε d' ≤ φ ε d := by
  if heq : d = d' then
    rw [heq]
  else if hd0 : d = 0 then
    exact le_of_le_of_eq (φ_le_1 hε) (by simp only [φ, hd0, ↓reduceDIte])
  else if hd1 : d = 1 then
    simp only [φ, hd1, one_ne_zero, ↓reduceDIte]
    suffices 2 / (d' + 1 : ℝ) ≤ 1 - ε by
      grind
    refine le_trans ?_ (by linarith : 2 / 3 ≤ 1 - ε)
    refine (div_le_div_iff₀ add_one_pos three_pos).mpr ?_
    refine mul_le_mul (le_refl _) ?_ zero_le_three zero_le_two
    rw [← Nat.cast_three, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    lia
  else if hd2 : d = 2 then
    sorry
  else
    have hd'0 : d' ≠ 0 := by lia
    have hd'1 : d' ≠ 1 := by lia
    simp only [φ, hd0, hd'0, hd1, hd'1, ↓reduceDIte]
    have H : 2 / (d' + 1 : ℝ) ≤ 2 / (d + 1 : ℝ) := by
      refine (div_le_div_iff_of_pos_left two_pos add_one_pos add_one_pos).mpr ?_
      simp only [add_le_add_iff_right, Nat.cast_le, hdd']
    grind

@[reducible]
private def H (n k : ℕ) : SimpleGraph (Fin n × Fin (k + 2)) where
  Adj u v := u ≠ v ∧ ((u.2 = 0 ∧ v.2 = 0) ∨ (u.2 = 0 ∧ u.1 = v.1) ∨ (v.2 = 0 ∧ u.1 = v.1))

private lemma _degree_bound_Hnk {n k : ℕ} (s : Finset (Fin n × Fin (k + 2)))
    (hsd : ∀ x ∈ s, (H n k).degree_in s x ≤ k) :
    #s ≤ n * (k + 1) := by
  have : ∀ u : Fin n, ∃ w : Fin (k + 2), ⟨u, w⟩ ∉ s := by
    by_contra
    simp only [not_forall, not_exists, Decidable.not_not] at this
    obtain ⟨x, hx⟩ := this
    suffices k + 1 ≤ (H n k).degree_in s ⟨x, 0⟩ by grind only
    have : #(@univ (Fin (k + 2)) _ \ {0}) = k + 1 := by
      simp only [card_sdiff, card_univ, Fintype.card_fin, inter_univ, card_singleton,
        Nat.add_one_sub_one]
    rw [← this, degree_in]
    let f : ↥(@univ (Fin (k + 2)) _ \ {0}) → ↥(((H n k).neighborFinset ⟨x, 0⟩) ∩ s) :=
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
  have : ∑ v, f ((H n k).degree v) = n * f (n + k) + n * (k + 1) * f 1 := by
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
              f ((H n k).degree v)
          + ∑ v ∈ ({⟨u, 0⟩ | u ∈ univ} : Finset (Fin n × Fin (k + 2))),
              f ((H n k).degree v) := by
        refine Eq.symm (sum_sdiff ?_)
        intro u
        simp only [inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
          mem_of_singleton_inter_ne_emty, true_and, univ_filter_exists, mem_image, implies_true]
      _ = ∑ v ∈ univ \ ({⟨u, 0⟩ | u ∈ univ} : Finset (Fin n × Fin (k + 2))), f 1
          + ∑ v ∈ ({⟨u, 0⟩ | u ∈ univ} : Finset (Fin n × Fin (k + 2))),
            f ((H n k).degree v) := by
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
        simp only [H, ne_eq, mem_neighborFinset, mem_singleton]
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
        have hNu : (H n k).neighborFinset ⟨u', 0⟩ = S1 ∪ S2 := by
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

private lemma _lb_bounded_by_extremal (f : ℕ → ℝ) {k : ℕ} (hk : 2 ≤ k)
    (hf : IsCaroWeiTypeLowerBound f (GraphParameter.BoundedDegreeCaterpillar k)) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ 2 / ((k + 1) * (k + 2 : ℝ)) ∧ f ≤ φ k ε := by
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

variable {V : Type} [Fintype V] [DecidableEq V]

private def _ABC {k : ℕ} (hk : 2 ≤ k) (X : Finset V) (G : SimpleGraph V) [DecidableRel G.Adj] :
    ABC.Tripartition V where
  A := fun x ↦ x ∈ (X \ G.Λ) ∧ G.degree_in G.Λ x ≤ k - 2
  B := fun x ↦ x ∈ (X \ G.Λ) ∧ G.degree_in G.Λ x = k - 1
  C := fun x ↦ x ∈ (X \ G.Λ) ∧ G.degree_in G.Λ x = k
  sound := by grind

instance {k : ℕ} (hk : 2 ≤ k) (X : Finset V) (G : SimpleGraph V) [DecidableRel G.Adj] :
    (_ABC hk X G).Decidable := by
  simp only [_ABC]
  refine { A := ?_, B := ?_, C := ?_ } <;> infer_instance

private lemma ABC'_inter_Λ_empty {k : ℕ} (hk : 2 ≤ k) {X : Finset V}
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    (_ABC hk X G).toFinset ∩ G.Λ = ∅ := by
  ext x
  simp only [mem_inter, notMem_empty, iff_false, not_and]
  intro hx
  rcases ABC.Tripartition.mem_toFinset _ |>.mpr hx with hx | hx | hx
  <;> exact mem_sdiff.mp hx.1 |>.2

private lemma cast_plus_one_pos (n : ℕ) : (0 : ℝ) < (n + 1 : ℕ) := by
  rw [← Nat.cast_zero, Nat.cast_lt]
  exact Nat.zero_lt_succ n

private lemma cast_ne {m n : ℕ} : m ≠ n ↔ (m : ℝ) ≠ (n : ℕ) :=
  not_iff_not.mpr Nat.cast_inj.symm

private lemma _TMP {n : ℕ} (h : 1 ≤ n) :
    (1 : ℝ) - ((n - 1 : ℕ) / (((n + 1) : ℕ) : ℝ)) = 2 / (((n + 1) : ℕ) : ℝ) := by
  have {x : ℝ} (hx : 0 < x) : (1 : ℝ) = x / x := by
    exact Eq.symm <| div_self (Ne.symm <| ne_of_lt hx)
  rw [this <| cast_plus_one_pos n]
  have {x y z : ℝ} : (x / y) - (z / y) = (x - z) / y := by
    ring
  rw [this, ← Nat.cast_sub (le_trans (Nat.sub_le ..) (Nat.le_add_right ..))]
  have H : (n + 1 : ℕ) ≠ (0 : ℝ) := by
    rw [← Nat.cast_zero]
    exact cast_ne.mp (Nat.zero_ne_add_one _).symm
  refine (div_eq_div_iff H H).mpr ?_
  refine (mul_left_inj' H).mpr ?_
  rw [← Nat.cast_two, Nat.cast_inj]
  lia

private lemma _φ_closed_Nv_le_f_Nv_of_deg0 {k : ℕ} (hk : 2 ≤ k) {ε : ℝ} (hε : 0 ≤ ε)
    {G : SimpleGraph V} [DecidableRel G.Adj] {x : V} (X : Finset V)
    (hx : x ∈ (_ABC hk X G).toFinset) (hdx : G.degree x = 0) :
    φ k ε (G.degree x) - #(G.neighborFinset x ∩ G.Λ) * ε
      ≤ ABC.f (G.deleteIncidencesOf G.Λ) (_ABC hk X G) x := by
  have hdx'0 : (G.deleteIncidencesOf G.Λ).degree x = 0 :=
    le_antisymm (le_of_le_of_eq deleteIncidencesOf_degree_le hdx) (Nat.zero_le _)
  simp only [ABC.f0 ((_ABC hk X G).mem_toFinset.mpr hx) hdx'0, φ, hdx, ↓reduceDIte]
  exact sub_le_self _ <| Left.mul_nonneg (Nat.cast_nonneg' _) hε

private lemma _φ_closed_Nv_le_f_Nv_of_2_le_deg_of_deg_le_k {k : ℕ} (hk : 2 ≤ k) {ε : ℝ} (hε : 0 ≤ ε)
    {G : SimpleGraph V} [DecidableRel G.Adj] {x : V} (X : Finset V)
    (hx : x ∈ (_ABC hk X G).toFinset) (hdx : 2 ≤ G.degree x) (hdx' : G.degree x ≤ k) :
    φ k ε (G.degree x) - #(G.neighborFinset x ∩ G.Λ) * ε
      ≤ ABC.f (G.deleteIncidencesOf G.Λ) (_ABC hk X G) x := by
  have H : 2 / (G.degree x + 1 : ℝ) ≤ 5 / 6 := by
    refine le_trans ?_ (by linarith : 2 / (3 : ℝ) ≤ 5 / 6)
    refine (div_le_div_iff₀ add_one_pos three_pos).mpr ?_
    simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
    rw [← Nat.cast_three, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    exact Nat.le_add_of_sub_le hdx
  have H' : 2 / (G.degree x + 1 : ℝ) ≤ 2 / ((G.deleteIncidencesOf G.Λ).degree x + 1 : ℝ) := by
    refine (div_le_div_iff₀ add_one_pos add_one_pos).mpr ?_
    simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀, add_le_add_iff_right, Nat.cast_le]
    exact deleteIncidencesOf_degree_le
  have hdABC' : ∀ x ∈ (_ABC hk X G).toFinset, G.degree x ≠ 1 :=
    fun x hx ↦ not_iff_not.mpr hdΛ |>.mp <| notMem_of_mem_of_empty_inter hx (ABC'_inter_Λ_empty hk)
  have hdx0 : G.degree x ≠ 0 := Nat.ne_zero_of_lt hdx
  simp only [φ, hdx, hdx', hdx0, hdABC' x hx, ↓reduceDIte, true_and]
  rcases (_ABC hk X G).mem_toFinset.mpr hx with hA | hB | hC
  · simp only [ABC.f, hA, ↓reduceDIte, ABC.fA]
    exact le_trans (sub_le_self _ <| Left.mul_nonneg (Nat.cast_nonneg' _) hε) (by grind)
  · simp only [ABC.f, hB, ABC.not_A_of_B, ↓reduceDIte, ABC.fB]
    simp only [_ABC, degree_in] at hB
    have : (G.deleteIncidencesOf G.Λ).degree x = 0 ∨ (G.deleteIncidencesOf G.Λ).degree x = 1 := by
      refine Nat.le_one_iff_eq_zero_or_eq_one.mp ?_
      have : (G.deleteIncidencesOf G.Λ).neighborFinset x = G.neighborFinset x \ G.Λ :=
        deleteIncidencesOf_neighborFinset_eq <| mem_sdiff.mp hB.1 |>.2
      rw [degree, this]
      refine le_of_eq_of_le card_sdiff ?_
      rw [inter_comm G.Λ _, hB.2]
      exact le_of_le_of_eq (Nat.sub_le_sub_right hdx' _)
          (Nat.sub_sub_self (Nat.one_le_of_lt hk))
    rcases this with h | h <;> {
      simp only [h, one_ne_zero, ↓reduceIte]
      exact le_trans (sub_le_self _ <| Left.mul_nonneg (Nat.cast_nonneg' _) hε) (by grind)
    }
  · simp only [ABC.f, hC, ABC.not_A_of_C, ABC.not_B_of_C, ↓reduceDIte, ABC.fC]
    simp only [_ABC, degree_in] at hC
    have : (G.deleteIncidencesOf G.Λ).degree x = 0 := by
      have : (G.deleteIncidencesOf G.Λ).neighborFinset x = G.neighborFinset x \ G.Λ :=
        deleteIncidencesOf_neighborFinset_eq <| mem_sdiff.mp hC.1 |>.2
      rw [degree, this, card_sdiff, inter_comm G.Λ _, hC.2]
      exact Nat.sub_eq_zero_of_le hdx'
    simp only [this, ↓reduceIte]
    exact le_trans (sub_le_self _ <| Left.mul_nonneg (Nat.cast_nonneg' _) hε) (by grind)

private lemma _φ_closed_Nv_le_f_Nv_of_2_le_deg_of_kp1_le_deg_of_min_right_of_B_or_C
    {k : ℕ} (hk : 2 ≤ k) {ε : ℝ} (hε : 0 ≤ ε)
    {G : SimpleGraph V} [DecidableRel G.Adj] {x : V} (X : Finset V)
    (hdx : 2 ≤ G.degree x) (hdx' : ¬G.degree x ≤ k)
    (hle : (2 / 3) / (G.degree x + 1 : ℝ) ≤ ε)
    (hBorC : (_ABC hk X G).B x ∨ (_ABC hk X G).C x) :
    φ k ε (G.degree x) - #(G.neighborFinset x ∩ G.Λ) * ε
      ≤ ABC.f (G.deleteIncidencesOf G.Λ) (_ABC hk X G) x := by
  obtain ⟨hdx0, hdx1⟩ : G.degree x ≠ 0 ∧ G.degree x ≠ 1 := by lia
  have hA : ¬(_ABC hk X G).A x := hBorC.elim ABC.not_A_of_B ABC.not_A_of_C
  simp only [φ, hdx0, hdx1, ↓reduceDIte, hdx', and_false, ABC.f, hA]
  calc _
    _ ≤ (2 / (↑(G.degree x) + 1)) - #(G.neighborFinset x ∩ G.Λ) * ε := by
      simp only [tsub_le_iff_right, sub_add_cancel, inf_le_right]
  split_ifs
  · rename_i hB
    simp only [ABC.fB]
    simp only [_ABC, degree_in] at hB
    rw [hB.2]
    calc _
      _ ≤ 2 / (↑(G.degree x) + 1) - (k - 1 : ℕ) * ((2 / 3) / (G.degree x + 1 : ℝ)) := by
        refine tsub_le_tsub (le_refl _) ?_
        exact mul_le_mul_of_nonneg (le_refl _) hle (Nat.cast_nonneg' _) hε
      _ ≤ 2 / (↑(G.degree x) + 1) - ((2 / 3) / (G.degree x + 1 : ℝ)) := by
        refine tsub_le_tsub (le_refl _) ?_
        refine le_of_eq_of_le (one_mul _).symm ?_
        refine mul_le_mul_of_nonneg ?_ (le_refl _) zero_le_one ?_
        · rw [← Nat.cast_one, Nat.cast_le]
          lia
        · exact div_nonneg zero_le_two_thirds add_one_nonneg
      _ = (4 / 3) / (G.degree x + 1 : ℝ) := by
        rw [div_sub_div_same]
        exact (div_left_inj' <| Nat.cast_add_one_ne_zero _).mpr (by linarith)
    if hdx' : (G.deleteIncidencesOf G.Λ).degree x ≤ 1 then
      suffices (4 / 3) / (G.degree x + 1 : ℝ) ≤ 5 / 6 by
        grind
      refine le_trans ?_ (by linarith : (4 / 3) / (3 : ℝ) ≤ 5 / 6)
      refine (div_le_div_iff₀ add_one_pos three_pos).mpr ?_
      refine mul_le_mul (le_refl _) ?_ zero_le_three zero_le_four_thirds
      rw [← Nat.cast_three, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
      linarith
    else if hdx' : (G.deleteIncidencesOf G.Λ).degree x = 2 then
      suffices (4 / 3) / (G.degree x + 1 : ℝ) ≤ 1 / 3 by
        grind
      rw [← div_mul_eq_div_div, mul_comm, div_mul_eq_div_div]
      refine (div_le_div_iff_of_pos_right three_pos).mpr ?_
      refine (div_le_one₀ add_one_pos).mpr ?_
      rw [← Nat.cast_four, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
      suffices 3 ≤ G.degree x by linarith
      have : #(G.neighborFinset x \ G.Λ) = (G.deleteIncidencesOf G.Λ).degree x := by
        refine congrArg Finset.card ?_
        exact Eq.symm <| deleteIncidencesOf_neighborFinset_eq <| mem_sdiff.mp (hB.1) |>.2
      rw [degree, ← card_inter_add_card_sdiff _ G.Λ, hB.2, this, hdx']
      lia
    else
      suffices (4 / 3) / (G.degree x + 1 : ℝ)
          ≤ (4 / 3) / ((G.deleteIncidencesOf G.Λ).degree x + 1 : ℝ) by
        grind
      refine (div_le_div_iff₀ add_one_pos add_one_pos).mpr ?_
      refine mul_le_mul_of_nonneg (le_refl _) ?_ zero_le_four_thirds add_one_nonneg
      simp only [add_le_add_iff_right, Nat.cast_le, deleteIncidencesOf_degree_le]
  · rename_i hC
    simp only [ABC.fC]
    simp only [_ABC, degree_in] at hC
    rw [hC.2]
    calc _
      _ ≤ 2 / (↑(G.degree x) + 1) - k * ((2 / 3) / (G.degree x + 1 : ℝ)) := by
        refine tsub_le_tsub (le_refl _) ?_
        exact mul_le_mul_of_nonneg (le_refl _) hle (Nat.cast_nonneg' _) hε
      _ ≤ 2 / (↑(G.degree x) + 1) - 2 * ((2 / 3) / (G.degree x + 1 : ℝ)) := by
        refine tsub_le_tsub (le_refl _) ?_
        refine mul_le_mul_of_nonneg ?_ (le_refl _) zero_le_two ?_
        · rw [← Nat.cast_two, Nat.cast_le]
          exact hk
        · exact div_nonneg zero_le_two_thirds add_one_nonneg
      _ ≤ 2 / (↑(G.degree x) + 1) - ((4 / 3) / (G.degree x + 1 : ℝ)) := by
        refine tsub_le_tsub (le_refl _) ?_
        rw [mul_comm, div_mul_eq_mul_div]
        refine (div_le_div_iff_of_pos_right add_one_pos).mpr <| by linarith
      _ = (2 / 3) / (G.degree x + 1 : ℝ) := by
        rw [div_sub_div_same]
        exact (div_left_inj' <| Nat.cast_add_one_ne_zero _).mpr (by linarith)
    have H : G.degree x = (G.deleteIncidencesOf G.Λ).degree x + k := by
      rw [degree, degree, deleteIncidencesOf_neighborFinset_eq (mem_sdiff.mp (hC.1) |>.2), ← hC.2]
      exact Eq.symm <| card_sdiff_add_card_inter ..
    if hdx' : (G.deleteIncidencesOf G.Λ).degree x = 0 then
      grind
    else if hdx' : (G.deleteIncidencesOf G.Λ).degree x ≤ 2 then
      suffices (2 / 3) / (G.degree x + 1 : ℝ) ≤ 1 / 6 by
        grind
      rw [← div_mul_eq_div_div]
      refine le_trans ?_ (by linarith : 2 / (3 * (4 : ℝ)) ≤ 1 / 6)
      refine div_le_div_of_nonneg_left zero_le_two (by linarith) ?_
      refine PosMulMono.mul_le_mul_of_nonneg_left zero_le_three ?_
      rw [← Nat.cast_four, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le, H]
      linarith
    else
      suffices (2 / 3) / (G.degree x + 1 : ℝ)
          ≤ (2 / 3) / ((G.deleteIncidencesOf G.Λ).degree x + 1 : ℝ) by
        grind
      refine (div_le_div_iff₀ add_one_pos add_one_pos).mpr ?_
      refine mul_le_mul_of_nonneg (le_refl _) ?_ zero_le_two_thirds add_one_nonneg
      simp only [add_le_add_iff_right, Nat.cast_le, deleteIncidencesOf_degree_le]
  · rename_i hB hC
    refine (?_ : False).elim
    simp only [hB, hC, false_or] at hBorC

private lemma _φ_closed_Nv_le_f_Nv_of_2_le_deg_of_kp1_le_deg_of_min_left_of_B_or_C
    {k : ℕ} (hk : 2 ≤ k) {ε : ℝ} (hε' : ε ≤ 2 / ((k + 1) * (k + 2 : ℝ)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {x : V} (X : Finset V)
    (hdx : 2 ≤ G.degree x) (hdx' : ¬G.degree x ≤ k)
    (hle : ε < (2 / 3) / (↑(G.degree x) + 1))
    (hBorC : (_ABC hk X G).B x ∨ (_ABC hk X G).C x) :
    φ k ε (G.degree x) - #(G.neighborFinset x ∩ G.Λ) * ε
      ≤ ABC.f (G.deleteIncidencesOf G.Λ) (_ABC hk X G) x := by
  have Hε : ε ≤ 1 / 6 := by
    refine le_trans hε' ?_
    refine le_trans ?_ (by linarith : 2 / ((3 : ℝ) * 4) ≤ 1 / 6)
    refine div_le_div_of_nonneg_left zero_le_two (by linarith) ?_
    refine mul_le_mul ?_ ?_ zero_le_four add_one_nonneg
    · rw [← Nat.cast_three, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
      linarith
    · rw [← Nat.cast_four, ← Nat.cast_two, ← Nat.cast_add, Nat.cast_le]
      linarith
  obtain ⟨hdx0, hdx1⟩ : G.degree x ≠ 0 ∧ G.degree x ≠ 1 := by lia
  have hA : ¬(_ABC hk X G).A x := hBorC.elim ABC.not_A_of_B ABC.not_A_of_C
  simp only [φ, hdx0, hdx1, ↓reduceDIte, hdx', and_false, ABC.f, hA]
  calc _
    _ ≤ ((k + 1) * ε) - #(G.neighborFinset x ∩ G.Λ) * ε := by
      simp only [tsub_le_iff_right, sub_add_cancel, inf_le_left]
    _ = ((k + 1 : ℝ) - #(G.neighborFinset x ∩ G.Λ)) * ε := by
      exact Eq.symm <| sub_mul ..
  split_ifs
  · rename_i hB
    simp only [ABC.fB]
    simp only [_ABC, degree_in] at hB
    rw [hB.2]
    calc _
      _ = 2 * ε := by
        refine mul_eq_mul_right_iff.mpr <| Or.inl ?_
        rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_two,
          ← Nat.cast_sub (le_trans (Nat.sub_le ..) (Nat.le_add_right ..)), Nat.cast_inj]
        lia
    if hdx' : (G.deleteIncidencesOf G.Λ).degree x ≤ 2 then
      suffices 2 * ε ≤ 1 / 3 by grind
      linarith
    else
      suffices 2 * ε ≤ (4 / 3) / (((G.deleteIncidencesOf G.Λ).degree x) + 1 : ℝ) by
        grind
      calc 2 * ε
        _ ≤ 2 * ((2 / 3) / (G.degree x + 1 : ℝ)) := by
          refine le_of_lt ?_
          linarith
        _ ≤ ((4 / 3) / (G.degree x + 1 : ℝ)) := by
          lia
      refine (div_le_div_iff₀ add_one_pos add_one_pos).mpr ?_
      refine mul_le_mul (le_refl _) ?_ add_one_nonneg zero_le_four_thirds
      simp only [add_le_add_iff_right, Nat.cast_le, deleteIncidencesOf_degree_le]
  · rename_i hC
    simp only [ABC.fC]
    simp only [_ABC, degree_in] at hC
    rw [hC.2]
    calc _
      _ = ε := by
        refine mul_left_eq_self₀.mpr <| Or.inl (by linarith)
    if hdx' : (G.deleteIncidencesOf G.Λ).degree x ≤ 2 then
      suffices ε ≤ 1 / 6 by grind
      linarith
    else
      suffices ε ≤ (2 / 3) / (((G.deleteIncidencesOf G.Λ).degree x) + 1 : ℝ) by
        grind
      calc ε
        _ ≤ ((2 / 3) / (G.degree x + 1 : ℝ)) := by
          refine le_of_lt ?_
          linarith
      refine (div_le_div_iff₀ add_one_pos add_one_pos).mpr ?_
      refine mul_le_mul (le_refl _) ?_ add_one_nonneg zero_le_two_thirds
      simp only [add_le_add_iff_right, Nat.cast_le, deleteIncidencesOf_degree_le]
  · rename_i hB hC
    refine (?_ : False).elim
    simp only [hB, hC, false_or] at hBorC

private lemma _φ_closed_Nv_le_f_Nv {k : ℕ} (hk : 2 ≤ k)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 2 / ((k + 1) * (k + 2 : ℝ)))
    {G : SimpleGraph V} [DecidableRel G.Adj] {x : V} (X : Finset V)
    (hx : x ∈ (_ABC hk X G).toFinset) :
    φ k ε (G.degree x) - #(G.neighborFinset x ∩ G.Λ) * ε
      ≤ ABC.f (G.deleteIncidencesOf G.Λ) (_ABC hk X G) x := by
  have hdABC' : ∀ x ∈ (_ABC hk X G).toFinset, G.degree x ≠ 1 :=
    fun x hx ↦ not_iff_not.mpr hdΛ |>.mp <| notMem_of_mem_of_empty_inter hx (ABC'_inter_Λ_empty hk)
  if hdx0 : G.degree x = 0 then
    exact _φ_closed_Nv_le_f_Nv_of_deg0 hk hε X hx hdx0
  else
    have hdx2 : 2 ≤ G.degree x := by grind
    if hA : (_ABC hk X G).A x then
      simp only [ABC.f, hA, ↓reduceDIte, ABC.fA]
      calc _
        _ ≤ φ k ε (G.degree x) := by
          refine sub_le_self _ <| Left.mul_nonneg (Nat.cast_nonneg' _) hε
        _ ≤ 2 / (G.degree x + 1 : ℝ) := by
          simp only [φ, hdx0, hdABC' x hx, ↓reduceDIte]
          grind
      have : 2 / (G.degree x + 1 : ℝ) ≤ 5 / 6 := by
        refine le_trans ?_ (by linarith : 2 / (3 : ℝ) ≤ 5 / 6)
        refine div_le_div_of_nonneg_left zero_le_two three_pos ?_
        rw [← Nat.cast_three, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
        linarith
      split_ifs
      · refine le_trans this (by linarith)
      · exact this
      · refine div_le_div_of_nonneg_left zero_le_two add_one_pos ?_
        simp only [add_le_add_iff_right, Nat.cast_le, deleteIncidencesOf_degree_le]
    else
      have hBorC : (_ABC hk X G).B x ∨ (_ABC hk X G).C x := by
        simp only [← ABC.Tripartition.mem_toFinset, ABC.Tripartition.mem_iff, hA, false_or] at hx
        exact hx
      if hdx_le_k : G.degree x ≤ k then
        exact _φ_closed_Nv_le_f_Nv_of_2_le_deg_of_deg_le_k hk hε X hx hdx2 hdx_le_k
      else if hdvε : (2 / 3) / (G.degree x + 1 : ℝ) ≤ ε then
        exact _φ_closed_Nv_le_f_Nv_of_2_le_deg_of_kp1_le_deg_of_min_right_of_B_or_C
          hk hε X hdx2 hdx_le_k hdvε hBorC
      else
        refine _φ_closed_Nv_le_f_Nv_of_2_le_deg_of_kp1_le_deg_of_min_left_of_B_or_C
          hk hε' X hdx2 hdx_le_k (not_le.mp hdvε) hBorC

private lemma _f_is_lb_of_degree_in_Λ_le_k {k : ℕ} (hk : 2 ≤ k)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 2 / ((k + 1) * (k + 2 : ℝ)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    (hX : G.support ⊆ X) (h : ¬∃ v ∈ X, k + 1 ≤ G.degree_in G.Λ v)
    (hΛ : ¬∃ x y, G.degree x = 1 ∧ G.degree y = 1 ∧ G.Adj x y) :
    ∃ s ⊆ X, G.InducesCaterpillar s
      ∧ (∀ v ∈ s, G.degree_in s v ≤ k) ∧ ∑ v ∈ X, φ k ε (G.degree v) ≤ #s := by
  have hABCX : (X \ G.Λ) = (_ABC hk X G).toFinset := by
    ext u
    constructor
    · intro huX
      simp only [← (_ABC ..).mem_toFinset, ABC.Tripartition.mem_iff]
      simp only [_ABC]
      grind
    · intro hu
      simp only [← (_ABC ..).mem_toFinset, ABC.Tripartition.mem_iff] at hu
      rcases hu with hu | hu | hu <;> exact hu.1
  obtain ⟨s, hs, hsf, hsresp, heval⟩ := by
    refine ABC.ABCLemma (G.deleteIncidencesOf G.Λ) (_ABC hk X G) ?_
    intro u hu
    simp only [← hABCX, coe_sdiff, Set.mem_diff, SetLike.mem_coe] at hu ⊢
    obtain ⟨husupp, huΛ⟩ := Set.mem_diff _ |>.mp <| deleteIncidencesOf_support_subset hu
    refine ⟨hX husupp, huΛ⟩
  simp only [ABC.eval] at heval
  have hscapΛ : s ∩ G.Λ = ∅ := by grind
  refine ⟨s ∪ G.Λ, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases mem_union.mp hx with hxs | hxΛ
    · exact mem_sdiff.mp (hABCX ▸ hs hxs) |>.1
    · exact hX <| (degree_pos_iff_mem_support G x).mp <| Nat.lt_of_sub_eq_succ (hdΛ.mp hxΛ)
  · refine InducesCaterpillar_union_deg_le_1 G ?_ ?_
    · exact fun x hx ↦ le_of_eq <| hdΛ.mp hx
    · refine (_ABC ..).linear_forest_of_forest_respects hs ?_ ?_
      · exact InducesForest_graph_mono' (by grind) hsf
      · have : (_ABC hk X G) = ((_ABC hk X G) \ G.Λ) := by
          simp only [_ABC]
          ext x <;> {
            simp only [mem_sdiff, degree_in, ABC.Tripartition.sdiff, iff_self_and, and_imp]
            exact fun _ h _ ↦ h
          }
        refine (_ABC ..).respects_mono G ?_ (this ▸ hsresp)
        intro x hx
        exact ABC.Tripartition.mem_toFinset _ |>.mp (this ▸ ((_ABC ..).mem_toFinset.mpr <| hs hx))
  · intro v hv
    rcases mem_union.mp hv with hv | hv
    · refine le_of_eq_of_le (degree_in_union_of_empty_inter <| by grind) ?_
      simp only [ABC.Tripartition.respects] at hsresp
      rcases (_ABC ..).mem_toFinset.mpr <| hs hv with hA | hB | hC
      · have : G.degree_in s v ≤ 2 := by
          refine le_of_eq_of_le ?_ (hsresp v hv |>.1 hA)
          refine Eq.symm <| degree_in_deleteIncidencesOf s G.Λ (inter_comm s G.Λ ▸ hscapΛ) ?_
          exact notMem_of_mem_of_empty_inter hv hscapΛ
        grind [_ABC]
      · have : G.degree_in s v ≤ 1 := by
          refine le_of_eq_of_le ?_ (hsresp v hv |>.2.1 hB)
          refine Eq.symm <| degree_in_deleteIncidencesOf s G.Λ (inter_comm s G.Λ ▸ hscapΛ) ?_
          exact notMem_of_mem_of_empty_inter hv hscapΛ
        grind [_ABC]
      · have : G.degree_in s v = 0 := by
          refine Eq.trans ?_ (hsresp v hv |>.2.2 hC)
          refine Eq.symm <| degree_in_deleteIncidencesOf s G.Λ (inter_comm s G.Λ ▸ hscapΛ) ?_
          exact notMem_of_mem_of_empty_inter hv hscapΛ
        grind [_ABC]
    · refine le_trans degree_in_le_degree <| le_of_eq_of_le (hdΛ.mp hv) (Nat.one_le_of_lt hk)
  · have hX' : X = (_ABC hk X G).toFinset ∪ G.Λ := by
      rw [← hABCX]
      suffices G.Λ ⊆ X by grind
      refine fun x hx ↦ hX <| degree_pos_iff_mem_support .. |>.mp ?_
      exact Nat.lt_of_sub_eq_succ (hdΛ.mp hx)
    rw [hX']
    let g : V → Finset V := by
      intro u
      if u ∈ (_ABC hk X G).toFinset then
        exact {u} ∪ (G.neighborFinset u ∩ G.Λ)
      else
        exact ∅
    have h : (_ABC hk X G).toFinset.sup g = ((_ABC hk X G).toFinset ∪ G.Λ) := by
      ext u
      constructor
      · intro hu
        simp only [mem_sup, mem_union] at hu ⊢
        obtain ⟨w, hw, hugw⟩ := hu
        simp only [g, hw, ↓reduceDIte, mem_union, mem_singleton, mem_inter] at hugw
        rcases hugw with huw | hu
        · exact Or.inl <| huw ▸ hw
        · exact Or.inr hu.2
      · intro hu
        simp only [mem_union, mem_sup] at hu ⊢
        rcases hu with hu | hu
        · exact ⟨u, hu, by simp only [g, hu, ↓reduceDIte, mem_union, mem_singleton, true_or]⟩
        · obtain ⟨w, huw⟩ := degree_eq_one_iff_existsUnique_adj.mp (hdΛ.mp hu) |>.exists
          refine ⟨w, hABCX ▸ ?_, ?_⟩
          · refine mem_sdiff.mpr ⟨hX <| (mem_support G).mpr ⟨u, huw.symm⟩, ?_⟩
            simp only [mem_filter, inter_univ, ne_eq, singleton_ne_empty, not_false_eq_true,
              mem_of_singleton_inter_ne_emty, true_and, Λ]
            refine (hΛ ⟨u, w, hdΛ.mp hu, ·, huw⟩)
          · have : w ∈ (_ABC hk X G).toFinset := by
              have hw := hX' ▸ (mem_def.mpr <| hX <| G.mem_support.mpr ⟨u, huw.symm⟩)
              rcases mem_union.mp hw with hw | hw
              · exact hw
              · exact hΛ ⟨u, w, hdΛ.mp hu, hdΛ.mp hw, huw⟩ |>.elim
            simp only [g, this, ↓reduceDIte]
            exact mem_union_right _ (mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr huw.symm, hu⟩)
    have hgdisjoint : ∀ x y, x ≠ y → g x ∩ g y = ∅ := by
      intro x y hne
      simp only [g]
      if H : x ∈ (_ABC hk X G).toFinset ∧ y ∈ (_ABC hk X G).toFinset then
        simp only [H.1, H.2, ↓reduceDIte]
        ext z
        simp only [singleton_union, mem_inter, mem_insert, mem_neighborFinset, notMem_empty,
          iff_false, not_and, not_or]
        intro h
        rcases h with h | ⟨h, h'⟩
        · subst h
          refine ⟨hne, fun _ ↦ ?_⟩
          refine notMem_of_mem_of_empty_inter H.1 (by grind)
        · simp only [h', not_true_eq_false, imp_false]
          refine ⟨?_, ?_⟩
          · refine ne_of_mem_of_not_mem h' (by grind)
          · refine not_adj_symm <| not_iff_not.mpr (G.mem_neighborFinset ..) |>.mp ?_
            rw [neighborFinset_eq_of_deg_eq_one_of_adj (hdΛ.mp h') h.symm]
            exact notMem_singleton.mpr hne.symm
      else
        grind
    have hdABC' : ∀ x ∈ (_ABC hk X G).toFinset, G.degree x ≠ 1 :=
      fun x hx ↦ not_iff_not.mpr hdΛ |>.mp <| mem_sdiff.mp (hABCX ▸ hx) |>.2
    rw [split_sum _ _ h hgdisjoint]
    clear h hgdisjoint
    calc _
      _ = ∑ x ∈ (_ABC hk X G).toFinset,
          (φ k ε (G.degree x) + ∑ y ∈ G.neighborFinset x ∩ G.Λ, φ k ε (G.degree y)) := by
        refine sum_congr rfl ?_
        intro x hx
        rw [← sum_singleton (fun v ↦ φ k ε (G.degree v)) x, ← sum_union]
        · refine sum_congr ?_ fun _ _ ↦ rfl
          simp only [g, hx, ↓reduceDIte]
        · refine disjoint_iff_inter_eq_empty.mpr <| singleton_inter_of_notMem ?_
          exact inter_subset_left.mt <| G.notMem_neighborFinset_self x
      _ = ∑ x ∈ (_ABC hk X G).toFinset,
          (φ k ε (G.degree x) + ∑ y ∈ G.neighborFinset x ∩ G.Λ, φ k ε 1) := by
        refine sum_congr rfl fun x hx ↦ ?_
        simp only [add_right_inj]
        refine sum_congr rfl fun y hy ↦ ?_
        refine congrArg _ (hdΛ.mp (mem_inter.mp hy |>.2))
      _ = ∑ x ∈ (_ABC hk X G).toFinset,
          (φ k ε (G.degree x) + ∑ y ∈ G.neighborFinset x ∩ G.Λ, (1 - ε)) := by
        rfl
      _ = ∑ x ∈ (_ABC hk X G).toFinset, (φ k ε (G.degree x) + (∑ y ∈ G.neighborFinset x ∩ G.Λ, 1
              - ∑ y ∈ G.neighborFinset x ∩ G.Λ, ε)) := by
        exact sum_congr rfl fun x hx ↦ add_right_inj _ |>.mpr <| sum_sub_distrib ..
      _ = ∑ x ∈ (_ABC hk X G).toFinset, ((φ k ε (G.degree x) - ∑ y ∈ G.neighborFinset x ∩ G.Λ, ε)
            + ∑ y ∈ G.neighborFinset x ∩ G.Λ, 1) := by
        exact sum_congr rfl fun x hx ↦ by ring
      _ = ∑ x ∈ (_ABC hk X G).toFinset, (φ k ε (G.degree x) - ∑ y ∈ G.neighborFinset x ∩ G.Λ, ε)
            + ∑ x ∈ (_ABC hk X G).toFinset, ∑ y ∈ G.neighborFinset x ∩ G.Λ, 1 := by
        exact sum_add_distrib
      _ = ∑ x ∈ (_ABC hk X G).toFinset, (φ k ε (G.degree x) - #(G.neighborFinset x ∩ G.Λ) * ε)
            + ∑ x ∈ (_ABC hk X G).toFinset, ∑ y ∈ G.neighborFinset x ∩ G.Λ, 1 := by
        refine add_left_inj _ |>.mpr ?_
        refine sum_congr rfl fun x hx ↦ ?_
        rw [sum_const' fun _ _ ↦ rfl]
      _ ≤ ∑ x ∈ (_ABC hk X G).toFinset, ABC.f (G.deleteIncidencesOf G.Λ) (_ABC hk X G) x
            + ∑ x ∈ (_ABC hk X G).toFinset, ∑ y ∈ G.neighborFinset x ∩ G.Λ, 1 := by
        refine add_le_add_left ?_ _
        refine sum_le_sum fun x hx ↦ _φ_closed_Nv_le_f_Nv hk hε hε' X hx
      _ ≤ #s + ∑ x ∈ (_ABC hk X G).toFinset, ∑ y ∈ G.neighborFinset x ∩ G.Λ, 1 := by
        exact add_le_add heval (le_refl _)
    suffices ∑ x ∈ (_ABC hk X G).toFinset, ∑ y ∈ G.neighborFinset x ∩ G.Λ, (1 : ℝ) = #G.Λ by
      clear * - this hscapΛ
      rw [card_union, hscapΛ, card_empty, tsub_zero, Nat.cast_add, ← this]
    let g : V → Finset V := by
      intro x
      if x ∈ (_ABC hk X G).toFinset then
        exact G.neighborFinset x ∩ G.Λ
      else
        exact ∅
    have hgdisjoint : ∀ x y, x ≠ y → g x ∩ g y = ∅ := by
      intro x y hne
      simp only [g]
      if hxy : x ∈ (_ABC hk X G).toFinset ∧ y ∈ (_ABC hk X G).toFinset then
        obtain ⟨hx, hy⟩ := hxy
        simp only [hx, hy, ↓reduceDIte]
        ext u
        simp only [inter_assoc, mem_inter, mem_neighborFinset, notMem_empty, iff_false, not_and]
        intro hxu _ hyu
        refine not_iff_not.mpr hdΛ |>.mpr ?_
        suffices 2 ≤ G.degree u by exact Nat.ne_of_lt' this
        have : #({x, y} : Finset _) = 2 := card_pair hne
        rw [← this]
        exact card_le_card <| fun w hw ↦ mem_neighborFinset .. |>.mpr <| Adj.symm <| by grind
      else
        grind
    have h : (_ABC hk X G).toFinset.sup g = G.Λ := by
      ext u
      constructor
      · intro hu
        simp only [mem_sup] at hu
        obtain ⟨w, hw, hugw⟩ := hu
        simp only [g, hw, ↓reduceDIte] at hugw
        exact mem_inter.mp hugw |>.2
      · intro hu
        simp only [hdΛ] at hu
        obtain ⟨w, huw⟩ : ∃ w, G.Adj u w := degree_eq_one_iff_existsUnique_adj.mp hu |>.exists
        have hw : w ∈ (_ABC hk X G).toFinset := by
          have := (mem_def.mpr <| hX <| G.mem_support.mpr ⟨u, huw.symm⟩)
          rcases mem_union.mp (hX' ▸ this) with hw | hw
          · exact hw
          · exact hΛ ⟨u, w, hu, hdΛ.mp hw, huw⟩ |>.elim
        refine mem_sup.mpr ⟨w, hw, ?_⟩
        simp only [g, hw, ↓reduceDIte]
        exact mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr huw.symm, hdΛ.mpr hu⟩
    calc ∑ x ∈ (_ABC hk X G).toFinset, ∑ y ∈ G.neighborFinset x ∩ G.Λ, (1 : ℝ)
      _ = ∑ x ∈ (_ABC hk X G).toFinset, ∑ y ∈ g x, 1 := by
        refine sum_congr rfl (fun x hx ↦ sum_congr ?_ fun _ _ ↦ rfl)
        simp only [g, hx, ↓reduceDIte]
      _ = ∑ x ∈ G.Λ, 1 := by
        exact Eq.symm <| split_sum _ _ h hgdisjoint
    exact Eq.symm (cast_card G.Λ)

private lemma _f_is_lb {k : ℕ} (hk : 2 ≤ k)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 2 / ((k + 1) * (k + 2 : ℝ)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (hX : G.support ⊆ X) :
    ∃ s ⊆ X, G.InducesCaterpillar s
      ∧ (∀ v ∈ s, G.degree_in s v ≤ k) ∧ ∑ v ∈ X, φ k ε (G.degree v) ≤ ↑(#s) := by
  if h : ∃ v ∈ X, k + 1 ≤ G.degree_in G.Λ v then
    obtain ⟨v, hvX, hdv⟩ := h
    obtain ⟨s, hs, ⟨hsf, hsbd⟩, hsdeg, hscard⟩ :=
      _f_is_lb hk hε hε' (G.deleteIncidencesOf {v}) (X \ {v}) ( deleteIncidencesOf_support hX)
    have hvs : v ∉ s := fun hvs ↦ false_of_ne <| notMem_singleton.mp <| mem_sdiff.mp (hs hvs) |>.2
    refine ⟨s, subset_eq_inter hs, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · refine @InducesForest_graph_mono' _ _ _ G _ _ {v} ?_ ?_
        · refine inter_singleton_of_notMem ?_
          simp only [mem_sdiff, mem_filter, hvs, false_and, not_false_eq_true]
        · refine InducesForest_mono ?_ hsf
          intro u hu
          simp only [mem_sdiff, mem_filter] at hu ⊢
          obtain ⟨hus, hu⟩ := hu
          simp only [hus, true_and] at hu ⊢
          refine ne_of_eq_of_ne ?_ hu
          refine degree_in_deleteIncidencesOf _ _ ?_ ?_
          · exact singleton_inter_of_notMem hvs
          · exact notMem_singleton.mpr <| ne_of_mem_of_not_mem hus hvs
      · intro x hx
        simp only [mem_sdiff, mem_filter] at hx ⊢
        obtain ⟨hxs, hx⟩ := hx
        simp only [hxs, true_and] at hx
        refine le_of_eq_of_le ?_ (hsbd x ?_)
        · refine congrArg Finset.card ?_
          ext u
          simp only [degree_in, mem_inter, mem_neighborFinset, mem_sdiff, mem_filter, not_and]
          constructor
          · intro ⟨hxu, hus, hu⟩
            simp only [hus, forall_const, true_and] at hu ⊢
            refine ⟨?_, ?_⟩
            · refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ hxu
              · exact notMem_singleton.mpr <| ne_of_mem_of_not_mem hxs hvs
              · exact notMem_singleton.mpr <| ne_of_mem_of_not_mem hus hvs
            · refine ne_of_eq_of_ne ?_ hu
              refine congrArg Finset.card ?_
              ext w
              simp only [mem_inter, mem_neighborFinset, and_congr_left_iff]
              refine fun hws ↦ ⟨adj_of_deleteIncidencesOf_adj, ?_⟩
              intro huw
              refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ huw
              · exact notMem_singleton.mpr <| ne_of_mem_of_not_mem hus hvs
              · exact notMem_singleton.mpr <| ne_of_mem_of_not_mem hws hvs
          · intro ⟨hxu, hus, hu⟩
            simp only [hus, forall_const, true_and] at hu ⊢
            refine ⟨?_, ?_⟩
            · exact adj_of_deleteIncidencesOf_adj hxu
            · refine ne_of_eq_of_ne ?_ hu
              refine congrArg Finset.card ?_
              ext w
              simp only [mem_inter, mem_neighborFinset, and_congr_left_iff]
              refine fun hws ↦ ⟨?_, adj_of_deleteIncidencesOf_adj⟩
              intro huw
              refine deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj ?_ ?_ huw
              · exact notMem_singleton.mpr <| ne_of_mem_of_not_mem hus hvs
              · exact notMem_singleton.mpr <| ne_of_mem_of_not_mem hws hvs
        · simp only [mem_sdiff, mem_filter, hxs, true_and] at ⊢
          refine ne_of_eq_of_ne ?_ hx
          refine degree_in_deleteIncidencesOf _ _ ?_ ?_
          · exact singleton_inter_of_notMem hvs
          · refine notMem_singleton.mpr <| ne_of_mem_of_not_mem hxs hvs
    · intro w hw
      refine le_of_eq_of_le ?_ (hsdeg w hw)
      refine Eq.symm <| degree_in_deleteIncidencesOf _ _ ?_ ?_
      · exact singleton_inter_of_notMem hvs
      · exact notMem_singleton.mpr (ne_of_mem_of_not_mem hw hvs)
    · refine le_trans ?_ hscard
      have hv : v ∈ X := by grind
      have hNv : G.neighborFinset v ⊆ X := by
        intro u hu
        refine mem_def.mpr <| hX <| G.mem_support.mpr ⟨v, ?_⟩
        refine Adj.symm <| mem_neighborFinset .. |>.mp hu
      rw [sum_sdiff_singleton' hv hNv]
      have {a b c : ℝ} (h : b + c ≤ 0) : a + b + c ≤ a := by grind
      refine this ?_
      calc _
        _ ≤ ∑ w ∈ (G.neighborFinset v ∩ G.Λ),
              (φ k ε (G.degree w) - φ k ε ((G.deleteIncidencesOf {v}).degree w))
            + φ k ε (G.degree v) := by
          refine add_le_add ?_ (le_refl _)
          refine sum_le_sum_of_subset_of_nonpos inter_subset_left fun w hw hw' ↦ ?_
          simp only [mem_inter, hw, true_and] at hw'
          simp only [tsub_le_iff_right, zero_add]
          refine φ_decreasing k ε hε ?_ deleteIncidencesOf_degree_le
          refine le_trans₃ hε' ?_ (by linarith : 2 / (3 * (4 : ℝ)) ≤ 1 / 6)
          refine (div_le_div_iff_of_pos_left two_pos ?_ (by linarith)).mpr ?_
          · exact Left.mul_pos add_one_pos add_two_pos
          · refine mul_le_mul ?_ ?_ zero_le_four add_one_nonneg
            · rw [← Nat.cast_three, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
              linarith
            · rw [← Nat.cast_four, ← Nat.cast_two, ← Nat.cast_add, Nat.cast_le]
              linarith
        _ = ∑ w ∈ (G.neighborFinset v ∩ G.Λ), (φ k ε 1 - φ k ε 0) + φ k ε (G.degree v) := by
          simp only [add_left_inj]
          refine sum_congr rfl fun w hw ↦ ?_
          rw [hdΛ.mp <| mem_inter.mp hw |>.2]
          simp only [sub_right_inj]
          refine congrArg _ ?_
          suffices (G.deleteIncidencesOf {v}).degree w < G.degree w by grind
          have H := (mem_neighborFinset .. |>.mp <| mem_inter.mp hw |>.1).symm
          exact deleteIncidencesOf_degree_lt H (mem_singleton.mpr rfl)
      nth_rewrite 1 [φ]; nth_rewrite 1 [φ]
      simp only [one_ne_zero, ↓reduceDIte, sub_sub_cancel_left, sum_neg_distrib, sum_const,
        nsmul_eq_mul, neg_add_le_iff_le_add, add_zero]
      have Hdv' : k + 1 ≤ G.degree v := le_trans hdv degree_in_le_degree
      have hdv2 : 2 ≤ G.degree v := by lia
      have hdv0 : G.degree v ≠ 0 := by lia
      have hdv1 : G.degree v ≠ 1 := by lia
      have hdv' : ¬G.degree v ≤ k := by lia
      simp only [φ, hdv2, hdv0, hdv1, hdv', true_and, ↓reduceDIte]
      refine le_trans Std.min_le_left ?_
      refine mul_le_mul ?_ (le_refl _) hε (Nat.cast_nonneg' _)
      rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_le, ← degree_in]
      exact hdv
  else if hΛ : ∃ x y, G.degree x = 1 ∧ G.degree y = 1 ∧ G.Adj x y then
    obtain ⟨x, y, hx, hy, hxy⟩ := hΛ
    have hnotadj {u w : V} (hu : u ∈ ({x, y} : Finset _)) (hw : w ∉ ({x, y} : Finset _)) :
        ¬G.Adj u w := by
      clear * - hu hw hx hy hxy
      refine not_iff_not.mpr (G.mem_neighborFinset ..) |>.mp ?_
      suffices G.neighborFinset x ⊆ {x, y} ∧ G.neighborFinset y ⊆ {x, y} by grind
      refine ⟨?_, ?_⟩
      · grind [neighborFinset_eq_of_deg_eq_one_of_adj hx hxy]
      · grind [neighborFinset_eq_of_deg_eq_one_of_adj hy hxy.symm]
    obtain ⟨s, hs, hs'cat, hsdeg, hscard⟩ := _f_is_lb hk hε hε'
        (G.deleteIncidencesOf {x, y}) (X \ {x, y}) (deleteIncidencesOf_support hX)
    refine ⟨s ∪ {x, y}, ?_, ?_, ?_, ?_⟩
    · intro u hu
      rcases mem_union.mp hu with hu | hu
      · exact mem_sdiff.mp (hs hu) |>.1
      · exact mem_def.mpr <| hX <| G.degree_pos_iff_mem_support _ |>.mp <| by grind
    · refine InducesCaterpillarIsUnionStable G s {x, y} ?_ ?_ ?_ ?_
      · grind
      · intro u hu z hz
        refine not_adj_symm <| hnotadj hz (by grind)
      · exact InducesCaterpillar_graph_mono' (by grind) hs'cat
      · exact G.InducesCaterpillar_pair
    · intro v hv
      rcases mem_union.mp hv with hv | hv
      · refine le_of_eq_of_le ?_ (hsdeg v hv)
        have : G.degree_in (s ∪ {x, y}) v = G.degree_in s v := by
          refine degree_in_union_eq ?_
          ext u
          simp only [mem_inter, mem_neighborFinset, notMem_empty, iff_false, not_and]
          exact fun hu ↦ not_adj_symm <| hnotadj hu (by grind)
        refine this.trans ?_
        exact Eq.symm <| degree_in_deleteIncidencesOf _ _ (by grind) (mem_sdiff.mp (hs hv) |>.2)
      · exact le_trans degree_in_le_degree <| by grind
    · calc _
        _ = ∑ v ∈ X \ {x, y}, φ k ε (G.degree v) + ∑ v ∈ {x, y}, φ k ε (G.degree v) := by
          refine Eq.symm <| sum_sdiff ?_
          exact fun v hv ↦ mem_def.mpr <| hX <| G.degree_pos_iff_mem_support _ |>.mp <| by grind
        _ = ∑ v ∈ X \ {x, y}, φ k ε ((G.deleteIncidencesOf {x, y}).degree v)
            + ∑ v ∈ {x, y}, φ k ε (G.degree v) := by
          simp only [add_left_inj]
          refine sum_congr rfl fun v hv ↦ congrArg (φ k ε ∘ Finset.card) (Eq.symm ?_)
          refine neighborFinset_eq_delelteIncidencesOf_of_empty_inter_neighborFinset ?_ ?_
          · ext u
            simp only [mem_inter, mem_neighborFinset, notMem_empty, iff_false, not_and]
            contrapose
            exact fun hu ↦ not_adj_symm <| hnotadj hu (mem_sdiff.mp hv |>.2)
          · exact mem_sdiff.mp hv |>.2
        _ ≤ #s + ∑ v ∈ {x, y}, φ k ε (G.degree v) := by
          simp only [add_le_add_iff_right, hscard]
        _ ≤ #s + ∑ v ∈ {x, y}, 1 := by
          simp only [add_le_add_iff_left]
          refine sum_le_sum fun v hv ↦ ?_
          have hdv : G.degree v = 1 := by grind
          rw [hdv]
          simp only [φ, one_ne_zero, ↓reduceDIte]
          exact sub_le_self 1 hε
        _ = #s + 2 := by
          simp only [sum_const, nsmul_eq_mul, mul_one, add_right_inj]
          rw [← Nat.cast_two, Nat.cast_inj, card_pair hxy.ne]
      rw [← Nat.cast_two, ← Nat.cast_add, Nat.cast_le]
      grind [Adj.ne]
  else
    exact _f_is_lb_of_degree_in_Λ_le_k hk hε hε' G X hX h hΛ
  termination_by X.card decreasing_by
  · refine card_lt_card <| sdiff_ssubset ?_ (singleton_nonempty _)
    refine singleton_subset_iff.mpr <| mem_def.mpr <| hX ?_
    refine G.degree_pos_iff_mem_support _ |>.mp ?_
    refine lt_of_lt_of_le (Nat.zero_lt_succ k) (hdv.trans ?_)
    exact card_le_card inter_subset_left
  · refine card_lt_card <| sdiff_ssubset ?_ pair_nonempty
    intro z hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with hu | hu
    · exact hX <| hu ▸ G.mem_support.mpr ⟨y, hxy⟩
    · exact hX <| hu ▸ G.mem_support.mpr ⟨x, hxy.symm⟩

private lemma f_is_lb {k : ℕ} {f : ℕ → ℝ} (hk : 2 ≤ k)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 2 / ((k + 1) * (k + 2 : ℝ))) (hf : f ≤ φ k ε) :
    IsCaroWeiTypeLowerBound f (GraphParameter.BoundedDegreeCaterpillar k) := by
  intro V _ _ G _
  obtain ⟨s, hs, hscat, hsdeg, hscard⟩ := by
    refine _f_is_lb hk hε hε' G univ ?_
    simp only [coe_univ, Set.subset_univ]
  exact ⟨s, ⟨hscat, hsdeg⟩, le_trans (sum_le_sum fun v _ ↦ hf _) hscard⟩

theorem BoundedDegreeCaterpillar_LowerBound_iff (f : ℕ → ℝ) :
    ∀ k : ℕ, 2 ≤ k →
      (IsCaroWeiTypeLowerBound f (GraphParameter.BoundedDegreeCaterpillar k)
      ↔ ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ 2 / ((k + 1) * (k + 2 : ℝ)) ∧ f ≤ φ k ε) := by
  intro k hk
  refine ⟨_lb_bounded_by_extremal f hk, ?_⟩
  -- No idea why Lean wants V and G to be explicit here.
  -- Why isn't `exact fun ⟨ε, ⟨hε, hε', hf⟩⟩ ↦ _f_is_lb hk hε hε' hf` valid?!
  exact fun ⟨ε, ⟨hε, hε', hf⟩⟩ V _ _ G ↦ f_is_lb hk hε hε' hf G


end CaroWeiType
-/
