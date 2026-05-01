import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim1
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim6
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim12
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim17

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

lemma Corollary2' {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] {x y v w : Fin n} (hG : G.support ⊆ ABC.toFinset)
    (hBv : ABC.B v) (hBw : ABC.B w) (hv : G.Adj x v) (hw : G.Adj y w) (hvnew : v ≠ w)
    (hcard : 2 ≥ ∑ v ∈ G.closed_neighborFinset_of_Finset {v, w}, f G ABC v)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  have hF : {v, w} ⊆ ABC.toFinset := by
    intro _ h
    simp only [mem_insert, mem_singleton] at h
    refine hG <| G.mem_support.mpr ?_
    rcases h with h | h
    · exact ⟨_, h ▸ hv.symm⟩
    · exact ⟨_, h ▸ hw.symm⟩
  refine Corollary2 pair_nonempty hG hF (respects_pair_of_Bs hBv hBw) ih
    InducesLinearForest_pair ?_
  refine le_of_le_of_eq hcard ?_
  rw [← Nat.cast_two, Nat.cast_inj]
  exact Eq.symm <| card_pair hvnew

private lemma Corollary2'' {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] {x y v w : Fin n} (hG : G.support ⊆ ABC.toFinset)
    (hBv : ABC.B v) (hBw : ABC.B w) (hv : G.Adj x v) (hw : G.Adj y w) (hvnew : v ≠ w)
    (hcard : 2 ≥ ∑ v ∈ G.closed_neighborFinset_of_Finset {v, w}, f G ABC v
      - ∑ z ∈ G.N2_of_Finset {v, w}, γ G ABC z)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  have hF : {v, w} ⊆ ABC.toFinset := by
    intro _ h
    simp only [mem_insert, mem_singleton] at h
    refine hG <| G.mem_support.mpr ?_
    rcases h with h | h
    · exact ⟨_, h ▸ hv.symm⟩
    · exact ⟨_, h ▸ hw.symm⟩
  refine Claim2' pair_nonempty hG hF (respects_pair_of_Bs hBv hBw) ih InducesLinearForest_pair ?_
  refine le_of_le_of_eq hcard ?_
  rw [← Nat.cast_two, Nat.cast_inj]
  exact Eq.symm <| card_pair hvnew

private lemma three_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {v x : Fin n} (hBv : ABC.B v) (hdv : G.degree v = 3) (hvx : G.Adj v x)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨ 3 ≤ G.degree x := by
  have hxABC : x ∈ ABC := ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨v, hvx.symm⟩
  if hdx : G.degree x ≤ 1 then
    exact Or.inl <| Claim5 hG ih ⟨x, hxABC, hdx⟩
  else if hdx : G.degree x = 2 then
    cases hxABC with
    | inl hAx => exact Or.inl <| Claim7 hG ih ⟨v, x, hdv, hBv, hdx, hAx, hvx⟩
    | inr hBC => exact Or.inl <| Claim6 hG ih ⟨x, hdx, by grind [not_A_of_B, not_A_of_C]⟩
  else
    exact Or.inr (by lia)

lemma hNvw {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {û v w x y : Fin n}
    (hNv : G.neighborFinset v = {û, w, x}) (hNw : G.neighborFinset w = {û, v, y}) :
    G.closed_neighborFinset_of_Finset {v, w} = {v, w, û, x, y} := by
  ext u
  simp only [closed_neighborFinset_of_Finset, biUnion_insert, singleton_biUnion]
  grind only [= mem_insert, = insert_union, = singleton_union]

lemma sum_hNvw {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {û v w x y : Fin n}
    (hxy : x ≠ y) (hdv : G.degree v = 3) (hdw : G.degree w = 3) (hvnew : v ≠ w)
    (hNv : G.neighborFinset v = {û, w, x}) (hNw : G.neighborFinset w = {û, v, y})
    {f : Fin n → ℝ} :
    ∑ u ∈ {v, w, û, x, y}, f u = f v + f w + f û + f x + f y := by
  have hvx : G.Adj v x := G.mem_neighborFinset .. |>.mp <| by simp [hNv]
  have hwy : G.Adj w y := G.mem_neighborFinset .. |>.mp <| by simp [hNw]
  have : y ∉ ({v, w, û, x} : Finset _) := by grind [degree, Adj.ne]
  have H : f v + f w + f û + f x = ∑ u ∈ {v, w, û, x}, f u := by
    grind [degree, Adj.ne, Adj.ne']
  suffices insert y ({v, w, û, x} : Finset _) = {v, w, û, x, y} by
    grind [hNvw hNv hNw]
  grind

private lemma _A3 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w x y : Fin n}
    (hAû : ABC.A û) (hdû : G.degree û = 4) (hxy : x ≠ y)
    (hBv : ABC.B v) (hdv : G.degree v = 3) (hBw : ABC.B w) (hdw : G.degree w = 3) (hvnew : v ≠ w)
    (hNv : G.neighborFinset v = {û, w, x}) (hNw : G.neighborFinset w = {û, v, y})
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨ (ABC.A x ∧ G.degree x = 3 ∧ ABC.A y ∧ G.degree y = 3) := by
  have hvx : G.Adj v x := G.mem_neighborFinset .. |>.mp <| by simp [hNv]
  have hwy : G.Adj w y := G.mem_neighborFinset .. |>.mp <| by simp [hNw]
  match three_le_deg hG hBv hdv hvx ih, three_le_deg hG hBw hdw hwy ih with
  | Or.inl h, _ => exact Or.inl h
  | _, Or.inl h => exact Or.inl h
  | Or.inr hdx, Or.inr hdy => ?_
  if hfxy' : f G ABC x + f G ABC y ≤ 14 / 15 then
    refine Or.inl <| Corollary2' hG hBv hBw hvx.symm hwy.symm hvnew ?_ ih
    calc (2 : ℝ)
      _ = 1 / 3 + 1 / 3 + 2 / 5 + 14 / 15 := by linarith
      _ ≥ f G ABC v + f G ABC w + f G ABC û + f G ABC x + f G ABC y := by
        rw [fB3 hBv hdv, fB3 hBw hdw, fA4 hAû hdû]
        linarith
    exact le_of_eq <| (hNvw hNv hNw) ▸ sum_hNvw hxy hdv hdw hvnew hNv hNw
  else
    have hdx : G.degree x = 3 := by
      by_contra
      have hdx : 4 ≤ G.degree x := by grind
      simp only [not_le] at hfxy'
      have : f G ABC x + f G ABC y ≤ 2 / 5 + 1 / 2 := by
        refine add_le_add ?_ ?_
        · have : f G ABC x ≤ fA 4 := le_trans f_le_fA (fA_decreasing hdx)
          grind
        · have : f G ABC y ≤ fA 3 := le_trans f_le_fA (fA_decreasing hdy)
          grind
      linarith
    have hdy : G.degree y = 3 := by
      by_contra
      have hdy : 4 ≤ G.degree y := by grind
      simp only [not_le] at hfxy'
      have : f G ABC x + f G ABC y ≤ 1 / 2 + 2 / 5 := by
        refine add_le_add ?_ ?_
        · have : f G ABC x ≤ fA 3 := le_trans f_le_fA (fA_decreasing (le_of_eq hdx.symm))
          grind
        · have : f G ABC y ≤ fA 4 := le_trans f_le_fA (fA_decreasing hdy)
          grind
      linarith
    have hxABC : x ∈ ABC := by
      refine ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨v, ?_⟩
      exact Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNv]
    have hyABC : y ∈ ABC := by
      refine ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨w, ?_⟩
      exact Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]
    have hAx : ABC.A x := by
      by_contra
      have hfB3 : fB 3 = 1 / 3 := by grind
      have : f G ABC x + f G ABC y ≤ 1 / 3 + 1 / 2 := by
        refine add_le_add ?_ ?_
        · exact hfB3 ▸ hdx ▸ (f_le_fB_of_not_A this)
        · have : f G ABC y ≤ fA 3 := hdy ▸ f_le_fA
          grind
      linarith
    have hAy : ABC.A y := by
      by_contra
      have hfB3 : fB 3 = 1 / 3 := by grind
      have : f G ABC x + f G ABC y ≤ 1 / 2 + 1 / 3 := by
        refine add_le_add ?_ ?_
        · have : f G ABC x ≤ fA 3 := hdx ▸ f_le_fA
          grind
        · exact hfB3 ▸ hdy ▸ (f_le_fB_of_not_A this)
      linarith
    exact Or.inr ⟨hAx, hdx, hAy, hdy⟩

private lemma γ_eq_zero_in_N2 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w x y : Fin n}
    (hû : IsVstar G ABC û) (hAû : ABC.A û) (hdû : G.degree û = 4) (hxy : x ≠ y)
    (hBv : ABC.B v) (hdv : G.degree v = 3) (hBw : ABC.B w) (hdw : G.degree w = 3) (hvnew : v ≠ w)
    (hNv : G.neighborFinset v = {û, w, x}) (hNw : G.neighborFinset w = {û, v, y})
    (hAx : ABC.A x) (hdx : G.degree x = 3) (hAy : ABC.A y) (hdy : G.degree y = 3)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨ ∀ z ∈ G.N2_of_Finset {v, w}, γ G ABC z = 0 := by
  have hvx : G.Adj v x := G.mem_neighborFinset .. |>.mp <| by simp [hNv]
  have hwy : G.Adj w y := G.mem_neighborFinset .. |>.mp <| by simp [hNw]
  if hN2 : ∀ z ∈ G.N2_of_Finset {v, w}, γ G ABC z = 0 then
    exact Or.inr hN2
  else
    simp only [not_forall] at hN2
    obtain ⟨z, hz, hγz⟩ := hN2
    refine Or.inl <| Corollary2'' hG hBv hBw hvx.symm hwy.symm hvnew ?_ ih
    rw [hNvw hNv hNw, sum_hNvw hxy hdv hdw hvnew hNv hNw]
    rw [fB3 hBv hdv, fB3 hBw hdw, fA4 hAû hdû, fA3 hAx hdx, fA3 hAy hdy]
    suffices ∑ z ∈ G.N2_of_Finset {v, w}, γ G ABC z ≥ 1 / 15 by
      linarith
    have hγz : γ G ABC z ≥ 1 / 10 := by
      rw [← γA4 hAû hdû]
      refine γ_vstar_le_γ hû ?_ hγz
      exact ABC.mem_toFinset.mpr <| hG
        <| G.degree_pos_iff_mem_support _ |>.mp <| one_le_degree_of_mem_N2 hz
    refine ge_trans ?_ (ge_trans hγz (by linarith))
    rw [← sum_singleton (γ G ABC ·) z]
    refine sum_le_sum_of_subset_of_nonneg (by simp only [singleton_subset_iff, hz]) ?_
    exact fun _ _ _ ↦ γ_nonneg

private lemma _respects {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite]
    {ABC : Tripartition n} {û v w x y : Fin n}
    (hBw : ABC.B w) (hAx : ABC.A x) (hAy : ABC.A y) (hwx : ¬G.Adj w x) (hdv : G.degree v = 3)
    (hNv : G.neighborFinset v = {û, w, x}) (hNw : G.neighborFinset w = {û, v, y}) :
    respects {w, x, y} G ABC := by
  intro u hu
  simp only [mem_insert, mem_singleton] at hu
  rcases hu with hu | hu | hu
  · subst hu
    simp only [hBw, not_A_of_B, not_C_of_B, forall_const, IsEmpty.forall_iff, and_true, true_and]
    simp only [degree_in, mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true,
      inter_insert_of_notMem]
    rw [← card_singleton y]
    refine card_le_card ?_
    intro u' hu'
    simp only [mem_inter, mem_neighborFinset, mem_insert, mem_singleton] at hu'
    obtain ⟨huu', hu'⟩ := hu'
    rcases hu' with hu' | hu'
    · exact hwx (hu' ▸ huu') |>.elim
    · exact mem_singleton.mpr hu'
  · subst hu
    simp only [hAx, not_B_of_A, not_C_of_A, forall_const, IsEmpty.forall_iff, and_true]
    have hF : ({w, u, y} : Finset _) = {u} ∪ {w, y} := by grind
    simp only [hF, ← degree_in_union_self']
    refine le_of_le_of_eq degree_in_le_card ?_
    refine card_pair ?_
    refine Adj.ne <| G.mem_neighborFinset .. |>.mp ?_
    simp only [hNw, mem_insert, mem_singleton, or_true]
  · subst hu
    simp only [hAy, not_B_of_A, not_C_of_A, forall_const, IsEmpty.forall_iff, and_true]
    have hF : ({w, x, u} : Finset _) = {u} ∪ {w, x} := by grind
    simp only [hF, ← degree_in_union_self']
    refine le_of_le_of_eq degree_in_le_card ?_
    refine card_pair ?_
    grind [degree]

lemma _induces_forest {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {û v w x y : Fin n}
    (hwx : ¬G.Adj w x)
    (hNv : G.neighborFinset v = {û, w, x}) (hNw : G.neighborFinset w = {û, v, y}) :
    G.InducesForest {w, x, y} := by
  intro t ht htne
  if hw : w ∈ t then
    refine ⟨_, hw, ?_⟩
    refine le_trans (degree_in_mono ht) ?_
    simp only [degree_in, mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true,
      inter_insert_of_notMem, ← card_singleton y]
    refine card_le_card ?_
    intro u
    simp only [mem_inter, mem_neighborFinset, mem_insert, mem_singleton, and_imp]
    intro hwu hu
    rcases hu with hu | hu
    · exact hwx (hu ▸ hwu) |>.elim
    · exact hu
  else if hx : x ∈ t then
    refine ⟨_, hx, ?_⟩
    simp only [degree_in, ← card_singleton y]
    refine card_le_card ?_
    intro u
    simp only [mem_inter, mem_neighborFinset, mem_singleton, and_imp]
    intro hxu _
    have hu : u = x ∨ u = y := by grind
    rcases hu with hu | hu
    · exact G.irrefl (hu ▸ hxu) |>.elim
    · exact hu
  else
    have ht : t = {y} := by grind
    refine ⟨y, by grind, ?_⟩
    refine le_of_le_of_eq degree_in_le_card ?_
    simp only [ht, card_singleton]

lemma Claim18 {n : ℕ} {G : SimpleGraph (Fin n)} [G.LocallyFinite] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w : Fin n} (hû : IsVstar G ABC û)
    (hAû : ABC.A û) (hdû : G.degree û = 4)
    (hBv : ABC.B v) (hdv : G.degree v = 3) (hBw : ABC.B w) (hdw : G.degree w = 3)
    (hv : G.Adj û v) (hw : G.Adj û w) (hvw : G.Adj v w)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [G'.LocallyFinite] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  obtain ⟨x, hNv⟩ := neighborFinset_of_adj_of_adj_of_ne hdv hw.ne hv.symm hvw
  obtain ⟨y, hNw⟩ := neighborFinset_of_adj_of_adj_of_ne hdw hv.ne hw.symm hvw.symm
  if hxy : x = y then
    have hne : û ≠ x := by grind [degree]
    exact Claim12 hG hvw.ne hBv hdv hBw hdw hne (by grind) ih
  else
    match _A3 hG hAû hdû hxy hBv hdv hBw hdw hvw.ne hNv hNw ih with
    | Or.inl h => exact h
    | Or.inr h => ?_
    obtain ⟨hAx, hdx, hAy, hdy⟩ := h
    match γ_eq_zero_in_N2 hG hû hAû hdû hxy hBv hdv hBw hdw hvw.ne hNv hNw hAx hdx hAy hdy ih with
    | Or.inl h => exact h
    | Or.inr hγN2 => ?_
    let F := ({x, y, w} : Finset _)
    if h : G.closed_neighborFinset_of_Finset F ⊆ {û, v, w, x, y} then
      have hNF : {û, v, w, x, y} = G.closed_neighborFinset_of_Finset {x, y, w} :=
        subset_antisymm (by grind [closed_neighborFinset_of_Finset]) h
      have hF : F.Nonempty := insert_nonempty ..
      have hcF : #F = 3 := by
        have : y ≠ w := by
          refine (G.mem_neighborFinset .. |>.mp ?_).ne'
          simp only [hNw, mem_insert, mem_singleton, or_true]
        grind [degree]
      have hF' : F ⊆ ABC.toFinset := by
        intro u hu
        simp only [mem_insert, mem_singleton, F] at hu
        refine hG <| G.mem_support.mpr ?_
        rcases hu with hu | hu | hu
        · refine ⟨v, hu ▸ ?_⟩
          suffices x ∈ G.neighborFinset v by
            exact (G.mem_neighborFinset .. |>.mp this).symm
          simp only [hNv, mem_insert, mem_singleton, or_true]
        · refine ⟨w, hu ▸ ?_⟩
          suffices y ∈ G.neighborFinset w by
            exact (G.mem_neighborFinset .. |>.mp this).symm
          simp only [hNw, mem_insert, mem_singleton, or_true]
        · refine ⟨v, hu ▸ ?_⟩
          suffices w ∈ G.neighborFinset v by
            exact (G.mem_neighborFinset .. |>.mp this).symm
          simp only [hNv, mem_insert, mem_singleton, or_true, true_or]
      have hdeginFw1 : G.degree_in F w ≤ 1 := by
        simp only [degree_in, F]
        rw [← card_singleton y]
        refine card_le_card ?_
        intro u
        contrapose
        simp only [mem_singleton, mem_inter, mem_neighborFinset, mem_insert, not_and, not_or]
        intro huney hwu
        refine ⟨?_, huney, hwu.ne'⟩
        let hu := hNw ▸ G.mem_neighborFinset .. |>.mpr hwu
        simp only [mem_insert, mem_singleton, huney, or_false] at hu
        rcases hu with hu | hu
        · grind only
        · intro heq
          subst heq hu
          refine notMem_neighborFinset_self G u ?_
          simp only [hNv, mem_insert, mem_singleton, or_true]
      have hresp : respects F G ABC := by
        intro u hu
        simp only [mem_insert, mem_singleton, F] at hu
        rcases hu with hu | hu | hu
        · simp only [hu, hAx, degree_in, forall_const, not_B_of_A, IsEmpty.forall_iff, not_C_of_A,
            card_eq_zero, and_self, and_true]
          have hu : u ∈ F := by simp only [hu, mem_insert, mem_singleton, true_or, F]
          refine le_of_le_of_eq (degree_in_le_card_minus_one_of_mem hu) (by lia)
        · simp only [hu, hAy, degree_in, forall_const, not_B_of_A, IsEmpty.forall_iff, not_C_of_A,
            card_eq_zero, and_self, and_true]
          have hu : u ∈ F := by simp only [hu, mem_insert, mem_singleton, true_or, or_true, F]
          refine le_of_le_of_eq (degree_in_le_card_minus_one_of_mem hu) (by lia)
        · simp only [hu, hBw, not_A_of_B, degree_in, IsEmpty.forall_iff, forall_const, not_C_of_B,
            card_eq_zero, and_true, hu ▸ hdeginFw1]
      refine Corollary2 hF hG hF' hresp ih ?_ ?_
      · refine linear_forest_of_forest_respects hF' ?_ hresp
        intro t ht htne
        if hcardF : #t ≤ 2 then
          obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr htne
          exact ⟨x, hx, degree_in_subpair_le_one_of_mem hx hcardF⟩
        else
          have heq : t = F := by
            refine eq_of_subset_and_eq_card ht ?_
            refine le_antisymm (card_le_card ht) (hcF ▸ ?_)
            exact Nat.succ_le_of_lt <| Nat.lt_of_not_le hcardF
          subst heq
          refine ⟨w, ?_, ?_⟩
          · simp only [mem_insert, mem_singleton, or_true, F]
          · exact hdeginFw1
      · simp only [ge_iff_le]
        rw [← hNF]
        calc _
          _ = f G ABC û + f G ABC v + f G ABC w + ∑ u ∈ {x, y}, f G ABC u := by
            grind [degree]
          _ = f G ABC û + f G ABC v + f G ABC w + f G ABC x + f G ABC y := by
            grind
        rw [hcF, Nat.cast_three, fA4 hAû hdû, fB3 hBv hdv, fB3 hBw hdw, fA3 hAx hdx, fA3 hAy hdy]
        linarith
    else if hNx : ∃ z ∈ G.neighborFinset x, z ≠ v ∧ γ G ABC z = 0 then
      obtain ⟨z, hz, hzv, hγz⟩ := hNx
      have hdz : 1 ≤ G.degree z := one_le_degree_of_mem_neighborFinset' hz
      have hzABC : z ∈ ABC :=
        ABC.mem_toFinset.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp hdz
      obtain ⟨_, hNx⟩ := by
        refine neighborFinset_of_adj_of_adj_of_ne hdx hzv ?_ ?_
        · exact G.mem_neighborFinset .. |>.mp <| hz
        · exact Adj.symm <| G.mem_neighborFinset .. |>.mp
            <| by simp only [hNv, mem_insert, mem_singleton, or_true]
      rcases γ_eq_0_iff hzABC hdz |>.mp <| hγz with ⟨hdz, hBz⟩ | ⟨hdz, hCz⟩ | ⟨hdz, hCz⟩
      · exact Claim11 hG hAx hdx hNx hBz hBv hdz hdv ih
      · simp only [mem_neighborFinset] at hz
        exact Corollary1 hG hz.symm ih
          <| by simp only [fC3 hCz hdz, γA3 hAx hdx, le_refl]
      · exact Claim6 hG ih ⟨z, hdz, not_A_of_C hCz⟩
    else if hNy : ∃ z ∈ G.neighborFinset y, z ≠ w ∧ γ G ABC z = 0 then
      obtain ⟨z, hz, hzw, hγz⟩ := hNy
      have hdz : 1 ≤ G.degree z := one_le_degree_of_mem_neighborFinset' hz
      have hzABC : z ∈ ABC :=
        ABC.mem_toFinset.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp hdz
      obtain ⟨_, hNy⟩ := by
        refine neighborFinset_of_adj_of_adj_of_ne hdy hzw ?_ ?_
        · exact G.mem_neighborFinset .. |>.mp <| hz
        · exact Adj.symm <| G.mem_neighborFinset .. |>.mp
            <| by simp only [hNw, mem_insert, mem_singleton, or_true]
      rcases γ_eq_0_iff hzABC hdz |>.mp <| hγz with ⟨hdz, hBz⟩ | ⟨hdz, hCz⟩ | ⟨hdz, hCz⟩
      · exact Claim11 hG hAy hdy hNy hBz hBw hdz hdw ih
      · simp only [mem_neighborFinset] at hz
        exact Corollary1 hG hz.symm ih
          <| by simp only [fC3 hCz hdz, γA3 hAy hdy, le_refl]
      · exact Claim6 hG ih ⟨z, hdz, not_A_of_C hCz⟩
    else
      simp only [mem_neighborFinset, ne_eq, not_exists, not_and', Decidable.not_not] at hNx hNy
      have hwx : ¬G.Adj w x := by
        rcases hNx w with hxw | h
        · exact fun hwx ↦ hxw hwx.symm
        · simp only [hvw.ne', false_or, γB3 hBw hdw, not_true_eq_false] at h
      have hvy : ¬G.Adj v y := by
        rcases hNy v with hyv | h
        · exact fun hvy ↦ hyv hvy.symm
        · simp only [hvw.ne, false_or, γB3 hBv hdv, not_true_eq_false] at h
      have hNx : G.neighborFinset x ⊆ {v, w, û, x, y} := by
        suffices G.neighborFinset x
              ⊆ G.closed_neighborFinset_of_Finset {v, w} ∪ G.N2_of_Finset {v, w} by
          intro u hu
          have hu' := this hu
          simp only [mem_union] at hu'
          rcases hu' with hu' | hu'
          · exact (hNvw hNv hNw) ▸ hu'
          · have Hu := hNx u
            simp only [hγN2 _ hu', not_true_eq_false, or_false, false_or,
              G.mem_neighborFinset .. |>.mp hu] at Hu
            grind
        intro u hu
        if hu1 : u ∈ G.closed_neighborFinset_of_Finset {v, w} then
          simp only [mem_union, hu1, true_or]
        else
          simp only [mem_union, hu1, false_or]
          refine mem_N2_of_Finset_iff'.mpr ⟨hu1, ?_⟩
          have := not_iff_not.mpr mem_closed_neighborFinset_iff |>.mp hu1
          simp only [not_or, not_exists, not_and] at this
          refine ⟨v, by simp only [mem_insert, mem_singleton, true_or], x, ?_, ?_, ?_⟩
          · simp only [mem_insert, mem_singleton, not_or]
            refine ⟨?_, ?_⟩
            · refine ne_of_mem_neighborFinset (by simp [hNv] : x ∈ G.neighborFinset v)
            · grind [degree]
          · exact Adj.symm <| G.mem_neighborFinset .. |>.mp hu
          · exact Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNv]
      have hNy : G.neighborFinset y ⊆ {v, w, û, x, y} := by
        suffices G.neighborFinset y
              ⊆ G.closed_neighborFinset_of_Finset {v, w} ∪ G.N2_of_Finset {v, w} by
          intro u hu
          have hu' := this hu
          simp only [mem_union] at hu'
          rcases hu' with hu' | hu'
          · exact (hNvw hNv hNw) ▸ hu'
          · have Hu := hNy u
            simp only [hγN2 _ hu', not_true_eq_false, or_false, false_or,
              G.mem_neighborFinset .. |>.mp hu] at Hu
            grind
        intro u hu
        if hu1 : u ∈ G.closed_neighborFinset_of_Finset {v, w} then
          simp only [mem_union, hu1, true_or]
        else
          simp only [mem_union, hu1, false_or]
          refine mem_N2_of_Finset_iff'.mpr ⟨hu1, ?_⟩
          refine ⟨w, by simp, y, ?_, ?_, ?_⟩
          · simp only [mem_insert, mem_singleton, not_or]
            grind [degree]
          · exact Adj.symm <| G.mem_neighborFinset .. |>.mp hu
          · exact Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNw]
      have hF : ({w, x, y} : Finset _).Nonempty := insert_nonempty ..
      have hF' : ({w, x, y} : Finset _) ⊆ ABC.toFinset := by
        refine fun u hu ↦ hG <| G.mem_support.mpr ?_
        simp only [mem_insert, mem_singleton] at hu
        rcases hu with hu | hu | hu
        · exact ⟨v, Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNv, hu]⟩
        · exact ⟨v, Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNv, hu]⟩
        · exact ⟨w, Adj.symm <| G.mem_neighborFinset .. |>.mp <| by simp [hNw, hu]⟩
      have hresp : respects {w, x, y} G ABC := _respects hBw hAx hAy hwx hdv hNv hNw
      refine Corollary2 hF hG hF' hresp ih
        (linear_forest_of_forest_respects hF' (_induces_forest hwx hNv hNw) hresp) ?_
      have hNwxy : G.closed_neighborFinset_of_Finset {w, x, y} = {û, v, w, x, y} := by
        simp only [closed_neighborFinset_of_Finset]
        ext u
        simp only [biUnion_insert, singleton_biUnion, hNw]
        grind
      have hF : #{w, x, y} = 3 := by grind [degree]
      have hN' : ({û, v, w, x, y} : Finset _) = {v, w, û, x, y} := by grind
      rw [hNwxy, hN', sum_hNvw hxy hdv hdw hvw.ne hNv hNw, hF, Nat.cast_three]
      rw [fB3 hBv hdv, fB3 hBw hdw, fA4 hAû hdû, fA3 hAx hdx, fA3 hAy hdy]
      linarith

end Tripartition
end ABC
end CaroWeiType
