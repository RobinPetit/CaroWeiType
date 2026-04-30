import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim1
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim2
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim3
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim5
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim6
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim7
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim9

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

private lemma exists_adj {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} (w : G.Walk u v)
    (P : Fin n → Prop) (hu : P u) (hv : ¬P v) : ∃ u₁ u₂ : Fin n, G.Adj u₁ u₂ ∧ P u₁ ∧ ¬P u₂ := by
  induction w with
  | nil => exact hv hu |>.elim
  | @cons u v w huv' w' ih => ?_
  if hPv : P v then
    exact ih hPv hv
  else
    exact ⟨u, v, huv', hu, hPv⟩

private lemma one_le_degree_of_nonsingleton_component {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (C : G.ConnectedComponent) [Fintype C.supp] (hC : 1 < #C.supp.toFinset) :
    ∀ x ∈ C.supp.toFinset, 1 ≤ G.degree x := by
  intro x hx
  obtain ⟨y, hy⟩ := by
    refine Finset_get_one (C.supp.toFinset \ {x}) ?_
    refine le_trans ?_ (le_card_sdiff ..)
    rw [card_singleton]
    exact Nat.le_sub_one_of_lt hC
  have hxney : x ≠ y :=
    Ne.symm <| notMem_singleton.mp <| mem_sdiff.mp hy |>.2
  have hxy : G.Reachable x y := by
    simp only [Set.mem_toFinset, ConnectedComponent.mem_supp_iff] at hx
    subst hx
    suffices y ∈ (G.connectedComponentMk x).supp by
      simp_all only [ne_eq, Set.toFinset_card, ConnectedComponent.mem_supp_iff,
        ConnectedComponent.eq, Reachable.symm]
    exact Set.mem_toFinset.mp <| mem_sdiff.mp hy |>.1
  exact one_le_degree_of_walk_begin hxney (Nonempty.some hxy)

private lemma split_eval_on_component {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset)
    (C : G.ConnectedComponent) [Fintype C.supp]
    (hC : 1 < #C.supp.toFinset) :
    eval G ABC = eval (G.deleteIncidencesOf C.supp.toFinset) (ABC \ C.supp.toFinset)
      + ∑ x ∈ C.supp.toFinset, f G ABC x := by
  calc eval G ABC
    _ = ∑ x ∈ ABC.toFinset \ C.supp.toFinset, f G ABC x + ∑ x ∈ C.supp.toFinset, f G ABC x := by
      refine Eq.symm <| sum_sdiff ?_
      intro x hx
      refine hG <| Set.mem_toFinset.mpr <| G.degree_pos_iff_mem_support _ |>.mp ?_
      exact Nat.zero_lt_of_lt <| one_le_degree_of_nonsingleton_component C hC _ hx
  simp only [add_left_inj]
  refine sum_congr ABC.sdiff_toFinset.symm ?_
  intro x hx
  let hx' := mem_sdiff.mp (ABC.sdiff_toFinset ▸ hx) |>.2
  have hx'' : x ∉ C.supp := not_iff_not.mpr Set.mem_toFinset |>.mp hx'
  rw [← f_eq_in_sdiff G ABC hx']
  suffices G.degree x = (G.deleteIncidencesOf C.supp.toFinset).degree x by
    exact f_mono_degree _ _ _ this
  refine congrArg Finset.card ?_
  ext y
  simp only [mem_neighborFinset, deleteIncidencesOf, deleteIncidenceSet, incidenceSet,
    Set.mem_toFinset, ConnectedComponent.mem_supp_iff, inf_adj, iInf_adj, deleteEdges_adj,
    Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq, iff_self_and]
  intro hxy
  have H : Nonempty (C.supp.toFinset) :=
    Nonempty.to_subtype <| nonempty_of_ne_empty <| by grind only [= card_empty]
  obtain ⟨z, hz⟩ := Nonempty.some H
  have hz : z ∈ C.supp := Set.mem_toFinset.mp hz
  have hy'' : y ∉ C.supp := by
    intro hy
    have hyz : G.Reachable y z := C.reachable_of_mem_supp hy hz
    have _ : G.Reachable x z := Reachable.trans hxy.reachable hyz
    have _ : x ∈ C.supp := (C.mem_supp_congr_adj hxy.symm).mp hy
    contradiction
  simp only [hxy, forall_const, true_and, hxy.ne, not_false_eq_true, and_true]
  intro z hz
  refine ⟨?_, ?_⟩
  · intro heq
    simp_all only [Set.toFinset_subset, Set.toFinset_card, ConnectedComponent.mem_supp_iff]
  · intro heq
    simp_all only [Set.toFinset_subset, Set.toFinset_card, ConnectedComponent.mem_supp_iff]

lemma respects_union_path {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {û : Fin n} {s : Finset (Fin n)}
    [Fintype ((G.connectedComponentMk û).supp)]
    (hs : s ⊆ (ABC \ (G.connectedComponentMk û).supp.toFinset).toFinset)
    (hsresp : respects s (G.deleteIncidencesOf (G.connectedComponentMk û).supp.toFinset)
        (ABC \ (G.connectedComponentMk û).supp.toFinset))
    (hC : ∀ z ∈ (G.connectedComponentMk û).supp, ABC.A z ∧ G.degree z = 2) :
    respects (s ∪ (G.connectedComponentMk û).supp.toFinset \ {û}) G ABC := by
  intro w hw
  have not_reachable_of_mem_s {u : Fin n} (hu : u ∈ s) : ¬G.Reachable u û := by
    refine not_iff_not.mpr ConnectedComponent.eq |>.mp ?_
    suffices u ∉ (G.connectedComponentMk û).supp by
      exact this
    exact not_iff_not.mpr Set.mem_toFinset |>.mp <| mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs hu) |>.2
  rw [degree_in]
  have H (hw : w ∈ s) : G.neighborFinset w ∩ (s ∪ (G.connectedComponentMk û).supp.toFinset \ {û})
      = (G.deleteIncidencesOf (G.connectedComponentMk û).supp.toFinset).neighborFinset w ∩ s := by
    ext u
    simp only [mem_inter, mem_neighborFinset, mem_union, mem_sdiff, Set.mem_toFinset,
      ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, mem_singleton, deleteIncidencesOf,
      deleteIncidenceSet, incidenceSet, inf_adj, iInf_adj, deleteEdges_adj, Set.mem_setOf_eq,
      mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq]
    constructor
    · intro ⟨h₁, h₂⟩
      rcases h₂ with h | h
      · simp only [h₁, forall_const, true_and, h₁.ne, not_false_eq_true, and_true, h]
        intro v hv
        refine ⟨?_, ?_⟩
        · exact fun heq ↦ not_reachable_of_mem_s h <| (Adj.reachable h₁.symm).trans (heq ▸ hv)
        · exact fun heq ↦ not_reachable_of_mem_s hw <| (Adj.reachable h₁).trans (heq ▸ hv)
      · simp only [h₁, h₁.ne, not_false_eq_true, true_and, and_true, forall_const]
        refine ⟨fun v hvû ↦ ⟨?_, ?_⟩, ?_⟩
        · exact fun heq ↦ not_reachable_of_mem_s hw (heq ▸ hvû)
        · exact fun heq ↦ not_reachable_of_mem_s hw <| (Adj.reachable (heq ▸ h₁)).trans hvû
        · exact not_reachable_of_mem_s hw (h₁.reachable.trans h.1) |>.elim
    · intro ⟨⟨hwu, h', _⟩, hus⟩
      simp only [hwu, hus, true_or, and_self]
  refine ⟨?_, ?_, ?_⟩
  · intro hAw
    rcases mem_union.mp hw with hw | hw
    · refine le_of_eq_of_le ?_
        (hsresp w hw |>.1 ⟨hAw, mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs hw) |>.2⟩)
      rw [degree_in]
      refine congrArg Finset.card (H hw)
    · exact le_of_le_of_eq degree_in_le_degree
        (hC w <| Set.mem_toFinset.mp <| mem_sdiff.mp hw |>.1).2
  · intro hBw
    rcases mem_union.mp hw with hw | hw
    · refine le_trans ?_ (hsresp w hw |>.2.1 ⟨hBw, mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs hw) |>.2⟩)
      exact card_le_card <| subset_of_eq <| H hw
    · exact not_A_of_B hBw (hC w <| Set.mem_toFinset.mp <| mem_sdiff.mp hw |>.1).1 |>.elim
  · intro hCw
    rcases mem_union.mp hw with hw | hw
    · refine card_eq_zero.mpr ?_
      exact H hw ▸ card_eq_zero.mp
        (hsresp w hw |>.2.2 ⟨hCw, mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs hw) |>.2⟩)
    · exact not_A_of_C hCw (hC w <| Set.mem_toFinset.mp <| mem_sdiff.mp hw |>.1).1 |>.elim

lemma _compute_final {x : ℝ} : 3 ≤ x ↔ x * (2 / 3) ≤ x - 1 := by
  grind

lemma _eval_ok {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset)
    {û : Fin n} (hdû : G.degree û = 2) [Fintype (G.connectedComponentMk û)]
    {s : Finset (Fin n)} (hs : s ⊆ (ABC \ (G.connectedComponentMk û).supp.toFinset).toFinset)
    (hC : ∀ x ∈ (G.connectedComponentMk û).supp, ABC.A x ∧ G.degree x = 2)
    (hscard : eval (G.deleteIncidencesOf (G.connectedComponentMk û).supp.toFinset)
      (ABC \ (G.connectedComponentMk û).supp.toFinset) ≤ #s) :
    eval G ABC ≤ ↑(#(s ∪ (G.connectedComponentMk û).supp.toFinset \ {û})) := by
  have H : 1 < #(G.connectedComponentMk û).supp.toFinset := by
    have : Nonempty (G.neighborFinset û) := by
      refine Nonempty.to_subtype <| nonempty_iff_ne_empty.mpr ?_
      refine ne_of_ne_congr Finset.card <| (Nat.ne_of_lt ?_).symm
      simp only [card_empty, card_neighborFinset_eq_degree, hdû, two_pos]
    obtain ⟨z, hz⟩ := nonempty_subtype.mp this
    refine one_lt_card_iff_exists_a_b.mpr ⟨û, z, ?_, (G.mem_neighborFinset .. |>.mp hz).ne⟩
    intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with hu | hu
    · simp only [hu, Set.mem_toFinset, ConnectedComponent.mem_supp_iff]
    · simp only [hu, Set.mem_toFinset, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
      exact (G.mem_neighborFinset .. |>.mp hz).symm.reachable
  have : #(s ∪ (G.connectedComponentMk û).supp.toFinset \ {û})
      = #s + (#(G.connectedComponentMk û).supp.toFinset - 1) := by
    rw [← card_singleton û]
    rw [card_union]
    have : (s ∩ ((G.connectedComponentMk û).supp.toFinset \ {û})) = ∅ := by
      ext u
      simp only [mem_inter, mem_sdiff, Set.mem_toFinset, ConnectedComponent.mem_supp_iff,
        ConnectedComponent.eq, mem_singleton, notMem_empty, iff_false, not_and, Decidable.not_not]
      intro hus huû
      let bla := mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs hus) |>.2
      refine bla ?_ |>.elim
      exact Set.mem_toFinset.mpr <| (ConnectedComponent.mem_supp_iff _ u).mpr
        <| ConnectedComponent.sound huû
    simp only [this, card_empty, tsub_zero, card_singleton, Nat.add_left_cancel_iff]
    exact card_setminus_singleton <| Set.mem_toFinset.mpr rfl
  rw [split_eval_on_component hG _ H, this, Nat.cast_add]
  calc eval (G.deleteIncidencesOf (G.connectedComponentMk û).supp.toFinset)
        (ABC \ (G.connectedComponentMk û).supp.toFinset)
      + ∑ x ∈ (G.connectedComponentMk û).supp.toFinset, f G ABC x
    _ ≤ #s + ∑ x ∈ (G.connectedComponentMk û).supp.toFinset, f G ABC x := add_le_add_left hscard _
  refine add_le_add_right ?_ _
  calc ∑ x ∈ (G.connectedComponentMk û).supp.toFinset, f G ABC x
    _ = ∑ x ∈ (G.connectedComponentMk û).supp.toFinset, 2 / 3 := by
      refine sum_congr rfl ?_
      intro x hx
      have hx' : x ∈ (G.connectedComponentMk û).supp := Set.mem_toFinset.mp hx
      simp only [f, hC _ hx', ↓reduceDIte, fA, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one,
        Nat.cast_ofNat]
      lia
    _ = #((G.connectedComponentMk û).supp.toFinset) * (2 / (3 : ℝ)) := sum_const' _ (fun _ _ ↦ rfl)
  rw [Nat.cast_sub <| Nat.one_le_of_lt H, Nat.cast_one]
  refine _compute_final.mp <| ?_
  rw [← Nat.cast_three, Nat.cast_le]
  refine le_of_eq_of_le ?_ card_connectedComponent_at_least_deg_plus_one
  simp only [hdû, Nat.reduceAdd]

private lemma ok_of_γ_eq_0
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    {û : Fin n} (hG : G.support.toFinset ⊆ ABC.toFinset) (hû : IsVstar G ABC û)
    (hAû : ABC.A û) (hdû : G.degree û = 2)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC')
    (hdeg1 : ∀ x ∈ ABC, 1 < G.degree x)
    (hv : ∃ v ∈ (G.connectedComponentMk û).supp, γ G ABC v = 0) :
    Objective G ABC := by
  obtain ⟨v, hvC, hγv⟩ := hv
  have _ : û ≠ v := fun heq ↦ (hû.1.2) <| heq ▸ hγv
  let w := Nonempty.some <| Reachable.symm (ConnectedComponent.exact hvC)
  obtain ⟨v₁, v₂, hv₁v₂, hγv₁, hγv₂⟩ := exists_adj w.reverse (γ G ABC · = 0) hγv hû.1.2
  have  hv₂ : v₂ ∈ ABC.toFinset :=
    hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨v₁, hv₁v₂.symm⟩
  have hdv₂ : 1 < G.degree v₂ := by
    exact hdeg1 _ <| ABC.coe_mem_toFinset.mpr hv₂
  if hv₂' : ABC.B v₂ ∧ G.degree v₂ = 2 then
    exact Claim6 hG ih ⟨v₂, hv₂'.2, not_A_of_B hv₂'.1⟩
  else
    have : ABC.A v₂ ∧ G.degree v₂ = 2 := by
      simp only [IsVstar, MinimalFor, ne_eq, key, and_imp] at hû
      if h : key G ABC v₂ ≤ key G ABC û then
        have h : key G ABC v₂ = key G ABC û := le_antisymm h (hû.2 hv₂ hγv₂ h)
        simp only [key] at h
        obtain ⟨h₁, h₂⟩ := Prod.mk_inj.mp h
        simp only [neg_inj, Nat.cast_inj] at h₂
        rw [γA2 hAû hdû] at h₁
        refine ⟨?_, h₂ ▸ hdû⟩
        rcases ABC.coe_mem_toFinset.mpr hv₂ with h | h | h
        · exact h
        · simp only [γ, h, not_A_of_B, ↓reduceDIte, fB, hdû ▸ h₂, Nat.add_one_sub_one,
            one_ne_zero, ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one] at h₁
          linarith
        · simp only [γ, h, not_A_of_C, not_B_of_C, ↓reduceDIte, fC, hdû ▸ h₂, one_ne_zero,
            Nat.add_one_sub_one, ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
            true_or, or_true] at h₁
          linarith
      else
        simp only [not_le, key] at h
        have h : (γ G ABC û < γ G ABC v₂)
            ∨ (γ G ABC û = γ G ABC v₂ ∧ -(G.degree û : ℤ) < -(G.degree v₂ : ℤ)) :=
          Prod.Lex.lt_iff.mp h
        rcases h with h | h
        · rw [γA2 hAû hdû] at h
          rcases if_γ_gt_one_over_six (ABC.coe_mem_toFinset.mpr hv₂) h with h | h <;> grind only
        · rw [γA2 hAû hdû] at h
          obtain ⟨h₁, h₂⟩ := h
          simp only [neg_lt_neg_iff, Nat.cast_lt, hdû] at h₂
          grind only
    have hv₁ : v₁ ∈ ABC :=
      ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨v₂, hv₁v₂⟩
    have hdv₁ : 1 ≤ G.degree v₁ := one_le_degree_of_adj hv₁v₂
    rcases γ_eq_0_iff hv₁ hdv₁ |>.mp hγv₁ with h | h | h
    · exact Claim7 hG ih ⟨v₁, v₂, h.1, h.2, this.2, this.1, hv₁v₂⟩
    · exact Corollary1 hG hv₁v₂ ih (by rw [fC3 h.2 h.1, γA2 this.1 this.2])
    · exact Claim6 hG ih ⟨v₁, h.1, not_A_of_C h.2⟩

private lemma ok_of_γ_ne_0
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    {û : Fin n} (hG : G.support.toFinset ⊆ ABC.toFinset) (hû : IsVstar G ABC û)
    (hAû : ABC.A û) (hdû : G.degree û = 2)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC')
    (hdeg1 : ∀ x ∈ ABC, 1 < G.degree x)
    (hB2 : ∀ (x : Fin n), ABC.B x → ¬G.degree x = 2)
    (hv : ∀ v ∈ (G.connectedComponentMk û).supp, γ G ABC v ≠ 0) :
    Objective G ABC := by
  have hC : ∀ z ∈ (G.connectedComponentMk û).supp, ABC.A z ∧ G.degree z = 2 := by
    by_contra
    simp only [not_forall] at this
    obtain ⟨z, hz, hdz⟩ := this
    have hz' : z ∈ ABC.toFinset := by
      refine hG <| Set.mem_toFinset.mpr ?_
      if heq : z = û then
        exact G.degree_pos_iff_mem_support _ |>.mp <| heq ▸ Nat.lt_of_sub_eq_succ hdû
      else
        refine G.degree_pos_iff_mem_support _ |>.mp ?_
        refine Nat.zero_lt_of_lt <| one_le_degree_of_walk_begin heq (Nonempty.some ?_)
        simp only [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq] at hz
        exact hz
    have hkey : key G ABC û ≤ key G ABC z := by
      if h : key G ABC û ≤ key G ABC z then
        exact h
      else
        simp only [not_le] at h
        let hû' := hû.2
        simp only [ne_eq, and_imp] at hû'
        refine hû' hz' (hv _ hz) (le_of_lt h)
    simp only [key] at hkey
    rcases lt_or_eq_of_le hkey with h | h
    · have : γ G ABC û < γ G ABC z
          ∨ (γ G ABC û = γ G ABC z ∧ -(G.degree û : ℤ) < -(G.degree z : ℤ)) :=
        Prod.Lex.lt_iff.mp h
      rw [γA2 hAû hdû] at this
      let hdz' := hdeg1 _ (ABC.coe_mem_toFinset.mpr hz')
      rcases this with h | h
      · let hobj := if_γ_gt_one_over_six (ABC.coe_mem_toFinset.mpr hz') h
        simp only [not_and] at hdz
        simp only [and_false, or_false, Ne.symm <| ne_of_lt <| hdz'] at hobj
        exact hB2 z hobj.1 hobj.2
      · simp only [neg_lt_neg_iff, Nat.cast_lt, hdû ] at h
        lia
    · obtain ⟨h₁, h₂⟩ := Prod.mk_inj.mp h
      simp only [neg_inj, Nat.cast_inj] at h₂
      have _ : z ∈ ABC := ABC.coe_mem_toFinset.mpr hz'
      have hCz : ABC.C z := by grind [mem_iff]
      rw [γA2 hAû hdû, γC2 hCz (h₂ ▸ hdû)] at h₁
      grind
  let C := G.connectedComponentMk û
  have : Fintype C := Fintype.ofFinite _
  obtain ⟨s, hs, hsforest, hsresp, hscard⟩ := by
    refine ih (G.deleteIncidencesOf C.supp.toFinset) (ABC \ C.supp.toFinset) (hsupp_mono hG) ?_
    refine sdiff_card ABC <| nonempty_iff_ne_empty.mp ⟨û, mem_inter.mpr ⟨?_, ?_⟩⟩
    · simp only [Set.mem_toFinset, ConnectedComponent.mem_supp_iff, C]
    · simp only [← ABC.coe_mem_toFinset, mem_iff, hAû, true_or]
  refine ⟨s ∪ (C.supp.toFinset \ {û}), ?_, ?_, ?_, ?_⟩
  · intro u hu
    simp only [mem_union, mem_sdiff, Set.mem_toFinset, mem_singleton] at hu
    rcases hu with hu | ⟨hu, huneû⟩
    · exact mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs hu) |>.1
    · let w := Nonempty.some (ConnectedComponent.exact hu).symm
      refine hG <| Set.mem_toFinset.mpr
        <| G.degree_pos_iff_mem_support _ |>.mp <| one_le_degree_of_walk_end (Ne.symm huneû) w
  · refine InducesForest_union_disjoint_neighborhoods ?_ ?_ ?_
    · refine InducesForest_mono' ?_ hsforest
      ext u
      simp only [mem_inter, Set.mem_toFinset, notMem_empty, iff_false, not_and]
      exact fun hu ↦ not_iff_not.mpr Set.mem_toFinset |>.mp
        <| mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs hu) |>.2
    · intro t ht htne
      obtain ⟨x, hx⟩ := nonempty_def.mp <| nonempty_iff_ne_empty.mpr htne
      let hobj := mem_sdiff.mp (ht hx) |>.1
      simp only [Set.mem_toFinset, ConnectedComponent.mem_supp_iff] at hobj
      have hûx : G.Reachable û x := ConnectedComponent.exact hobj.symm
      let w := Nonempty.some hûx
      obtain ⟨y, z, hyz, hy, hz⟩ := by
        refine exists_adj w.reverse (· ∈ t) ?_ ?_
        · simp only [hx]
        · simp only
          intro hû
          let bla := mem_sdiff.mp (ht hû) |>.2
          simp only [mem_singleton, not_true_eq_false] at bla
      have hdy : G.degree y = 2 := (hC _ <| Set.mem_toFinset.mp <| mem_sdiff.mp (ht hy) |>.1).2
      refine ⟨y, hy, ?_⟩
      simp only [degree_in]
      have H : (G.neighborFinset y ∩ t) ⊆ (G.neighborFinset y \ {z}) := by
        intro u
        simp only [mem_inter, mem_neighborFinset, mem_sdiff, mem_singleton]
        intro h
        simp only [h.1, true_and]
        exact fun heq ↦ hz <| heq ▸ h.2
      refine le_trans (card_le_card H) ?_
      have H : #(G.neighborFinset y \ {z}) = #(G.neighborFinset y) - #{z} :=
        card_sdiff_of_subset <| by simp only [singleton_subset_iff, mem_neighborFinset, hyz]
      grind [degree]
    · intro x h y hy hxy
      refine  mem_sdiff.mp (ABC.sdiff_toFinset ▸ hs h) |>.2 ?_
      have Hy : G.Reachable û y := by
        refine ConnectedComponent.reachable_of_mem_supp C ?_ ?_
        · exact (C.mem_supp_iff û).mpr rfl
        · exact Set.mem_toFinset.mp <| mem_sdiff.mp hy |>.1
      suffices G.Reachable û x by
        refine Set.mem_toFinset.mpr <| (C.mem_supp_iff x).mpr ?_
        exact ConnectedComponent.sound this.symm
      have H : G.Reachable x y := Adj.reachable hxy
      exact Hy.trans H.symm
  · exact respects_union_path hs hsresp hC
  · exact _eval_ok hG hdû hs hC hscard

lemma Claim14' {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) {û : Fin n} (hû : IsVstar G ABC û)
    (hAû : ABC.A û) (hdû : G.degree û = 2)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  let C := G.connectedComponentMk û
  have : Fintype C.supp := Fintype.ofFinite ↑C.supp
  if hdeg1 : ∃ x ∈ ABC, G.degree x ≤ 1 then
    exact Claim5 hG ih hdeg1
  else if hB2 : ∃ x, ABC.B x ∧ G.degree x = 2 then
    obtain ⟨x, hBx, hdx⟩ := hB2
    exact Claim6 hG ih ⟨x, hdx, not_A_of_B hBx⟩
  else
    simp only [not_exists, not_and] at hB2
    simp only [not_exists, not_and, not_le] at hdeg1
    if hv : ∃ v ∈ C.supp, γ G ABC v = 0 then
      exact ok_of_γ_eq_0 hG hû hAû hdû ih hdeg1 hv
    else
      simp only [not_exists, not_and] at hv
      exact ok_of_γ_ne_0 hG hû hAû hdû ih hdeg1 hB2 hv

lemma Claim14 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) {û : Fin n} (hû : IsVstar G ABC û)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      G'.support.toFinset ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨
      (¬(ABC.A û ∧ G.degree û = 2) ∧ 3 ≤ G.degree û ∧ f G ABC û = G.degree û * γ G ABC û ∧
        ∃ w ∈ G.neighborFinset û, (G.degree w = 3 ∧ ¬ABC.A w)) := by
  have hûABC : û ∈ ABC :=
    ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr
      <| G.degree_pos_iff_mem_support _ |>.mp <| one_le_deg_of_vstar hû
  if hdû : G.degree û ≤ 2 then
    rcases Nat.eq_or_lt_of_le hdû with hdû | hdû
    · rcases hûABC with hA | hB | hC
      · exact Or.inl <| Claim14' hG hû hA hdû ih
      · exact Or.inl <| Claim6 hG ih ⟨û, hdû, not_A_of_B hB⟩
      · exact Or.inl <| Claim6 hG ih ⟨û, hdû, not_A_of_C hC⟩
    · exact Or.inl <| Claim5 hG ih ⟨û, hûABC, Nat.le_of_lt_succ hdû⟩
  else
    simp only [not_le] at hdû
    have hfû : f G ABC û = G.degree û * γ G ABC û := by
      let hcases := not_iff_not.mpr (γ_eq_0_iff hûABC (one_le_deg_of_vstar hû)) |>.mp hû.1.2
      rcases hûABC with hA | hB | hC
      · refine fA_eq_deg_mul_γ_of_three_le_deg hA (Nat.succ_le_of_lt hdû)
      · simp only [hB, and_true, not_C_of_B, and_false, or_false] at hcases
        refine fB_eq_deg_mul_γ_of_four_le_deg hB (by lia)
      · simp only [hC, and_true, not_B_of_C, and_false, false_or, not_or] at hcases
        refine fC_eq_deg_mul_γ_of_four_le_deg hC (by lia)
    if hNû : ∃ w ∈ G.neighborFinset û, (G.degree w = 3 ∧ ¬ABC.A w) then
      refine Or.inr ⟨?_, Nat.succ_le_of_lt hdû, hfû, hNû⟩
      simp only [Nat.ne_of_lt' hdû, and_false, not_false_eq_true]
    else
      simp only [not_exists, not_and, not_not] at hNû
      if hNû' : ∃ w ∈ G.neighborFinset û, γ G ABC w = 0 then
        obtain ⟨w, hwNû, hγw⟩ := hNû'
        have hdw : 1 ≤ G.degree w := one_le_card.mpr ⟨û, mem_neighborFinset_symm hwNû⟩
        have hwABC : w ∈ ABC := by
          refine ABC.coe_mem_toFinset.mpr <| hG <| Set.mem_toFinset.mpr ?_
          exact G.mem_support.mpr ⟨û, Adj.symm <| G.mem_neighborFinset .. |>.mp hwNû⟩
        rcases γ_eq_0_iff hwABC hdw |>.mp hγw with ⟨hdw, hw⟩ | ⟨hdw, hw⟩ | ⟨hdw, hw⟩
        · exact not_A_of_B hw (hNû _ hwNû hdw) |>.elim
        · exact not_A_of_C hw (hNû _ hwNû hdw) |>.elim
        · exact Or.inl <| Claim6 hG ih ⟨w, hdw, not_A_of_C hw⟩
      else
        simp only [not_exists, not_and] at hNû'
        refine Or.inl <| Claim1 hûABC hG ih ?_
        rw [hfû, degree]
        rw[← sum_const' _ fun _ _  ↦ rfl]
        refine sum_le_sum ?_
        intro w hw
        have hwABC : w ∈ ABC.toFinset := by
          refine hG <| Set.mem_toFinset.mpr ?_
          refine G.mem_support.mpr ⟨û, ?_⟩
          exact Adj.symm <| G.mem_neighborFinset .. |>.mp hw
        exact γ_vstar_le_γ hû (ABC.coe_mem_toFinset.mpr hwABC) (hNû' _ hw)

end Tripartition
end ABC
end CaroWeiType
