import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim1
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim2
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim6
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim13
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim15
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim16

open SimpleGraph
open Finset

namespace CaroWeiType
namespace ABC
namespace Tripartition

private lemma Corollary2' {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} [ABC.Decidable] {u v w : Fin n} (hG : G.support ⊆ ABC.toFinset)
    (hvw : ¬G.Adj v w) (hv : G.Adj u v) (hw : G.Adj u w) (hvnew : v ≠ w)
    (hcard : 2 ≥ ∑ v ∈ G.closed_neighborFinset_of_Finset {v, w}, f G ABC v)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  have hF : {v, w} ⊆ ABC.toFinset := by
    intro _ h
    simp only [mem_insert, mem_singleton] at h
    refine hG <| G.mem_support.mpr ⟨u, ?_⟩
    rcases h with h | h
    · exact h ▸ hv.symm
    · exact h ▸ hw.symm
  refine Corollary2 pair_nonempty hG hF (respects_pair_of_non_adj hvw) ih
    InducesLinearForest_pair ?_
  refine le_of_le_of_eq hcard ?_
  rw [← Nat.cast_two, Nat.cast_inj]
  exact Eq.symm <| card_pair hvnew

private lemma Corollary2'' {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} [ABC.Decidable] {û v w x y s t : Fin n}
    (hG : G.support ⊆ ABC.toFinset)
    (hvw : ¬G.Adj v w) (hv : G.Adj û v) (hw : G.Adj û w) (hvnew : v ≠ w)
    (hdv : G.degree v = 3) (hdw : G.degree w = 3)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t})
    (hNvw : ¬∃ u ∈ G.neighborFinset v ∩ G.neighborFinset w, u ≠ û)
    (hcard : 2 ≥ f G ABC v + f G ABC w + f G ABC û + f G ABC x + f G ABC y + f G ABC s + f G ABC t)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  refine Corollary2' hG hvw hv hw hvnew ?_ ih
  simp only [ge_iff_le] at hcard ⊢
  refine le_of_eq_of_le ?_ hcard
  suffices {v, w, û, x, y, s, t} = G.closed_neighborFinset_of_Finset {v, w} by
    simp only [← this]
    simp only [mem_inter, ne_eq, not_exists, not_and, Decidable.not_not, and_imp] at hNvw
    calc _
      _ = ∑ u ∈ {v, w}, f G ABC u + f G ABC û + ∑ u ∈ {x, y, s, t}, f G ABC u := by
        have _ : v ∉ ({û, x, y, s, t} : Finset _) := by
          have _ : v ∉ ({s, t} : Finset _) := by
            refine fun h ↦ hvw ?_
            refine Adj.symm <| G.mem_neighborFinset .. |>.mp <| by grind
          have _ : v ∉ ({û, x, y} : Finset _) :=
            hNv ▸ (G.notMem_neighborFinset_self v)
          grind only [= mem_insert, = mem_singleton]
        have _ : w ∉ ({û, x, y, s, t} : Finset _) := by
          have _ : w ∉ ({x, y} : Finset _) := by
            refine fun h ↦ hvw ?_
            refine G.mem_neighborFinset .. |>.mp <| by grind
          have _ : w ∉ ({û, s, t} : Finset _) :=
            hNw ▸ (G.notMem_neighborFinset_self w)
          grind only [= mem_insert, = mem_singleton]
        grind [degree]
      _ = f G ABC v + f G ABC w + f G ABC û + f G ABC x + f G ABC y + f G ABC s + f G ABC t := by
        have : ({x, y} : Finset _) ∩ {s, t} = ∅ := by
          ext u
          simp only [mem_inter, mem_insert, mem_singleton, notMem_empty, iff_false,
            not_and, not_or]
          intro hu
          rcases hu with hu | hu <;> {
            refine ⟨?_, ?_⟩ <;> {
              intro heq
              have hobj : u ≠ û := by
                grind only [= insert_eq_of_mem, degree, = mem_insert,
                  = mem_singleton, = card_insert_of_notMem, = card_singleton]
              refine hobj ?_
              refine hNvw _ ?_ ?_
              · simp only [hNv, hu, mem_insert, mem_singleton, true_or, or_true]
              · simp only [hNw, heq, mem_insert, mem_singleton, true_or, or_true]
            }
          }
        grind [degree]
  ext u
  simp only [closed_neighborFinset_of_Finset, biUnion_insert, singleton_biUnion]
  grind only [= union_insert, = insert_union, = insert_eq_of_mem, = singleton_union, = mem_insert]

private lemma _step1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    {u v w : Fin n}
    (hCv : ABC.C v) (hdv : G.degree v = 3) (hCw : ABC.C w) (hdw : G.degree w = 3)
    (hvnew : v ≠ w) (hv : G.Adj u v) (hw : G.Adj u w) :
    ∃ v w x y s t : Fin n,
      v ≠ w ∧ ABC.C v ∧ ABC.C w ∧ G.degree v = 3 ∧ G.degree w = 3 ∧ G.Adj u v ∧ G.Adj u w ∧
      G.neighborFinset v = {u, x, y} ∧ G.neighborFinset w = {u, s, t} ∧
      f G ABC y ≤ f G ABC x ∧ f G ABC t ≤ f G ABC s ∧ f G ABC s ≤ f G ABC x := by
  obtain ⟨x, y, hNv, hfyx⟩ :=
    neighborFinset_eq_deg3' (G.mem_neighborFinset .. |>.mpr hv.symm) (f G ABC ·) hdv
  obtain ⟨s, t, hNw, hfts⟩ :=
    neighborFinset_eq_deg3' (G.mem_neighborFinset .. |>.mpr hw.symm) (f G ABC ·) hdw
  if hfsx : f G ABC s ≤ f G ABC x then
    exact ⟨v, w, x, y, s, t, hvnew, hCv, hCw, hdv, hdw, hv, hw, hNv, hNw, hfyx, hfts, hfsx⟩
  else
    have hfxs : f G ABC x ≤ f G ABC s := by lia
    exact ⟨w, v, s, t, x, y, hvnew.symm, hCw, hCv, hdw, hdv, hw, hv, hNw, hNv, hfts, hfyx, hfxs⟩

private lemma _step2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset)
    {v w : Fin n} (hCv : ABC.C v) (hdv : G.degree v = 3) (hCw : ABC.C w) (hdw : G.degree w = 3)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    (∃ z ∈ G.neighborFinset v ∪ G.neighborFinset w, 1 / 6 ≤ γ G ABC z) → Objective G ABC := by
  intro h
  obtain ⟨z, hz, hγz⟩ := h
  simp only [mem_union, mem_neighborFinset] at hz
  rcases hz with hz | hz
  · exact Corollary1 hG hz ih <| (fC3 hCv hdv) ▸ hγz
  · exact Corollary1 hG hz ih <| (fC3 hCw hdw) ▸ hγz

private lemma _step3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w x y s t : Fin n}
    (hCv : ABC.C v) (hdv : G.degree v = 3) (hCw : ABC.C w) (hdw : G.degree w = 3)
    (hv : G.Adj û v) (hw : G.Adj û w) (hvw : ¬G.Adj v w) (hvnew : v ≠ w)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t})
    (h : ¬∃ z ∈ G.neighborFinset v ∪ G.neighborFinset w, 1 / 6 ≤ γ G ABC z)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    (∃ u ∈ G.neighborFinset v ∩ G.neighborFinset w, u ≠ û) → Objective G ABC := by
  have hF' : {v, w} ⊆ ABC.toFinset := by
    intro u hu
    simp only [mem_insert, mem_singleton] at hu
    refine hG <| G.mem_support.mpr ⟨û, ?_⟩
    rcases hu with hu | hu
    · exact hu ▸ hv.symm
    · exact hu ▸ hw.symm
  intro hNvw
  refine Corollary2' hG hvw hv hw hvnew ?_ ih
  have hNclosedvw : G.closed_neighborFinset_of_Finset {v, w}
      = {v, w} ∪ (G.neighborFinset v ∪ G.neighborFinset w) := by
    ext u
    simp only [closed_neighborFinset_of_Finset, biUnion_insert, singleton_biUnion, insert_union,
      singleton_union, mem_insert, mem_union, mem_neighborFinset]
  rw [hNclosedvw]
  calc (2 : ℝ)
    _ ≥ 1 / 6 + 1 / 6 + 4 * (2 / 5) := by linarith
    _ ≥ f G ABC v + f G ABC w + #(G.neighborFinset v ∪ G.neighborFinset w) * (2 / 5) := by
      rw [fC3 hCv hdv, fC3 hCw hdw]
      simp only [one_div, ge_iff_le, add_le_add_iff_left, Nat.ofNat_pos,
        div_pos_iff_of_pos_left, mul_le_mul_iff_left₀, Nat.cast_le_ofNat]
      grind [degree]
    _ = f G ABC v + f G ABC w + ∑ _ ∈ (G.neighborFinset v ∪ G.neighborFinset w), (2 / 5) := by
      simp only [add_right_inj]
      exact Eq.symm <| sum_const' fun _ _ ↦ rfl
    _ ≥ f G ABC v + f G ABC w + ∑ u ∈ (G.neighborFinset v ∪ G.neighborFinset w), f G ABC u := by
      simp only [ge_iff_le, add_le_add_iff_left]
      refine sum_le_sum ?_
      simp only [not_exists, not_and, not_le] at h
      intro u hu
      refine f_le_two_fifths_of_γ_lt_one_sixth ?_ (h _ hu)
      refine (degree_pos_iff_exists_adj G u).mpr ?_
      simp only [mem_union, mem_neighborFinset] at hu
      grind [Adj.symm]
    _ = ∑ u ∈ {v, w}, f G ABC u
        + ∑ u ∈ (G.neighborFinset v ∪ G.neighborFinset w), f G ABC u := by
      grind
  refine le_of_eq <| sum_union ?_
  refine disjoint_iff_inter_eq_empty.mpr ?_
  ext u
  simp only [mem_inter, mem_insert, mem_singleton, mem_union, mem_neighborFinset, notMem_empty,
    iff_false, not_and, not_or]
  intro h
  rcases h with h | h
  · simp only [h, SimpleGraph.irrefl, not_false_eq_true, true_and]
    exact fun h ↦ hvw h.symm
  · simp only [h, SimpleGraph.irrefl, not_false_eq_true, and_true, hvw]

private lemma _step4 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {v w : Fin n}
    (hCv : ABC.C v) (hdv : G.degree v = 3) (hCw : ABC.C w) (hdw : G.degree w = 3)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    (∃ u ∈ G.neighborFinset v ∪ G.neighborFinset w, γ G ABC u = 0) → Objective G ABC := by
  intro hNvwγ
  obtain ⟨u, hu, hγu⟩ := hNvwγ
  simp only [mem_union, mem_neighborFinset] at hu
  have hdu : 0 < G.degree u := by
    rcases hu with hu | hu <;> exact one_le_degree_of_adj' hu
  have huABC : u ∈ ABC := by
    refine ABC.mem_toFinset.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp hdu
  rcases γ_eq_0_iff huABC hdu |>.mp hγu with ⟨hdu, hu'⟩ | ⟨hdu, hu'⟩ | ⟨hdu, hu'⟩
  · rcases hu with hu | hu
    · exact Corollary9 hG hu' hdu ih ⟨v, hu.symm, hCv⟩
    · exact Corollary9 hG hu' hdu ih ⟨w, hu.symm, hCw⟩
  · rcases hu with hu | hu
    · exact Claim13 hG hu hCv hdv hu' hdu ih
    · exact Claim13 hG hu hCw hdw hu' hdu ih
  · exact Claim6 hG ih ⟨u, hdu, not_A_of_C hu'⟩

private lemma _step5 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w x y s t : Fin n}
    (hfû : f G ABC û ≤ 2 / 7)
    (hCv : ABC.C v) (hdv : G.degree v = 3) (hCw : ABC.C w) (hdw : G.degree w = 3)
    (hv : G.Adj û v) (hw : G.Adj û w) (hvw : ¬G.Adj v w) (hvnew : v ≠ w)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t})
    (hNvw : ¬∃ u ∈ G.neighborFinset v ∩ G.neighborFinset w, u ≠ û)
    (hfyx : f G ABC y ≤ f G ABC x) (hfts : f G ABC t ≤ f G ABC s) (hfsx : f G ABC s ≤ f G ABC x)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    (f G ABC x ≤ 1 / 3) → Objective G ABC := by
  intro hfx
  refine Corollary2'' hG hvw hv hw hvnew hdv hdw hNv hNw hNvw ?_ ih
  calc (2 : ℝ)
    _ ≥ 1 / 6 + 1 / 6 + 2 / 7 + 4 * (1 / 3) := by linarith
    _ ≥ f G ABC v + f G ABC w + f G ABC û + 4 * (f G ABC x) := by
      rw [fC3 hCv hdv, fC3 hCw hdw]
      refine add_le_add (add_le_add (le_refl _) hfû) ?_
      simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
      exact hfx
    _ ≥ f G ABC v + f G ABC w + f G ABC û + f G ABC x + f G ABC y + f G ABC s + f G ABC t := by
      linarith

private lemma _step6 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w x y : Fin n}
    (hd1 : ∀ u ∈ ABC, 1 < G.degree u)
    (h : ∀ z ∈ G.neighborFinset v ∪ G.neighborFinset w, γ G ABC z < 1 / 6)
    (hNv : G.neighborFinset v = {û, x, y}) (hfx : ¬f G ABC x ≤ 1 / 3) :
    ABC.A x ∧ G.degree x = 4 := by
  have hdx : 1 ≤ G.degree x := by
    have hx : x ∈ G.neighborFinset v := by
      simp only [hNv, mem_insert, mem_singleton, true_or, or_true]
    exact one_le_degree_of_mem_neighborFinset' hx
  have hAx : ABC.A x := by
    have hxABC : x ∈ ABC := ABC.mem_toFinset.mpr <| hG <| G.degree_pos_iff_mem_support _ |>.mp hdx
    have hdx : 2 ≤ G.degree x := by grind
    rcases hxABC with hA | hB | hC
    · exact hA
    · simp only [f, hB, not_A_of_B, ↓reduceDIte, not_le] at hfx
      grind [fB_decreasing hdx]
    · simp only [f, hC, not_A_of_C, not_B_of_C, ↓reduceDIte, not_le] at hfx
      grind [fC_decreasing hdx]
  have hdx : G.degree x = 4 := by
    simp only [mem_union, hNv] at h
    have hγx : γ G ABC x < 1 / 6 :=
      h _ <| by simp only [mem_insert, mem_singleton, true_or, or_true, mem_neighborFinset]
    have _ : 3 < G.degree x := by grind [γA1, γA2, γA3]
    suffices G.degree x < 5 by linarith
    simp only [f, hAx, ↓reduceDIte, not_le] at hfx
    exact fA_decreasing' (by grind)
  exact ⟨hAx, hdx⟩

private lemma _step7 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w x y : Fin n} (hû : IsVstar G ABC û)
    (hAx : ABC.A x) (hdx : G.degree x = 4) (hCv : ABC.C v) (hdv : G.degree v = 3)
    (hv : G.Adj û v) (hNv : G.neighborFinset v = {û, x, y})
    (hNvwγ : ¬∃ u ∈ G.neighborFinset v ∪ G.neighborFinset w, γ G ABC u = 0)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨ γ G ABC û < 1 / 30 := by
  simp only [mem_union, not_exists, not_and] at hNvwγ
  if hγû : γ G ABC û < 1 / 30 then
    exact Or.inr hγû
  else
  simp only [not_lt] at hγû
  have hvABC : v ∈ ABC := ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨û, hv.symm⟩
  refine Or.inl <| Claim1 hvABC hG ih ?_
  rw [fC3 hCv hdv, hNv]
  calc 1 / (6 : ℝ)
    _ = 1 / 10 + 1 / 30 + 1 / 30 := by linarith
    _ ≤ γ G ABC x + γ G ABC û + γ G ABC û := by
      rw [γA4 hAx hdx]
      refine add_le_add (add_le_add (le_refl _) ?_) ?_ <;> exact hγû
    _ ≤ γ G ABC x + γ G ABC y + γ G ABC û := by
      refine add_le_add (add_le_add (le_refl _) ?_) (le_refl _)
      have hy : y ∈ ABC := by
        refine ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨v, ?_⟩
        refine Adj.symm <| G.mem_neighborFinset .. |>.mp ?_
        simp only [hNv, mem_insert, mem_singleton, or_true]
      refine γ_vstar_le_γ hû hy ?_
      refine hNvwγ _ ?_
      simp only [hNv, mem_insert, mem_singleton, or_true, mem_neighborFinset, true_or]
    _ = ∑ u ∈ {û, x, y}, γ G ABC u := by grind [degree]

private lemma _step8 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v x y : Fin n}
    (hAx : ABC.A x) (hdx : G.degree x = 4) (hCv : ABC.C v) (hdv : G.degree v = 3)
    (hv : G.Adj û v) (hNv : G.neighborFinset v = {û, x, y})
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨ γ G ABC y < 1 / 15 := by
  if hγy : γ G ABC y < 1 / 15 then exact Or.inr hγy
  else
  simp only [not_lt] at hγy
  have hvABC : v ∈ ABC := ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨û, hv.symm⟩
  refine Or.inl <| Claim1 hvABC hG ih ?_
  rw [fC3 hCv hdv, hNv]
  calc 1 / (6 : ℝ)
    _ = 1 / 10 + 1 / 15 := by linarith
    _ ≤ γ G ABC x + γ G ABC y := by
      rw [γA4 hAx hdx]
      simp only [add_le_add_iff_left, hγy]
  grind [degree]

private lemma _step9 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w x y s t : Fin n}
    (hCv : ABC.C v) (hdv : G.degree v = 3) (hCw : ABC.C w) (hdw : G.degree w = 3)
    (hvw : ¬G.Adj v w) (hvnew : v ≠ w) (hv : G.Adj û v) (hw : G.Adj û w)
    (hfû : f G ABC û ≤ 2 / 9) (hfx : f G ABC x = 2 / 5) (hfy : f G ABC y ≤ 2 / 7)
    (hNv : G.neighborFinset v = {û, x, y}) (hNw : G.neighborFinset w = {û, s, t})
    (hNvw : ¬∃ u ∈ G.neighborFinset v ∩ G.neighborFinset w, u ≠ û)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC ∨ 239 / 315 < f G ABC s + f G ABC t := by
  if H : 239 / 315 < f G ABC s + f G ABC t then exact Or.inr H
  else
  refine Or.inl <| Corollary2'' hG hvw hv hw hvnew hdv hdw hNv hNw hNvw ?_ ih
  rw [fC3 hCv hdv, fC3 hCw hdw]
  linarith

private lemma _A4 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {u : Fin n} (hdu : 2 ≤ G.degree u)
    (hfu : 1 / 3 < f G ABC u) (hγu : γ G ABC u < 1 / 6) :
    ABC.A u ∧ G.degree u = 4 := by
  have huABC : u ∈ ABC :=
    ABC.mem_toFinset.mpr <| hG <| (degree_pos_iff_mem_support G u).mp <| Nat.zero_lt_of_lt hdu
  rcases huABC with hA | hB | hC
  · refine ⟨hA, ?_⟩
    by_contra
    have fA5 : fA 5 = 1 / 3 := by grind
    simp only [f, hA, ↓reduceDIte] at hfu
    have := fA_decreasing' (fA5 ▸ hfu)
    have hdu : G.degree u ≤ 3 := by lia
    grind [γA1, γA2, γA3]
  · have hfB3 : fB 3 = 1 / 3 := by grind
    simp only [f, hB, not_A_of_B, ↓reduceDIte, ← hfB3] at hfu
    grind [fB_decreasing' hfu]
  · have hfC1 : fC 2 = 1 / 6 := by grind
    let hobj := hfC1 ▸ (fC_decreasing hdu)
    simp only [f, hC, not_A_of_C, not_B_of_C, ↓reduceDIte] at hfu
    linarith

lemma Claim17 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    [ABC.Decidable] (hG : G.support ⊆ ABC.toFinset) {û v w : Fin n} (hû : IsVstar G ABC û)
    (hCv : ABC.C v) (hdv : G.degree v = 3) (hCw : ABC.C w) (hdw : G.degree w = 3)
    (hvnew : v ≠ w) (hv : G.Adj û v) (hw : G.Adj û w)
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n)
      [ABC'.Decidable], G'.support ⊆ ABC'.toFinset → ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  obtain ⟨v, w, x, y, s, t, hvnew, hCv, hCw, hdv, hdw, hv, hw, hNv, hNw, hfyx, hfts, hfsx⟩ :=
    _step1 hCv hdv hCw hdw hvnew hv hw
  match Corollary16 hG hû hCv hdv ih, Claim15 hG hû ih with
  | Or.inl h, _ => exact h
  | _, Or.inl h => exact h
  | Or.inr h, Or.inr hdû => ?_
  obtain ⟨hfû, hγû⟩ := h
  if hdeg_le_1 : ∃ u ∈ ABC, G.degree u ≤ 1 then
    exact Claim5 hG ih hdeg_le_1
  else if hdeg2 : ∃ u, G.degree u = 2 ∧ ¬ABC.A u then
    refine Claim6 hG ih hdeg2
  else if hvw : G.Adj v w then
    exact Claim13 hG hvw hCv hdv hCw hdw ih
  else if h : ∃ z ∈ G.neighborFinset v ∪ G.neighborFinset w, 1 / 6 ≤ γ G ABC z then
    exact _step2 hG hCv hdv hCw hdw ih h
  else if hNvw : ∃ u ∈ G.neighborFinset v ∩ G.neighborFinset w, u ≠ û then
    exact _step3 hG hCv hdv hCw hdw hv hw hvw hvnew hNv hNw h ih hNvw
  else if hNvwγ : ∃ u ∈ G.neighborFinset v ∪ G.neighborFinset w, γ G ABC u = 0 then
    exact _step4 hG hCv hdv hCw hdw ih hNvwγ
  else if hfx : f G ABC x ≤ 1 / 3 then
    exact _step5 hG hfû hCv hdv hCw hdw hv hw hvw hvnew hNv hNw hNvw hfyx hfts hfsx ih hfx
  else
    simp only [not_exists, not_and, not_not] at hdeg2
    simp only [not_exists, not_and, not_le] at hdeg_le_1
    simp only [not_exists, not_and, not_le] at h
    obtain ⟨hAx, hdx⟩ := _step6 hG hdeg_le_1 h hNv hfx
    match _step7 hG hû hAx hdx hCv hdv hv hNv hNvwγ ih, _step8 hG hAx hdx hCv hdv hv hNv ih with
    | Or.inl h, _ => exact h
    | _, Or.inl h => exact h
    | Or.inr hγû, Or.inr hγy => ?_
    have hfû := f_le_two_ninths_of_γ_lt_one_thirtieth hdû hγû
    have hfy := by
      simp only [mem_union, not_exists, not_and] at hNvwγ
      refine f_le_two_sevenths_of_γ_lt_one_fifteenth_of_γ_ne_zero hγy ?_
      refine hNvwγ _ (by grind)
    match _step9 hG hCv hdv hCw hdw hvw hvnew hv hw hfû (fA4 hAx hdx) hfy hNv hNw hNvw ih with
    | Or.inl h => exact h
    | Or.inr hfst => ?_
    have hsw : s ∈ G.neighborFinset w := by simp [hNw]
    let hsABC := ABC.mem_toFinset.mpr <| hG
        <| G.mem_support.mpr ⟨w, Adj.symm <| G.mem_neighborFinset .. |>.mp hsw⟩
    obtain ⟨hAs, hds⟩ := by
      refine _A4 hG (hdeg_le_1 _ hsABC) ?_ (h _ (by simp only [mem_union, hsw, or_true]))
      calc (1 : ℝ) / 3
        _ = (2 / 3) / 2 := by linarith
        _ < (f G ABC s + f G ABC t) / 2 := by linarith
        _ ≤ (f G ABC s + f G ABC s) / 2 := by
          refine (div_le_div_iff_of_pos_right two_pos).mpr ?_
          simp only [add_le_add_iff_left, hfts]
        _ = f G ABC s := by linarith
    have htw : t ∈ G.neighborFinset w := by simp [hNw]
    let htABC := ABC.mem_toFinset.mpr <| hG
        <| G.mem_support.mpr ⟨w, Adj.symm <| G.mem_neighborFinset .. |>.mp htw⟩
    obtain ⟨hAt, hdt⟩ := by
      refine _A4 hG (hdeg_le_1 _ htABC) ?_ (h _ (by simp only [mem_union, htw, or_true]))
      linarith [fA4 hAs hds]
    have hwABC : w ∈ ABC := ABC.mem_toFinset.mpr <| hG <| G.mem_support.mpr ⟨û, hw.symm⟩
    refine Claim1 hwABC hG ih ?_
    refine le_of_lt ?_
    calc f G ABC w
      _ = 1 / 6 := by rw [fC3 hCw hdw]
      _ < 1 / 10 + 1 / 10 := by linarith
      _ = γ G ABC s + γ G ABC t := by rw [γA4 hAs hds, γA4 hAt hdt]
      _ = ∑ u ∈ {s, t}, γ G ABC u := by grind [degree]
      _ ≤ ∑ u ∈ G.neighborFinset w, γ G ABC u :=
        sum_le_sum_of_subset_of_nonneg (by grind) fun _ _ _ ↦ γ_nonneg

end Tripartition
end ABC
end CaroWeiType
