import CWType.SimpleGraph.CaroWeiType.Lemmas
import CWType.SimpleGraph.CaroWeiType.ForestOfStars.AB
import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas

open Finset

namespace CaroWeiType
namespace AB

variable {V : Type} [Fintype V]

@[simp]
lemma not_A_of_B {AB : Bipartition V} {v : V} (hB : AB.B v) : ¬AB.A v :=
  fun hA ↦ AB.sound v ⟨hA, hB⟩

@[simp]
lemma not_B_of_A {AB : Bipartition V} {v : V} (hA : AB.A v) : ¬AB.B v :=
  fun hB ↦ AB.sound v ⟨hA, hB⟩

lemma f_eq_one_of_degree_eq_zero (G : SimpleGraph V) {AB : Bipartition V} {v : V} (hv : v ∈ AB)
    [Fintype (G.neighborSet v)] (hdv : G.degree v = 0) :
    f G AB v = 1 := by
  rcases hv with hA | hB
  · simp only [f, hA, ↓reduceDIte, fA, hdv, ↓reduceIte]
  · simp only [f, hB, not_A_of_B, ↓reduceDIte, fB, hdv, Nat.cast_zero, zero_add,
      div_self one_ne_zero]

lemma f_eq_zero_of_notMem (G : SimpleGraph V) {AB : Bipartition V}
    {v : V} [Fintype (G.neighborSet v)] (hv : v ∉ AB) :
    0 = f G AB v := by
  simp only [Bipartition.mem_iff, not_or] at hv
  simp only [f, hv.1, hv.2, ↓reduceDIte]

lemma γ_eq_zero_of_notMem (G : SimpleGraph V) {AB : Bipartition V}
    {v : V} [Fintype (G.neighborSet v)] (hv : v ∉ AB) :
    0 = γ G AB v := by
  simp only [Bipartition.mem_iff, not_or] at hv
  simp only [γ, hv.1, hv.2, ↓reduceDIte]

lemma ℓ_eq_zero_of_notMem (G : SimpleGraph V) {AB : Bipartition V}
    {v : V} [Fintype (G.neighborSet v)] (hv : v ∉ AB) :
    0 = ℓ G AB v := by
  simp only [Bipartition.mem_iff, not_or] at hv
  simp only [ℓ, hv.1, hv.2, ↓reduceDIte]

lemma AB_iff {v : V} {AB : Bipartition V} {s : Finset V} (hvs : v ∉ s) :
    (AB.A v → (AB \ s).A v) ∧ (AB.B v → (AB \ s).B v) ∧ (v ∉ AB → v ∉ (AB \ s)) :=
  ⟨fun hAv ↦ ⟨hAv, hvs⟩, fun hBv ↦ ⟨hBv, hvs⟩, mt <| fun h ↦ h.elim (Or.inl ·.1) (Or.inr ·.1)⟩

open SimpleGraph

lemma f_congr {G G' : SimpleGraph V} {AB AB' : Bipartition V}
    {v : V} [Fintype (G.neighborSet v)] [Fintype (G'.neighborSet v)]
    (hdv : G.degree v = G'.degree v)
    (hv : (AB.A v → AB'.A v) ∧ (AB.B v → AB'.B v) ∧ (v ∉ AB → v ∉ AB')) :
    f G AB v = f G' AB' v := by
  if hvAB : v ∈ AB then
    rcases hvAB with hA | hB
    · simp only [f, hA, hv.1 hA, ↓reduceDIte, hdv]
    · simp only [f, hB, hv.2.1 hB, not_A_of_B, ↓reduceDIte, hdv]
  else
    rw [← f_eq_zero_of_notMem G hvAB, ← f_eq_zero_of_notMem G' <| by grind]

lemma f_congr' {G : SimpleGraph V} {AB : Bipartition V} {s : Finset V} {v : V} (hvs : v ∉ s)
    [Fintype (G.neighborSet v)] [Fintype ((G.deleteIncidencesOf s).neighborSet v)]
    (hdv : G.degree v = (G.deleteIncidencesOf s).degree v) :
    f G AB v = f (G.deleteIncidencesOf s) (AB \ s) v :=
  f_congr hdv (AB_iff hvs)

lemma f_congr'' [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] {AB : Bipartition V}
    {s : Finset V} {v : V} (hvs' : v ∉ G.closed_neighborFinset_of_Finset s)
    [Fintype ((G.deleteIncidencesOf s).neighborSet v)] :
    f G AB v = f (G.deleteIncidencesOf s) (AB \ s) v := by
  have hvs : v ∉ s := notMem_mono closed_neighborFinset_contains_Finset hvs'
  simp only [mem_closed_neighborFinset_iff, not_or, not_exists, not_and] at hvs'
  refine f_congr' hvs ?_
  refine degree_eq_deleteIncidencesOf_degree_of_inter_neighborhood_empty hvs ?_
  ext w
  simp only [mem_inter, mem_neighborFinset, notMem_empty, iff_false, not_and]
  refine fun hws ↦ not_adj_symm <| hvs'.2 w hws

lemma fB_le_fA {d : ℕ} : fB d ≤ fA d := by
  if hd : d = 0 then
    simp only [fA, fB, hd, ↓reduceIte, Nat.cast_zero, zero_add, div_self one_ne_zero, le_refl]
  else if hd : d = 1 then
    simp only [fA, fB, hd, one_ne_zero, ↓reduceIte, Nat.cast_one]
    linarith
  else if hd : d = 2 then
    simp only [fA, fB, hd, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.cast_ofNat]
    linarith
  else
    simp only [fA, fB, ↓reduceIte, *]
    exact (div_le_div_iff_of_pos_right add_one_pos).mpr one_le_two

lemma fB_pos {d : ℕ} : 0 < fB d :=
  Nat.one_div_pos_of_nat

lemma zero_le_fB {d : ℕ} : 0 ≤ fB d :=
  le_of_lt fB_pos

lemma fA_pos {d : ℕ} : 0 < fA d :=
  lt_of_lt_of_le fB_pos fB_le_fA

lemma zero_le_fA {d : ℕ} : 0 ≤ fA d :=
  le_trans zero_le_fB fB_le_fA

namespace Bipartition
open SimpleGraph

variable {V : Type} [Fintype V]

lemma mem_toSet (AB : Bipartition V) {x : V} :
    x ∈ AB ↔ x ∈ AB.toSet := by
  simp only [toSet, Set.mem_setOf_eq]

lemma mem_toFinset (AB : Bipartition V) [AB.Decidable] {x : V} :
    x ∈ AB ↔ x ∈ AB.toFinset := by
  simp only [mem_toSet, toFinset, Set.mem_toFinset]

@[simp]
lemma sdiff_notMem (AB : Bipartition V) (s : Finset V) :
    ∀ x ∈ s, x ∉ AB \ s := by
  intro x hx
  simp [sdiff, hx]

@[simp]
lemma sdiff_mem (AB : Bipartition V) (s : Finset V) :
    ∀ x ∈ AB, x ∉ s → x ∈ AB \ s := by
  intro x hx hxs
  simp only [mem_iff] at hx
  rcases hx with hx | hx
  · exact (mem_iff _).mpr <| Or.inl ⟨hx, hxs⟩
  · exact (mem_iff _).mpr <| Or.inr ⟨hx, hxs⟩

@[simp]
lemma mem_sdiff_iff (AB : Bipartition V) (s : Finset V) {x : V} :
    x ∈ AB \ s ↔ (x ∈ AB ∧ x ∉ s) := by
  refine ⟨?_, fun ⟨hx, hxs⟩ ↦ sdiff_mem AB s x hx hxs⟩
  refine fun hx ↦ ⟨?_, fun this ↦ AB.sdiff_notMem s _ this hx |>.elim⟩
  rcases (mem_iff _).mpr hx with h | h
  <;> simp only [mem_iff, h.1, or_true, true_or, not_A_of_B, not_B_of_A]

@[simp]
lemma toFinset_mono [DecidableEq V] {AB : Bipartition V} [AB.Decidable] {s : Finset V} :
    (AB \ s).toFinset ⊆ AB.toFinset := by
  simp only [toFinset, toSet, sdiff, mem_iff]
  intro x hx
  simp only [and_or_2, Set.toFinset_setOf, mem_filter, mem_univ, true_and] at hx ⊢
  exact hx.1

@[simp]
lemma toFinset_eq [DecidableEq V] {AB : Bipartition V} [AB.Decidable] {s : Finset V} :
    (AB \ s).toFinset = AB.toFinset \ s := by
  ext w
  simp only [toFinset, toSet, sdiff, mem_iff, Set.toFinset_setOf, mem_sdiff, mem_filter, mem_univ,
    true_and, and_or_2]

lemma sdiff_card [DecidableEq V] (AB : Bipartition V) [AB.Decidable] {s : Finset V}
    (hs : s ∩ AB.toFinset ≠ ∅) : (AB \ s).card < AB.card := by
  simp only [card, card, toFinset_eq, card_sdiff]
  suffices 0 < #(s ∩ AB.toFinset) by
    exact Nat.sub_lt (lt_of_lt_of_le this <| card_le_card inter_subset_right) this
  exact card_lt_card <| Finset.ssubset_iff_subset_ne.mpr ⟨empty_subset _, Ne.symm hs⟩

lemma sdiff_toFinset [DecidableEq V] (AB : Bipartition V) [AB.Decidable] {s : Finset V} :
    (AB \ s).toFinset = AB.toFinset \ s := by
  ext y
  simp only [toFinset, toSet, sdiff, mem_iff, and_or_2, Set.toFinset_setOf, mem_sdiff, mem_filter,
    mem_univ, true_and]

lemma hsupp_mono [DecidableEq V] {G : SimpleGraph V} {AB : Bipartition V} [AB.Decidable]
    {W : Finset _} (hG : G.support ⊆ AB.toFinset) :
    (G.deleteIncidencesOf W).support ⊆ (AB \ W).toFinset := by
  intro u hu
  simp only [support, SetRel.mem_dom, Set.mem_setOf_eq] at hu
  obtain ⟨v, hv⟩ := hu
  simp only [AB.sdiff_toFinset]
  simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, inf_adj, iInf_adj,
    deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq] at hv
  obtain ⟨huv, h, _⟩ := hv
  refine mem_sdiff.mpr ⟨?_, ?_⟩
  · exact hG <| G.mem_support.mpr ⟨v, huv⟩
  · exact fun hu ↦ false_of_ne <| h u |>.1 hu |>.2 huv |>.1

end Bipartition

lemma fA_decreasing {d d' : ℕ} (h : d ≤ d') : fA d' ≤ fA d := by
  if heq : d = d' then exact le_of_eq (heq ▸ rfl) else ?_
  simp only [fA]
  split_ifs
  any_goals grind
  · refine (div_le_one₀ add_one_pos).mpr ?_
    rw [← Nat.cast_two, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    lia
  · refine @le_trans _ _ _ (2 / 3) _ ?_ (by linarith)
    refine (div_le_div_iff_of_pos_left two_pos add_one_pos three_pos).mpr ?_
    rw [← Nat.cast_three, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    suffices 2 ≤ d' by linarith
    refine two_le_of_ne_zero_of_ne_one ?_ ?_ <;> grind only
  · refine (div_le_div_iff₀ add_one_pos five_pos).mpr ?_
    suffices 4 ≤ (d' + 1 : ℝ) by
      linarith
    rw [← Nat.cast_four, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    lia
  · refine (div_le_div_iff₀ add_one_pos add_one_pos).mpr
      <| mul_le_mul (le_refl _) ?_ add_one_nonneg zero_le_two
    rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.cast_le]
    exact Nat.add_le_add_right h _

lemma fA_decreasing' {d d' : ℕ} (h : fA d' < fA d) : d < d' := by
  exact Nat.lt_of_not_le <| fA_decreasing.mt <| not_le.mpr h

lemma fB_decreasing {d d' : ℕ} (h : d ≤ d') : fB d' ≤ fB d := by
  simp only [fB]
  exact Nat.one_div_le_one_div h

lemma fB_decreasing' {d d' : ℕ} (h : fB d' < fB d) : d < d' := by
  exact Nat.lt_of_not_le <| fB_decreasing.mt <| not_le.mpr h

lemma f_congr_degree (G₁ G₂ : SimpleGraph V) (AB : Bipartition V)
    {v : V} [Fintype (G₁.neighborSet v)] [Fintype (G₂.neighborSet v)] :
    G₁.degree v = G₂.degree v → f G₁ AB v = f G₂ AB v := by
  intro heq
  simp only [f, fA, fB, one_div, dite_eq_ite, heq]

lemma f_le_f {G G' : SimpleGraph V} {AB AB' : Bipartition V}
    {v : V} [Fintype (G.neighborSet v)] [Fintype (G'.neighborSet v)]
    (hdv : G.degree v ≤ G'.degree v)
    (hv : (AB.A v → AB'.A v) ∧ (AB.B v → AB'.B v) ∧ (v ∉ AB → v ∉ AB')) :
    f G' AB v ≤ f G AB' v := by
  if hAv : AB.A v then
    simp only [f, hAv, hv, ↓reduceDIte]
    exact fA_decreasing hdv
  else if hBv : AB.B v then
    simp only [f, hBv, hv, not_A_of_B, ↓reduceDIte]
    exact fB_decreasing hdv
  else
    have hvAB : v ∉ AB := by simp only [AB.mem_iff, hAv, hBv, false_or, not_false_eq_true]
    rw [← f_eq_zero_of_notMem _ hvAB, ← f_eq_zero_of_notMem _ (hv.2.2 hvAB)]

lemma f_le_f' {G : SimpleGraph V} {AB : Bipartition V} {v : V} {s : Finset V}
    [Fintype (G.neighborSet v)] [Fintype ((G.deleteIncidencesOf s).neighborSet v)] :
    f G AB v ≤ f (G.deleteIncidencesOf s) AB v :=
  f_le_f deleteIncidencesOf_degree_le (by grind)

lemma f_eq_in_sdiff (G : SimpleGraph V) (AB : Bipartition V)
    {s : Finset V} {w : V} [Fintype (G.neighborSet w)] (hw : w ∉ s) :
    f G (AB \ s) w = f G AB w := by
  have hAiff : AB.A w ↔ (AB \ s).A w := ⟨fun h ↦ ⟨h, hw⟩, fun ⟨h, _⟩ ↦ h⟩
  have hBiff : AB.B w ↔ (AB \ s).B w := ⟨fun h ↦ ⟨h, hw⟩, fun ⟨h, _⟩ ↦ h⟩
  if hw : w ∈ AB then
    rcases hw with hA | hB
    · simp only [f, hA, hAiff.mp, ↓reduceDIte]
    · simp only [f, hB, hBiff.mp, not_A_of_B, ↓reduceDIte]
  else
    have hw' : w ∉ (AB \ s) := by grind only [Bipartition.mem_iff]
    rw [← f_eq_zero_of_notMem _ hw, ← f_eq_zero_of_notMem _ hw']

lemma fB_le_f {G : SimpleGraph V} {AB : Bipartition V}
    {v : V} [Fintype (G.neighborSet v)] (hv : v ∈ AB) :
    fB (G.degree v) ≤ f G AB v  := by
  rcases hv with hA | hB
  · simp only [f, hA, ↓reduceDIte, fB_le_fA]
  · simp only [f, hB, not_A_of_B, ↓reduceDIte, le_refl]

lemma fA_le_one {d : ℕ} : fA d ≤ 1 := by
  refine le_of_le_of_eq (fA_decreasing <| Nat.zero_le d) ?_
  simp only [fA, ↓reduceIte]

lemma fB_le_one {d : ℕ} : fB d ≤ 1 :=
  le_trans fB_le_fA fA_le_one

lemma f_le_one {G : SimpleGraph V} {AB : Bipartition V} {v : V} [Fintype (G.neighborSet v)] :
    f G AB v ≤ 1 := by
  rw [f]
  split_ifs
  · exact fA_le_one
  · exact fB_le_one
  · exact zero_le_one

lemma f_le_fA {G : SimpleGraph V} {AB : Bipartition V} {v : V} [Fintype (G.neighborSet v)] :
    f G AB v ≤ fA (G.degree v) := by
  rw [f]
  split_ifs
  · exact le_refl _
  · exact fB_le_fA
  · exact zero_le_fA

lemma f_le_five_sixths_of_one_le_degree {G : SimpleGraph V} {AB : Bipartition V}
    {v : V} [Fintype (G.neighborSet v)] (hdv : 1 ≤ G.degree v) :
    f G AB v ≤ 5 / 6 := by
  simp only [f]
  split_ifs
  · refine le_trans (fA_decreasing hdv) ?_
    simp only [fA, one_ne_zero, ↓reduceIte, le_refl]
  · refine le_trans (fB_decreasing hdv) ?_
    simp only [fB, Nat.cast_one]
    linarith
  · linarith

namespace Bipartition

@[simp]
lemma demote_finset_from_A (AB : Bipartition V) {v : V} (hAv : AB.A v)
    {s : Finset _} (hv : v ∈ s) : (AB.demote_finset s).B v :=
  Or.inr ⟨hAv, hv⟩

@[simp]
lemma demote_finset_from_B (AB : Bipartition V) {v : V} (hBv : AB.B v)
    {s : Finset _} : (AB.demote_finset s).B v :=
  Or.inl hBv

@[simp]
lemma demote_from_A (AB : Bipartition V) {v : V} (hAv : AB.A v) :
    (AB.demote v).B v :=
  AB.demote_finset_from_A hAv (Finset.mem_singleton.mpr rfl)

@[simp]
lemma demote_from_A' (AB : Bipartition V) {v : V} (hAv : AB.A v) :
    ¬(AB.demote v).A v :=
  not_A_of_B <| demote_from_A AB hAv

@[simp]
lemma demote_from_B (AB : Bipartition V) {v : V} (hBv : AB.B v) :
    (AB.demote v).B v :=
  AB.demote_finset_from_B hBv

@[simp]
lemma demote_B_self (AB : Bipartition V) {v : V} (hv : v ∈ AB) :
    (AB.demote v).B v := by
  rcases hv with hA | hB
  · exact AB.demote_from_A hA
  · exact AB.demote_from_B hB

@[simp]
lemma demote_finset_A_of_notin_of_A (AB : Bipartition V) {v : V} {s : Finset _}
    (hv : v ∉ s) (hAv : AB.A v) : (AB.demote_finset s).A v :=
  ⟨hAv, hv⟩

@[simp]
lemma demote_finset_B_of_A_of_mem (AB : Bipartition V) {v : V} {s : Finset _}
    (hAv : AB.A v) (hvs : v ∈ s) :
    (AB.demote_finset s).B v :=
  Or.inr ⟨hAv, hvs⟩

@[simp]
lemma demote_finset_B_of_B (AB : Bipartition V) {v : V} {s : Finset _} (hBv : AB.B v) :
    (AB.demote_finset s).B v :=
  Or.inl hBv

@[simp]
lemma demote_finset_B_of_mem (AB : Bipartition V) {v : V} {s : Finset _}
    (hv : v ∈ AB) (hvs : v ∈ s) :
    (AB.demote_finset s).B v :=
  hv.elim (demote_finset_B_of_A_of_mem _ · hvs) (demote_finset_B_of_B _ ·)

@[simp]
lemma demote_A_of_ne (AB : Bipartition V) {v w : V} (h : v ≠ w) (hAv : AB.A v) :
    (AB.demote w).A v :=
  AB.demote_finset_A_of_notin_of_A (not_iff_not.mpr mem_singleton |>.mpr h) hAv

@[simp]
lemma demote_B_of_B (AB : Bipartition V) {v w : V} (hBv : AB.B v) : (AB.demote w).B v :=
  AB.demote_finset_B_of_B hBv

lemma mem_promote_finset_of_mem (AB : Bipartition V) {x : V} {s : Finset _} :
    x ∈ AB → x ∈ AB.promote_finset s := by
  intro h
  if hin : x ∈ s then
    rcases h with h | h
    · simp only [mem_iff, promote_finset, h, true_or]
    · simp only [mem_iff, promote_finset, h, true_and, hin, or_true, true_or]
  else
    rcases h with h | h <;>
    simp only [mem_iff, promote_finset, h, hin, true_or, or_true, not_false_eq_true, and_true]

lemma mem_promote_of_mem (AB : Bipartition V) {x y : V} :
    x ∈ AB → x ∈ AB.promote y := by
  intro h
  simp only [promote]
  exact AB.mem_promote_finset_of_mem h

lemma mem_of_mem_promote_finset (AB : Bipartition V) {x : V} {s : Finset _} :
    x ∈ AB.promote_finset s → x ∈ AB := by
  intro h
  rcases h with h | h <;> {
    simp only [promote_finset, mem_iff] at h ⊢
    grind
  }

lemma mem_of_mem_promote (AB : Bipartition V) {x y : V} :
    x ∈ AB.promote y → x ∈ AB := by
  simp only [promote]
  exact AB.mem_of_mem_promote_finset

lemma mem_demote_finset_of_mem (AB : Bipartition V) {x : V} {s : Finset _} :
    x ∈ AB → x ∈ AB.demote_finset s := by
  intro h
  if hin : x ∈ s then
    rcases h with h | h
    · exact Bipartition.mem_iff _ |>.mpr <| Or.inr <| AB.demote_finset_from_A h hin
    · exact Bipartition.mem_iff _ |>.mpr <| Or.inr <| AB.demote_finset_from_B h
  else
    rcases h with h | h
    · exact Bipartition.mem_iff _ |>.mpr <| Or.inl <| AB.demote_finset_A_of_notin_of_A hin h
    · exact Bipartition.mem_iff _ |>.mpr <| Or.inr <| AB.demote_finset_from_B h

lemma mem_demote_of_mem (AB : Bipartition V) {x y : V} :
    x ∈ AB → x ∈ AB.demote y := by
  intro h
  simp only [demote]
  exact AB.mem_demote_finset_of_mem h

lemma mem_of_mem_demote_finset (AB : Bipartition V) {x : V} {s : Finset _} :
    x ∈ AB.demote_finset s → x ∈ AB := by
  intro h
  rcases h with h | h | h
  · simp only [mem_iff, h.1, true_or]
  · exact Or.inr h
  · exact Or.inl h.1

lemma mem_of_mem_demote (AB : Bipartition V) {x y : V} :
    x ∈ AB.demote y → x ∈ AB := by
  simp only [demote]
  exact AB.mem_of_mem_demote_finset

@[simp]
lemma mem_iff_mem_demote (AB : Bipartition V) {x y : V} :
    x ∈ AB ↔ x ∈ AB.demote y :=
  ⟨AB.mem_demote_of_mem, AB.mem_of_mem_demote⟩

@[simp]
lemma mem_iff_mem_demote_tofinset (AB : Bipartition V) {x : V} {s : Finset _} :
    x ∈ AB ↔ x ∈ AB.demote_finset s :=
  ⟨AB.mem_demote_finset_of_mem, AB.mem_of_mem_demote_finset⟩

lemma promote_from_A (AB : Bipartition V) (v : V) (hv : AB.A v) :
    (AB.promote v).A v := by
  simp only [promote, promote_finset, hv, not_B_of_A, true_or]

lemma promote_from_B (AB : Bipartition V) (v : V) (hv : AB.B v) :
    (AB.promote v).A v := by
  simp only [promote, promote_finset, hv, not_A_of_B, false_or, true_and, mem_singleton_self]

lemma promote_from_B' (AB : Bipartition V) (v : V) (hv : AB.B v) :
    ¬(AB.promote v).B v := by
  exact not_B_of_A <| promote_from_B AB v hv

@[simp]
lemma A_of_promote_ne (AB : Bipartition V) {v w : V} (h : v ≠ w) :
    AB.A v → (AB.promote w).A v := by
  intro hA
  simp only [promote, promote_finset, mem_singleton, h, hA, true_or]

@[simp]
lemma B_of_promote_ne (AB : Bipartition V) {v w : V} (h : v ≠ w) :
    AB.B v → (AB.promote w).B v := by
  intro hB
  simp only [promote, promote_finset, mem_singleton, h, hB, true_and, not_false_eq_true]

lemma demote_toFinset_eq [DecidableEq V] (AB : Bipartition V) [AB.Decidable] {x : V} :
    AB.toFinset = (AB.demote x).toFinset := by
  ext y
  simp only [← mem_toFinset]
  exact ⟨AB.mem_demote_of_mem, AB.mem_of_mem_demote⟩

lemma promote_finset_toFinset_eq [DecidableEq V] (AB : Bipartition V) [AB.Decidable]
    {s : Finset V} :
    AB.toFinset = (AB.promote_finset s).toFinset := by
  ext y
  simp only [← mem_toFinset]
  refine ⟨?_, ?_⟩
  · exact AB.mem_promote_finset_of_mem
  · exact AB.mem_of_mem_promote_finset

lemma demote_finset_toFinset_eq [DecidableEq V] (AB : Bipartition V) [AB.Decidable]
    {s : Finset V} :
    AB.toFinset = (AB.demote_finset s).toFinset := by
  ext y
  simp only [← mem_toFinset]
  refine ⟨?_, ?_⟩
  · exact AB.mem_demote_finset_of_mem
  · exact AB.mem_of_mem_demote_finset

lemma promote_toFinset_eq [DecidableEq V] (AB : Bipartition V) [AB.Decidable] {x : V} :
    AB.toFinset = (AB.promote x).toFinset := by
  ext y
  simp only [← mem_toFinset]
  exact ⟨mem_promote_of_mem AB, mem_of_mem_promote AB⟩

@[simp]
lemma card_promote_finset_eq_card [DecidableEq V] {AB : Bipartition V} [AB.Decidable]
    {s : Finset _} :
    AB.card = (AB.promote_finset s).card := by
  simp only [card]
  rw [promote_finset_toFinset_eq]

@[simp]
lemma card_demote_finset_eq_card [DecidableEq V] {AB : Bipartition V} [AB.Decidable]
    {s : Finset _} :
    AB.card = (AB.demote_finset s).card := by
  simp only [card]
  rw [demote_finset_toFinset_eq]

@[simp]
lemma card_demote_eq_card [DecidableEq V] {AB : Bipartition V} [AB.Decidable] {x : V} :
    AB.card = (AB.demote x).card := by
  simp only [card]
  rw [demote_toFinset_eq]

@[simp]
lemma card_promote_eq_card [DecidableEq V] {AB : Bipartition V} [AB.Decidable] {x : V} :
    AB.card = (AB.promote x).card := by
  simp only [card]
  rw [promote_toFinset_eq]

lemma f_eq_of_demote_finset_of_notMem (G : SimpleGraph V) (AB : Bipartition V) [AB.Decidable]
    {x : V} {s : Finset V} (h : x ∉ s) [Fintype (G.neighborSet x)] :
    f G AB x = f G (AB.demote_finset s) x := by
  refine f_congr rfl ⟨AB.demote_finset_A_of_notin_of_A h, AB.demote_finset_B_of_B , ?_⟩
  grind [mem_iff, demote_finset]

lemma f_eq_of_demote_of_ne (G : SimpleGraph V) (AB : Bipartition V) [AB.Decidable]
    {x y : V} (hne : x ≠ y) [Fintype (G.neighborSet x)] :
    f G AB x = f G (AB.demote y) x :=
  f_eq_of_demote_finset_of_notMem _ _ (notMem_singleton.mpr hne)

lemma f_pos_of_mem (G : SimpleGraph V) (AB : Bipartition V)
    (v : V) [Fintype (G.neighborSet v)] : v ∈ AB → 0 < f G AB v :=
  (lt_of_lt_of_le fB_pos <| fB_le_f ·)

lemma f_mono {G₁ G₂ : SimpleGraph V} {AB : Bipartition V}
    {v : V} [Fintype (G₁.neighborSet v)] [Fintype (G₂.neighborSet v)] (hle : G₂ ≤ G₁) :
    f G₁ AB v ≤ f G₂ AB v := by
  if hv : v ∈ AB then
    rcases AB.mem_iff.mp hv with hA | hB
    · simp only [f, hA, ↓reduceDIte]
      exact fA_decreasing <| degree_le_of_le hle
    · simp only [f, not_A_of_B, hB, ↓reduceDIte]
      exact fB_decreasing <| degree_le_of_le hle
  else
    rw [← f_eq_zero_of_notMem G₁ hv, ← f_eq_zero_of_notMem G₂ hv]

@[simp, grind! .]
lemma γ_nonneg {G : SimpleGraph V} {AB : Bipartition V}
    {v : V} [Fintype (G.neighborSet v)] : 0 ≤ γ G AB v := by
  have h : G.degree v - 1 ≤ G.degree v := Nat.sub_le ..
  simp only [γ, dite_eq_ite]
  split_ifs <;> simp only [sub_nonneg, fA_decreasing h, fB_decreasing h, le_refl]

lemma f_eq_sdiff {G : SimpleGraph V} {AB : Bipartition V}
    {s : Finset V} {v : V} [Fintype (G.neighborSet v)] (hv : v ∉ s) :
    f G AB v = f G (AB \ s) v := by
  if hvAB : v ∈ AB then
    rcases hvAB with hA | hB
    · have hA' : (AB \ s).A v := ⟨hA, hv⟩
      simp only [f, hA, hA', ↓reduceDIte]
    · have hB' : (AB \ s).B v := ⟨hB, hv⟩
      simp only [f, hB, hB', not_A_of_B, ↓reduceDIte]
  else
    have hvAB' : v ∉ (AB \ s) := by
      simp only [AB.mem_iff, not_or] at hvAB
      simp only [Bipartition.sdiff, Bipartition.mem_iff, hvAB, hv, not_false_eq_true, and_true,
        or_self]
    rw [← f_eq_zero_of_notMem G hvAB, ← f_eq_zero_of_notMem G hvAB']

lemma sdiff_demote_eq_demote_sdiff {AB : Bipartition V} {s₁ s₂ : Finset V} :
    (AB \ s₁).demote_finset s₂ = ((AB.demote_finset s₂) \ s₁) := by
  ext x <;> {
    simp only [demote_finset, sdiff]
    grind
  }

private lemma eval_mono (G₁ G₂ : SimpleGraph V) (hle : G₁ ≤ G₂)
    [G₁.LocallyFinite] [G₂.LocallyFinite] (AB : Bipartition V) [AB.Decidable] :
    eval G₂ AB ≤ eval G₁ AB := by
  unfold eval
  refine sum_le_sum ?_
  intro w hw
  simp only [Bipartition.toFinset, Bipartition.toSet, AB.mem_iff, Set.toFinset_setOf, mem_filter,
    mem_univ, true_and] at hw
  rcases hw with hA | hB
  · simp only [f, hA, ↓reduceDIte, fA]
    exact fA_decreasing <| degree_le_of_le hle
  · simp only [f, hB, not_A_of_B, ↓reduceDIte, fB]
    exact fB_decreasing <| degree_le_of_le hle

lemma respects_pair [DecidableEq V] {v w : V} {G : SimpleGraph V} [DecidableRel G.Adj]
    {AB : Bipartition V} (hAv : AB.A v) : respects {v, w} G AB := by
  intro x hx hBx y hy hyx
  have : x = w ∧ y = v := by grind [Adj.ne, not_A_of_B]
  obtain ⟨hx, hy⟩ := this
  refine ⟨hy ▸ hAv, hy ▸ ?_⟩
  rw [insert_eq, ← degree_in_union_self', ← card_singleton w]
  exact degree_in_le_card

lemma respects_pair' [DecidableEq V] {v w : V} {G : SimpleGraph V} [DecidableRel G.Adj]
    {AB : Bipartition V} (hAv : AB.A w) : respects {v, w} G AB :=
  pair_comm v w ▸ respects_pair hAv

lemma respects_singleton [DecidableEq V] {v : V} {G : SimpleGraph V} [DecidableRel G.Adj]
    {AB : Bipartition V} : respects {v} G AB :=
  fun _ hx _ _ hy hyx ↦ (mem_singleton.mp hx ▸ mem_singleton.mp hy ▸ hyx).ne rfl |>.elim

lemma respects_of_union_disjoint_neighborhood
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V}
    {s₁ s₂ : Finset V} (hs₁ : respects s₁ G AB) (hs₂ : respects s₂ G AB)
    (h : ∀ x ∈ s₁, ∀ y ∈ s₂, ¬G.Adj x y) :
    respects (s₁ ∪ s₂) G AB := by
  intro x hx hBx u hu hux
  rcases mem_union.mp hx with hx | hx
  · simp only [mem_union, or_false, h x hx u |>.mt <| Decidable.not_not.mpr hux.symm] at hu
    obtain ⟨hAu, hdu⟩ := hs₁ x hx hBx u hu hux
    refine ⟨hAu, le_of_eq_of_le ?_ hdu⟩
    refine congrArg Finset.card ?_
    ext v
    simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff, or_iff_left_iff_imp]
    exact fun huv hv ↦ (h u hu v hv) huv |>.elim
  · simp only [mem_union, false_or, (h u · x hx).mt <| Decidable.not_not.mpr hux] at hu
    obtain ⟨hAu, hdu⟩ := hs₂ x hx hBx u hu hux
    refine ⟨hAu, le_of_eq_of_le ?_ hdu⟩
    refine congrArg Finset.card ?_
    ext v
    simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff, or_iff_right_iff_imp]
    intro huv hv
    exact h v hv u hu huv.symm |>.elim

lemma respects_of_A [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V}
    {s : Finset V} (hs : ∀ v ∈ s, AB.A v) :
    respects s G AB :=
  fun x hx hBx ↦ not_B_of_A (hs x hx) hBx |>.elim

end Bipartition

section

variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {AB : Bipartition V}

lemma fA_eq_of_three_le_d {d : ℕ} (hd : 3 ≤ d) : fA d = 2 / (d + 1 : ℝ) := by
  simp only [fA]
  split_ifs
  any_goals grind

lemma fA1' : fA 1 = 5 / 6 := by
  simp only [fA, one_ne_zero, ↓reduceIte]

lemma fA2' : fA 2 = 3 / 5 := by
  simp only [fA, Nat.add_one_ne_zero, Nat.add_one_add_one_ne_one, ↓reduceIte]

lemma fA1 {v : V} (hAv : AB.A v) (hdv : G.degree v = 1) : f G AB v = 5 / 6 := by
  simp only [f, hAv, ↓reduceDIte, hdv, fA, one_ne_zero, ↓reduceIte]

lemma fA2 {v : V} (hAv : AB.A v) (hdv : G.degree v = 2) : f G AB v = 3 / 5 := by
  simp only [f, hAv, ↓reduceDIte, hdv, fA, two_ne_zero, Nat.add_one_add_one_ne_one, ↓reduceIte]

lemma fA3 {v : V} (hAv : AB.A v) (hdv : G.degree v = 3) : f G AB v = 1 / 2 := by
  simp only [f, hAv, ↓reduceDIte, fA_eq_of_three_le_d (le_of_eq hdv.symm)]
  rw [hdv, Nat.cast_three]
  linarith

lemma fAle1 {v : V} (hAv : AB.A v) (hdv : G.degree v ≤ 1) : 5 / 6 ≤ f G AB v := by
  simp only [f, hAv, ↓reduceDIte]
  exact le_of_eq_of_le fA1'.symm (fA_decreasing hdv)

lemma fAlt2 {v : V} (hAv : AB.A v) (hdv : G.degree v < 2) : 5 / 6 ≤ f G AB v :=
  fAle1 hAv (Nat.le_of_lt_succ hdv)

lemma fAle2 {v : V} (hAv : AB.A v) (hdv : G.degree v ≤ 2) : 3 / 5 ≤ f G AB v := by
  simp only [f, hAv, ↓reduceDIte]
  exact le_of_eq_of_le fA2'.symm (fA_decreasing hdv)

lemma fAlt3 {v : V} (hAv : AB.A v) (hdv : G.degree v < 3) : 3 / 5 ≤ f G AB v :=
  fAle2 hAv (Nat.le_of_lt_succ hdv)

lemma fB0 {v : V} (hBv : AB.B v) (hdv : G.degree v = 0) : f G AB v = 1 := by
  simp only [f, hBv, not_A_of_B, ↓reduceDIte, fB, hdv, Nat.cast_zero, zero_add, one_div_one]

lemma fB1 {v : V} (hBv : AB.B v) (hdv : G.degree v = 1) : f G AB v = 1 / 2 := by
  simp only [f, hBv, not_A_of_B, ↓reduceDIte, fB, hdv, Nat.cast_one]
  linarith

lemma fBle1 {v : V} (hBv : AB.B v) (hdv : G.degree v ≤ 1) : 1 / 2 ≤ f G AB v := by
  have : G.degree v = 0 ∨ G.degree v = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hdv
  rcases this with hdv | hdv
  · rw [fB0 hBv hdv]
    linarith
  · rw [fB1 hBv hdv]

lemma fB2 {v : V} (hBv : AB.B v) (hdv : G.degree v = 2) : f G AB v = 1 / 3 := by
  simp only [f, hBv, not_A_of_B, ↓reduceDIte, fB, hdv, Nat.cast_two]
  linarith

lemma fBle2 {v : V} (hBv : AB.B v) (hdv : G.degree v ≤ 2) : 1 / 3 ≤ f G AB v := by
  have : G.degree v ≤ 1 ∨ G.degree v = 2 := Nat.le_or_eq_of_le_succ hdv
  rcases this with hdv | hdv
  · linarith [fBle1 hBv hdv]
  · rw [fB2 hBv hdv]

lemma fBlt3 {v : V} (hBv : AB.B v) (hdv : G.degree v < 3) : 1 / 3 ≤ f G AB v :=
  fBle2 hBv (Nat.le_of_lt_succ hdv)

lemma fB3 {v : V} (hBv : AB.B v) (hdv : G.degree v = 3) : f G AB v = 1 / 4 := by
  simp only [f, hBv, not_A_of_B, ↓reduceDIte, fB, hdv, Nat.cast_three]
  linarith

lemma γA_eq_of_four_le_d {d : ℕ} (hd : 4 ≤ d) : fA (d - 1) - fA d = 2 / (d * (d + 1 : ℝ)) := by
  repeat rw [fA_eq_of_three_le_d (by omega)]
  have : ((d - 1 : ℕ) + 1 : ℝ) = d := by
    nth_rewrite 2 [← Nat.cast_one]
    simp only [← Nat.cast_add, Nat.sub_one_add_one (by linarith)]
  grind only

lemma γB_eq_of_one_le_d {d : ℕ} (hd : 1 ≤ d) : fB (d - 1) - fB d = 1 / (d * (d + 1 : ℝ)) := by
  simp only [fB]
  have : ((d - 1 : ℕ) + 1 : ℝ) = d := by
    nth_rewrite 2 [← Nat.cast_one]
    simp only [← Nat.cast_add, Nat.sub_one_add_one (by linarith)]
  grind only

lemma γA0' : fA (0 - 1) - fA 0 = 0 := by
  simp only [Nat.zero_sub_one, sub_self]

lemma γA0 {v : V} (hAv : AB.A v) (hdv : G.degree v = 0) : γ G AB v = 0 := by
  simp only [γ, hAv, ↓reduceDIte, hdv, γA0']

lemma γA1' : fA (1 - 1) - fA 1 = 1 / 6 := by
  simp only [Nat.add_one_sub_one, fA, one_ne_zero, ↓reduceIte]
  linarith

lemma γA1 {v : V} (hAv : AB.A v) (hdv : G.degree v = 1) : γ G AB v = 1 / 6 := by
  simp only [γ, hAv, ↓reduceDIte, hdv, γA1']

lemma γA2' : fA (2 - 1) - fA 2 = 7 / 30 := by
  simp only [Nat.add_one_sub_one, fA, one_ne_zero, ↓reduceIte, two_ne_zero,
    Nat.add_one_add_one_ne_one]
  linarith

lemma γA2 {v : V} (hAv : AB.A v) (hdv : G.degree v = 2) : γ G AB v = 7 / 30 := by
  simp only [γ, hAv, ↓reduceDIte, hdv, γA2']

lemma γA3' : fA (3 - 1) - fA 3 = 1 / 10 := by
  have : 3 ≠ 2 := by omega
  simp only [Nat.add_one_sub_one, fA, ↓reduceIte, two_ne_zero, three_ne_zero, this,
    Nat.add_one_add_one_ne_one, Nat.cast_three]
  linarith

lemma γA3 {v : V} (hAv : AB.A v) (hdv : G.degree v = 3) : γ G AB v = 1 / 10 := by
  simp only [γ, hAv, ↓reduceDIte, hdv, γA3']

lemma γA4' : fA (4 - 1) - fA 4 = 1 / 10 := by
  have three_ne_two : 3 ≠ 2 := by omega
  have four_ne_two : 4 ≠ 2 := by omega
  simp only [Nat.add_one_sub_one, fA, ↓reduceIte, four_ne_zero, three_ne_zero, three_ne_two,
    four_ne_two, Nat.add_one_add_one_ne_one, Nat.cast_three]
  linarith

lemma γA4 {v : V} (hAv : AB.A v) (hdv : G.degree v = 4) : γ G AB v = 1 / 10 := by
  simp only [γ, hAv, ↓reduceDIte, hdv, γA4']

lemma γA5' : fA (5 - 1) - fA 5 = 1 / 15 := by
  have four_ne_two : 4 ≠ 2 := by omega
  have five_ne_zero : 5 ≠ 0 := by omega
  have five_ne_two : 5 ≠ 2 := by omega
  simp only [Nat.add_one_sub_one, fA, ↓reduceIte, four_ne_zero, five_ne_zero, five_ne_two,
    four_ne_two, Nat.add_one_add_one_ne_one, Nat.cast_four, cast_five]
  linarith

lemma γB2' : fB (2 - 1) - fB 2 = 1 / 6 := by
  simp only [fB, Nat.reduceSub, Nat.cast_one, Nat.cast_two]
  linarith

lemma γB2 {v : V} (hBv : AB.B v) (hdv : G.degree v = 2) : γ G AB v = 1 / 6 := by
  simp only  [γ, hBv, not_A_of_B, ↓reduceDIte, hdv, γB2']

lemma γA_decreasing' {d : ℕ} (hd : 3 ≤ d) : fA ((d + 1) - 1) - fA (d + 1) ≤ fA (d - 1) - fA d := by
  have h3ne2 : 3 ≠ 2 := by omega
  have h4ne2 : 4 ≠ 2 := by omega
  rcases (by lia : d = 3 ∨ 4 ≤ d) with hd3 | hd4
  · simp only [hd3, Nat.reduceAdd, Nat.add_one_sub_one, fA, two_ne_zero, Nat.add_one_add_one_ne_one,
      h3ne2, h4ne2, three_ne_zero, four_ne_zero, ↓reduceIte, Nat.cast_three, Nat.cast_four]
    linarith
  · repeat rw [fA_eq_of_three_le_d (by grind)]
    have : ((d + 1 : ℕ) + 1 : ℝ) = (d + 1 + 1 : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [Δf_eq'' (Nat.zero_lt_of_lt hd), this, Nat.add_one_sub_one, Δf_eq]
    refine div_le_div_of_nonneg_left zero_le_two ?_ ?_
    · refine Left.mul_pos ?_ ?_
      · rw [← Nat.cast_zero, Nat.cast_lt]
        exact Nat.zero_lt_of_lt hd
      · rw [← Nat.cast_zero, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_lt]
        exact Nat.zero_lt_succ d
    · exact mul_le_mul le_add_one le_add_one add_one_nonneg add_one_nonneg

lemma γA_decreasing {d d' : ℕ} (hdd' : d ≤ d') (hd : 3 ≤ d) :
    fA (d' - 1) - fA d' ≤ fA (d - 1) - fA d := by
  induction hdiff : d' - d generalizing d d' with
  | zero => grind
  | succ n ih => ?_
  refine le_trans ?_ (γA_decreasing' hd)
  exact (ih (by omega : d + 1 ≤ d') (Nat.le_add_right_of_le hd) (by omega))

lemma γB_decreasing {d d' : ℕ} (hdd' : d ≤ d') (hd : 1 ≤ d) :
    fB (d' - 1) - fB d' ≤ fB (d - 1) - fB d := by
  simp only [fB]
  repeat rw [Δf_eq'' (by omega)]
  refine one_div_le_one_div_of_le ?_ ?_
  · exact Left.mul_pos (Nat.cast_pos'.mpr hd) add_one_pos
  · refine mul_le_mul (Nat.cast_le.mpr hdd') ?_ add_one_nonneg (Nat.cast_nonneg' _)
    simp only [add_le_add_iff_right, Nat.cast_le, hdd']

lemma eval_eq [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {AB : Bipartition V} [AB.Decidable] {s : Finset V} (hs : s ⊆ AB.toFinset)
    (hG : G.support ⊆ AB.toFinset) :
    eval G AB
      = eval (G.deleteIncidencesOf s) (AB \ s)
        + ∑ z ∈ G.closed_neighborFinset_of_Finset s \ s,
          (f G AB z - f (G.deleteIncidencesOf s) (AB \ s) z)
        + ∑ z ∈ s, f G AB z := by
  have H : G.closed_neighborFinset_of_Finset s ⊆ AB.toFinset := by
    intro z hz
    rcases mem_closed_neighborFinset_iff.mp hz with h | h
    · exact hs h
    · obtain ⟨_, _, hz'z⟩ := h
      exact hG <| G.mem_support.mpr ⟨_, hz'z.symm⟩
  calc _
    _ = ∑ z ∈ AB.toFinset \ G.closed_neighborFinset_of_Finset s, f G AB z
        + ∑ z ∈ G.closed_neighborFinset_of_Finset s, f G AB z := by
      refine Eq.symm <| sum_sdiff H
    _ = ∑ z ∈ AB.toFinset \ G.closed_neighborFinset_of_Finset s, f G AB z
        + ∑ z ∈ G.closed_neighborFinset_of_Finset s \ s, f G AB z
        + ∑ z ∈ s, f G AB z := by
      suffices ∑ z ∈ G.closed_neighborFinset_of_Finset s, f G AB z =
          ∑ z ∈ G.closed_neighborFinset_of_Finset s \ s, f G AB z + ∑ z ∈ s, f G AB z by
        linarith
      exact Eq.symm <| sum_sdiff closed_neighborFinset_contains_Finset
  suffices ∑ z ∈ AB.toFinset \ G.closed_neighborFinset_of_Finset s, f G AB z +
      ∑ z ∈ G.closed_neighborFinset_of_Finset s \ s, f G AB z
      = eval (G.deleteIncidencesOf s) (AB \ s) +
        ∑ z ∈ G.closed_neighborFinset_of_Finset s \ s,
          (f G AB z - f (G.deleteIncidencesOf s) (AB \ s) z) by
    linarith
  have : ∑ z ∈ AB.toFinset \ G.closed_neighborFinset_of_Finset s, f G AB z
      = ∑ z ∈ AB.toFinset \ G.closed_neighborFinset_of_Finset s,
          f (G.deleteIncidencesOf s) (AB \ s) z := by
    exact sum_congr rfl fun z hz ↦ f_congr'' <| mem_sdiff.mp hz |>.2
  rw [this]; clear this
  have : eval (G.deleteIncidencesOf s) (AB \ s)
      = ∑ z ∈ (AB \ s).toFinset \ (G.closed_neighborFinset_of_Finset s \ s),
          f (G.deleteIncidencesOf s) (AB \ s) z
        + ∑ z ∈ (G.closed_neighborFinset_of_Finset s \ s),
          f (G.deleteIncidencesOf s) (AB \ s) z := by
      refine Eq.symm <| sum_sdiff ?_
      rw [AB.sdiff_toFinset]
      exact sdiff_subset_sdiff H (subset_refl _)
  rw [this]; clear this
  have : ((AB \ s).toFinset \ (G.closed_neighborFinset_of_Finset s \ s))
      = AB.toFinset \ G.closed_neighborFinset_of_Finset s := by
    rw [AB.sdiff_toFinset]
    ext x
    simp only [mem_sdiff, not_and, Decidable.not_not]
    constructor
    · exact fun ⟨⟨h, h'⟩, h''⟩ ↦ ⟨h, fun H ↦  h' (h'' H)⟩
    · refine fun ⟨h, h'⟩ ↦ ⟨⟨h, ?_⟩, fun H ↦ h' H |>.elim⟩
      exact notMem_mono (closed_neighborFinset_contains_Finset) h'
  rw [this]; clear this
  suffices ∑ z ∈ G.closed_neighborFinset_of_Finset s \ s, f G AB z
      = ∑ z ∈ G.closed_neighborFinset_of_Finset s \ s, f (G.deleteIncidencesOf s) (AB \ s) z +
        ∑ z ∈ G.closed_neighborFinset_of_Finset s \ s,
            (f G AB z - f (G.deleteIncidencesOf s) (AB \ s) z) by
    linarith
  simp only [sum_sub_distrib]
  grind

end

lemma InducesForestOfStars_union_leaf_to_B [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {AB : Bipartition V} {s : Finset V}
    (hsresp : AB.respects s G) {v w : V} (hNv : (G.neighborFinset v ∩ s) = {w}) (hBw : AB.B w)
    (hsf : G.InducesForestOfStars s) :
    G.InducesForestOfStars (s ∪ {v}) := by
  if hvs : v ∈ s then
    suffices s = s ∪ {v} by
      exact this ▸ hsf
    exact left_eq_union.mpr <| singleton_subset_iff.mpr hvs
  else
    have : w ∈ G.neighborFinset v ∩ s := hNv ▸ mem_singleton.mpr rfl
    simp only [mem_inter, mem_neighborFinset] at this
    obtain ⟨hvw, hws⟩ := this
    have hdv : G.degree_in s v = 1 := by
      rw [degree_in, ← card_singleton w]
      exact congrArg Finset.card hNv
    if hdw : G.degree_in s w = 1 then
      have : (G.neighborFinset w ∩ s).Nonempty := by
        refine nonempty_of_ne_empty <| ne_of_apply_ne card ?_
        rw [← degree_in, hdw, card_empty]
        exact one_ne_zero
      obtain ⟨w', hw'⟩ := this
      simp only [mem_inter, mem_neighborFinset] at hw'
      obtain ⟨hww', hw's⟩ := hw'
      refine InducesForestOfStars_union_leaf_on_K2 ?_ hdv hdw hvw hww'.symm hw's hws ?_ hsf
      · refine le_antisymm ?_ ?_
        · exact hsresp w hws hBw w' hw's hww'.symm |>.2
        · rw [← card_singleton w]
          refine card_le_card <| singleton_subset_iff.mpr ?_
          exact mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr hww'.symm, hws⟩
      · exact ne_of_mem_of_not_mem hw's hvs
    else
      exact InducesForestOfStars_union_leaf' hdv hws hvw hdw hsf

end AB
end CaroWeiType
