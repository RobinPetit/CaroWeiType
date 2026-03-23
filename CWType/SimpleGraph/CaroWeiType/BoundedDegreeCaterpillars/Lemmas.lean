import CWType.SimpleGraph.CaroWeiType.Basic
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.ABC

namespace CaroWeiType
namespace ABC

open Finset

open SimpleGraph

private lemma five_pos : (0 : ℝ) < 5 := by
  exact Nat.ofNat_pos'

@[simp]
lemma not_A_of_B {n : ℕ} {ABC : Tripartition n} {v : Fin n} (hB : ABC.B v) : ¬ABC.A v :=
  fun hA ↦ ABC.sound v |>.1 ⟨hA, hB⟩

@[simp]
lemma not_A_of_C {n : ℕ} {ABC : Tripartition n} {v : Fin n} (hC : ABC.C v) : ¬ABC.A v :=
  fun hA ↦ ABC.sound v |>.2.1 ⟨hA, hC⟩

@[simp]
lemma not_B_of_A {n : ℕ} {ABC : Tripartition n} {v : Fin n} (hA : ABC.A v) : ¬ABC.B v :=
  fun hB ↦ ABC.sound v |>.1 ⟨hA, hB⟩

@[simp]
lemma not_B_of_C {n : ℕ} {ABC : Tripartition n} {v : Fin n} (hC : ABC.C v) : ¬ABC.B v :=
  fun hB ↦ ABC.sound v |>.2.2 ⟨hB, hC⟩

@[simp]
lemma not_C_of_A {n : ℕ} {ABC : Tripartition n} {v : Fin n} (hA : ABC.A v) : ¬ABC.C v :=
  fun hC ↦ ABC.sound v |>.2.1 ⟨hA, hC⟩

@[simp]
lemma not_C_of_B {n : ℕ} {ABC : Tripartition n} {v : Fin n} (hB : ABC.B v) : ¬ABC.C v :=
  fun hC ↦ ABC.sound v |>.2.2 ⟨hB, hC⟩

namespace Tripartition

@[simp 10]
lemma coe_mem_toFinset {n : ℕ} (ABC : Tripartition n) {x : Fin n} :
    x ∈ ABC ↔ x ∈ ABC.toFinset := by
  simp [Tripartition.toFinset]

@[simp]
lemma mem_iff {n : ℕ} (ABC : Tripartition n) {x : Fin n} :
    x ∈ ABC ↔ ABC.A x ∨ ABC.B x ∨ ABC.C x := by
  rfl
end Tripartition

-- f(0)

@[simp]
lemma fA0 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 0) : f G ABC v = 1 := by
  simp only [f, hA, ↓reduceDIte, fA, hv, ↓reduceIte]

@[simp]
lemma fB0 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 0) : f G ABC v = 1 := by
  simp only [f, hB, not_A_of_B, ↓reduceDIte, fB, hv, ↓reduceIte]

@[simp]
lemma fC0 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 0) : f G ABC v = 1 := by
  simp only [f, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, ↓reduceIte]

-- f(1)

@[simp]
lemma fA1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 1) : f G ABC v = 5 / 6 := by
  simp only [f, hA, ↓reduceDIte, fA, hv, one_ne_zero, ↓reduceIte]

@[simp]
lemma fB1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 1) : f G ABC v = 5 / 6 := by
  simp only [f, hB, not_A_of_B, ↓reduceDIte, fB, hv, one_ne_zero, ↓reduceIte]

@[simp]
lemma fC1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 1) : f G ABC v = 1 / 6 := by
  simp only [f, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, one_ne_zero, ↓reduceIte,
    OfNat.one_ne_ofNat, or_false, one_div]

-- f(2)

@[simp]
lemma fA2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 2) : f G ABC v = 2 / 3 := by
  simp only [f, hA, ↓reduceDIte, fA, hv, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one,
    Nat.cast_ofNat]
  grind only

@[simp]
lemma fB2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 2) : f G ABC v = 1 / 3 := by
  simp only [f, hB, not_A_of_B, ↓reduceDIte, fB, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, one_div]

@[simp]
lemma fC2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 2) : f G ABC v = 1 / 6 := by
  simp only [f, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, or_true, one_div]

-- f(3)

@[simp]
lemma fA3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 3) : f G ABC v = 1 / 2 := by
  simp only [f, hA, ↓reduceDIte, fA, hv, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one,
    Nat.cast_ofNat]
  grind only

@[simp]
lemma fB3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 3) : f G ABC v = 1 / 3 := by
  simp only [f, hB, not_A_of_B, ↓reduceDIte, fB, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, Nat.succ_ne_self, Nat.cast_ofNat, one_div]
  grind only

@[simp]
lemma fC3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 3) : f G ABC v = 1 / 6 := by
  simp only [f, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, Nat.succ_ne_self, or_self, Nat.cast_ofNat, one_div]
  grind only

@[simp]
lemma fA_le_25_of_4_le_deg' {d : ℕ} (hv : 4 ≤ d) : fA d ≤ 2 / 5 := by
  simp only [fA]
  split_ifs
  any_goals grind
  refine (div_le_div_iff_of_pos_left two_pos add_one_pos five_pos).mpr ?_
  rw [← Nat.cast_one, ← Nat.cast_add]
  refine Nat.cast_le.mpr ?_
  simp only [Nat.reduceLeDiff, hv]

@[simp]
lemma fA_le_25_of_4_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hA : ABC.A v) (hv : 4 ≤ G.degree v) :
    f G ABC v ≤ 2 / 5 := by
  simp only [f, hA, ↓reduceDIte]
  exact fA_le_25_of_4_le_deg' hv

@[simp]
lemma fA_le_12_of_3_le_deg' {d : ℕ} (hv : 3 ≤ d) : fA d ≤ 1 / 2 := by
  simp only [fA]
  split_ifs
  any_goals grind
  calc _
    _ ≤ 2 / (4 : ℝ) := by
      refine (div_le_div_iff_of_pos_left two_pos add_one_pos four_pos).mpr ?_
      rw [← Nat.cast_four, ← Nat.cast_one, ← Nat.cast_add]
      exact Nat.cast_le.mpr <| Nat.le_add_of_sub_le hv
    _ ≤ 1 / 2 := by grind

@[simp]
lemma fA_le_12_of_3_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hA : ABC.A v) (hv : 3 ≤ G.degree v) :
    f G ABC v ≤ 1 / 2 := by
  simp only [f, hA, ↓reduceDIte]
  exact fA_le_12_of_3_le_deg' hv

@[simp]
lemma fA_le_23_of_2_le_deg' {d : ℕ} (hd : 2 ≤ d) : fA d ≤ 2 / 3 := by
  if h2 : d = 2 then
    simp only [fA, h2, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.cast_ofNat]
    grind
  else
    exact le_trans (fA_le_12_of_3_le_deg' (by grind)) (by grind)

@[simp]
lemma fA_le_23_of_2_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hA : ABC.A v) (hv : 2 ≤ G.degree v) :
    f G ABC v ≤ 2 / 3 := by
  simp only [f, hA, ↓reduceDIte]
  exact fA_le_23_of_2_le_deg' hv

@[simp]
lemma fA_le_56_of_1_le_deg' {d : ℕ} (hd : 1 ≤ d) : fA d ≤ 5 / 6 := by
  if h1 : d = 1 then
    simp [h1]
  else
    exact le_trans (fA_le_23_of_2_le_deg' (by grind)) (by grind)

@[simp]
lemma fA_le_56_of_1_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hA : ABC.A v) (hv : 1 ≤ G.degree v) :
    f G ABC v ≤ 5 / 6 := by
  simp only [f, hA, ↓reduceDIte]
  exact fA_le_56_of_1_le_deg' hv

@[simp]
lemma fB_le_13_if_2_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hB : ABC.B v) (hv : 2 ≤ G.degree v) :
    f G ABC v ≤ 1 / 3 := by
  simp only [f, hB, not_A_of_B, ↓reduceDIte, fB]
  split_ifs
  any_goals grind
  calc (4 / 3) / (G.degree v + 1 : ℝ)
    _ ≤ (4 / 3) / (4 : ℝ) := by
      refine (div_le_div_iff_of_pos_left (by grind) add_one_pos four_pos).mpr ?_
      rw [← Nat.cast_four, ← Nat.cast_one, ← Nat.cast_add]
      exact Nat.cast_le.mpr (by grind)
    _ ≤ 1 / 3 := by grind

@[simp]
lemma fB_le_56_if_1_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hB : ABC.B v) (hv : 1 ≤ G.degree v) :
    f G ABC v ≤ 5 / 6 := by
  if h1 : G.degree v = 1 then
    rw [fB1 hB h1]
  else
    exact le_trans (fB_le_13_if_2_le_deg hB (by grind)) (by grind)

@[simp]
lemma fC_le_16_if_2_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hC : ABC.C v) (hv : 2 ≤ G.degree v) :
    f G ABC v ≤ 1 / 6 := by
  simp only [f, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC]
  split_ifs
  any_goals grind
  calc (2 / 3) / (G.degree v + 1 : ℝ)
    _ ≤ (2 / 3) / (4 : ℝ) := by
      refine (div_le_div_iff_of_pos_left (by grind) add_one_pos four_pos).mpr ?_
      rw [← Nat.cast_four, ← Nat.cast_one, ← Nat.cast_add]
      exact Nat.cast_le.mpr (by grind)
    _ ≤ 1 / 6 := by grind

@[simp]
lemma fC_le_16_if_1_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hC : ABC.C v) (hv : 1 ≤ G.degree v) :
    f G ABC v ≤ 1 / 6 := by
  if h1 : G.degree v = 1 then
    rw [fC1 hC h1]
  else
    exact fC_le_16_if_2_le_deg hC (by grind)

@[simp]
lemma f_le_1_over_2_of_3_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : 3 ≤ G.degree v) :
    f G ABC v ≤ 1 / 2 := by
  -- simp only [f]
  if hvABC : v ∈ ABC then
    rcases ABC.mem_iff.mp hvABC with hA | hB | hC
    · exact fA_le_12_of_3_le_deg hA hv
    · exact le_trans (fB_le_13_if_2_le_deg hB (Nat.le_of_add_left_le hv)) (by grind)
    · exact le_trans (fC_le_16_if_2_le_deg hC (Nat.le_of_add_left_le hv)) (by grind)
  else
    grind [f, ABC.mem_iff]

@[simp]
lemma A2_of_f_lt_12_of_2_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : 2 ≤ G.degree v) (h : v ∈ ABC)
    (hf : 1 / 2 < f G ABC v) : ABC.A v ∧ G.degree v = 2 := by
  rcases h with hA | hB | hC
  · refine ⟨hA, ?_⟩
    refine le_antisymm ?_ hv
    refine Nat.le_of_not_lt ?_
    refine Function.mt (fA_le_12_of_3_le_deg hA) <| not_le.mpr hf
  · grind [fB_le_13_if_2_le_deg hB hv]
  · grind [fC_le_16_if_2_le_deg hC hv]

@[simp]
lemma A2_or_A3_of_f_lt_25_of_2_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : 2 ≤ G.degree v) (h : v ∈ ABC)
    (hf : 2 / 5 < f G ABC v) : ABC.A v ∧ (G.degree v = 2 ∨ G.degree v = 3) := by
  rcases h with hA | hB | hC
  · refine ⟨hA, ?_⟩
    have hobj := Function.mt (fA_le_25_of_4_le_deg hA) <| not_le.mpr hf
    grind
  · grind [fB_le_13_if_2_le_deg hB hv]
  · grind [fC_le_16_if_2_le_deg hC hv]

@[simp]
lemma γA1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 1) : γ G ABC v = 1 / 6 := by
  simp only [γ, hA, ↓reduceDIte, fA, hv, tsub_self, ↓reduceIte, one_ne_zero, one_div]
  grind

@[simp]
lemma γA2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 2) : γ G ABC v = 1 / 6 := by
  simp only [γ, hA, ↓reduceDIte, fA, hv, Nat.add_one_sub_one, one_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Nat.cast_ofNat, one_div]
  grind

@[simp]
lemma γA3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 3) : γ G ABC v = 1 / 6 := by
  simp only [γ, hA, ↓reduceDIte, fA, hv, Nat.add_one_sub_one, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, Nat.cast_ofNat, one_div]
  grind

@[simp]
lemma γB1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 1) : γ G ABC v = 1 / 6 := by
  simp only [γ, hB, not_A_of_B, ↓reduceDIte, fB, hv, tsub_self, ↓reduceIte, one_ne_zero, one_div]
  grind

@[simp]
lemma γB2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 2) : γ G ABC v = 1 / 2 := by
  simp only [γ, hB, not_A_of_B, ↓reduceDIte, fB, hv, Nat.add_one_sub_one, one_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, one_div]
  grind

@[simp]
lemma γC1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 1) : γ G ABC v = 5 / 6 := by
  simp only [γ, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, tsub_self, ↓reduceIte, one_ne_zero,
    OfNat.one_ne_ofNat, or_false, one_div]
  grind

@[simp]
lemma γC2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 2) : γ G ABC v = 0 := by
  simp only [γ, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, Nat.add_one_sub_one, one_ne_zero,
    ↓reduceIte, OfNat.one_ne_ofNat, or_false, one_div, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    or_true, sub_self]

@[simp]
lemma ℓA1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 1) : ℓ G ABC v = 1 / 6 := by
  simp only [ℓ, hA, ↓reduceDIte, fA, hv, ↓reduceIte, one_ne_zero, one_div]
  grind

@[simp]
lemma ℓA2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 2) : ℓ G ABC v = 1 / 6 := by
  simp only [ℓ, hA, ↓reduceDIte, fA, hv, ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    Nat.cast_ofNat, one_div]
  grind

@[simp]
lemma ℓA3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 3) : ℓ G ABC v = 1 / 10 := by
  simp only [ℓ, hA, ↓reduceDIte, fA, hv, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one,
    Nat.cast_ofNat, one_div]
  grind

@[simp]
lemma ℓB1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 1) : ℓ G ABC v = 1 / 2 := by
  simp only [ℓ, hB, not_A_of_B, ↓reduceDIte, fB, hv, ↓reduceIte, one_ne_zero, one_div]
  grind

@[simp]
lemma ℓB2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 2) : ℓ G ABC v = 0 := by
  simp only [ℓ, hB, not_A_of_B, ↓reduceDIte, fB, hv, ↓reduceIte, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, one_div]
  grind

@[simp]
lemma ℓB3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 3) : ℓ G ABC v = 1 / 15 := by
  simp only [ℓ, hB, not_A_of_B, ↓reduceDIte, fB, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, Nat.succ_ne_self, Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceEqDiff]
  grind

@[simp]
lemma ℓC1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 1) : ℓ G ABC v = 0 := by
  simp only [ℓ, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, ↓reduceIte, one_ne_zero,
    OfNat.one_ne_ofNat, or_false, one_div]
  grind

@[simp]
lemma ℓC2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 2) : ℓ G ABC v = 0 := by
  simp only [ℓ, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, ↓reduceIte, one_div,
    OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, or_true]
  grind

@[simp]
lemma ℓC3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 3) : ℓ G ABC v = 1 / 30 := by
  simp only [ℓ, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, Nat.succ_ne_self, or_self, Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceEqDiff,
    one_div]
  grind

lemma Δf_eq {c : ℝ} {d : ℕ} :
    c / (d + 1 : ℝ) - c / (d + 1 + 1 : ℝ) = c / ((d + 1 : ℝ)*(d + 1 + 1 : ℝ)) := by
  grind

lemma ΔfA_decreasing {d d' : ℕ} (hdd' : d ≤ d') :
  (fA d' - fA (d' + 1)) ≤ (fA d - fA (d + 1)) := by
  simp only [fA, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_eq_right,
    Nat.cast_add, Nat.cast_one]
  have H {m : ℕ} (hm : 2 ≤ m) : 2 / ((m + 1 : ℝ) * (m + 1 + 1 : ℝ)) ≤ 1 / 6 := by
    calc _
      _ ≤ 2 / ((3 : ℝ) * (4 : ℝ)) := by
        refine div_le_div_iff₀ (by simp) (by simp) |>.mpr ?_
        simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
        refine mul_le_mul ?_ ?_ zero_le_four (le_of_lt add_one_pos)
        · rw [← Nat.cast_three, ← Nat.cast_one, ← Nat.cast_add]
          refine Nat.cast_le.mpr (by simp [hm])
        · rw [← Nat.cast_four, ← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add]
          refine Nat.cast_le.mpr (by simp [hm])
    grind
  split_ifs
  any_goals grind [Δf_eq]
  · rename_i hd' hd; rw [hd']
    grind
  · rename_i hd; rw [Δf_eq, hd]
    refine le_trans (H (by grind)) (by grind)
  · simp_rw [Δf_eq]
    refine (div_le_div_iff₀ (by simp) (by simp)).mpr ?_
    simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
    refine mul_le_mul ?_ ?_ ?_ ?_ <;> simp [hdd', le_of_lt]

@[simp]
lemma ℓ_le_1_over_10_of_3_le_degree {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (h : 3 ≤ G.degree v) :
    ℓ G ABC v ≤ 1 / 10 := by
  simp only [ℓ, fA, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_eq_right,
    Nat.cast_add, Nat.cast_one, fB, Nat.reduceEqDiff, fC, dite_eq_ite]
  have H : 4 * 5 ≤ (G.degree v + 1) * (G.degree v + 1 + 1) :=
    mul_le_mul (by grind) (by grind) (Nat.zero_le _) (Nat.zero_le _)
  have H' : 20 ≤ (G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ) := by
    rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_mul]
    exact Nat.cast_le.mpr H
  split_ifs
  any_goals grind
  · rw [Δf_eq]
    calc 2 / ((G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ))
      _ ≤ 2 / 20 := div_le_div₀ zero_le_two (le_refl _) (by exact Nat.ofNat_pos') H'
      _ = 1 / 10 := by grind
  · rw [Δf_eq]
    calc (4 / 3) / ((G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ))
      _ ≤ (4 / 3) / 20 := div_le_div₀ (by grind) (le_refl _) (by exact Nat.ofNat_pos') H'
      _ ≤ 1 / 10 := by grind
  · rw [Δf_eq]
    calc (2 / 3) / ((G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ))
      _ ≤ (2 / 3) / 20 := div_le_div₀ (by grind) (le_refl _) (by exact Nat.ofNat_pos') H'
      _ ≤ 1 / 10 := by grind

@[simp]
lemma ℓ_le_1_over_15_of_4_le_degree {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (h : 4 ≤ G.degree v) :
    ℓ G ABC v ≤ 1 / 15 := by
  simp only [ℓ, fA, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_eq_right,
    Nat.cast_add, Nat.cast_one, fB, Nat.reduceEqDiff, fC, dite_eq_ite]
  have H : 5 * 6 ≤ (G.degree v + 1) * (G.degree v + 1 + 1) :=
    mul_le_mul (by grind) (by grind) (Nat.zero_le _) (Nat.zero_le _)
  have H' : 30 ≤ (G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ) := by
    rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_mul]
    exact Nat.cast_le.mpr H
  split_ifs
  any_goals grind
  · rw [Δf_eq]
    calc 2 / ((G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ))
      _ ≤ 2 / 30 := div_le_div₀ zero_le_two (le_refl _) (by exact Nat.ofNat_pos') H'
      _ = 1 / 15 := by grind
  · rw [Δf_eq]
    calc (4 / 3) / ((G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ))
      _ ≤ (4 / 3) / 30 := div_le_div₀ (by grind) (le_refl _) (by exact Nat.ofNat_pos') H'
      _ ≤ 1 / 15 := by grind
  · rw [Δf_eq]
    calc (2 / 3) / ((G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ))
      _ ≤ (2 / 3) / 30 := div_le_div₀ (by grind) (le_refl _) (by exact Nat.ofNat_pos') H'
      _ ≤ 1 / 15 := by grind

namespace Tripartition

@[simp]
lemma demote_from_A {n : ℕ} (ABC : Tripartition n) (v : Fin n) (hv : ABC.A v) :
    (ABC.demote v).B v := by
  simp [demote, demote_A, hv]

@[simp]
lemma demote_from_A' {n : ℕ} (ABC : Tripartition n) (v : Fin n) (hv : ABC.A v) :
    ¬(ABC.demote v).A v := by
  exact fun hA ↦ (ABC.demote v).sound v |>.1 ⟨hA, ABC.demote_from_A v hv⟩

@[simp]
lemma demote_from_B {n : ℕ} (ABC : Tripartition n) (v : Fin n) (hv : ABC.B v) :
    (ABC.demote v).C v := by
  simp only [demote, hv, not_A_of_B, ↓reduceDIte, demote_B, ne_eq, not_C_of_B, or_true]

@[simp]
lemma demote_from_B' {n : ℕ} (ABC : Tripartition n) (v : Fin n) (hv : ABC.B v) :
    ¬(ABC.demote v).B v := by
  exact fun hB ↦ (ABC.demote v).sound v |>.2.2 ⟨hB, ABC.demote_from_B v hv⟩

@[simp]
lemma demote_from_C {n : ℕ} (ABC : Tripartition n) (v : Fin n) (hv : ABC.C v) :
    (ABC.demote v).C v := by
  simp only [demote, hv, not_A_of_C, ↓reduceDIte, not_B_of_C]

@[simp]
lemma A_of_demote_ne {n : ℕ} (ABC : Tripartition n) {v w : Fin n} (h : v ≠ w) :
    ABC.A v → (ABC.demote w).A v := by
  intro hA
  simp only [demote, demote_A, demote_B]
  split_ifs <;> simp [h, hA]

@[simp]
lemma B_of_demote_ne {n : ℕ} (ABC : Tripartition n) {v w : Fin n} (h : v ≠ w) :
    ABC.B v → (ABC.demote w).B v := by
  intro hB
  simp only [demote, demote_A, demote_B]
  split_ifs <;> simp [h, hB]

@[simp]
lemma C_of_demote_ne {n : ℕ} (ABC : Tripartition n) {v w : Fin n} (h : v ≠ w) :
    ABC.C v → (ABC.demote w).C v := by
  intro hC
  simp only [demote, demote_A, demote_B]
  split_ifs <;> simp [h, hC]

lemma mem_demote_of_mem {n : ℕ} (ABC : Tripartition n) {x y : Fin n} :
    x ∈ ABC → x ∈ ABC.demote y := by
  grind [mem_iff, demote, demote_A, demote_B]

lemma mem_of_mem_demote {n : ℕ} (ABC : Tripartition n) {x y : Fin n} :
    x ∈ ABC.demote y → x ∈ ABC := by
  grind [mem_iff, demote, demote_A, demote_B]

lemma demote_toFinset_eq {n : ℕ} (ABC : Tripartition n) {x : Fin n} :
    ABC.toFinset = (ABC.demote x).toFinset := by
  ext y
  simp only [← coe_mem_toFinset]
  exact ⟨mem_demote_of_mem ABC, mem_of_mem_demote ABC⟩

@[simp 100]
lemma sdiff_empty {n : ℕ} (ABC : Tripartition n) : (ABC \ ∅) = ABC := by
  ext <;> simp [Tripartition.sdiff]

@[simp 10]
lemma sdiff_eq {n : ℕ} (ABC : Tripartition n) (W : Finset (Fin n)) :
    (ABC \ W) = (ABC \ (W ∩ ABC.toFinset)) := by
  ext w <;> { simp [sdiff, toFinset]; grind }

@[simp]
lemma card_demote_eq_card {n : ℕ} {ABC : Tripartition n} {x : Fin n} :
    ABC.card = (ABC.demote x).card := by
  simp only [card]
  rw [demote_toFinset_eq]

@[simp]
lemma sdiff_notMem {n : ℕ} (ABC : Tripartition n) (s : Finset (Fin n)) :
    ∀ x ∈ s, x ∉ ABC \ s := by
  intro x hx
  simp [sdiff, hx]

@[simp]
lemma toFinset_mono {n : ℕ} {ABC : Tripartition n} {s : Finset (Fin n)} :
    (ABC \ s).toFinset ⊆ ABC.toFinset := by
  simp only [toFinset, sdiff, mem_iff]
  intro x hx
  simp only [mem_iff, mem_filter, mem_univ, true_and] at hx ⊢
  grind

@[simp]
lemma toFinset_eq {n : ℕ} {ABC : Tripartition n} {s : Finset (Fin n)} :
    (ABC \ s).toFinset = ABC.toFinset \ s := by
  ext w
  simp only [toFinset, sdiff, mem_iff, mem_filter, mem_univ, true_and, mem_sdiff]
  grind

lemma sdiff_card {n : ℕ} (ABC : Tripartition n) {s : Finset (Fin n)}
    (hs : s ∩ ABC.toFinset ≠ ∅) : (ABC \ s).card < ABC.card := by
  simp only [card, toFinset, sdiff]
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro z hz
    simp only [mem_iff, mem_filter, mem_univ, true_and] at hz ⊢
    grind
  · intro this
    obtain ⟨z, hz⟩ := nonempty_def.mp <| nonempty_iff_ne_empty.mpr hs
    have hzABC : z ∈ ABC.toFinset := by exact mem_of_mem_inter_right hz
    let hobj := this hzABC
    simp only [mem_iff, mem_filter, mem_univ, true_and] at hobj
    rcases hobj with ⟨_, h⟩ | ⟨⟨_, h⟩ | ⟨_, h⟩⟩ <;> exact h <| mem_of_mem_filter z hz

lemma sdiff_toFinset {n : ℕ} (ABC : Tripartition n) {s : Finset (Fin n)} :
    (ABC \ s).toFinset = ABC.toFinset \ s := by
  ext y
  simp only [toFinset, sdiff, mem_iff, mem_filter, mem_univ, true_and, mem_sdiff]
  constructor <;> exact fun hy ↦ by grind

lemma linear_forest_of_forest_respects {n : ℕ} (s : Finset (Fin n)) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ABC : Tripartition n) (hs : s ⊆ ABC.toFinset) :
    G.InducesForest s → respects s G ABC → G.InducesLinearForest s := by
  intro hf hresp
  refine ⟨hf, ?_⟩
  intro x hx
  obtain ⟨h₁, h₂, h₃⟩ := hresp x hx
  rw [degree_in] at h₁ h₂ h₃ ⊢
  rcases ABC.mem_iff.mp <| ABC.coe_mem_toFinset.mpr (hs hx) with hA | hB | hC <;> grind

lemma respects_singleton {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} : respects {v} G ABC := by
  simp [respects, degree_in]

lemma respects_union {n : ℕ} {s t : Finset (Fin n)} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (hs : respects s G ABC) (ht : respects t G ABC)
    (hst' : ∀ y ∈ s, ∀ z ∈ t, ¬G.Adj y z) :
    respects (s ∪ t) G ABC := by
  intro w hw
  rcases mem_union.mp hw with hw | hw
  · have heq : G.degree_in (s ∪ t) w = G.degree_in s w := by
      refine congrArg Finset.card ?_
      ext y
      simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff, or_iff_left_iff_imp]
      exact fun hwy hy ↦ hst' w hw y hy hwy |>.elim
    obtain ⟨hs1, hs2, hs3⟩ := hs w hw
    refine ⟨?_, ?_, ?_⟩ <;> { intro _; rw [heq]; grind }
  · have heq : G.degree_in (s ∪ t) w = G.degree_in t w := by
      refine congrArg Finset.card ?_
      ext y
      simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff,
        or_iff_right_iff_imp]
      refine fun hwy hy ↦ hst' y hy w hw hwy.symm |>.elim
    obtain ⟨hs1, hs2, hs3⟩ := ht w hw
    refine ⟨?_, ?_, ?_⟩ <;> { intro _; rw [heq]; grind }

lemma respects_mono {n : ℕ} {s t : Finset (Fin n)} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (hs : s ⊆ (ABC \ t).toFinset)
    (hresp : respects s (G.deleteIncidencesOf t) (ABC \ t)) :
    respects s G ABC := by
  intro w hw
  have mem_s_implies_notMem_t {z : Fin n} : z ∈ s → z ∉ t := by
    intro hz
    simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff] at hs
    let hobj := hs hz
    simp only [Tripartition.mem_iff, mem_filter, mem_univ, true_and] at hobj
    grind
  have hwt : w ∉ t := mem_s_implies_notMem_t hw
  have heqGNw : ((G.deleteIncidencesOf t).neighborFinset w ∩ s) = G.neighborFinset w ∩ s := by
    ext x
    simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_inter, mem_neighborFinset,
      inf_adj, iInf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and,
      not_or, ne_eq, and_congr_left_iff, and_iff_left_iff_imp]
    intro hx hwx
    simp only [hwx, forall_const, true_and, hwx.ne, not_false_eq_true, and_true]
    exact fun _ hu ↦ ⟨fun heq ↦ hwt <| heq ▸ hu, fun heq ↦ mem_s_implies_notMem_t (heq ▸ hx) <| hu⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hAw
    let hobj := hresp w hw |>.1 ⟨hAw, hwt⟩
    simp only [degree_in] at hobj ⊢
    exact heqGNw ▸ hobj
  · intro hBw
    let hobj := hresp w hw |>.2.1 ⟨hBw, hwt⟩
    simp only [degree_in] at hobj ⊢
    exact heqGNw ▸ hobj
  · intro hCw
    let hobj := hresp w hw |>.2.2 ⟨hCw, hwt⟩
    simp only [degree_in] at hobj ⊢
    exact heqGNw ▸ hobj

end Tripartition

lemma fA_decreasing {d d' : ℕ} (h : d ≤ d') : fA d' ≤ fA d := by
  if heq : d = d' then exact le_of_eq (heq ▸ rfl) else ?_
  simp only [fA]
  split_ifs
  any_goals grind
  · ring_nf
    calc (1 + d' : ℝ)⁻¹ * 2
      _ ≤ (1 + 2 : ℝ)⁻¹ * 2 := by
        simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
        refine inv_anti₀ (by grind) ?_
        simp only [add_le_add_iff_left, Nat.ofNat_le_cast]
        grind
      _ ≤ 1 := by grind
  · ring_nf
    calc (1 + d' : ℝ)⁻¹ * 2
      _ ≤ (1 + 2 : ℝ)⁻¹ * 2 := by
        simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
        refine inv_anti₀ (by grind) ?_
        simp only [add_le_add_iff_left, Nat.ofNat_le_cast]
        grind
      _ ≤ 5 / 6 := by grind
  · ring_nf
    simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
    refine inv_anti₀ (by grind) (by simp [h])

lemma fB_decreasing {d d' : ℕ} (h : d ≤ d') : fB d' ≤ fB d := by
  have H : 3 ≤ d' → fB d' ≤ 1 / (3 : ℝ) := by
    simp only [fB, one_div]
    intro hd'
    split_ifs
    any_goals grind
    calc (4 / 3) / (d' + 1 : ℝ)
      _ ≤ 4 / (3 : ℝ) / (3 + 1 : ℝ) := by
        ring_nf
        have h : (1 + d' : ℝ)⁻¹ * (4 / 3) = (1 + d' : ℝ)⁻¹ * 4 * 3⁻¹ := by grind
        have _ : 3⁻¹ = 1 / (3 : ℝ) := by exact inv_eq_one_div 3
        rw [h, inv_eq_one_div 3]
        simp only [one_div, inv_pos, Nat.ofNat_pos, mul_le_iff_le_one_left, ge_iff_le]
        suffices (1 + d' : ℝ)⁻¹ ≤ 4⁻¹ by grind
        refine inv_anti₀ four_pos ?_
        calc (4 : ℝ)
          _ = (1 + 3 : ℝ) := by grind
          _ ≤ (1 + d' : ℝ) := by
            simp only [add_le_add_iff_left, Nat.ofNat_le_cast]
            exact Nat.succ_le_of_lt hd'
      _ ≤ (3 : ℝ)⁻¹ := by grind
  simp only [fB] at H ⊢
  split_ifs
  any_goals grind
  ring_nf
  simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀, ge_iff_le]
  refine inv_anti₀ (by grind) (by simp [h])

lemma fC_decreasing {d d' : ℕ} (h : d ≤ d') : fC d' ≤ fC d := by
  simp only [fC]
  split_ifs
  any_goals grind
  · ring_nf
    have h' : 3 ≤ d' := by grind
    calc (1 + d' : ℝ)⁻¹ * (2 / 3)
      _ ≤ (1 + 1 : ℝ)⁻¹ * (2 / 3) := by
        simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀]
        refine inv_anti₀ (by grind) ?_
        rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add]
        refine Nat.cast_le.mpr (by grind)
      _ ≤ 1 := by grind
  · ring_nf
    simp only [one_div]
    have h' : 3 ≤ d' := by grind
    calc (1 + d' : ℝ)⁻¹ * (2 / 3)
      _ ≤ (1 + 3 : ℝ)⁻¹ * (2 / 3) := by
        simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀]
        refine inv_anti₀ (by grind) (by simp [h'])
      _ ≤ 6⁻¹ := by grind
  · ring_nf
    simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀]
    refine inv_anti₀ (by grind) (by simp [h])

lemma f_le_56 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    {v : Fin n} (hv : 0 < G.degree v) : f G ABC v ≤ 5 / (6 : ℝ) := by
  simp only [f, fA, fB, one_div, fC, dite_eq_ite]
  split_ifs
  any_goals grind
  · calc 2 / (G.degree v + 1 : ℝ)
      _ ≤ 2 / (2 + 1 : ℝ) := by
        refine div_le_div_iff_of_pos_left two_pos (by grind) (by grind) |>.mpr ?_
        simp only [add_le_add_iff_right, Nat.ofNat_le_cast]
        grind
      _ ≤ 5 / 6 := by grind
  · calc (4 / 3) / (G.degree v + 1 : ℝ)
      _ ≤ (4 / 3) / (2 + 1 : ℝ) := by
        refine div_le_div_iff_of_pos_left (by grind) (by grind) (by grind) |>.mpr ?_
        simp only [add_le_add_iff_right, Nat.ofNat_le_cast]
        grind
      _ ≤ 5 / 6 := by grind
  · calc (2 / 3) / (G.degree v + 1 : ℝ)
      _ ≤ (2 / 3) / (2 + 1 : ℝ) := by
        refine div_le_div_iff_of_pos_left (by grind) (by grind) (by grind) |>.mpr ?_
        simp only [add_le_add_iff_right, Nat.ofNat_le_cast]
        grind
      _ ≤ 5 / 6 := by grind

lemma f_eq_in_sdiff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    {s : Finset (Fin n)} {w : Fin n} (hw : w ∉ s) :
    f G (ABC \ s) w = f G ABC w := by
  have : ABC.A w ↔ (ABC \ s).A w := ⟨fun h ↦ ⟨h, hw⟩, fun ⟨h, _⟩ ↦ h⟩
  have : ABC.B w ↔ (ABC \ s).B w := ⟨fun h ↦ ⟨h, hw⟩, fun ⟨h, _⟩ ↦ h⟩
  have : ABC.C w ↔ (ABC \ s).C w := ⟨fun h ↦ ⟨h, hw⟩, fun ⟨h, _⟩ ↦ h⟩
  simp only [f]
  split_ifs
  any_goals grind

lemma f_mono_degree {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n))
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (ABC : Tripartition n)
    {v : Fin n} : G₁.degree v = G₂.degree v → f G₁ ABC v = f G₂ ABC v := by
  intro heq
  simp only [f, fA, fB, one_div, fC, dite_eq_ite, heq]

lemma f_pos_of_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    (v : Fin n) : v ∈ ABC → 0 < f G ABC v := by
  have _ : (0 : ℝ) ≤ G.degree v := Nat.cast_nonneg' _
  intro h
  rcases ABC.mem_iff.mp h with hA | hB | hC
  · simp only [f, hA, ↓reduceDIte, fA]
    split_ifs
    any_goals grind
    ring_nf
    simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_right, inv_pos]
    grind [Nat.pos_of_neZero]
  · simp only [f, hB, not_A_of_B, ↓reduceDIte, fB, one_div]
    split_ifs
    any_goals grind
    ring_nf
    simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_pos_iff_of_pos_right, inv_pos]
    grind
  · simp only [f, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, one_div]
    split_ifs
    any_goals grind
    ring_nf
    simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_pos_iff_of_pos_right, inv_pos]
    grind

lemma f_eq_zero_of_notMem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n)
    (v : Fin n) : v ∉ ABC → 0 = f G ABC v := by
  intro hv
  simp only [Tripartition.mem_iff, not_or] at hv
  obtain ⟨hvA, hvB, hvC⟩ := hv
  simp [f, hvA, hvB, hvC]

@[simp, grind! .]
lemma γ_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    {v : Fin n} : 0 ≤ γ G ABC v := by
  have h : G.degree v - 1 ≤ G.degree v := Nat.sub_le ..
  simp only [γ, dite_eq_ite]
  split_ifs
  any_goals simp only [sub_nonneg, fA_decreasing h, fB_decreasing h, fC_decreasing h, le_refl]

private lemma eval_mono {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n))
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hle : G₁ ≤ G₂)
    (ABC : Tripartition n) :
    eval G₂ ABC ≤ eval G₁ ABC := by
  unfold eval
  refine sum_le_sum ?_
  intro w hw
  simp only [Tripartition.toFinset, Tripartition.mem_iff, mem_filter, mem_univ,
    true_and] at hw
  rcases hw with hA | hB | hC
  · simp only [f, hA, ↓reduceDIte, fA]
    exact fA_decreasing <| degree_le_of_le hle
  · simp only [f, hB, not_A_of_B, ↓reduceDIte, fB]
    exact fB_decreasing <| degree_le_of_le hle
  · simp only [f, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC]
    exact fC_decreasing <| degree_le_of_le hle

lemma eval_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ABC : Tripartition n) (W : Finset (Fin n)) (hW : W ∩ ABC.toFinset ≠ ∅) :
    eval G (ABC \ W) < eval G ABC := by
  unfold eval
  calc ∑ v ∈ (ABC \ W).toFinset, f G (ABC \ W) v
    _ = ∑ v ∈ (ABC \ W).toFinset, f G ABC v := by
      refine sum_congr rfl ?_
      intro x hx
      simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff,
        mem_filter, mem_univ, true_and, f, fA, fB, one_div, fC, dite_eq_ite] at hx ⊢
      grind
    _ < ∑ v ∈ (ABC \ W).toFinset, f G ABC v + ∑ v ∈ (W ∩ ABC.toFinset), f G ABC v := by
      simp only [Tripartition.sdiff_eq, inter_assoc, inter_self, lt_add_iff_pos_right]
      obtain ⟨w, hw⟩ := nonempty_def.mp <| nonempty_iff_ne_empty.mpr hW
      calc 0
        _ < f G ABC w :=
          f_pos_of_mem G ABC w <| ABC.coe_mem_toFinset.mpr (mem_inter.mp hw).2
        _ = ∑ v ∈ ((W ∩ ABC.toFinset) ∩ {w}), f G ABC v := by
          have this : ((W ∩ ABC.toFinset) ∩ {w}) = {w} := by grind
          rw [this]
          exact Eq.symm <| sum_singleton _ _
        _ ≤ ∑ v ∈ ((W ∩ ABC.toFinset) ∩ {w}), f G ABC v
          + ∑ v ∈ (W ∩ ABC.toFinset) \ {w}, f G ABC v := by
          simp only [inter_assoc, le_add_iff_nonneg_right]
          refine sum_nonneg' ?_
          intro v
          if hv : v ∈ ABC then
            exact le_of_lt <| f_pos_of_mem G ABC v hv
          else
            exact le_of_eq <| f_eq_zero_of_notMem G ABC v hv
        _ = ∑ v ∈ (W ∩ ABC.toFinset), f G ABC v := sum_inter_add_sum_diff ..
    _ = ∑ v ∈ ABC.toFinset, f G ABC v := by
      have _ {s t : Finset (Fin n)} : s ∩ t = t ∩ s := by exact inter_comm s t
      have h' : (ABC \ W).toFinset = ABC.toFinset \ W := by
        ext
        simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff,
          mem_filter, mem_univ, true_and, mem_sdiff]
        grind
      rw [add_comm, inter_comm, h']
      exact Finset.sum_inter_add_sum_diff ..

lemma degree_deleteIncidencesOf_neighbor {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {v w : Fin n} (hw : G.Adj v w) :
    G.degree w = (G.deleteIncidencesOf {v}).degree w + 1 := by
  suffices G.neighborFinset w = (G.deleteIncidencesOf {v}).neighborFinset w ∪ {v} by
    simp only [degree, congrArg card this]
    calc #((G.deleteIncidencesOf {v}).neighborFinset w ∪ {v})
      _ = #((G.deleteIncidencesOf {v}).neighborFinset w ∪ {v})
        + #((G.deleteIncidencesOf {v}).neighborFinset w ∩ {v}) := by
        simp only [union_singleton, Nat.left_eq_add, card_eq_zero]
        ext x
        simp [deleteIncidencesOf, deleteIncidenceSet, incidenceSet]
      _ = #((G.deleteIncidencesOf {v}).neighborFinset w) + #({v} : Finset _) := by
        exact card_union_add_card_inter ..
      _ = #((G.deleteIncidencesOf {v}).neighborFinset w) + 1 := by
        simp only [card_neighborFinset_eq_degree, card_singleton]
  ext x
  simp only [mem_neighborFinset, deleteIncidencesOf, deleteIncidenceSet, incidenceSet,
    union_singleton, mem_insert, mem_singleton, iInf_iInf_eq_left, inf_adj, deleteEdges_adj,
    Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, and_self_left]
  constructor
  · intro hwx
    if heq : x = v then exact Or.inl heq
    else                exact Or.inr (by simp [hwx, hw.ne, Ne.symm heq])
  · intro h
    rcases h with h | h
    · exact h ▸ hw.symm
    · exact h.1

lemma f_deleteIncidencesOf_singleton {n : ℕ} (ABC : Tripartition n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {v w : Fin n} (hw : G.Adj v w) :
    f (G.deleteIncidencesOf {v}) (ABC \ {v}) w = f G ABC w + γ G ABC w := by
  simp only [f, Tripartition.sdiff_eq, inter_assoc, inter_self, fA, fB, one_div, fC, dite_eq_ite, γ,
    Nat.pred_eq_succ_iff, zero_add, Nat.reduceAdd]
  rw [degree_deleteIncidencesOf_neighbor G hw]
  simp only [Tripartition.sdiff, mem_singleton, hw.ne', not_false_eq_true, and_true,
    Tripartition.sdiff.eq_1, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_eq_right, Nat.cast_add, Nat.cast_one, Nat.reduceEqDiff, add_tsub_cancel_right]
  if hA : (ABC \ {v}).A w then
    simp [hA.left, hw.ne']
  else if hB : (ABC \ {v}).B w then
    simp [hw.ne', hB.left]
  else if hC : (ABC \ {v}).C w then
    simp [hw.ne', hC.left]
  else
    have hA' : ¬ABC.A w := fun this ↦ hA <| by simp [Tripartition.sdiff, this, hw.ne']
    have hB' : ¬ABC.B w := fun this ↦ hB <| by simp [Tripartition.sdiff, this, hw.ne']
    have hC' : ¬ABC.C w := fun this ↦ hC <| by simp [Tripartition.sdiff, this, hw.ne']
    simp [*]

lemma f_deleteIncidencesOf_isolated {n : ℕ} (ABC : Tripartition n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {v w : Fin n} (hv : G.degree v = 0) (hwne : w ≠ v) :
    f (G.deleteIncidencesOf {v}) (ABC \ {v}) w = f G ABC w := by
  have hdeg : G.degree w = (G.deleteIncidencesOf {v}).degree w := by
    refine congrArg card ?_
    ext x
    simp only [mem_neighborFinset, deleteIncidencesOf, deleteIncidenceSet, incidenceSet,
      mem_singleton, iInf_iInf_eq_left, inf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet,
      Sym2.mem_iff, not_and, not_or, and_self_left, iff_self_and, forall_self_imp]
    refine fun hwx ↦ ⟨?_, ?_⟩
    · exact ne_of_deg0_of_adj hv hwx
    · exact ne_of_deg0_of_adj' hv hwx
  let hw' := (not_iff_not.mpr mem_singleton).mpr hwne
  if hA : ABC.A w then
    simp only [f, Tripartition.sdiff, mem_singleton, hA, hwne, not_false_eq_true, and_self,
      ↓reduceDIte, fA, hdeg]
  else if hB : ABC.B w then
    simp only [f, Tripartition.sdiff, mem_singleton, hA, hwne, not_false_eq_true, and_true,
      ↓reduceDIte, hB, and_self, fB, one_div, hdeg]
  else if hC : ABC.C w then
    simp only [f, Tripartition.sdiff, mem_singleton, hA, hwne, not_false_eq_true, and_true,
      ↓reduceDIte, hB, hC, and_self, fC, one_div, hdeg]
  else
    simp only [f, Tripartition.sdiff, mem_singleton, hA, false_and, ↓reduceDIte, hB, hC]

lemma deleteIncidencesOf_le {n : ℕ} {G : SimpleGraph (Fin n)} {s : Finset (Fin n)} :
    (G.deleteIncidencesOf s) ≤ G := by
  intro v w
  simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, inf_adj, iInf_adj,
    deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq, and_imp]
  intro hvw
  simp [hvw, hvw.ne]

lemma deleteIncidencesOf_degree_le {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {s : Finset (Fin n)} {v : Fin n} : (G.deleteIncidencesOf s).degree v ≤ G.degree v := by
  exact degree_le_of_le deleteIncidencesOf_le

end ABC
end CaroWeiType
