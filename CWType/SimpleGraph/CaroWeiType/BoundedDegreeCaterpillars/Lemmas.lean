import CWType.SimpleGraph.CaroWeiType.Basic
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.ABC

namespace CaroWeiType
namespace ABC

open Finset

open SimpleGraph

lemma Δf_eq {c : ℝ} {d : ℕ} :
    c / (d + 1 : ℝ) - c / (d + 1 + 1 : ℝ) = c / ((d + 1 : ℝ)*(d + 1 + 1 : ℝ)) := by
  grind only

lemma Δf_eq' {c : ℝ} {d : ℕ} (hd : 0 < d) :
    c / (d : ℝ) - c / (d + 1 : ℝ) = c / ((d : ℝ)*(d + 1 : ℝ)) := by
  have heq : (d : ℝ) = ((d - 1 : ℕ) + 1 : ℝ) := by
    rw [← @Nat.cast_one ℝ _, ← Nat.cast_add]
    exact Nat.cast_inj.mpr <| Nat.sub_eq_iff_eq_add hd |>.mp rfl
  let hobj := @Δf_eq c (d - 1)
  rw [← heq] at hobj
  exact hobj

lemma Δf_eq'' {c : ℝ} {d : ℕ} (hd : 0 < d) :
    c / ((d - 1 : ℕ) + 1: ℝ) - c / (d + 1 : ℝ) = c / ((d : ℝ)*(d + 1 : ℝ)) := by
  let hobj := @Δf_eq c (d - 1)
  have heq : (d : ℝ) = ((d - 1 : ℕ) + 1 : ℝ) := by
    rw [← @Nat.cast_one ℝ _, ← Nat.cast_add]
    exact Nat.cast_inj.mpr <| Nat.sub_eq_iff_eq_add hd |>.mp rfl
  exact heq ▸ hobj

lemma fA_decreasing {d d' : ℕ} (h : d ≤ d') : fA d' ≤ fA d := by
  if heq : d = d' then exact le_of_eq (heq ▸ rfl) else ?_
  simp only [fA]
  split_ifs
  any_goals grind
  · ring_nf
    calc (1 + d' : ℝ)⁻¹ * 2
      _ ≤ (1 + 2 : ℝ)⁻¹ * 2 := by
        simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
        refine inv_anti₀ (by lia) ?_
        simp only [add_le_add_iff_left, Nat.ofNat_le_cast]
        lia
      _ ≤ 1 := by linarith
  · ring_nf
    calc (1 + d' : ℝ)⁻¹ * 2
      _ ≤ (1 + 2 : ℝ)⁻¹ * 2 := by
        simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
        refine inv_anti₀ (by lia) ?_
        simp only [add_le_add_iff_left, Nat.ofNat_le_cast]
        lia
      _ ≤ 5 / 6 := by linarith
  · ring_nf
    simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
    exact inv_anti₀ one_add_pos <| by simp only [add_le_add_iff_left, Nat.cast_le, h]

lemma fA_decreasing' {d d' : ℕ} (h : fA d' < fA d) : d < d' := by
  exact Nat.lt_of_not_le <| fA_decreasing.mt <| not_le.mpr h

lemma fB_decreasing {d d' : ℕ} (h : d ≤ d') : fB d' ≤ fB d := by
  have H : 3 ≤ d' → fB d' ≤ 1 / (3 : ℝ) := by
    simp only [fB, one_div]
    intro hd'
    split_ifs
    any_goals lia
    calc (4 / 3) / (d' + 1 : ℝ)
      _ ≤ 4 / (3 : ℝ) / (3 + 1 : ℝ) := by
        ring_nf
        have h : (1 + d' : ℝ)⁻¹ * (4 / 3) = (1 + d' : ℝ)⁻¹ * 4 * 3⁻¹ := by linarith
        rw [h, inv_eq_one_div 3]
        simp only [one_div, inv_pos, Nat.ofNat_pos, mul_le_iff_le_one_left, ge_iff_le]
        suffices (1 + d' : ℝ)⁻¹ ≤ 4⁻¹ by linarith
        refine inv_anti₀ four_pos ?_
        calc (4 : ℝ)
          _ = (1 + 3 : ℝ) := by lia
          _ ≤ (1 + d' : ℝ) := by
            simp only [add_le_add_iff_left, Nat.ofNat_le_cast, Nat.succ_le_of_lt hd']
      _ ≤ (3 : ℝ)⁻¹ := by linarith
  simp only [fB] at H ⊢
  split_ifs
  any_goals grind
  ring_nf
  simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀, ge_iff_le]
  exact inv_anti₀ one_add_pos <| by simp only [add_le_add_iff_left, Nat.cast_le, h]

lemma fB_decreasing' {d d' : ℕ} (h : fB d' < fB d) : d < d' := by
  exact Nat.lt_of_not_le <| fB_decreasing.mt <| not_le.mpr h

lemma fC_decreasing {d d' : ℕ} (h : d ≤ d') : fC d' ≤ fC d := by
  simp only [fC]
  split_ifs
  any_goals grind
  · ring_nf
    have h' : 3 ≤ d' := by lia
    calc (1 + d' : ℝ)⁻¹ * (2 / 3)
      _ ≤ (1 + 1 : ℝ)⁻¹ * (2 / 3) := by
        simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀]
        refine inv_anti₀ (pos_add_self_iff.mpr zero_lt_one) ?_
        rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add]
        exact Nat.cast_le.mpr <| by lia
      _ ≤ 1 := by linarith
  · ring_nf
    simp only [one_div]
    have h' : 3 ≤ d' := by lia
    calc (1 + d' : ℝ)⁻¹ * (2 / 3)
      _ ≤ (1 + 3 : ℝ)⁻¹ * (2 / 3) := by
        simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀]
        exact inv_anti₀ (by lia) <| by simp only [add_le_add_iff_left, Nat.ofNat_le_cast, h']
      _ ≤ 6⁻¹ := by linarith
  · ring_nf
    simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_left₀]
    exact inv_anti₀ one_add_pos (by simp only [add_le_add_iff_left, Nat.cast_le, h])

lemma fC_decreasing' {d d' : ℕ} (h : fC d' < fC d) : d < d' := by
  exact Nat.lt_of_not_le <| fC_decreasing.mt <| not_le.mpr h

lemma disjoint_of_sdiff {α : Type*} [DecidableEq α] {X Y Z : Finset α} (h : X ⊆ Y \ Z) :
    X ∩ Z = ∅ := by
  ext x
  simp only [mem_inter, notMem_empty, iff_false, not_and]
  exact fun hx ↦ mem_sdiff.mp (h hx) |>.2

@[simp]
lemma and_or_3 {p₁ p₂ p₃ q : Prop} : (p₁ ∧ q) ∨ (p₂ ∧ q) ∨ (p₃ ∧ q) ↔ (p₁ ∨ p₂ ∨ p₃) ∧ q := by
  constructor
  · intro h
    rcases h with h | h | h <;> simp only [h, true_or, or_true, and_self]
  · intro ⟨hp, hq⟩
    rcases hp with h | h | h <;> simp only [hq, and_true, h, and_self, true_or, or_true]

@[simp]
lemma not_and' {p q : Prop} : ¬(p ∧ q) ↔ (¬p) ∨ (¬q) := by
  constructor
  · intro h
    simp only [not_and] at h
    if hp : p then
      exact Or.inr <| h hp
    else
      exact Or.inl hp
  · intro h
    rcases h with h | h <;> simp only [h, false_and, and_false, not_false_eq_true]

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

lemma f_eq_zero_of_notMem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : v ∉ ABC) : 0 = f G ABC v := by
  simp only [Tripartition.mem_iff, not_or] at hv
  obtain ⟨hvA, hvB, hvC⟩ := hv
  simp only [f, hvA, ↓reduceDIte, hvB, hvC]

lemma γ_eq_zero_of_notMem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : v ∉ ABC) : 0 = γ G ABC v := by
  simp only [Tripartition.mem_iff, not_or] at hv
  obtain ⟨hvA, hvB, hvC⟩ := hv
  simp only [γ, hvA, ↓reduceDIte, hvB, hvC]

lemma one_sixth_pos : (0 : ℝ) < 1 / 6 := by linarith

lemma one_third_pos : (0 : ℝ) < 1 / 3 := by linarith

lemma two_thirds_pos : (0 : ℝ) < 2 / 3 := by linarith

lemma four_thirds_pos : (0 : ℝ) < 4 / 3 := by linarith

lemma zero_le_one_sixth : (0 : ℝ) ≤ 1 / 6 := by linarith

lemma zero_le_one_third : (0 : ℝ) ≤ 1 / 3 := by linarith

lemma zero_le_two_thirds : (0 : ℝ) ≤ 2 / 3 := by linarith

lemma zero_le_five_sixths : (0 : ℝ) ≤ 5 / 6 := by linarith

lemma zero_le_four_thirds : (0 : ℝ) ≤ 4 / 3 := by linarith

lemma two_thirds_le_five_sixths : (2 : ℝ) / 3 ≤ 5 / 6 := by linarith

lemma two_thirds_le_one : (2 : ℝ) / 3 ≤ 1 := by linarith

lemma four_thirds_le_two : (4 : ℝ) / 3 ≤ 2 := by linarith

lemma fB_le_fA {d : ℕ} : fB d ≤ fA d := by
  if hd : d = 0 then
    simp only [fA, fB, hd, ↓reduceIte, le_refl]
  else if hd : d = 1 then
    simp only [fA, fB, hd, one_ne_zero, ↓reduceIte, le_refl]
  else if hd : d = 2 then
    simp only [fA, fB, hd, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.cast_ofNat]
    linarith
  else
    simp only [fA, fB, ↓reduceIte, *]
    ring_nf
    simp only [inv_pos, one_add_pos, mul_le_mul_iff_right₀]
    linarith

lemma fC_le_fB {d : ℕ} : fC d ≤ fB d := by
  if hd : d = 0 then
    simp only [fB, fC, hd, ↓reduceIte, le_refl]
  else if hd : d = 1 then
    simp only [fC, hd, one_ne_zero, ↓reduceIte, OfNat.one_ne_ofNat, or_false, one_div, fB]
    linarith
  else if hd : d = 2 then
    simp only [fC, hd, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, or_true, one_div, fB]
    linarith
  else
    simp only [fC, ↓reduceIte, or_self, fB, *]
    ring_nf
    simp only [inv_pos, one_add_pos, mul_le_mul_iff_right₀]
    linarith

lemma fC_le_fA {d : ℕ} : fC d ≤ fA d :=
  le_trans fC_le_fB fB_le_fA

lemma zero_le_fA {d : ℕ} : 0 ≤ fA d := by
  rw [fA]
  split_ifs
  · exact zero_le_one
  · exact zero_le_five_sixths
  · exact div_nonneg zero_le_two (le_of_lt add_one_pos)

lemma zero_le_fB {d : ℕ} : 0 ≤ fB d := by
  rw [fB]
  split_ifs
  · exact zero_le_one
  · exact zero_le_five_sixths
  · exact zero_le_one_third
  · exact div_nonneg zero_le_four_thirds (le_of_lt add_one_pos)

lemma zero_le_fC {d : ℕ} : 0 ≤ fC d := by
  rw [fC]
  split_ifs
  · exact zero_le_one
  · exact zero_le_one_sixth
  · exact div_nonneg zero_le_two_thirds (le_of_lt add_one_pos)

lemma fA_le_one {d : ℕ} : fA d ≤ 1 := by
  rw [fA]
  split_ifs
  · exact le_refl _
  · linarith
  · refine div_le_one₀ add_one_pos |>.mpr ?_
    rw [← Nat.cast_one, ← Nat.cast_add]
    refine Nat.cast_le.mpr <| by lia

lemma fB_le_one {d : ℕ} : fB d ≤ 1 := by
  rw [fB]
  split_ifs
  · exact le_refl _
  · linarith
  · linarith
  · refine div_le_one₀ add_one_pos |>.mpr ?_
    rw [← Nat.cast_one, ← Nat.cast_add]
    have H : 4 / 3 ≤ (2 : ℝ) := by linarith
    exact le_trans H (Nat.cast_le.mpr <| by lia)

lemma fC_le_one {d : ℕ} : fC d ≤ 1 := by
  rw [fC]
  split_ifs
  · exact le_refl _
  · linarith
  · refine div_le_one₀ add_one_pos |>.mpr ?_
    rw [← Nat.cast_one, ← Nat.cast_add]
    have H : 2 / 3 ≤ (1 : ℝ) := by linarith
    refine le_trans H ?_
    rw [← Nat.cast_one]
    exact Nat.cast_le.mpr <| by lia

lemma f_le_one {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    {v : Fin n} : f G ABC v ≤ 1 := by
  rw [f]
  split_ifs
  · exact fA_le_one
  · exact fB_le_one
  · exact fC_le_one
  · exact zero_le_one

-- f(0)

lemma fA0 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 0) : f G ABC v = 1 := by
  simp only [f, hA, ↓reduceDIte, fA, hv, ↓reduceIte]

lemma fB0 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 0) : f G ABC v = 1 := by
  simp only [f, hB, not_A_of_B, ↓reduceDIte, fB, hv, ↓reduceIte]

lemma fC0 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 0) : f G ABC v = 1 := by
  simp only [f, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, ↓reduceIte]

lemma f0 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (h : v ∈ ABC) (hv : G.degree v = 0) : f G ABC v = 1 := by
  rcases h with h | h | h
  · exact fA0 h hv
  · exact fB0 h hv
  · exact fC0 h hv

-- f(1)

lemma fA1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 1) : f G ABC v = 5 / 6 := by
  simp only [f, hA, ↓reduceDIte, fA, hv, one_ne_zero, ↓reduceIte]

lemma fB1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 1) : f G ABC v = 5 / 6 := by
  simp only [f, hB, not_A_of_B, ↓reduceDIte, fB, hv, one_ne_zero, ↓reduceIte]

lemma fC1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 1) : f G ABC v = 1 / 6 := by
  simp only [f, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, one_ne_zero, ↓reduceIte,
    OfNat.one_ne_ofNat, or_false, one_div]

-- f(2)

lemma fA2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 2) : f G ABC v = 2 / 3 := by
  simp only [f, hA, ↓reduceDIte, fA, hv, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one,
    Nat.cast_ofNat]
  lia

lemma fB2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 2) : f G ABC v = 1 / 3 := by
  simp only [f, hB, not_A_of_B, ↓reduceDIte, fB, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, one_div]

lemma fC2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 2) : f G ABC v = 1 / 6 := by
  simp only [f, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, or_true, one_div]

-- f(3)

lemma fA3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 3) : f G ABC v = 1 / 2 := by
  simp only [f, hA, ↓reduceDIte, fA, hv, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one,
    Nat.cast_ofNat]
  linarith

lemma fB3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 3) : f G ABC v = 1 / 3 := by
  simp only [f, hB, not_A_of_B, ↓reduceDIte, fB, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, Nat.succ_ne_self, Nat.cast_ofNat, one_div]
  linarith

lemma fC3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 3) : f G ABC v = 1 / 6 := by
  simp only [f, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, Nat.succ_ne_self, or_self, Nat.cast_ofNat, one_div]
  linarith

-- f(4)

lemma fA4 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 4) : f G ABC v = 2 / 5 := by
  simp only [f, hA, ↓reduceDIte, fA, hv, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one,
    Nat.cast_ofNat]
  linarith

lemma fB4 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 4) : f G ABC v = 4 / 15 := by
  simp only [f, not_A_of_B, hB, ↓reduceDIte, fB, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, Nat.cast_ofNat, Nat.reduceEqDiff]
  linarith

lemma fC4 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 4) : f G ABC v = 2 / 15 := by
  simp only [f, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, Nat.cast_ofNat, false_or, Nat.reduceEqDiff, ↓reduceIte]
  linarith

-- f(6)

lemma fA6 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 6) : f G ABC v = 2 / 7 := by
  simp only [f, hA, ↓reduceDIte, fA, hv, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one,
    Nat.cast_ofNat]
  linarith

lemma f_le_fA {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    {v : Fin n} : f G ABC v ≤ fA (G.degree v) := by
  if hvABC : v ∈ ABC then
    rcases hvABC with hA | hB | hC
    · simp only [f, hA, ↓reduceDIte, le_refl]
    · simp only [f, hB, not_A_of_B, ↓reduceDIte, fB_le_fA]
    · simp only [f, hC, not_A_of_C, not_B_of_C, ↓reduceDIte, fC_le_fA]
  else
    exact (f_eq_zero_of_notMem G hvABC) ▸ zero_le_fA

lemma fA_eq_deg_mul_γ_of_three_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hAv : ABC.A v) (hdv : 3 ≤ G.degree v) :
    f G ABC v = G.degree v * γ G ABC v := by
  simp only [f, γ, hAv, ↓reduceDIte]
  have h1 : fA (G.degree v) = 2 / (G.degree v + 1 : ℝ) := by grind
  have h2 : fA (G.degree v - 1) = 2 / ((G.degree v - 1 : ℕ) + 1 : ℝ) := by grind
  rw [h1, h2]
  have h : (↑(G.degree v - 1 : ℕ) + 1 : ℝ) = G.degree v := by
    rw [← @Nat.cast_one ℝ _, ← Nat.cast_add, Nat.cast_inj]
    exact Nat.sub_add_cancel <| Nat.one_le_of_lt hdv
  rw [h, Δf_eq' (Nat.zero_lt_of_lt hdv)]
  grind only

lemma fB_eq_deg_mul_γ_of_four_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hBv : ABC.B v) (hdv : 4 ≤ G.degree v) :
    f G ABC v = G.degree v * γ G ABC v := by
  simp only [f, γ, hBv, not_A_of_B, ↓reduceDIte]
  have h1 : fB (G.degree v) = (4 / 3) / (G.degree v + 1 : ℝ) := by grind
  have h2 : fB (G.degree v - 1) = (4 / 3) / ((G.degree v - 1 : ℕ) + 1 : ℝ) := by grind
  rw [h1, h2]
  have h : (↑(G.degree v - 1 : ℕ) + 1 : ℝ) = G.degree v := by
    rw [← @Nat.cast_one ℝ _, ← Nat.cast_add, Nat.cast_inj]
    exact Nat.sub_add_cancel <| Nat.one_le_of_lt hdv
  rw [h, Δf_eq' (Nat.zero_lt_of_lt hdv)]
  grind only

lemma fC_eq_deg_mul_γ_of_four_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hCv : ABC.C v) (hdv : 4 ≤ G.degree v) :
    f G ABC v = G.degree v * γ G ABC v := by
  simp only [f, γ, hCv, not_A_of_C, not_B_of_C, ↓reduceDIte]
  have h1 : fC (G.degree v) = (2 / 3) / (G.degree v + 1 : ℝ) := by grind
  have h2 : fC (G.degree v - 1) = (2 / 3) / ((G.degree v - 1 : ℕ) + 1 : ℝ) := by grind
  rw [h1, h2]
  have h : (↑(G.degree v - 1 : ℕ) + 1 : ℝ) = G.degree v := by
    rw [← @Nat.cast_one ℝ _, ← Nat.cast_add, Nat.cast_inj]
    exact Nat.sub_add_cancel <| Nat.one_le_of_lt hdv
  rw [h, Δf_eq' (Nat.zero_lt_of_lt hdv)]
  grind only

lemma fA_le_13_of_5_le_deg' {d : ℕ} (hv : 5 ≤ d) : fA d ≤ 1 / 3 := by
  haveI : (1 : ℝ) / 3 = 2 / 6 := by linarith
  rw [this]
  simp only [fA]
  split_ifs
  any_goals linarith
  refine (div_le_div_iff_of_pos_left two_pos add_one_pos Nat.ofNat_pos').mpr ?_
  rw [← Nat.cast_one, ← Nat.cast_add]
  refine Nat.cast_le.mpr ?_
  simp only [Nat.reduceLeDiff, hv]

lemma fA_le_13_of_5_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hA : ABC.A v) (hv : 5 ≤ G.degree v) :
    f G ABC v ≤ 1 / 3 := by
  simp only [f, hA, ↓reduceDIte]
  exact fA_le_13_of_5_le_deg' hv

lemma fA_le_25_of_4_le_deg' {d : ℕ} (hv : 4 ≤ d) : fA d ≤ 2 / 5 := by
  simp only [fA]
  split_ifs
  any_goals linarith
  refine (div_le_div_iff_of_pos_left two_pos add_one_pos five_pos).mpr ?_
  rw [← Nat.cast_one, ← Nat.cast_add]
  refine Nat.cast_le.mpr ?_
  simp only [Nat.reduceLeDiff, hv]

lemma fA_le_25_of_4_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hA : ABC.A v) (hv : 4 ≤ G.degree v) :
    f G ABC v ≤ 2 / 5 := by
  simp only [f, hA, ↓reduceDIte]
  exact fA_le_25_of_4_le_deg' hv

lemma fA_le_12_of_3_le_deg' {d : ℕ} (hv : 3 ≤ d) : fA d ≤ 1 / 2 := by
  simp only [fA]
  split_ifs
  any_goals linarith
  calc _
    _ ≤ 2 / (4 : ℝ) := by
      refine (div_le_div_iff_of_pos_left two_pos add_one_pos four_pos).mpr ?_
      rw [← Nat.cast_four, ← Nat.cast_one, ← Nat.cast_add]
      exact Nat.cast_le.mpr <| Nat.le_add_of_sub_le hv
    _ ≤ 1 / 2 := by linarith

lemma fA_le_12_of_3_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hA : ABC.A v) (hv : 3 ≤ G.degree v) :
    f G ABC v ≤ 1 / 2 := by
  simp only [f, hA, ↓reduceDIte]
  exact fA_le_12_of_3_le_deg' hv

lemma fA_le_23_of_2_le_deg' {d : ℕ} (hd : 2 ≤ d) : fA d ≤ 2 / 3 := by
  if h2 : d = 2 then
    simp only [fA, h2, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.cast_ofNat]
    lia
  else
    exact le_trans (fA_le_12_of_3_le_deg' (by lia)) (by linarith)

lemma fA_le_23_of_2_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hA : ABC.A v) (hv : 2 ≤ G.degree v) :
    f G ABC v ≤ 2 / 3 := by
  simp only [f, hA, ↓reduceDIte]
  exact fA_le_23_of_2_le_deg' hv

lemma fA_le_56_of_1_le_deg' {d : ℕ} (hd : 1 ≤ d) : fA d ≤ 5 / 6 := by
  if h1 : d = 1 then
    simp [h1]
  else
    exact le_trans (fA_le_23_of_2_le_deg' (by lia)) (by linarith)

lemma fA_le_56_of_1_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hA : ABC.A v) (hv : 1 ≤ G.degree v) :
    f G ABC v ≤ 5 / 6 := by
  simp only [f, hA, ↓reduceDIte]
  exact fA_le_56_of_1_le_deg' hv

lemma fB_le_13_if_2_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hB : ABC.B v) (hv : 2 ≤ G.degree v) :
    f G ABC v ≤ 1 / 3 := by
  simp only [f, hB, not_A_of_B, ↓reduceDIte, fB]
  split_ifs
  any_goals linarith
  calc (4 / 3) / (G.degree v + 1 : ℝ)
    _ ≤ (4 / 3) / (4 : ℝ) := by
      refine (div_le_div_iff_of_pos_left (by linarith) add_one_pos four_pos).mpr ?_
      rw [← Nat.cast_four, ← Nat.cast_one, ← Nat.cast_add]
      exact Nat.cast_le.mpr (by lia)
    _ ≤ 1 / 3 := by linarith

lemma fB_le_56_if_1_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hB : ABC.B v) (hv : 1 ≤ G.degree v) :
    f G ABC v ≤ 5 / 6 := by
  if h1 : G.degree v = 1 then
    rw [fB1 hB h1]
  else
    exact le_trans (fB_le_13_if_2_le_deg hB (by lia)) (by linarith)

lemma fC_le_16_if_2_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hC : ABC.C v) (hv : 2 ≤ G.degree v) :
    f G ABC v ≤ 1 / 6 := by
  simp only [f, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC]
  split_ifs
  any_goals linarith
  calc (2 / 3) / (G.degree v + 1 : ℝ)
    _ ≤ (2 / 3) / (4 : ℝ) := by
      refine (div_le_div_iff_of_pos_left (by linarith) add_one_pos four_pos).mpr ?_
      rw [← Nat.cast_four, ← Nat.cast_one, ← Nat.cast_add]
      exact Nat.cast_le.mpr (by lia)
    _ ≤ 1 / 6 := by linarith

lemma fC_le_16_if_1_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hC : ABC.C v) (hv : 1 ≤ G.degree v) :
    f G ABC v ≤ 1 / 6 := by
  if h1 : G.degree v = 1 then
    rw [fC1 hC h1]
  else
    exact fC_le_16_if_2_le_deg hC (by lia)

lemma f_le_1_over_2_of_3_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : 3 ≤ G.degree v) :
    f G ABC v ≤ 1 / 2 := by
  if hvABC : v ∈ ABC then
    rcases ABC.mem_iff.mp hvABC with hA | hB | hC
    · exact fA_le_12_of_3_le_deg hA hv
    · exact le_trans (fB_le_13_if_2_le_deg hB (Nat.le_of_add_left_le hv)) (by linarith)
    · exact le_trans (fC_le_16_if_2_le_deg hC (Nat.le_of_add_left_le hv)) (by linarith)
  else
    grind [f, ABC.mem_iff]

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

lemma A2_or_A3_of_f_lt_25_of_2_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : 2 ≤ G.degree v) (h : v ∈ ABC)
    (hf : 2 / 5 < f G ABC v) : ABC.A v ∧ (G.degree v = 2 ∨ G.degree v = 3) := by
  rcases h with hA | hB | hC
  · refine ⟨hA, ?_⟩
    have hobj := Function.mt (fA_le_25_of_4_le_deg hA) <| not_le.mpr hf
    grind only
  · grind [fB_le_13_if_2_le_deg hB hv]
  · grind [fC_le_16_if_2_le_deg hC hv]

lemma γA_eq_of_three_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hAv : ABC.A v) (hdv : 3 ≤ G.degree v) :
    γ G ABC v = 2 / ((G.degree v) * (G.degree v + 1 : ℝ)) := by
  simp only [γ, hAv, ↓reduceDIte, fA]
  split_ifs
  any_goals grind
  have heq : (G.degree v : ℝ) = ((G.degree v - 1 : ℕ) + 1 : ℝ) := by
    rw [← @Nat.cast_one ℝ _, ← Nat.cast_add]
    exact Nat.cast_inj.mpr <| Nat.sub_eq_iff_eq_add (Nat.one_le_of_lt hdv) |>.mp rfl
  rw [← heq, Δf_eq']
  lia

lemma γB_eq_of_four_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hBv : ABC.B v) (hdv : 4 ≤ G.degree v) :
    γ G ABC v = (4 / 3) / ((G.degree v) * (G.degree v + 1 : ℝ)) := by
  simp only [γ, hBv, not_A_of_B, ↓reduceDIte, fB]
  split_ifs
  any_goals grind
  have heq : (G.degree v : ℝ) = ((G.degree v - 1 : ℕ) + 1 : ℝ) := by
    rw [← @Nat.cast_one ℝ _, ← Nat.cast_add]
    exact Nat.cast_inj.mpr <| Nat.sub_eq_iff_eq_add (Nat.one_le_of_lt hdv) |>.mp rfl
  rw [← heq, Δf_eq']
  lia

lemma γC_eq_of_four_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hCv : ABC.C v) (hdv : 4 ≤ G.degree v) :
    γ G ABC v = (2 / 3) / ((G.degree v) * (G.degree v + 1 : ℝ)) := by
  simp only [γ, hCv, not_A_of_C, not_B_of_C, ↓reduceDIte, fC]
  split_ifs
  any_goals grind
  have heq : (G.degree v : ℝ) = ((G.degree v - 1 : ℕ) + 1 : ℝ) := by
    rw [← @Nat.cast_one ℝ _, ← Nat.cast_add]
    exact Nat.cast_inj.mpr <| Nat.sub_eq_iff_eq_add (Nat.one_le_of_lt hdv) |>.mp rfl
  rw [← heq, Δf_eq']
  lia

lemma γ_le_γA_of_four_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hdv : 4 ≤ G.degree v) :
    γ G ABC v ≤ fA (G.degree v - 1) - fA (G.degree v) := by
  if hvABC : v ∈ ABC then
    cases hvABC with
    | inl hA => simp only [γ, hA, ↓reduceDIte, le_refl]
    | inr hBC => ?_
    have hdv1 : G.degree v ≠ 1 := by linarith
    have hdv1' : G.degree v - 1 ≠ 0 := by lia
    have hdv2 : G.degree v ≠ 2 := by linarith
    simp only [fA, hdv1', ↓reduceIte, Nat.pred_eq_succ_iff, zero_add, hdv2, Nat.ne_zero_of_lt hdv,
      hdv1, ge_iff_le]
    rw [Δf_eq'' (by lia)]
    rcases hBC with hB | hC
    · simp only [γB_eq_of_four_le_deg hB hdv]
      refine div_le_div_iff_of_pos_right ?_ |>.mpr ?_
      · refine Left.mul_pos ?_ add_one_pos
        rw [← Nat.cast_zero, Nat.cast_lt]
        exact Nat.zero_lt_of_lt hdv
      · linarith
    · rw [γC_eq_of_four_le_deg hC hdv]
      refine div_le_div_iff_of_pos_right ?_ |>.mpr ?_
      · refine Left.mul_pos ?_ add_one_pos
        rw [← Nat.cast_zero, Nat.cast_lt]
        exact Nat.zero_lt_of_lt hdv
      · linarith
  else
    rw [← γ_eq_zero_of_notMem G hvABC]
    exact sub_nonneg_of_le <| fA_decreasing <| Nat.sub_le ..

lemma γA1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 1) : γ G ABC v = 1 / 6 := by
  simp only [γ, hA, ↓reduceDIte, fA, hv, tsub_self, ↓reduceIte, one_ne_zero, one_div]
  linarith

lemma γA2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 2) : γ G ABC v = 1 / 6 := by
  simp only [γ, hA, ↓reduceDIte, fA, hv, Nat.add_one_sub_one, one_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Nat.cast_ofNat, one_div]
  linarith

lemma γA3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 3) : γ G ABC v = 1 / 6 := by
  rw [γA_eq_of_three_le_deg hA (le_of_eq hv.symm), hv]
  linarith

lemma γA4 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 4) : γ G ABC v = 1 / 10 := by
  rw [γA_eq_of_three_le_deg hA (by lia), hv]
  linarith

lemma γA5 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 5) : γ G ABC v = 1 / 15 := by
  rw [γA_eq_of_three_le_deg hA (by lia), hv]
  linarith

lemma γA6 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 6) : γ G ABC v = 1 / 21 := by
  rw [γA_eq_of_three_le_deg hA (by lia), hv]
  linarith

lemma γA_decreasing_of_three_le_degree {d d' : ℕ} (hdd' : d ≤ d') (hd : 3 ≤ d) :
    fA (d' - 1) - fA d' ≤ fA (d - 1) - fA d := by
  simp only [fA]
  have hd0 : d ≠ 0 := by linarith
  have hd'0 : d' ≠ 0 := by linarith
  have hd1 : d ≠ 1 := by linarith
  have hd'1 : d' ≠ 1 := by linarith
  have hd1' : d - 1 ≠ 0 := by lia
  have hd'1' : d' - 1 ≠ 0 := by lia
  have hd2 : d ≠ 2 := by linarith
  have hd'2 : d' ≠ 2 := by linarith
  simp only [ ↓reduceIte, Nat.pred_eq_succ_iff, zero_add, ge_iff_le,
    hd0, hd'0, hd1, hd'1, hd1', hd'1', hd2, hd'2]
  repeat rw [Δf_eq'' (by lia)]
  refine (div_le_div_iff₀ ?_ ?_).mpr ?_
  · refine Left.mul_pos ?_ add_one_pos
    rw [← Nat.cast_zero, Nat.cast_lt]
    lia
  · refine Left.mul_pos ?_ add_one_pos
    rw [← Nat.cast_zero, Nat.cast_lt]
    lia
  · simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
    rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_le]
    refine Nat.mul_le_mul hdd' ?_
    simp only [add_le_add_iff_right, hdd']

lemma γA_le_1_10_of_4_le_degree {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hdv : 4 ≤ G.degree v) (hAv : ABC.A v) :
    γ G ABC v ≤ 1 / 10 := by
  simp only [γ, hAv, ↓reduceDIte, fA]
  split_ifs
  any_goals grind
  have hdv' : ((G.degree v - 1 : ℕ) + 1 : ℝ) = G.degree v := by
    rw [← @Nat.cast_one ℝ _, ← Nat.cast_add, Nat.cast_inj]
    exact Nat.succ_pred_eq_of_ne_zero (by lia)
  rw [hdv', Δf_eq' (by lia)]
  calc 2 / ((G.degree v : ℝ) * (G.degree v + 1))
    _ ≤ 2 / ((4 : ℝ) * 5) := by
      refine div_le_div_of_nonneg_left zero_le_two (by lia) ?_
      refine mul_le_mul_of_nonneg' ?_ ?_ ?_ ?_
      · rw [← Nat.cast_four, Nat.cast_le]
        exact hdv
      · rw [← Nat.cast_one, ← Nat.cast_add, ← cast_five, Nat.cast_le]
        lia
      · exact le_of_lt five_pos
      · rw [← Nat.cast_zero, Nat.cast_le]
        exact Nat.zero_le _
    _ ≤ 1 / 10 := by linarith

lemma γB1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 1) : γ G ABC v = 1 / 6 := by
  simp only [γ, hB, not_A_of_B, ↓reduceDIte, fB, hv, tsub_self, ↓reduceIte, one_ne_zero, one_div]
  linarith

lemma γB2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 2) : γ G ABC v = 1 / 2 := by
  simp only [γ, hB, not_A_of_B, ↓reduceDIte, fB, hv, Nat.add_one_sub_one, one_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
  linarith

lemma γB3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hdv : G.degree v = 3) : γ G ABC v = 0 := by
  simp only [γ, hB, not_A_of_B, ↓reduceDIte, fB, hdv, ↓reduceIte, Nat.add_one_sub_one,
    OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.succ_ne_self, Nat.cast_ofNat]
  linarith

lemma γB4 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hdv : G.degree v = 4) : γ G ABC v = 1 / 15 := by
  rw [γB_eq_of_four_le_deg hB (by lia), hdv]
  linarith

lemma γB_decreasing_of_four_le_degree {d d' : ℕ} (hdd' : d ≤ d') (hd : 4 ≤ d) :
    fB (d' - 1) - fB d' ≤ fB (d - 1) - fB d := by
  simp only [fB]
  have hd0 : d ≠ 0 := by linarith
  have hd'0 : d' ≠ 0 := by linarith
  have hd1 : d ≠ 1 := by linarith
  have hd'1 : d' ≠ 1 := by linarith
  have hd1' : d - 1 ≠ 0 := by lia
  have hd'1' : d' - 1 ≠ 0 := by lia
  have hd2 : d ≠ 2 := by linarith
  have hd'2 : d' ≠ 2 := by linarith
  have hd3 : d ≠ 3 := by linarith
  have hd'3 : d' ≠ 3 := by linarith
  simp only [ ↓reduceIte, Nat.pred_eq_succ_iff, zero_add, ge_iff_le,
    hd0, hd'0, hd1, hd'1, hd1', hd'1', hd2, hd'2, hd3, hd'3]
  repeat rw [Δf_eq'' (by lia)]
  refine (div_le_div_iff₀ ?_ ?_).mpr ?_
  · refine Left.mul_pos ?_ add_one_pos
    rw [← Nat.cast_zero, Nat.cast_lt]
    lia
  · refine Left.mul_pos ?_ add_one_pos
    rw [← Nat.cast_zero, Nat.cast_lt]
    lia
  · simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_right₀]
    rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_le]
    refine Nat.mul_le_mul hdd' ?_
    simp only [add_le_add_iff_right, hdd']

lemma γC_decreasing_of_four_le_degree {d d' : ℕ} (hdd' : d ≤ d') (hd : 4 ≤ d) :
    fC (d' - 1) - fC d' ≤ fC (d - 1) - fC d := by
  simp only [fC]
  have hd0 : d ≠ 0 := by linarith
  have hd'0 : d' ≠ 0 := by linarith
  have hd1 : d ≠ 1 := by linarith
  have hd'1 : d' ≠ 1 := by linarith
  have hd1' : d - 1 ≠ 0 := by lia
  have hd'1' : d' - 1 ≠ 0 := by lia
  have hd2 : d ≠ 2 := by linarith
  have hd'2 : d' ≠ 2 := by linarith
  have hd3 : d ≠ 3 := by linarith
  have hd'3 : d' ≠ 3 := by linarith
  simp only [ ↓reduceIte, Nat.pred_eq_succ_iff, zero_add, ge_iff_le, false_or,
    hd0, hd'0, hd1, hd'1, hd1', hd'1', hd2, hd'2, hd3, hd'3]
  repeat rw [Δf_eq'' (by lia)]
  refine (div_le_div_iff₀ ?_ ?_).mpr ?_
  · refine Left.mul_pos ?_ add_one_pos
    rw [← Nat.cast_zero, Nat.cast_lt]
    lia
  · refine Left.mul_pos ?_ add_one_pos
    rw [← Nat.cast_zero, Nat.cast_lt]
    lia
  · simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_right₀]
    rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_le]
    refine Nat.mul_le_mul hdd' ?_
    simp only [add_le_add_iff_right, hdd']

lemma γB_le_1_15_of_4_le_degree {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hdv : 4 ≤ G.degree v) (hBv : ABC.B v) :
    γ G ABC v ≤ 1 / 15 := by
  simp only [γ, hBv, not_A_of_B, ↓reduceDIte, fB]
  split_ifs
  any_goals grind
  have hdv' : ((G.degree v - 1 : ℕ) + 1 : ℝ) = G.degree v := by
    rw [← @Nat.cast_one ℝ _, ← Nat.cast_add, Nat.cast_inj]
    exact Nat.succ_pred_eq_of_ne_zero (by lia)
  rw [hdv', Δf_eq' (by lia)]
  calc (4 / 3) / ((G.degree v : ℝ) * (G.degree v + 1))
    _ ≤ (4 / 3) / ((4 : ℝ) * 5) := by
      refine div_le_div_of_nonneg_left zero_le_four_thirds (by lia) ?_
      refine mul_le_mul_of_nonneg' ?_ ?_ ?_ ?_
      · rw [← Nat.cast_four, Nat.cast_le]
        exact hdv
      · rw [← Nat.cast_one, ← Nat.cast_add, ← cast_five, Nat.cast_le]
        lia
      · exact le_of_lt five_pos
      · rw [← Nat.cast_zero, Nat.cast_le]
        exact Nat.zero_le _
    _ ≤ 1 / 15 := by linarith

lemma γC1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 1) : γ G ABC v = 5 / 6 := by
  simp only [γ, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, tsub_self, ↓reduceIte, one_ne_zero,
    OfNat.one_ne_ofNat, or_false, one_div]
  linarith

lemma γC2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 2) : γ G ABC v = 0 := by
  simp only [γ, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, Nat.add_one_sub_one, one_ne_zero,
    ↓reduceIte, OfNat.one_ne_ofNat, or_false, one_div, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    or_true, sub_self]

lemma γC3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hdv : G.degree v = 3) : γ G ABC v = 0 := by
  simp only [γ, hC, not_A_of_C, not_B_of_C, ↓reduceDIte, fC, hdv, ↓reduceIte, Nat.add_one_sub_one,
    OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.succ_ne_self, Nat.cast_ofNat, false_or]
  linarith

lemma γC_le_1_30_of_4_le_degree {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hdv : 4 ≤ G.degree v) (hCv : ABC.C v) :
    γ G ABC v ≤ 1 / 30 := by
  simp only [γ, hCv, not_A_of_C, not_B_of_C, ↓reduceDIte, fC]
  split_ifs
  any_goals grind
  have hdv' : ((G.degree v - 1 : ℕ) + 1 : ℝ) = G.degree v := by
    rw [← @Nat.cast_one ℝ _, ← Nat.cast_add, Nat.cast_inj]
    exact Nat.succ_pred_eq_of_ne_zero (by lia)
  rw [hdv', Δf_eq' (by lia)]
  calc (2 / 3) / ((G.degree v : ℝ) * (G.degree v + 1))
    _ ≤ (2 / 3) / ((4 : ℝ) * 5) := by
      refine div_le_div_of_nonneg_left zero_le_two_thirds (by lia) ?_
      refine mul_le_mul_of_nonneg' ?_ ?_ ?_ ?_
      · rw [← Nat.cast_four, Nat.cast_le]
        exact hdv
      · rw [← Nat.cast_one, ← Nat.cast_add, ← cast_five, Nat.cast_le]
        lia
      · exact le_of_lt five_pos
      · rw [← Nat.cast_zero, Nat.cast_le]
        exact Nat.zero_le _
    _ ≤ 1 / 30 := by linarith

lemma γ_le_1_10_of_4_le_degree {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hdv : 4 ≤ G.degree v) (hv : v ∈ ABC) :
    γ G ABC v ≤ 1 / 10 := by
  rcases hv with h | h | h
  · exact γA_le_1_10_of_4_le_degree hdv h
  · refine le_trans (γB_le_1_15_of_4_le_degree hdv h) (by linarith)
  · refine le_trans (γC_le_1_30_of_4_le_degree hdv h) (by linarith)

lemma γA_pos_of_four_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hAv : ABC.A v) (hdv : 4 ≤ G.degree v) :
    0 < γ G ABC v := by
  simp only [γ, hAv, ↓reduceDIte]
  haveI : fA (G.degree v - 1) - fA (G.degree v)
      = 2 / ((G.degree v - 1 : ℕ) + 1 : ℝ) - 2 / (G.degree v + 1 : ℝ) := by
    grind
  rw [this, sub_pos]
  refine div_lt_div_of_pos_left zero_lt_two add_one_pos ?_
  simp only [add_lt_add_iff_right, Nat.cast_lt, tsub_lt_self_iff, zero_lt_one, and_true]
  exact Nat.zero_lt_of_lt hdv

lemma γB_pos_of_four_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hBv : ABC.B v) (hdv : 4 ≤ G.degree v) :
    0 < γ G ABC v := by
  simp only [γ, not_A_of_B, hBv, ↓reduceDIte]
  haveI : fB (G.degree v - 1) - fB (G.degree v)
      = (4 / 3) / ((G.degree v - 1 : ℕ) + 1 : ℝ) - (4 / 3) / (G.degree v + 1 : ℝ) := by
    grind
  rw [this, sub_pos]
  refine div_lt_div_of_pos_left four_thirds_pos add_one_pos ?_
  simp only [add_lt_add_iff_right, Nat.cast_lt, tsub_lt_self_iff, zero_lt_one, and_true]
  exact Nat.zero_lt_of_lt hdv

lemma γC_pos_of_four_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hCv : ABC.C v) (hdv : 4 ≤ G.degree v) :
    0 < γ G ABC v := by
  simp only [γ, not_A_of_C, not_B_of_C, hCv, ↓reduceDIte]
  haveI : fC (G.degree v - 1) - fC (G.degree v)
      = (2 / 3) / ((G.degree v - 1 : ℕ) + 1 : ℝ) - (2 / 3) / (G.degree v + 1 : ℝ) := by
    grind
  rw [this, sub_pos]
  refine div_lt_div_of_pos_left two_thirds_pos add_one_pos ?_
  simp only [add_lt_add_iff_right, Nat.cast_lt, tsub_lt_self_iff, zero_lt_one, and_true]
  exact Nat.zero_lt_of_lt hdv

lemma γ_pos_of_four_le_deg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : v ∈ ABC) (hdv : 4 ≤ G.degree v) :
    0 < γ G ABC v := by
  rcases hv with hAv | hBv | hCv
  · exact γA_pos_of_four_le_deg hAv hdv
  · exact γB_pos_of_four_le_deg hBv hdv
  · exact γC_pos_of_four_le_deg hCv hdv

lemma γ_eq_0_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    {v : Fin n} (hv : v ∈ ABC) (hdv : 1 ≤ G.degree v) :
    γ G ABC v = 0 ↔
      ((G.degree v = 3 ∧ ABC.B v) ∨ (G.degree v = 3 ∧ ABC.C v) ∨ (G.degree v = 2 ∧ ABC.C v)) := by
  constructor
  · intro h
    if hdv' : 4 ≤ G.degree v then
      suffices 0 < (0 : ℝ) by exact (lt_self_iff_false _).mp this |>.elim
      exact lt_of_lt_of_eq (γ_pos_of_four_le_deg hv hdv') h
    else
      have hdv : G.degree v = 1 ∨ G.degree v = 2 ∨ G.degree v = 3 := by lia
      rcases hv with hAv | hBv | hCv <;> grind only [γA1, γA2, γA3, γB1, γB2, γC1]
  · intro h
    rcases h with ⟨hdv, hBv⟩ | ⟨hdv, hCv⟩ | ⟨hdv, hCv⟩
    · exact γB3 hBv hdv
    · exact γC3 hCv hdv
    · exact γC2 hCv hdv

lemma γ_eq_zero_of_deg_eq_zero {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hdv : G.degree v = 0) : γ G ABC v = 0 := by
  simp only [γ, fA, hdv, zero_tsub, ↓reduceIte, sub_self, fB, fC, dite_eq_ite, ite_self]

lemma if_γ_gt_one_over_six {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : v ∈ ABC) (hγ : 1 / 6 < γ G ABC v) :
    ABC.B v ∧ G.degree v = 2 ∨ ABC.C v ∧ G.degree v = 1 := by
  have hdv : G.degree v ≠ 0 := by
    intro hdv
    have h : γ G ABC v ≠ 0 := by linarith
    exact h <| γ_eq_zero_of_deg_eq_zero hdv
  have H : G.degree v = 1 ∨ G.degree v = 2 ∨ G.degree v = 3 ∨ 4 ≤ G.degree v := by
    grind
  rcases H with h | h | h | h
  · simp only [one_div, γ, fA, h, tsub_self, ↓reduceIte, one_ne_zero, fB, fC, OfNat.one_ne_ofNat,
      or_false, dite_eq_ite] at hγ
    rcases hv with hv | hv | hv <;> grind [not_A_of_B]
  · simp only [one_div, γ, fA, h, Nat.add_one_sub_one, one_ne_zero, ↓reduceIte,
      OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Nat.cast_ofNat, fB, fC, OfNat.one_ne_ofNat, or_false,
      or_true, sub_self, dite_eq_ite, ite_self] at hγ
    rcases hv with hv | hv | hv <;> grind [not_A_of_C, not_B_of_C]
  · simp only [one_div, γ, fA, h, Nat.add_one_sub_one, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, Nat.cast_ofNat, fB, Nat.succ_ne_self, fC, or_true, or_self,
    dite_eq_ite] at hγ
    rcases hv with hv | hv | hv <;> grind [not_A_of_C, not_B_of_C]
  · grind only [γ_le_1_10_of_4_le_degree h hv]

lemma ℓA1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 1) : ℓ G ABC v = 1 / 6 := by
  simp only [ℓ, hA, ↓reduceDIte, fA, hv, ↓reduceIte, one_ne_zero, one_div, Nat.reduceAdd,
    OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.cast_ofNat]
  linarith

lemma ℓA2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 2) : ℓ G ABC v = 1 / 6 := by
  simp only [ℓ, hA, ↓reduceDIte, fA, hv, Nat.reduceAdd, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, Nat.cast_ofNat]
  linarith

lemma ℓA3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hA : ABC.A v) (hv : G.degree v = 3) : ℓ G ABC v = 1 / 10 := by
  simp only [ℓ, hA, ↓reduceDIte, ↓reduceIte, fA, hv, Nat.reduceAdd, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, Nat.cast_ofNat]
  linarith

lemma ℓB1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 1) : ℓ G ABC v = 1 / 2 := by
  simp only [ℓ, not_A_of_B, hB, ↓reduceDIte, ↓reduceIte, one_div, one_ne_zero, fB, hv,
    Nat.reduceAdd, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
  linarith

lemma ℓB2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 2) : ℓ G ABC v = 0 := by
  simp only [ℓ, hB, not_A_of_B, ↓reduceDIte, fB, hv, ↓reduceIte, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, OfNat.ofNat_ne_one, Nat.reduceAdd, Nat.succ_ne_self, Nat.cast_ofNat]
  linarith

lemma ℓB3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hB : ABC.B v) (hv : G.degree v = 3) : ℓ G ABC v = 1 / 15 := by
  simp only [ℓ, hB, not_A_of_B, ↓reduceDIte, fB, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, Nat.succ_ne_self, Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceEqDiff]
  linarith

lemma ℓC1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 1) : ℓ G ABC v = 0 := by
  simp only [ℓ, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, one_ne_zero, ↓reduceIte,
    OfNat.one_ne_ofNat, or_false, one_div, Nat.reduceAdd, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    or_true, sub_self]

lemma ℓC2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 2) : ℓ G ABC v = 0 := by
  simp only [ℓ, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, or_true, one_div, Nat.reduceAdd, Nat.succ_ne_self, or_self, Nat.cast_ofNat]
  linarith

lemma ℓC3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n} {v : Fin n}
    (hC : ABC.C v) (hv : G.degree v = 3) : ℓ G ABC v = 1 / 30 := by
  simp only [ℓ, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, hv, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, Nat.succ_ne_self, or_self, Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceEqDiff]
  linarith

lemma ΔfA_decreasing {d d' : ℕ} (hdd' : d ≤ d') :
  (fA d' - fA (d' + 1)) ≤ (fA d - fA (d + 1)) := by
  simp only [fA, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_eq_right,
    Nat.cast_add, Nat.cast_one]
  have H {m : ℕ} (hm : 2 ≤ m) : 2 / ((m + 1 : ℝ) * (m + 1 + 1 : ℝ)) ≤ 1 / 6 := by
    calc _
      _ ≤ 2 / ((3 : ℝ) * (4 : ℝ)) := by
        refine div_le_div_iff₀ ?_ ?_ |>.mpr ?_
        · simp only [add_one_pos, mul_pos_iff_of_pos_left, add_one_add_one_pos]
        · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left]
        · simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
          refine mul_le_mul ?_ ?_ zero_le_four (le_of_lt add_one_pos)
          · rw [← Nat.cast_three, ← Nat.cast_one, ← Nat.cast_add]
            refine Nat.cast_le.mpr (by simp only [Nat.reduceLeDiff, hm])
          · rw [← Nat.cast_four, ← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add]
            refine Nat.cast_le.mpr (by simp only [Nat.reduceLeDiff, hm])
    linarith
  split_ifs
  any_goals grind [!Δf_eq]
  · rename_i hd' hd; rw [hd']
    linarith
  · rename_i hd; rw [Δf_eq, hd]
    refine le_trans (H (by lia)) (by linarith)
  · simp_rw [Δf_eq]
    refine (div_le_div_iff₀ ?_ ?_).mpr ?_
    · simp only [add_one_pos, mul_pos_iff_of_pos_left, add_one_add_one_pos]
    · simp only [add_one_pos, mul_pos_iff_of_pos_left, add_one_add_one_pos]
    · simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
      refine mul_le_mul ?_ ?_ ?_ ?_ <;> simp [hdd', le_of_lt]

lemma ℓ_le_1_over_10_of_3_le_degree {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (h : 3 ≤ G.degree v) :
    ℓ G ABC v ≤ 1 / 10 := by
  simp only [ℓ, fA, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_eq_right,
    Nat.cast_add, Nat.cast_one, fB, Nat.reduceEqDiff, fC, dite_eq_ite]
  have H : 4 * 5 ≤ (G.degree v + 1) * (G.degree v + 1 + 1) :=
    mul_le_mul (by lia) (by lia) (Nat.zero_le _) (Nat.zero_le _)
  have H' : 20 ≤ (G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ) := by
    rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_mul]
    exact Nat.cast_le.mpr H
  split_ifs
  any_goals grind only
  · rw [Δf_eq]
    calc 2 / ((G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ))
      _ ≤ 2 / 20 := div_le_div₀ zero_le_two (le_refl _) Nat.ofNat_pos' H'
      _ = 1 / 10 := by linarith only
  · rw [Δf_eq]
    calc (4 / 3) / ((G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ))
      _ ≤ (4 / 3) / 20 := div_le_div₀ (by grind) (le_refl _) Nat.ofNat_pos' H'
      _ ≤ 1 / 10 := by linarith only
  · rw [Δf_eq]
    calc (2 / 3) / ((G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ))
      _ ≤ (2 / 3) / 20 := div_le_div₀ (by grind) (le_refl _) Nat.ofNat_pos' H'
      _ ≤ 1 / 10 := by grind

lemma ℓ_le_1_over_15_of_4_le_degree {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (h : 4 ≤ G.degree v) :
    ℓ G ABC v ≤ 1 / 15 := by
  simp only [ℓ, fA, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_eq_right,
    Nat.cast_add, Nat.cast_one, fB, Nat.reduceEqDiff, fC, dite_eq_ite]
  have H : 5 * 6 ≤ (G.degree v + 1) * (G.degree v + 1 + 1) :=
    mul_le_mul (by lia) (by lia) (Nat.zero_le _) (Nat.zero_le _)
  have H' : 30 ≤ (G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ) := by
    rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_mul]
    exact Nat.cast_le.mpr H
  split_ifs
  any_goals grind only
  · rw [Δf_eq]
    calc 2 / ((G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ))
      _ ≤ 2 / 30 := div_le_div₀ zero_le_two (le_refl _) Nat.ofNat_pos' H'
      _ = 1 / 15 := by linarith only
  · rw [Δf_eq]
    calc (4 / 3) / ((G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ))
      _ ≤ (4 / 3) / 30 := div_le_div₀ (by linarith) (le_refl _) Nat.ofNat_pos' H'
      _ ≤ 1 / 15 := by linarith only
  · rw [Δf_eq]
    calc (2 / 3) / ((G.degree v + 1 : ℝ) * (G.degree v + 1 + 1 : ℝ))
      _ ≤ (2 / 3) / 30 := div_le_div₀ (by linarith) (le_refl _) Nat.ofNat_pos' H'
      _ ≤ 1 / 15 := by linarith only

namespace Tripartition

@[simp]
lemma demote_finset_from_A {n : ℕ} (ABC : Tripartition n) {v : Fin n} (hAv : ABC.A v)
    {s : Finset _} (hv : v ∈ s) : (ABC.demote_finset s).B v := by
  exact Or.inr ⟨hAv, hv⟩

@[simp]
lemma demote_finset_from_B {n : ℕ} (ABC : Tripartition n) {v : Fin n} (hBv : ABC.B v)
    {s : Finset _} (hv : v ∈ s) : (ABC.demote_finset s).C v := by
  exact Or.inr ⟨hBv, hv⟩

@[simp]
lemma demote_finset_from_C {n : ℕ} (ABC : Tripartition n) {v : Fin n} (hCv : ABC.C v)
    {s : Finset _} : (ABC.demote_finset s).C v := by
  exact Or.inl hCv

@[simp]
lemma demote_from_A {n : ℕ} (ABC : Tripartition n) {v : Fin n} (hAv : ABC.A v) :
    (ABC.demote v).B v := by
  exact demote_finset_from_A ABC hAv (mem_singleton.mpr rfl)

@[simp]
lemma demote_from_A' {n : ℕ} (ABC : Tripartition n) {v : Fin n} (hAv : ABC.A v) :
    ¬(ABC.demote v).A v := by
  exact not_A_of_B <| demote_from_A ABC hAv

@[simp]
lemma demote_from_B {n : ℕ} (ABC : Tripartition n) {v : Fin n} (hBv : ABC.B v) :
    (ABC.demote v).C v := by
  exact demote_finset_from_B _  hBv (mem_singleton.mpr rfl)

@[simp]
lemma demote_from_B' {n : ℕ} (ABC : Tripartition n) {v : Fin n} (hv : ABC.B v) :
    ¬(ABC.demote v).B v := by
  exact not_B_of_C <| demote_from_B ABC hv

@[simp]
lemma demote_from_C {n : ℕ} (ABC : Tripartition n) {v : Fin n} (hv : ABC.C v) :
    (ABC.demote v).C v := by
  exact Or.inl hv

@[simp]
lemma A_of_demote_finset_notin {n : ℕ} (ABC : Tripartition n) {v : Fin n} {s : Finset _}
    (hv : v ∉ s) : ABC.A v → (ABC.demote_finset s).A v := by
  exact fun hA ↦ ⟨hA, hv⟩

@[simp]
lemma B_of_demote_finset_notin {n : ℕ} (ABC : Tripartition n) {v : Fin n} {s : Finset _}
    (hv : v ∉ s) : ABC.B v → (ABC.demote_finset s).B v := by
  exact fun hB ↦ Or.inl ⟨hB, hv⟩

@[simp]
lemma C_of_demote_finset_notin {n : ℕ} (ABC : Tripartition n) {v : Fin n} {s : Finset _} :
    ABC.C v → (ABC.demote_finset s).C v := by
  exact fun hC ↦ Or.inl hC

@[simp]
lemma A_of_demote_ne {n : ℕ} (ABC : Tripartition n) {v w : Fin n} (h : v ≠ w) :
    ABC.A v → (ABC.demote w).A v := by
  exact fun hA ↦ ABC.A_of_demote_finset_notin (not_iff_not.mpr mem_singleton |>.mpr h) hA

@[simp]
lemma B_of_demote_ne {n : ℕ} (ABC : Tripartition n) {v w : Fin n} (h : v ≠ w) :
    ABC.B v → (ABC.demote w).B v := by
  exact fun hB ↦ ABC.B_of_demote_finset_notin (not_iff_not.mpr mem_singleton |>.mpr h) hB

@[simp]
lemma C_of_demote_ne {n : ℕ} (ABC : Tripartition n) {v w : Fin n} :
    ABC.C v → (ABC.demote w).C v := by
  exact fun hC ↦ ABC.C_of_demote_finset_notin hC

lemma mem_demote_of_mem {n : ℕ} (ABC : Tripartition n) {x y : Fin n} :
    x ∈ ABC → x ∈ ABC.demote y := by
  intro h
  if heq : x = y then
    rcases h with h | h | h
    · exact Tripartition.mem_iff _ |>.mpr <| Or.inr <| Or.inl <| Or.inr ⟨h, mem_singleton.mpr heq⟩
    · exact Tripartition.mem_iff _ |>.mpr <| Or.inr <| Or.inr <| Or.inr ⟨h, mem_singleton.mpr heq⟩
    · exact Tripartition.mem_iff _ |>.mpr <| Or.inr <| Or.inr <| Or.inl h
  else
    rcases h with h | h | h
    · exact Tripartition.mem_iff _ |>.mpr <| Or.inl <| ⟨h, not_iff_not.mpr mem_singleton |>.mpr heq⟩
    · exact Tripartition.mem_iff _ |>.mpr <| Or.inr <| Or.inl <| Or.inl
        <| ⟨h, not_iff_not.mpr mem_singleton |>.mpr heq⟩
    · exact Tripartition.mem_iff _ |>.mpr <| Or.inr <| Or.inr <| Or.inl h

lemma mem_of_mem_demote {n : ℕ} (ABC : Tripartition n) {x y : Fin n} :
    x ∈ ABC.demote y → x ∈ ABC := by
  intro h
  rcases h with h | h | h
  · simp only [mem_iff, h.1, true_or]
  · rcases h with h | h <;> simp only [mem_iff, h.1, true_or, or_true]
  · rcases h with h | h
    · simp only [mem_iff, h, or_true]
    · simp only [mem_iff, h.1, or_true, true_or]

lemma mem_demote_finset_of_mem {n : ℕ} (ABC : Tripartition n) {x : Fin n} {s : Finset _} :
    x ∈ ABC → x ∈ ABC.demote_finset s := by
  intro h
  if hin : x ∈ s then
    rcases h with h | h | h
    · exact Tripartition.mem_iff _ |>.mpr <| Or.inr <| Or.inl <| Or.inr ⟨h, hin⟩
    · exact Tripartition.mem_iff _ |>.mpr <| Or.inr <| Or.inr <| Or.inr ⟨h, hin⟩
    · exact Tripartition.mem_iff _ |>.mpr <| Or.inr <| Or.inr <| Or.inl h
  else
    rcases h with h | h | h
    · exact Tripartition.mem_iff _ |>.mpr <| Or.inl ⟨h, hin⟩
    · exact Tripartition.mem_iff _ |>.mpr <| Or.inr <| Or.inl <| Or.inl ⟨h, hin⟩
    · exact Tripartition.mem_iff _ |>.mpr <| Or.inr <| Or.inr <| Or.inl h

lemma mem_of_mem_demote_finset {n : ℕ} (ABC : Tripartition n) {x : Fin n} {s : Finset _} :
    x ∈ ABC.demote_finset s → x ∈ ABC := by
  intro h
  rcases h with h | h | h
  · simp only [mem_iff, h.1, true_or]
  · rcases h with h | h <;> simp only [mem_iff, h.1, true_or, or_true]
  · rcases h with h | h
    · simp only [mem_iff, h, or_true]
    · simp only [mem_iff, h.1, or_true, true_or]

@[simp]
lemma mem_iff_mem_demote {n : ℕ} (ABC : Tripartition n) {x y : Fin n} :
    x ∈ ABC ↔ x ∈ ABC.demote y :=
  ⟨ABC.mem_demote_of_mem, ABC.mem_of_mem_demote⟩

@[simp]
lemma mem_iff_mem_demote_tofinset {n : ℕ} (ABC : Tripartition n) {x : Fin n} {s : Finset _} :
    x ∈ ABC ↔ x ∈ ABC.demote_finset s :=
  ⟨ABC.mem_demote_finset_of_mem, ABC.mem_of_mem_demote_finset⟩

lemma promote_from_A {n : ℕ} (ABC : Tripartition n) (v : Fin n) (hv : ABC.A v) :
    (ABC.promote v).A v := by
  simp only [promote, hv, not_B_of_A, ↓reduceDIte, not_C_of_A]

lemma promote_from_B {n : ℕ} (ABC : Tripartition n) (v : Fin n) (hv : ABC.B v) :
    (ABC.promote v).A v := by
  simp only [promote, hv, ↓reduceDIte, promote_B, ne_eq, not_A_of_B, or_true]

lemma promote_from_B' {n : ℕ} (ABC : Tripartition n) (v : Fin n) (hv : ABC.B v) :
    ¬(ABC.promote v).B v := by
  exact not_B_of_A <| promote_from_B ABC v hv

lemma promote_from_C {n : ℕ} (ABC : Tripartition n) (v : Fin n) (hv : ABC.C v) :
    (ABC.promote v).B v := by
  simp only [promote, hv, not_B_of_C, ↓reduceDIte, promote_C, ne_eq, or_true]

lemma promote_from_C' {n : ℕ} (ABC : Tripartition n) (v : Fin n) (hv : ABC.C v) :
    ¬(ABC.promote v).C v := by
  exact not_C_of_B <| promote_from_C ABC v hv

@[simp]
lemma A_of_promote_ne {n : ℕ} (ABC : Tripartition n) {v w : Fin n} (h : v ≠ w) :
    ABC.A v → (ABC.promote w).A v := by
  intro hA
  simp only [promote, promote_B, promote_C]
  split_ifs <;> simp [h, hA, or_false]

@[simp]
lemma B_of_promote_ne {n : ℕ} (ABC : Tripartition n) {v w : Fin n} (h : v ≠ w) :
    ABC.B v → (ABC.promote w).B v := by
  intro hB
  simp only [promote, promote_B, promote_C]
  split_ifs <;> simp only [hB, ne_eq, h, not_false_eq_true, and_self, or_false]

@[simp]
lemma C_of_promote_ne {n : ℕ} (ABC : Tripartition n) {v w : Fin n} (h : v ≠ w) :
    ABC.C v → (ABC.promote w).C v := by
  intro hC
  simp only [promote, promote_B, promote_C]
  split_ifs <;> simp only [hC, ne_eq, h, not_false_eq_true, and_self]

lemma mem_promote_of_mem {n : ℕ} (ABC : Tripartition n) {x y : Fin n} :
    x ∈ ABC → x ∈ ABC.promote y := by
  grind [mem_iff, promote, promote_B, promote_C]

lemma mem_of_mem_promote {n : ℕ} (ABC : Tripartition n) {x y : Fin n} :
    x ∈ ABC.promote y → x ∈ ABC := by
  grind [mem_iff, promote, promote_B, promote_C]

lemma demote_toFinset_eq {n : ℕ} (ABC : Tripartition n) {x : Fin n} :
    ABC.toFinset = (ABC.demote x).toFinset := by
  ext y
  simp only [← coe_mem_toFinset]
  exact ⟨ABC.mem_demote_of_mem, ABC.mem_of_mem_demote⟩

lemma demote_finset_toFinset_eq {n : ℕ} (ABC : Tripartition n) {s : Finset (Fin n)} :
    ABC.toFinset = (ABC.demote_finset s).toFinset := by
  ext y
  simp only [← coe_mem_toFinset]
  refine ⟨?_, ?_⟩
  · exact ABC.mem_demote_finset_of_mem
  · exact ABC.mem_of_mem_demote_finset

lemma promote_toFinset_eq {n : ℕ} (ABC : Tripartition n) {x : Fin n} :
    ABC.toFinset = (ABC.promote x).toFinset := by
  ext y
  simp only [← coe_mem_toFinset]
  exact ⟨mem_promote_of_mem ABC, mem_of_mem_promote ABC⟩

@[simp]
lemma sdiff_empty {n : ℕ} (ABC : Tripartition n) : (ABC \ ∅) = ABC := by
  ext <;> simp only [sdiff, notMem_empty, not_false_eq_true, and_true]

lemma sdiff_eq {n : ℕ} (ABC : Tripartition n) (W : Finset (Fin n)) :
    (ABC \ W) = (ABC \ (W ∩ ABC.toFinset)) := by
  ext w <;> {
    simp only [sdiff, toFinset, mem_iff,
      mem_inter, mem_filter, mem_univ, true_and, not_and, not_or, and_congr_right_iff]
    intro H
    simp only [H, not_true_eq_false,
      not_A_of_B, not_A_of_C, not_B_of_A, not_B_of_C, not_C_of_A, not_C_of_B, not_false_eq_true,
      and_self, and_true, imp_false, and_false]
  }

@[simp]
lemma card_demote_finset_eq_card {n : ℕ} {ABC : Tripartition n} {s : Finset _} :
    ABC.card = (ABC.demote_finset s).card := by
  simp only [card]
  rw [demote_finset_toFinset_eq]

@[simp]
lemma card_demote_eq_card {n : ℕ} {ABC : Tripartition n} {x : Fin n} :
    ABC.card = (ABC.demote x).card := by
  simp only [card]
  rw [demote_toFinset_eq]

@[simp]
lemma card_promote_eq_card {n : ℕ} {ABC : Tripartition n} {x : Fin n} :
    ABC.card = (ABC.promote x).card := by
  simp only [card]
  rw [promote_toFinset_eq]

@[simp]
lemma sdiff_notMem {n : ℕ} (ABC : Tripartition n) (s : Finset (Fin n)) :
    ∀ x ∈ s, x ∉ ABC \ s := by
  intro x hx
  simp [sdiff, hx]

@[simp]
lemma sdiff_mem {n : ℕ} (ABC : Tripartition n) (s : Finset (Fin n)) :
    ∀ x ∈ ABC, x ∉ s → x ∈ ABC \ s := by
  intro x hx hxs
  simp only [mem_iff] at hx
  rcases hx with hx | hx | hx
  · exact (mem_iff _).mpr <| Or.inl ⟨hx, hxs⟩
  · exact (mem_iff _).mpr <| Or.inr <| Or.inl ⟨hx, hxs⟩
  · exact (mem_iff _).mpr <| Or.inr <| Or.inr ⟨hx, hxs⟩

@[simp]
lemma mem_sdiff_iff {n : ℕ} (ABC : Tripartition n) (s : Finset (Fin n)) {x : Fin n} :
    x ∈ ABC \ s ↔ (x ∈ ABC ∧ x ∉ s) := by
  refine ⟨?_, fun ⟨hx, hxs⟩ ↦ sdiff_mem ABC s x hx hxs⟩
  refine fun hx ↦ ⟨?_, fun this ↦ ABC.sdiff_notMem s _ this hx |>.elim⟩
  rcases (mem_iff _).mpr hx with h | h | h <;> simp only [mem_iff, h.1, or_true, or_false,
    not_A_of_B, not_A_of_C, not_B_of_A, not_B_of_C, not_C_of_A, not_C_of_B]

@[simp]
lemma toFinset_mono {n : ℕ} {ABC : Tripartition n} {s : Finset (Fin n)} :
    (ABC \ s).toFinset ⊆ ABC.toFinset := by
  simp only [toFinset, sdiff, mem_iff]
  intro x hx
  simp only [mem_iff, mem_filter, mem_univ, true_and] at hx ⊢
  rcases hx with hx | hx | hx <;> simp only [hx.1, true_or, or_true]

lemma sdiff_demote_finset_eq_demote_finset_sdiff {n : ℕ} {ABC : Tripartition n}
    {s s' : Finset (Fin n)} :
    (ABC \ s).demote_finset s' = ((ABC.demote_finset s') \ s) := by
  ext u
  · refine ⟨?_, ?_⟩ <;> exact fun ⟨⟨h₁, h₂⟩, h₃⟩ ↦ ⟨⟨h₁, h₃⟩, h₂⟩
  · refine ⟨?_, ?_⟩
    · intro h
      rcases h with h | h
      · exact ⟨Or.inl ⟨h.1.1, h.2⟩, h.1.2⟩
      · exact ⟨Or.inr ⟨h.1.1, h.2⟩, h.1.2⟩
    · intro ⟨h, hs⟩
      rcases h with ⟨h, h'⟩ | ⟨h, h'⟩
      · exact Or.inl ⟨⟨h, hs⟩, h'⟩
      · exact Or.inr ⟨⟨h, hs⟩, h'⟩
  · refine ⟨?_, ?_⟩
    · intro h
      rcases h with h | h
      · exact ⟨Or.inl h.1, h.2⟩
      · exact ⟨Or.inr ⟨h.1.1, h.2⟩, h.1.2⟩
    · intro ⟨h, hs⟩
      rcases h with h | h
      · exact Or.inl ⟨h, hs⟩
      · refine Or.inr ⟨⟨h.1, hs⟩, h.2⟩

@[simp]
lemma toFinset_eq {n : ℕ} {ABC : Tripartition n} {s : Finset (Fin n)} :
    (ABC \ s).toFinset = ABC.toFinset \ s := by
  ext w
  simp only [toFinset, sdiff, mem_iff, mem_filter, mem_univ, true_and, mem_sdiff]
  constructor
  · intro hw
    rcases hw with hw | hw | hw <;>
      simp only [hw, not_A_of_B, not_A_of_C, not_B_of_A, not_B_of_C, not_C_of_A, not_C_of_B,
        or_self, or_false, not_false_eq_true, and_self, or_true]
  · intro ⟨hx, hxs⟩
    rcases hx with hx | hx | hx <;>
      simp only [ not_A_of_B, not_A_of_C, not_B_of_A, not_B_of_C, not_C_of_A, not_C_of_B, hx, hxs,
        not_false_eq_true, and_self, and_true, or_self, or_false, or_true]

lemma sdiff_card {n : ℕ} (ABC : Tripartition n) {s : Finset (Fin n)}
    (hs : s ∩ ABC.toFinset ≠ ∅) : (ABC \ s).card < ABC.card := by
  simp only [card, toFinset, sdiff]
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro z hz
    simp only [mem_iff, mem_filter, mem_univ, true_and] at hz ⊢
    rcases hz with hz | hz | hz <;>
      simp only [hz.1, not_A_of_B, not_C_of_B, or_false, or_true, true_or]
  · intro this
    obtain ⟨z, hz⟩ := nonempty_def.mp <| nonempty_iff_ne_empty.mpr hs
    have hzABC : z ∈ ABC.toFinset := mem_of_mem_inter_right hz
    let hobj := this hzABC
    simp only [mem_iff, mem_filter, mem_univ, true_and] at hobj
    rcases hobj with ⟨_, h⟩ | ⟨⟨_, h⟩ | ⟨_, h⟩⟩ <;> exact h <| mem_of_mem_filter z hz

lemma sdiff_toFinset {n : ℕ} (ABC : Tripartition n) {s : Finset (Fin n)} :
    (ABC \ s).toFinset = ABC.toFinset \ s := by
  ext y
  simp only [toFinset, sdiff, mem_iff, mem_filter, mem_univ, true_and, mem_sdiff]
  constructor <;> simp only [or_and_right, imp_self]

lemma linear_forest_of_forest_respects {n : ℕ} (s : Finset (Fin n)) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ABC : Tripartition n) (hs : s ⊆ ABC.toFinset) :
    G.InducesForest s → respects s G ABC → G.InducesLinearForest s := by
  intro hf hresp
  refine ⟨hf, ?_⟩
  intro x hx
  obtain ⟨h₁, h₂, h₃⟩ := hresp x hx
  rw [degree_in] at h₁ h₂ h₃ ⊢
  rcases ABC.mem_iff.mp <| ABC.coe_mem_toFinset.mpr (hs hx) with hA | hB | hC
  · exact h₁ hA
  · exact le_trans (h₂ hB) one_le_two
  · exact le_of_eq_of_le (h₃ hC) zero_le_two

lemma respects_singleton {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} : respects {v} G ABC := by
  simp only [respects, mem_singleton, degree_in, card_eq_zero, forall_eq, mem_neighborFinset,
    SimpleGraph.irrefl, not_false_eq_true, inter_singleton_of_notMem, card_empty, zero_le,
    implies_true, and_self]

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
    rw [heq]
    obtain ⟨hs1, hs2, hs3⟩ := hs w hw
    refine ⟨?_, ?_, ?_⟩ <;> { intro _; grind only }
  · have heq : G.degree_in (s ∪ t) w = G.degree_in t w := by
      refine congrArg Finset.card ?_
      ext y
      simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff,
        or_iff_right_iff_imp]
      refine fun hwy hy ↦ hst' y hy w hw hwy.symm |>.elim
    rw [heq]
    obtain ⟨hs1, hs2, hs3⟩ := ht w hw
    refine ⟨?_, ?_, ?_⟩ <;> { intro _; grind only }

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
    rcases hobj with h | h | h <;> exact h.2
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

lemma f_le_56 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    {v : Fin n} (hv : 0 < G.degree v) : f G ABC v ≤ 5 / (6 : ℝ) := by
  simp only [f, fA, fB, one_div, fC, dite_eq_ite]
  split_ifs
  any_goals grind
  · calc 2 / (G.degree v + 1 : ℝ)
      _ ≤ 2 / (2 + 1 : ℝ) := by
        refine div_le_div_iff_of_pos_left two_pos add_one_pos (by lia) |>.mpr ?_
        simp only [add_le_add_iff_right, Nat.ofNat_le_cast]
        lia
      _ ≤ 5 / 6 := by linarith
  · calc (4 / 3) / (G.degree v + 1 : ℝ)
      _ ≤ (4 / 3) / (2 + 1 : ℝ) := by
        refine div_le_div_iff_of_pos_left (by linarith) add_one_pos (by lia) |>.mpr ?_
        simp only [add_le_add_iff_right, Nat.ofNat_le_cast]
        lia
      _ ≤ 5 / 6 := by linarith
  · calc (2 / 3) / (G.degree v + 1 : ℝ)
      _ ≤ (2 / 3) / (2 + 1 : ℝ) := by
        refine div_le_div_iff_of_pos_left (by linarith) add_one_pos (by lia) |>.mpr ?_
        simp only [add_le_add_iff_right, Nat.ofNat_le_cast]
        lia
      _ ≤ 5 / 6 := by linarith

lemma f_eq_in_sdiff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    {s : Finset (Fin n)} {w : Fin n} (hw : w ∉ s) :
    f G (ABC \ s) w = f G ABC w := by
  have : ABC.A w ↔ (ABC \ s).A w := ⟨fun h ↦ ⟨h, hw⟩, fun ⟨h, _⟩ ↦ h⟩
  have : ABC.B w ↔ (ABC \ s).B w := ⟨fun h ↦ ⟨h, hw⟩, fun ⟨h, _⟩ ↦ h⟩
  have : ABC.C w ↔ (ABC \ s).C w := ⟨fun h ↦ ⟨h, hw⟩, fun ⟨h, _⟩ ↦ h⟩
  simp only [f]
  split_ifs
  any_goals lia

lemma f_mono_degree {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n))
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (ABC : Tripartition n)
    {v : Fin n} : G₁.degree v = G₂.degree v → f G₁ ABC v = f G₂ ABC v := by
  intro heq
  simp only [f, fA, fB, one_div, fC, dite_eq_ite, heq]

lemma f_pos_of_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ABC : Tripartition n)
    (v : Fin n) : v ∈ ABC → 0 < f G ABC v := by
  intro h
  rcases ABC.mem_iff.mp h with hA | hB | hC
  · simp only [f, hA, ↓reduceDIte, fA]
    split_ifs
    any_goals linarith
    ring_nf
    simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_right, inv_pos, one_add_pos]
  · simp only [f, hB, not_A_of_B, ↓reduceDIte, fB, one_div]
    split_ifs
    any_goals linarith
    ring_nf
    simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_pos_iff_of_pos_right, inv_pos,
      one_add_pos]
  · simp only [f, hC, not_A_of_C, ↓reduceDIte, not_B_of_C, fC, one_div]
    split_ifs
    any_goals linarith
    ring_nf
    simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_pos_iff_of_pos_right, inv_pos,
      one_add_pos]

lemma f_mono {n : ℕ} {G₁ G₂ : SimpleGraph (Fin n)} [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    {ABC : Tripartition n} {v : Fin n} (hle : G₂ ≤ G₁) :
    f G₁ ABC v ≤ f G₂ ABC v := by
  if hv : v ∈ ABC then
    rcases ABC.mem_iff.mp hv with hA | hB | hC
    · simp only [f, hA, ↓reduceDIte]
      refine fA_decreasing <| degree_le_of_le hle
    · simp only [f, not_A_of_B, hB, ↓reduceDIte]
      refine fB_decreasing <| degree_le_of_le hle
    · simp only [f, not_A_of_C, not_B_of_C, hC, ↓reduceDIte]
      refine fC_decreasing <| degree_le_of_le hle
  else
    rw [← f_eq_zero_of_notMem G₁ hv, ← f_eq_zero_of_notMem G₂ hv]

@[simp, grind! .]
lemma γ_nonneg {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    {v : Fin n} : 0 ≤ γ G ABC v := by
  have h : G.degree v - 1 ≤ G.degree v := Nat.sub_le ..
  simp only [γ, dite_eq_ite]
  split_ifs <;> simp only [sub_nonneg, fA_decreasing h, fB_decreasing h, fC_decreasing h, le_refl]

lemma f_eq_sdiff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    {s : Finset (Fin n)} {v : Fin n} (hv : v ∉ s) :
    f G ABC v = f G (ABC \ s) v := by
  if hvABC : v ∈ ABC then
    rcases hvABC with hA | hB | hC
    · have hA' : (ABC \ s).A v := ⟨hA, hv⟩
      simp only [f, hA, hA', ↓reduceDIte]
    · have hB' : (ABC \ s).B v := ⟨hB, hv⟩
      simp only [f, hB, hB', not_A_of_B, ↓reduceDIte]
    · have hC' : (ABC \ s).C v := ⟨hC, hv⟩
      simp only [f, hC, hC', not_A_of_C, not_B_of_C, ↓reduceDIte]
  else
    have hvABC' : v ∉ (ABC \ s) := by
      simp only [Tripartition.mem_iff, not_or] at hvABC
      simp only [Tripartition.sdiff, Tripartition.mem_iff, hvABC, hv, not_false_eq_true, and_true,
        or_self]
    rw [← f_eq_zero_of_notMem G hvABC, ← f_eq_zero_of_notMem G hvABC']

private lemma eval_mono {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n)) (hle : G₁ ≤ G₂)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (ABC : Tripartition n) :
    eval G₂ ABC ≤ eval G₁ ABC := by
  unfold eval
  refine sum_le_sum ?_
  intro w hw
  simp only [Tripartition.toFinset, Tripartition.mem_iff, mem_filter, mem_univ, true_and] at hw
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
      lia
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
          refine sum_nonneg' <| fun v ↦ ?_
          if hv : v ∈ ABC then
            exact le_of_lt <| f_pos_of_mem G ABC v hv
          else
            exact le_of_eq <| f_eq_zero_of_notMem G hv
        _ = ∑ v ∈ (W ∩ ABC.toFinset), f G ABC v := sum_inter_add_sum_diff ..
    _ = ∑ v ∈ ABC.toFinset, f G ABC v := by
      have _ {s t : Finset (Fin n)} : s ∩ t = t ∩ s := inter_comm s t
      have h' : (ABC \ W).toFinset = ABC.toFinset \ W := by
        ext
        simp only [Tripartition.toFinset, Tripartition.sdiff, Tripartition.mem_iff,
          mem_filter, mem_univ, true_and, mem_sdiff, and_or_3]
      rw [add_comm, inter_comm, h']
      exact Finset.sum_inter_add_sum_diff ..

lemma degree_deleteIncidencesOf_neighbor {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {w : Fin n} {s : Finset (Fin n)} (hs : s ⊆ G.neighborFinset w) :
    G.degree w = (G.deleteIncidencesOf s).degree w + #s := by
  suffices G.neighborFinset w = (G.deleteIncidencesOf s).neighborFinset w ∪ s by
    simp only [degree, congrArg card this]
    refine card_union_of_disjoint ?_
    refine disjoint_iff_inter_eq_empty.mpr ?_
    ext u
    simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_inter, mem_neighborFinset,
      inf_adj, iInf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and,
      not_or, ne_eq, notMem_empty, iff_false, and_imp]
    intro hwu h hne hus
    exact (h u |>.1 hus |>.2 hwu |>.2) rfl
  ext u
  simp only [mem_neighborFinset, deleteIncidencesOf, deleteIncidenceSet, incidenceSet, mem_union,
    inf_adj, iInf_adj, deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and,
    not_or, ne_eq]
  constructor
  · intro h
    simp only [h, forall_const, true_and, h.ne, not_false_eq_true, and_true]
    if hus : u ∈ s then
      exact Or.inr hus
    else
      refine Or.inl ?_
      intro i hi
      refine ⟨?_, ?_⟩
      · have hws : w ∉ s := hs.mt <| notMem_neighborFinset_self G _
        exact fun heq ↦ hws (heq ▸ hi)
      · exact fun heq ↦ hus (heq ▸ hi)
  · intro h
    rcases h with h | h
    · exact h.1
    · exact G.mem_neighborFinset .. |>.mp <| hs h

lemma degree_deleteIncidencesOf_neighbor_singleton {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {v w : Fin n} (hw : G.Adj v w) :
    G.degree w = (G.deleteIncidencesOf {v}).degree w + 1 := by
  rw [← card_singleton v]
  refine degree_deleteIncidencesOf_neighbor G ?_
  simp only [singleton_subset_iff, mem_neighborFinset, hw.symm]

lemma f_deleteIncidencesOf_singleton {n : ℕ} (ABC : Tripartition n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {v w : Fin n} (hw : G.Adj v w) :
    f (G.deleteIncidencesOf {v}) (ABC \ {v}) w = f G ABC w + γ G ABC w := by
  simp only [f, Tripartition.sdiff_eq, inter_assoc, inter_self, fA, fB, one_div, fC, dite_eq_ite, γ,
    Nat.pred_eq_succ_iff, zero_add, Nat.reduceAdd]
  rw [degree_deleteIncidencesOf_neighbor_singleton G hw]
  simp only [Tripartition.sdiff, mem_singleton, hw.ne', not_false_eq_true, and_true,
    Tripartition.sdiff.eq_1, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_eq_right, Nat.cast_add, Nat.cast_one, Nat.reduceEqDiff, add_tsub_cancel_right]
  if hA : (ABC \ {v}).A w then
    simp only [hA.left, mem_singleton, hw.ne', not_false_eq_true, and_self, ↓reduceIte,
      add_sub_cancel]
  else if hB : (ABC \ {v}).B w then
    simp only [hB.left, not_A_of_B, mem_singleton, hw.ne', not_false_eq_true, and_true, ↓reduceIte,
      and_self, add_sub_cancel]
  else if hC : (ABC \ {v}).C w then
    simp only [hC.left, not_A_of_C, mem_singleton, hw.ne', not_false_eq_true, and_true, ↓reduceIte,
      not_B_of_C, and_self, add_sub_cancel]
  else
    have hA' : ¬ABC.A w := fun this ↦ hA
      <| by simp only [Tripartition.sdiff, mem_singleton, this, hw.ne', not_false_eq_true, and_self]
    have hB' : ¬ABC.B w := fun this ↦ hB
      <| by simp only [Tripartition.sdiff, mem_singleton, this, hw.ne', not_false_eq_true, and_self]
    have hC' : ¬ABC.C w := fun this ↦ hC
      <| by simp only [Tripartition.sdiff, mem_singleton, this, hw.ne', not_false_eq_true, and_self]
    simp only [mem_singleton, false_and, ↓reduceIte, add_zero, hA', hB', hC']

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

lemma hsupp_mono {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset)
    {W : Finset _} : (G.deleteIncidencesOf W).support.toFinset ⊆ (ABC \ W).toFinset := by
  intro u hu
  simp only [support, Set.mem_toFinset, SetRel.mem_dom, Set.mem_setOf_eq] at hu
  obtain ⟨v, hv⟩ := hu
  simp only [ABC.sdiff_toFinset]
  simp only [deleteIncidencesOf, deleteIncidenceSet, incidenceSet, inf_adj, iInf_adj,
    deleteEdges_adj, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, not_and, not_or, ne_eq] at hv
  obtain ⟨huv, h, _⟩ := hv
  refine mem_sdiff.mpr ⟨?_, ?_⟩
  · exact hG <| Set.mem_toFinset.mpr <| G.mem_support.mpr ⟨v, huv⟩
  · exact fun hu ↦ false_of_ne <| h u |>.1 hu |>.2 huv |>.1

lemma one_le_deg_of_vstar {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : IsVstar G ABC v) :
    1 ≤ G.degree v := by
  by_contra
  simp only [not_le, Nat.lt_one_iff] at this
  let hγv := hv.1.2
  have hdv' : G.degree v - 1 = G.degree v := Nat.sub_one_eq_self.mpr this
  simp only [γ, hdv', sub_self, dite_eq_ite, ite_self, ne_eq, not_true_eq_false] at hγv

lemma mem_ABC_of_vstar {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : IsVstar G ABC v) : v ∈ ABC :=
  ABC.coe_mem_toFinset.mpr hv.1.1

lemma γ_ne_zero_of_vstar {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : IsVstar G ABC v) : γ G ABC v ≠ 0 :=
  hv.1.2

lemma γ_vstar_le_γ {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {u v : Fin n} (hv : IsVstar G ABC v) (hu : u ∈ ABC)
    (hγu : γ G ABC u ≠ 0) : γ G ABC v ≤ γ G ABC u := by
  if hkey : key G ABC v ≤ key G ABC u then
    exact Prod.Lex.monotone_fst _ _ hkey
  else
    simp only [not_le] at hkey
    exact Prod.Lex.monotone_fst _ _ <| hv.2 ⟨ABC.coe_mem_toFinset.mp hu, hγu⟩ (le_of_lt hkey)

lemma ne_B3_of_vstar {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : IsVstar G ABC v) :
    ¬(ABC.B v ∧ G.degree v = 3) :=
  fun h ↦ γ_ne_zero_of_vstar hv
    <| γ_eq_0_iff (mem_ABC_of_vstar hv) (one_le_deg_of_vstar hv) |>.mpr <| Or.inl h.symm

lemma ne_C3_of_vstar {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ABC : Tripartition n} {v : Fin n} (hv : IsVstar G ABC v) :
    ¬(ABC.C v ∧ G.degree v = 3) :=
  fun h ↦ γ_ne_zero_of_vstar hv
    <| γ_eq_0_iff (mem_ABC_of_vstar hv) (one_le_deg_of_vstar hv) |>.mpr <| Or.inr <| Or.inl h.symm

end ABC
end CaroWeiType
