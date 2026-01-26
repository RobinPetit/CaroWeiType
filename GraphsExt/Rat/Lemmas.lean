import Mathlib.Tactic

import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.Init

open Rat

@[simp]
lemma Rat_eq_one_iff_num_eq_den {q : ℚ} : q = 1 ↔ q.num = q.den := by
  constructor
  · intro q_eq_1
    refine Int.le_antisymm_iff.mpr ?_
    simp_all only [le_refl, num_ofNat, den_ofNat, Nat.cast_one, and_self]
  · intro num_eq_den
    have den_eq_1 : q.den = 1 := by
      refine @Eq.trans ℕ q.den (gcd q.num.natAbs q.den) 1 ?_ ?_
      · simp only [Int.natAbs_natCast, gcd_same, _root_.normalize_eq, num_eq_den, Eq.symm]
      · exact q.reduced
    have num_eq_1 : q.num = 1 := by simp only [Nat.cast_one, num_eq_den, den_eq_1]
    have goal : q = q.num /. q.den := Eq.symm (num_divInt_den q)
    rw [num_eq_1, den_eq_1] at goal
    exact goal

@[simp]
lemma divint_iff {a b : ℤ} {h₁ : b ≠ 0} {h₂ : a ≠ 0} : (divInt a b).inv = divInt b a := by
  let q₁ : ℚ := divInt a b
  let n₁ : ℤ := q₁.num
  let d₁ : ℤ := q₁.den
  obtain ⟨c₁, ⟨prop_num₁, prop_den₁⟩⟩ := @num_den_mk q₁ a b h₁ rfl
  have c₁_ne_0 : c₁ ≠ 0 := by
    rw [prop_num₁] at h₂
    exact (mul_ne_zero_iff.mp h₂).left
  let q₂ : ℚ := divInt b a
  have prod_eq_1 : q₁ * q₂ = 1 := by
    let n₂ : ℤ := q₂.num
    let d₂ : ℤ := q₂.den
    obtain ⟨c₂, ⟨prop_num₂, prop_den₂⟩⟩ := @num_den_mk q₂ b a h₂ rfl
    have obj : (c₁ * c₂) * ((q₁ * q₂).num * d₁ * d₂) = (c₁ * c₂) * (n₁ * n₂ * (q₁ * q₂).den) :=
      congrArg (fun x : ℤ => c₁ * c₂ * x) (mul_num_den' q₁ q₂)
    have obj : a * b * (q₁ * q₂).num = a * b * (q₁ * q₂).den := by
      grind only
    have ab_ne_0 : a*b ≠ 0 := by exact Int.mul_ne_zero h₂ h₁
    have obj : (q₁ * q₂).num = (q₁ * q₂).den := by
      exact (@Int.mul_eq_mul_left_iff (q₁ * q₂).num (q₁ * q₂).den (a*b) ab_ne_0).mp obj
    exact Rat_eq_one_iff_num_eq_den.mpr obj
  let q_inv : ℚ := q₁.inv
  have prod'_eq_1 : q₁ * q_inv = 1 := by
    rw [mul_comm]
    have h : q₁ ≠ 0 := by exact (divInt_ne_zero h₁).mpr h₂
    exact Rat.inv_mul_cancel q₁ h
  exact inv_unique prod'_eq_1 prod_eq_1

@[simp, grind! .]
lemma rat_inv_num_den_eq {n : ℤ} (hn : n > 0) : (1 /. n).num = 1 ∧ (1 /. n).den = n.toNat := by
  let inv : ℚ := 1 /. n
  have n_ne_0 : n ≠ 0 := Ne.symm (Int.ne_of_lt hn)
  obtain ⟨k, ⟨prop_num, prop_den⟩⟩ := @num_den_mk inv 1 n n_ne_0 rfl
  let a : ℤ := 1
  let b : ℤ := n
  let c : ℤ := inv.num
  let d : ℤ := inv.den
  have b_gt_0 : b > 0 := hn
  have d_gt_0 : d > 0 :=
    lt_iff_le_and_ne'.mpr ⟨Int.natCast_nonneg inv.den, Int.ofNat_ne_zero.mpr inv.den_nz⟩
  have h : (a : ℚ) / b = (c : ℚ) / d := by
    simp only [Int.cast_one, Int.cast_natCast, one_div, num_div_den, a, b, c, d]
    rw [intCast_eq_divInt n]
    apply @divint_iff n 1 Int.one_ne_zero n_ne_0
  obtain ⟨a_eq_c, b_eq_d⟩ := Rat.div_int_inj b_gt_0 d_gt_0 (Int.gcd_one_left n) inv.reduced h
  constructor
  · exact Eq.symm a_eq_c
  · have d_eq_b := Eq.symm b_eq_d
    simp only [d, b] at d_eq_b
    have n_nonneg : n ≥ 0 := by exact Int.le_of_lt hn
    rw [←@Int.toNat_of_nonneg n n_nonneg] at d_eq_b
    exact Int.ofNat_inj.mp d_eq_b

@[simp, grind! .]
lemma rat_divInt_num_den_eq {a b c : ℕ} {h : a ≠ 0} : ((a * b) /. (a * c)) = (b /. c) := by
  exact divInt_mul_left <| Int.ofNat_ne_zero.mpr h
