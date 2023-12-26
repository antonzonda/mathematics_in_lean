import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  match le_or_gt 0 x with
    | Or.inl h =>
      rw [abs_eq_self.mpr]
      exact h
    | Or.inr h =>
      have h₁ : x ≤ 0 := by linarith
      rw [abs_eq_neg_self.mpr]
      linarith
      exact h₁

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rw [← abs_neg]
  apply le_abs_self (-x)


theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor
  · apply neg_le_of_neg_le
    rw [neg_add]
    apply add_le_add (neg_le_abs_self x) (neg_le_abs_self y)
  apply add_le_add (le_abs_self x) (le_abs_self y)

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_eq_self.mpr h]
      intro h'; left; exact h'
    | Or.inr h =>
      have h₁ : y ≤ 0 := by linarith
      rw [abs_eq_neg_self.mpr h₁]
      intro h'; right; exact h'

  match le_or_gt 0 y with
  | Or.inl h =>
    rw [abs_eq_self.mpr h]
    intro h'
    match h' with
    | Or.inl g =>
      exact g
    | Or.inr g =>
      apply (@lt_of_le_of_lt' _ _ x (-y) y)
      apply neg_le_self; exact h
      exact g
  | Or.inr h =>
    intro h'
    have h₀ : y ≤ 0 := by linarith
    rw [abs_eq_neg_self.mpr h₀]
    rcases h' with h₁ | h₂
    apply (@lt_of_le_of_lt' _ _ x y)
    apply Left.self_le_neg; exact h₀
    exact h₁
    exact h₂


theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · match le_or_gt 0 x with
    | Or.inl h =>
      rw [abs_eq_self.mpr h]
      intro h'
      constructor
      linarith
      apply h'
    | Or.inr h =>
      have h₁ : x ≤ 0 := by linarith
      rw [abs_eq_neg_self.mpr h₁]
      intro h''
      constructor
      linarith
      linarith

  intro h0
  match le_or_gt 0 x with
  | Or.inl h =>
    rw [abs_eq_self.mpr h]
    linarith
  | Or.inr h =>
    have h₁ : x ≤ 0 := by linarith
    rw [abs_eq_neg_self.mpr h₁]
    linarith



end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, zxy | zxy1⟩
  · rw [zxy]
    have h := add_le_add (pow_two_nonneg x) (pow_two_nonneg y)
    linarith
  · have h := add_le_add (pow_two_nonneg x) (pow_two_nonneg y)
    rw [zxy1]
    linarith

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : (x + 1) * (x - 1) = 0 := by linarith
  have h'' : x + 1 = 0 ∨ x - 1 = 0 := mul_eq_zero.mp h'
  rcases h'' with h₁ | h₂
  · right; linarith
  · left; linarith


example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x + y) * (x - y) = 0 := by linarith
  have h'' : x + y = 0 ∨ x - y = 0 := mul_eq_zero.mp h'
  rcases h'' with h₁ | h₂
  · right; linarith
  · left; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : (x + 1) * (x - 1) = 0 := by
    rw [add_mul, mul_sub, mul_sub, mul_one, mul_one, one_mul]
    rw [add_sub_assoc', add_comm_sub, add_sub_assoc', add_sub_cancel]
    rw [← sq, sub_eq_zero]
    exact h

  have h'' : x + 1 = 0 ∨ x - 1 = 0 := mul_eq_zero.mp h'
  rcases h'' with h₁ | h₂
  · right; rw [← sub_neg_eq_add] at h₁; apply sub_eq_zero.mp h₁
  · left; apply sub_eq_zero.mp h₂

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x + y) * (x - y) = 0 := by
    rw [add_mul, mul_sub, mul_sub, ]
    rw [add_sub_assoc', add_comm_sub, mul_comm x y, sub_self, add_zero]
    rw [← sq, ← sq, sub_eq_zero]
    exact h

  have h'' : x + y = 0 ∨ x - y = 0 := mul_eq_zero.mp h'
  rcases h'' with h₁ | h₂
  · right; rw [← sub_neg_eq_add] at h₁; apply sub_eq_zero.mp h₁
  · left; apply sub_eq_zero.mp h₂

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro h
  by_cases h' : P
  · right; apply h h'
  · left; exact h'

  intro h₁ h₂
  rcases h₁ with g₁ | g₂
  · contradiction
  · assumption
