import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

theorem min_eq : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left


example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    apply le_min
    calc
      min (min a b) c ≤ min a b := by
        apply min_le_left
      _ ≤ a := by
        apply min_le_left
    apply le_min
    calc
      min (min a b) c ≤ min a b := by
        apply min_le_left
      _ ≤ b := by
        apply min_le_right
    apply min_le_right
  · show min a (min b c) ≤ min (min a b) c
    apply le_min
    · apply le_min
      apply min_le_left
      calc
        min a (min b c) ≤ min b c := by
          apply min_le_right
        _ ≤ b := by
          apply min_le_left
    calc
      min a (min b c) ≤ min b c := by
        apply min_le_right
      _ ≤ c := by
        apply min_le_right


theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  have h : ∀ x y z: ℝ, min x y + z ≤ x + z := by
    intro x y z
    apply add_le_add_right (min_le_left x y) z

  apply le_min
  · apply h
  rw [min_eq]
  apply h


example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  apply aux
  have h : ∀ x y z : ℝ, min (x + z) (y + z) + -z ≤ x := by
    intro x y z
    nth_rewrite 2 [← add_neg_cancel_right  x z]
    apply add_le_add_right (min_le_left (x + z) (y + z)) (-z)
  have h₁ : min (a + c) (b + c) + -c ≤ min a b := by
    apply le_min
    · apply h
    rw [min_eq]
    apply h
  -- rw [← add_zero (min (a+c) (b+c)), ← add_left_neg c, ← add_assoc]
  -- have h₂ := add_le_add_right h₁ c
  linarith

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h := abs_add (a - b) b
  rw [sub_add_cancel] at h
  linarith

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
   apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  apply dvd_add
  · apply dvd_mul_of_dvd_right
    apply dvd_mul_right
  apply dvd_mul_left
  apply dvd_pow
  exact h
  exact Nat.succ_ne_zero 1

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  have h : ∀ x y : ℕ, Nat.gcd x y ∣ Nat.gcd y x := by
    intro x y
    have h₁ := Nat.gcd_dvd_left x y
    have h₂ := Nat.gcd_dvd_right x y
    apply Nat.dvd_gcd h₂ h₁

  apply Nat.dvd_antisymm
  apply h
  apply h

end
