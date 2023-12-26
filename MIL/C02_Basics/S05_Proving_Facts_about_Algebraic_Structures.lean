import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    apply inf_le_right
    apply inf_le_left

theorem inf_le_left_left : x ⊓ y ⊓ z ≤ x := by
  calc
    x ⊓ y ⊓ z ≤ x ⊓ y := by
      apply inf_le_left
    _ ≤ x := by
      apply inf_le_left

theorem inf_le_left_mid : x ⊓ y ⊓ z ≤ y := by
  calc
    x ⊓ y ⊓ z ≤ x ⊓ y := by
      apply inf_le_left
    _ ≤ y := by
      apply inf_le_right

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    apply inf_le_left_left
    apply le_inf
    apply inf_le_left_mid
    apply inf_le_right
  rw [inf_comm]
  apply le_inf
  · apply le_inf
    apply inf_le_right
    apply inf_le_left_left
  apply inf_le_left_mid

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    apply sup_le
    apply le_sup_left
    apply (le_trans (@le_sup_left _ _ y z))
    apply le_sup_right
    apply (le_trans (@le_sup_right _ _ y z))
    apply le_sup_right
  apply sup_le
  apply (le_trans  (@le_sup_left _ _ x y))
  apply le_sup_left
  apply sup_le
  apply (le_trans (@le_sup_right _ _ x y))
  apply le_sup_left
  apply le_sup_right




theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  apply le_inf
  · apply le_refl
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    apply le_refl
    apply inf_le_left
  apply le_sup_left
end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h (a ⊔ b) a c, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b)]
  rw [h c a b, ← @sup_assoc _ _ a (c ⊓ a), @inf_comm _ _ c a, absorb2]
  rw [inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h (a ⊓ b), @sup_comm _ _ (a ⊓ b), absorb2, @sup_comm _ _ (a ⊓ b)]
  rw [h, ← @inf_assoc _ _ a, @sup_comm _ _ c a, absorb1, sup_comm]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

theorem fact1 (h : a ≤ b) : 0 ≤ b - a := by
  have h₁ := add_le_add_left h (-a)
  rw [add_left_neg, add_comm, ← sub_eq_add_neg] at h₁
  exact h₁

theorem fact2 (h: 0 ≤ b - a) : a ≤ b := by
  have h₁ := add_le_add_left h a
  rw [add_zero, sub_eq_add_neg, ← add_assoc, add_comm a b, add_assoc, add_right_neg, add_zero] at h₁
  exact h₁

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h₁ := fact1 a b h
  have h₂ := mul_nonneg h₁ h'
  rw [sub_mul] at h₂
  apply fact2
  exact h₂

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h₀ := dist_triangle x y x
  rw [dist_self, dist_comm y x] at h₀
  linarith

end
