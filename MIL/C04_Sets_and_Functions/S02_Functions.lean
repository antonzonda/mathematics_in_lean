import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    have g₀ : f x ∈ f '' s
    · use x
    have g : f x ∈ v
    · apply h
      apply g₀
    simp
    exact g
  · intro h
    simp
    exact h


example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x g
  simp at g
  rcases g with ⟨x₁, h₁⟩
  rcases h₁ with ⟨h₂, h₃⟩
  have g₁ : x = x₁
  · apply h
    rw [h₃]
  rw [g₁]
  exact h₂

example : f '' (f ⁻¹' u) ⊆ u := by
  intro x g
  simp at g
  rcases g with ⟨x₁, ⟨h₁, h₂⟩⟩
  rw [h₂] at h₁
  exact h₁

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x g
  simp
  have g₁ := h x
  rcases g₁ with ⟨y, H⟩
  exists y
  constructor
  · rw [H]
    exact g
  · exact H

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x g
  simp
  simp at g
  rcases g with ⟨x₁, ⟨g₁, g₂⟩⟩
  have g₁ : x₁ ∈ t
  · apply h
    apply g₁
  exists x₁


example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x g
  simp
  simp at g
  apply h
  exact g

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  simp

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x g
  simp at g
  rcases g with ⟨y, ⟨⟨g₀, g₂⟩, g₁⟩⟩
  simp
  constructor
  · exists y
  · exists y

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x g
  simp
  simp at g
  rcases g with ⟨⟨y₀, ⟨g₀₀, g₀₁⟩⟩, ⟨y₁, ⟨g₁₀, g₁₁⟩⟩⟩
  have yeq : y₀ = y₁
  . apply h
    rw [g₀₁, g₁₁]
  exists y₀
  constructor
  · constructor
    exact g₀₀
    rw [yeq]
    exact g₁₀
  · exact g₀₁

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x g
  simp at g
  rcases g with ⟨⟨y, ⟨g₀₀, g₀₁⟩ ⟩, g₁⟩
  simp
  exists y
  constructor
  · constructor
    · exact g₀₀
    · intro c
      have contra := g₁ y c g₀₁
      exact contra
  · exact g₀₁


example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x g
  simp at g
  simp
  rcases g with ⟨g₁, g₂⟩
  constructor
  · exact g₁
  · exact g₂

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  apply Subset.antisymm
  · intro x g
    simp at g
    rcases g with ⟨⟨y, ⟨g₁, g₂⟩⟩, g₃⟩
    simp
    exists y
    constructor
    · constructor
      exact g₁
      rw [g₂]
      exact g₃
    · exact g₂
  · intro x g
    simp at g
    rcases g with ⟨y, ⟨⟨g₁, g₂⟩, g₃⟩⟩
    simp
    constructor
    · exists y
    · rw [g₃] at g₂
      exact g₂

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro x g
  simp at g
  rcases g with ⟨y, ⟨⟨g₁, g₂⟩, g₃⟩⟩
  simp
  constructor
  · exists y
  · rewrite [g₃] at g₂
    exact g₂

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x g
  simp at g
  rcases g with ⟨g₁, g₂⟩
  simp
  constructor
  · exists x
  · exact g₂

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x g
  simp at g
  rcases g with h | h
  · simp
    left
    exists x
  · simp
    right
    exact h

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
  rintro ⟨i, x, xAi, fxeq⟩
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y; simp
  intro x h fxeq i
  use x
  exact ⟨h i, fxeq⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y; simp
  intro h
  rcases h i with ⟨x, _, fxeq⟩
  use x; constructor
  · intro i'
    rcases h i' with ⟨x', x'Ai, fx'eq⟩
    have : f x = f x' := by rw [fxeq, fx'eq]
    have : x = x' := injf this
    rw [this]
    exact x'Ai
  exact fxeq

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x H₁ y H₂ e
  calc
    x =  (sqrt x) ^ 2 := by
      rw [sq_sqrt]
      simp at H₁
      exact H₁
    _ = (sqrt y) ^ 2 := by
      rw [e]
    _ = y := by
      rw [sq_sqrt]
      simp at H₂
      exact H₂

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x H₁ y H₂ e
  simp at e
  calc
    x = sqrt (x ^ 2) := by
      rw [sqrt_sq]
      simp at H₁
      exact H₁
    _ = sqrt (y ^ 2) := by rw [e]
    _ = y := by
      rw [sqrt_sq]
      simp at H₂
      exact H₂

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  apply Subset.antisymm
  · intro x g
    simp at g
    rcases g with ⟨z, ⟨_, g₂⟩⟩
    simp
    rw [← g₂]
    apply sqrt_nonneg
  · intro x g
    simp at g
    simp
    exists (x ^ 2)
    constructor
    · apply pow_two_nonneg
    · rw [sqrt_sq]
      exact g

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  apply Subset.antisymm
  · intro x g
    simp at g
    rcases g with ⟨y, H⟩
    simp
    rewrite [← H]
    apply pow_two_nonneg
  · intro x g
    simp at g
    simp
    exists (sqrt x)
    rw [sq_sqrt]
    exact g

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro g
    unfold LeftInverse
    intro x
    unfold Injective at g
    have g₁ : f (inverse f (f x)) = f x
    · apply inverse_spec
      exists x
    apply g
    exact g₁
  · intro g
    unfold LeftInverse at g
    unfold Injective
    intro x y H
    have G : inverse f (f x) = inverse f (f y)
    · rw [H]
    rw [g, g] at G
    exact G

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro g
    unfold Function.RightInverse
    unfold LeftInverse
    intro x
    apply inverse_spec
    unfold Surjective at g
    rcases (g x) with ⟨y, Hy⟩
    exists y
  · intro g
    unfold Function.RightInverse at g
    unfold LeftInverse at g
    unfold Surjective
    intro y
    exists (inverse f y)
    apply g

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  · simp
    exact h₁
  have h₃ : j ∉ S
  · rw [h] at h₁
    exact h₁
  contradiction

-- COMMENTS: TODO: improve this
end
