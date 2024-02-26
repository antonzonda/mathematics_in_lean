import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import MIL.Common

open Set
open Function

noncomputable section
open Classical
variable {α β : Type*} [Nonempty β]

section
variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n

def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have g₁ : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
    constructor
    · simp at hx
      simp
    · simp at hx
      simp
      apply hx
  have g₂ : ∃ y, g y = x := by
    simp at g₁
    apply g₁
  unfold invFun
  rw [dif_pos g₂]
  apply Exists.choose_spec g₂

theorem sb_injective (hf : Injective f) (_ : Injective g) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂
  intro (hxeq : h x₁ = h x₂)
  show x₁ = x₂
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      apply not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
        simp at x₂nA
        rw [hxeq, sb_right_inv f g]
        apply x₂nA

      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq.symm⟩
    rw [if_pos x₁A, if_pos x₂A] at hxeq
    apply hf
    exact hxeq
  push_neg  at xA
  rcases xA with ⟨x₁A, x₂A⟩
  rw [if_neg x₁A, if_neg x₂A] at hxeq
  rw [← sb_right_inv f g x₁A, ← sb_right_inv f g x₂A, hxeq]

theorem sb_surjective (_ : Injective f) (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with _ | n
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, mem_iUnion]
      exact ⟨n, xmem⟩
    simp only [h_def, sbFun, if_pos this]
    exact hg hx
  exists (g y)
  simp
  unfold sbFun
  rw [if_neg gyA]
  unfold invFun
  have h₁ : ∃ x, g x = g y := by
    exists y
  rw [dif_pos h₁]
  apply hg
  rw [Exists.choose_spec h₁]

end

theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf hg, sb_surjective f g hf hg⟩

-- Auxiliary information
section
variable (g : β → α) (x : α)

#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)

end
