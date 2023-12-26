import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a


theorem fNoUb (f: ℝ → ℝ) (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example {f: ℝ → ℝ} (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a, fnlba⟩
  rcases h a with ⟨x, hx⟩
  have : a ≤ f x := fnlba x
  linarith


variable (f : ℝ → ℝ)
example : ¬FnHasUb fun x ↦ x := by
  have h : ∀ a : ℝ, ∃ x, (fun x ↦ x) x > a := by
    intro a
    use a + 1
    dsimp
    linarith
  apply fNoUb (fun x ↦ x) h

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  --apply lt_of_not_ge
  apply by_contradiction
  intro g
  have h₂ : b ≤ a := by
    apply le_of_not_lt g
  have h₃ : f b ≤ f a := by
    apply h h₂
  linarith

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro monof
  have h₁ : f a ≤ f b := by
    apply monof h
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun _ : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b
    dsimp
    exact fun _ => le_refl 0

  have h' : f 1 ≤ f 0 := le_refl _
  have h₂ := @h f (monof) 1 0 h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply by_contradiction
  intro g
  have g₁ : 0 < x := by
    apply lt_of_not_le g
  have g₂ : x < x / 2 := by
    apply h (x/2)
    linarith
  linarith

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x Px
  have h' : ∃ x, P x := ⟨x, Px⟩
  exact h h'

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro expx
  rcases expx with ⟨a, Pa⟩
  have h' : ¬ P a := by
    apply h a
  apply h' Pa

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  by_contra h''
  apply h'
  use x

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro fxpx
  rcases h with ⟨a, nPa⟩
  have h' := fxpx a
  apply nPa h'

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra h'
  apply h h'

example (h : Q) : ¬¬Q := by
  by_contra h'
  contradiction

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  apply h
  use a
  intro x
  by_contra h''
  apply h'
  use x
  linarith

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp [Monotone] at h
  push_neg at h
  exact h


example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have _ : ¬0 < 0 := lt_irrefl 0
  contradiction

end
