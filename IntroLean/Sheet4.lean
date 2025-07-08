import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

/-! Set theory

In Lean's library,  a set is always a set of objects of some type. Basic set operations are built-in.
* s ⊆ t ↔ ∀ x ∈ s, x ∈ t
* s ∪ t ↔ ∀ x, x ∈ s ∨ x ∈ t
* s ∩ t ↔ ∀ x, x ∈ s ∩ x ∈ t
-/

open Set

def S1 : Set (ℕ) := {10}
def S2 : Set (ℕ) := {10,20}

#check S1 ⊆ S2

example : S1 ⊆ S2 := by
  unfold S1 S2
  sorry

#check S1
#check 10 ∈ S1

variable {α : Type*}
variable (A B C D: Set α)

example : A ⊆ A := by rfl

/-!
  Another useage of `apply` tactic
  * `apply` -- to reduce a goal of the form `∀ x : ℕ , P(x)` to `P(x)` and obtain `x : ℕ`
    i.e., to prove for-all statement, let fix an arbitrary element x, and then we prove P(x)
    This is because, in Lean, ∀ x : N, P(x) is equivalent to (x :ℕ) →  P(x)
-/

def f (x :ℕ) := x = 0
#check f
example : (∀ x : ℕ, f x) ↔ ((x : ℕ) → f x) := by rfl


example : A ⊆ B → B ⊆ C → A ⊆ C := by
  repeat rw [@subset_def]
  intro h1 h2 x hx
  apply h2
  apply h1
  exact hx

-- the following exercises are copied directly from Bhavik Metha's lecture note
-- https://github.com/b-mehta/formalising-mathematics-notes/blob/main/FormalisingMathematics2025/Section04sets/Sheet1.lean

example : A ∩ B ⊆ A := by sorry

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := by sorry

example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D := by sorry

/-! New tactics
 * `left`  -- change the goal of the form P ∨ Q to P
 * `right` -- change the goal of the form P ∨ Q to Q
 * `cases` -- deal with cases
 * `by_cases` -- prove by cases
-/

example : A ⊆ A ∪ B := by sorry

example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by sorry

example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D := by sorry
