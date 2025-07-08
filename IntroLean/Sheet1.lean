import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-!

Lean = Functional Programming Language + Interactive Proof Assistant

We start with how to prove a logical statement in Lean using basic tactics

## term and type in Lean
In Lean, we manipulate data using 'term' and 'type' of objects.
We can think of 'type' as a class of objects and 'term' as a data point/element of that type
Let's define some constant
-/

def n : ℕ := 100 -- n has type ℕ with specific value of 100
def z : ℚ := -0.1

def P1 : Prop := 1 = 1 -- P has type proposition, and its term is 1 = 1
def Q1 : Prop := 1 ≠ 1

/-!
## How to state a theorem in Lean

theorem [name] {optional parameters/assumptions} : [proposition] := [proof]
-/

theorem one_eq_one : 1 = 1 := sorry
theorem one_eq_one': P1 := sorry

-- Let's check type of these thoerems
#check one_eq_one
-- one_eq_one has type 1 = 1

-- Every true proposition has a proof. In Lean, a proof is represented as a term of the proposition.
-- That is, `P : Prop` means P is a (specfic) proposition
-- and `h : P` means `h` is a proof of `P`.
-- `theorem` tells Lean not to unfold anything inside a proof.

-- another example
theorem x_pos (x : ℤ) (h: 1 < x) : 0 ≤ x := sorry
#check x_pos

/-!
## How to prove a theorem in Lean
Under the hood, Lean verifies a proof by type-checking. The details how type-checking works are not our main focus here.
Given a theorem statement, our objective is to tell Lean the proof by using basic tactics.
This is a game: we start with initial goal given by the theorem and provide a sequence of tactics to close the goal.
There are ∼ 20 tactics that will be often used. We will introduce new tactics as we go along.

* `rfl` -- reflexive property a = a: the goal can be close because two objects are defitionally equal
* `exact` -- the goal can be closed by exactly this hypothesis (i.e., because the goal is definitionally equal to it)
* `intro` -- reduce a goal of the form `P → Q` to `Q` and obtain `h : P` as a new hypothesis
          -- reduce a goal of the form `∀ x : N, x > 0` to `x > 0` and obtain `x : ℕ`
* `apply` -- forward and backward
* `constructor` -- break `decomposable` goals into subgoals
-/

-- Throughout this sheet, `P`, `Q` denote propositions.
variable (P Q: Prop)

example : P = P := rfl
example : 2 + 1 + 1 = 4 := rfl

example (h: P → Q)(h2: P) : Q := by
  apply h
  exact h2

example : P → P := by
  intro h
  exact h

example : P → Q → P := by
  intro h h2
  exact h

example (hP: P) (hQ: Q) : P ∧ Q := by
  constructor
  exact hP
  exact hQ

example: P ∧ Q ↔ Q ∧ P:= by
  constructor
  intro h
  obtain ⟨hp,hq⟩ := h
  constructor
  exact hq
  exact hp
  sorry
