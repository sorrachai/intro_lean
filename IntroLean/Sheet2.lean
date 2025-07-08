import Mathlib.Tactic

/-! New tactics
  * `apply` -- Suppose we have `h: P → Q`, which can be from the current assumptions or from the library.
            -- we apply `h` on hypothesis to move assumptions forward and apply on goal to push the goal backward.
  * If we have `hp: P`, then `apply h at hp` yields a new assumption `Q`
  * If the goal is in the form `Q`, then `apply h` changes the goal to `P`
-/
variable (P Q R: Prop)

-- Example 1: Using apply to Transform a Goal
example (h: P → Q)(h2: P): Q := by sorry

-- Example 2: Using apply with Existing Assumptions
example (h: P → Q)(h2: P): Q := by
  apply h at h2
  trivial

example (h: P → Q)(h2: Q → R): P → R := sorry -- [TODO]


/-!
## `apply` is flexible
The apply tactic in Lean can be used not only to transform goals but also to produce subgoals when the hypothesis you are applying has multiple premises.
This is often the case when you have implications or functions that require more than one argument.
-/
example (h0: P ∧ Q ∧ R)(h: P → Q → R → S): S := by
  apply h
  exact h0.1
  exact h0.2.1
  exact h0.2.2

/-!
## More examples
-/
#check lt_trans
example (a b c : ℝ) (hab : a < b) (hbc: b < c) : a < c := by
  apply lt_trans
  pick_goal 3
  exact b
  exact hab
  exact hbc

example (a b c : ℝ) (hab : a < b) (hbc: b < c) : a < c := by
  trans b
  exact hab
  exact hbc
