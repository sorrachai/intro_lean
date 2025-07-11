import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


-- inductive predicate

inductive IsSorted: List ℕ  → Prop
  -- Base Case 1: The empty list is sorted.
  | nil : IsSorted []
  -- Base Case 2: A list with a single element is sorted.
  | single (a : ℕ) : IsSorted [a]
  -- Inductive Step: If we have an element `a` and another element `b`,
  -- and a tail list `t`, then the list `a :: b :: t` is sorted if:
  -- 1. `a` is less than or equal to `b` (`a ≤ b`).
  -- 2. The rest of the list, `b :: t`, is already sorted.
  | cons (a b : ℕ ) (t : List ℕ ) : a ≤ b → IsSorted (b :: t) → IsSorted (a :: b :: t)


#check IsSorted [20, 3]      -- Output: Prop
example: IsSorted [1] := by
  exact IsSorted.single 1

example: IsSorted [1,3] := by
  apply IsSorted.cons
  omega
  apply IsSorted.single

example: ¬ IsSorted [20,3] := by
  by_contra!
  cases this
  absurd a_1
  omega

def Merge: List ℕ → List ℕ → List ℕ
  | [],[] => []
  | x, [] => x
  | [], y => y
  | x::xs, y::ys =>
    if x ≤ y then x :: Merge xs (y::ys)
    else y :: Merge (x :: xs) ys

#check Merge

def Merge' (xs ys : List ℕ):  List ℕ :=
  match xs,ys with
  | [],[] => []
  | x, [] => x
  | [], y => y
  | x::xs, y::ys =>
    if x ≤ y then x :: Merge xs (y::ys)
    else y :: Merge (x :: xs) ys

def list1 := [1,2,10]
def list2 := [3,5,20]
#eval Merge list1 list2

theorem sorted_merge (xs ys : List ℕ)(hxs: IsSorted xs) (hys: IsSorted ys): IsSorted (Merge xs ys) := by sorry
