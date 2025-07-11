import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


/-! Inductive Type

In Lean 4, an inductive type is a way to define a new type by specifying its constructors,
which describe all possible ways to create values of that type.

* An inductive type is defined by listing its constructors. Each constructor can take arguments, allowing the creation of more complex structures.
* Inductive types can be recursive, meaning a constructor can include the type itself as part of its arguments. This enables defining structures like lists or trees.

-/

-- Simple Inductive Type: Enumeration
inductive Color
| Red : Color
| Green : Color
| Blue : Color

#check Color
#check Color.Red

inductive Color'
| Red
| Green
| Blue

def favoriteColor : Color → String
| Color.Red   => "Red is lovely"
| Color.Green => "Green is calming."
| Color.Blue  => "Blue is clear."

#eval favoriteColor Color.Red

-- Inductive Type with Parameters
inductive MyOption (α : Type)
| none : MyOption α
| some : α → MyOption α

#check MyOption
#check MyOption.none
#check MyOption.some

def getOrElse {α : Type} (opt : MyOption α) (default : α) : α :=
  match opt with
  | MyOption.none   => default
  | MyOption.some x => x
-- Recursive Inductive Type: Nat
inductive nat : Type
| zero
| succ : nat → nat

-- Examples from Mathmatics in Lean Chapter 6.3 Inductively Defined Types
-- Recursive Inductive Type: List
namespace MyList
inductive List (α : Type)
| nil : List α
| cons : α → List α → List α
-- the type List α is either
-- 1. an empty list (nil) or
-- 2. cons x xs where x : α and xs : List α
-- {[], [x], [x₁ x₂], [x₁ x₂ x₃] … }

#check List
#check List.nil
#check List.cons

end MyList

-- Lean defines the notation [] for nil and :: for cons,
-- [a,b,c] = a :: b :: c :: []

def append {α : Type} : List α → List α → List α
| [], bs => bs
| a :: as, bs => a :: (append as bs)

#check append
#eval append [1, 2, 3] [4, 5, 6]
-- append has notation ++

-- Exercise: write reverse list
def reverse {α : Type} : List α → List α
| [] => []
| a :: xs => reverse xs ++ [a]

#eval reverse [1,2,3]

-- Exercise: compute the length of a list
def len {α : Type} : List α → ℕ
| []     =>  0
| _ :: xs => 1 + len xs

#check len

-- proving by induction
theorem len_append (x : ℕ) (l : List ℕ) : len (l ++ [x]) = 1 + len l  := by
  induction' l with y ys
  aesop
  simp only [List.cons_append, len]
  rw [tail_ih]

theorem len_eq_len_rev (xs: List ℕ): len xs = len (reverse xs) := by
  induction' xs with x xs
  simp_all [len,reverse]
  simp [len,reverse]
  have: len (reverse xs ++ [x]) = 1+ len (reverse xs) := by
    apply len_append
  rw [this,tail_ih]
