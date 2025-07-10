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

-- Recursive Inductive Type: List
inductive MyList (α : Type)
| nil : MyList α
| cons : α → MyList α → MyList α

def emptyList : MyList ℕ := MyList.nil
def myList1 : MyList ℕ :=  MyList.cons 1 emptyList
def myList21 :  MyList ℕ := MyList.cons 2 myList1

def listLength {α : Type} : MyList α → Nat
| MyList.nil          => 0
| MyList.cons _ tail  => 1 + listLength tail

def listSum : MyList Nat → Nat
| MyList.nil          => 0
| MyList.cons x xs    => x + listSum xs

-- Tactics for inductive types
