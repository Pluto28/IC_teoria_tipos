/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false


#check Nat → Nat
#check Nat -> Nat

#check Nat × Nat
#check Prod Nat Nat

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)

#check Nat.succ
#check (0, 1)
#check Nat.add

#check Nat.succ
#check Nat.add 3
#check Nat.add 3 5
#check (5, 9).1
#check (5, 9).2


#eval Nat.succ 2  -- 3
#eval Nat.add 5 2 -- 7
#eval (5, 9).1    --  5
#eval (5, 9).2    -- 9


-- In lean, types have types themselves
#check Nat              -- Type
#check Bool             -- Type
#check Nat → Bool       -- Type
#check Nat × Bool       -- Type
#check Nat × Nat → Nat  -- ...
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α                -- Type
#check F α              -- Type
#check F Nat            -- Type
#check G α              -- Type
#check G α β            -- Type
#check G α Nat          -- Type

#check Prod α β         -- Type
#check α × β            -- Type

#check Prod Nat Nat     -- Type
#check Nat × Nat        -- Type

#check List α           -- Type
#check List Nat           -- Type

#check Type
#check Type 1

#check List


universe u                  -- This gives name to an  universe

def H (α : Type u) : Type u := Prod α α
def I.{k} (α : Type k) : Type k := Prod α α

#check H
#check I

/- Those are magical functions that perform. The fun and λ mean the same thing -/
#check fun (x: Nat) => x + 5  -- Nat → Nat
#check λ (x: Nat) => x + 5    -- Nat → Nat
#check fun x => x + 5         -- Using type inference for x: Nat
#check λ x => x + 5           -- Also using type inference

/- Evaluate a lambda by passing the required paramters -/
#eval (λ x => x + 5) 20        -- 25

#check fun (x : Nat) => fun y : Bool => if not y then x + 1 else x + 2
#check λ (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y =>  if not y then x + 1 else x + 2 -- Nat -> Bool -> Nat

/- Nat -> Nat. This is the identity function on the naturals -/
#check fun x : Nat => x
/- Nat -> Bool. This function returns true without care for x -/
#check fun x : Nat => true

def f (n: Nat) : String := toString n
def g (s: String) : Bool := s.length > 0

/- The composition of f with g-/
#check fun x : Nat => g (f x)
#check fun x => g (f x)

#check fun (h : String -> Nat) (i: Nat -> String) (x: Nat) => h (i x)
#check fun (α β γ: Type) (g: α → β) (h: β → γ) (k: α) => h (g  k)

def double (x: Nat) : Nat :=
    x + x
set_option diagnostics true

#eval double 4

def add (x : Nat) (y : Nat) : Nat  :=
    x + y

#eval add 1 2

def greater (x : Nat) (y : Nat) : Bool :=
    if x > y then true else false

#eval greater 2 3

def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
    f (f x)

#eval doTwice (double) (2) -- 8

/- Takes two functions that can be composed : e.g the domain of one
    matches the codomain of the other, and compose them-/
def compose (α β γ: Type) (g : β → γ) (f : α → β) (x : α) :=
    g (f x)

def square (x : Nat) : Nat :=
    x * x

#eval compose Nat Nat Nat double square 2000

/-LOCAL DEFINITIONS-/

#check let y := 2 + 2; y * y -- Nat
#eval let y := 2 + 2; y * y  -- 16

def twice_double (x: Nat) : Nat :=
    let y := x + x; y * y

#eval twice_double 2


/-  This definition typechecks because as a is simply standing sintatically for
    Nat, it's essentially the same as if we were explicitly annotating the Nat
    type explicitly for x.-/
def foo := let a := Nat; fun x : a => x + 2

/-  My guess is that since the expression has to make sense without considering
    the type that is given as an argument for a, and the add operation is not
    defined for every possible type that can be passed as an argument, this
    expression will always fail to typecheck.
     -/
-- def bar := (fun a => fun x : a => x + 2) Nat


#check foo
--#check bar

section useful

    variable (α β γ: Type)
    variable (g: β → γ) (f: α → β)  (x: α) (h: α → α)

    def compose2 (g: β → γ) (f: α → β) (x: α) :=
        g (f x)

    #check compose2

    /- Definitions using only the variables that we defined beforehand -/


    def compose3 :=
        g (f x)

    def doTwice1 :=
        h (h x)

    def doThrice :=
        h (h (h x))

    #check compose3
    #check doTwice1
    #check doThrice

end useful

namespace Foo
    def a : Int := 3
    def f (x: Nat) : Nat := x + 7
end Foo

#check @List.cons
#check @List.nil
#check @List.length
#check @List.append


namespace depPairs
    universe w v
    def h (α : Type w) (β : α → Type v) (a : α) (b : β a) : α × β a :=
        (a, b)

    def i (α : Type w) (β : α → Type v) (a : α) (b: β a) : Σ a : α, β a :=
        Sigma.mk a b

    def h1 (x : Nat) : Nat :=
        (h Type (fun α => α) Nat x).2

end depPairs

#check depPairs.h
#check depPairs.i
#check depPairs.h1
#eval depPairs.h1 4

#check List          -- Lst.{u} (α : Type u) : Type u
#check List.cons     -- Lst.cons.{u} (α : Type u) (a : α) (as : Lst α) : Lst α
#check List.nil      -- Lst.nil.{u} (α : Type u) : Lst α
#check List.append   -- Lst.append.{u} (α : Type u) (as bs : Lst α) : Lst α

#check List.cons Nat
