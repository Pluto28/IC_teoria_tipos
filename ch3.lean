def Implies (p q: Prop) := p → q
structure Proof (p: Prop) : Type where
  proof : p
#check Proof

#check And      -- Prop → Prop → Prop
#check Or       -- Prop → Prop → Prop
#check Not      -- Prop → Prop
#check Implies  -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q
#check Or (And p q) r
#check Implies (And p q) (And p q)

#check Proof

axiom and_comm_mine (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)
#check and_comm_mine p q

axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q
axiom implies_intro : (p q : Prop) → (Proof p → Proof q)  → Proof (Implies p q)

variable {p : Prop}
variable {q : Prop}


theorem t1: p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

theorem t2 {p q : Prop} (hp : p) (hq : q) : p := hp
theorem t3 (hp : p) (hq : q) : p := hp
theorem t4:  ∀ {p q: Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp

/- I don't know, this is supposed to work but doesn't. -/
--theorem t5 : q → p := fun (hq : q) => hp

theorem t6 (t1 t2 : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s: Prop)
#check t6 p q                 -- p → q → p
#check t6 r s                 -- r → s → r
#check t6 (r → s) (s → r)     -- (r → s) → (s → r) → r → s

variable (h : r → s)
#check t6 (r → s) (s → r) h

-- We do this in here, yep.
theorem t7 (h₁: q → r) (h₂: p → q) : p → r :=
  fun h₃: p =>
  show r from h₁ (h₂ h₃)

#check t7
#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p


variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h


#print t1
#print t2
#print t3
#print t4
--#print t5
#print t6
#print t7


-- Disjunction

variable (p q r: Prop)

example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p  from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)


example (hpq : p → q) (hnq: ¬ q) : ¬ p :=
  fun hp: p =>
    show False from hnq (hpq hp)

variable (p q r: Prop)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h: p ∧ q =>
      show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h: q ∧ p =>
      show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q

variable (h : p ∧ q)
variable (l : q ∧ p)

example : q ∧ p := Iff.mp (and_swap p q) h
example : p ∧ q := Iff.mp (and_swap q p) l


theorem and_swap_an : p ∧ q ↔ q ∧ p :=
  ⟨fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h


open Classical

variable (p : Prop)
#check em p

theorem dne {p: Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
  (fun hp : p => hp)
  (fun hnp : ¬p => absurd hnp h)

example (h : ¬ ¬ p ) : p :=
  byContradiction
    (fun h1 : ¬p =>
      show False from h h1)

#check Or.inr

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
      (show ¬q from
        fun hq : q =>
         h ⟨ hp, hq ⟩))
    (fun hp : ¬p =>
      Or.inl hp)

#check (fun yp: p => (fun hp: ¬p => hp yp))
#check (fun yp: p → q => yp)

#check   (fun hpq: p → q =>
      (fun hnq: ¬q =>
        (fun hp: p =>
          hnq.elim (hpq hp)
        )
      )
  )
