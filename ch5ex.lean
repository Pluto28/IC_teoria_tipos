/- CH 3 EXERCISES -/

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro <;>
  . intro h
    apply And.intro h.right h.left

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro <;>
  . intro h
    cases h with
    | inl hp => apply Or.inr hp
    | inr hq => apply Or.inl hq

  -- First we need a proof of q to prove that q ∨ p
  --(fun h: p ∨ q => (Or.elim h
  --  (fun hp: p => (Or.inr hp))
  --  (fun hq: q => (Or.inl hq))
  --  ))
  --(fun h: q ∨ p => (Or.elim h
  --  (fun hq: q => (Or.inr hq))
  --  (fun hp: p => (Or.inl hp))
  --  ))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro h
    apply And.intro
      (h.left.left)
      (And.intro h.left.right h.right)
  . intro h
    apply And.intro
      (And.intro h.left (h.right.left))
      (h.right.right)


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hpq => cases hpq with
      | inl hp => apply Or.inl hp
      | inr hq => apply Or.inr (Or.inl hq)
    | inr hr => apply Or.inr (Or.inr hr)
  . intro h
    cases h with
    | inl hp  => apply Or.inl (Or.inl hp)
    | inr hqr => cases hqr with
      | inl hq => apply Or.inl (Or.inr hq)
      | inr hr => apply Or.inr hr

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => apply Or.inl (And.intro h.left hq)
    | inr hr => apply Or.inr (And.intro h.left hr)
  . intro h
    cases h with
    | inl hpq => apply And.intro hpq.left (Or.inl hpq.right)
    | inr hpr => apply And.intro hpr.left (Or.inr hpr.right)

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hp => apply And.intro; repeat (apply Or.inl hp)
    | inr hqr => apply And.intro
                  (Or.inr hqr.left)
                  (Or.inr hqr.right)
    --apply And.intro ; repeat constructor
  . intro h
    cases h with
    | intro hpq hpr =>
      cases hpq with
      | inl hp => apply Or.inl hp
      | inr hq =>
        cases hpr with
        | inl hp => apply Or.inl hp
        | inr hr => apply Or.inr (And.intro hq hr)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  intro h
  . apply And.intro
    . intro hp
      apply h (Or.inl hp)
    . intro hq
      apply h (Or.inr hq)
  intro h
  . cases h with
    | intro hnp hnq =>
      intro hpq
      . cases hpq with
        | inl hp => apply hnp hp
        | inr hq => apply hnq hq


example : (p → q) → (¬q → ¬p) := by
  intro hpq
  intro hnq
  intro hp
  apply hnq (hpq hp)

example : p ∧ ¬q → ¬(p → q) := by
  intro hpnq
  intro hpq
  cases hpnq with
  | intro hp hnq => apply hnq (hpq hp)

example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro hpqr hpq
    apply (hpqr hpq.left) hpq.right
  . intro hpqr hp hq
    apply hpqr (And.intro hp hq)

/- CH 4 EXERCISES -/
variable (α : Type) (p q : α → Prop)
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro hpq
    constructor
    . apply (fun val: α => (hpq val).left)
    . apply (fun val: α => (hpq val).right)
  . intro hpq
    apply (fun val: α => And.intro (hpq.left val) (hpq.right val))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro hpq hp val
  apply (hpq val) (hp val)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro hpq val
  cases hpq with
  | inl hp => apply Or.inl (hp val)
  | inr hq => apply Or.inr (hq val)

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

open Classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  . intro hpr
    cases (em r) with
    | inl hr => apply Or.inr hr
    | inr hnr =>
      apply Or.inl
       (fun val: α => (hpr val).elim
          (fun pval: p val => pval)
          (fun rval: r => False.elim (hnr rval))
       )
  . intro hpr
    cases hpr with
    | inl hp => apply (fun val: α => Or.inl (hp val))
    | inr hr => apply (fun val: α => Or.inr hr)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  . intro all_hpr hr val
    apply (all_hpr val) hr
  . intro hpr val
    apply (fun hr: r => (hpr hr) val)


example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  . intro hxr
    cases hxr with
    | intro w hr =>
      have hpAndr := Exists.
  . sorry

example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩
