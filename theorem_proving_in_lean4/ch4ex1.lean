variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun pp1: ∀x, p x ∧ q x =>
      have proof1: ∀ x, p x := (fun val: α => (pp1 val).left)
      have proof2: ∀ x, q x := (fun val: α => (pp1 val).right)

      And.intro proof1 proof2
    )
    (fun pp2 : (∀ x, p x) ∧ (∀ x, q x) =>
      (fun val : α =>
        And.intro (pp2.left val) (pp2.right val)
      )
    )


example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  (fun proof1: ∀ x, p x → q x =>
    (fun proof2: ∀ x, p x =>
      (fun val: α =>
        have proof3: p val → q val := (proof1 val)
        have proof4: p val := proof2 val
        (proof3 proof4)
      )
    )
  )

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  (fun proof1: (∀ x, p x) ∨ (∀ x, q x) => proof1.elim
    (fun proof2: (∀ x, p x) => (
      (fun val: α => Or.inl (proof2 val))
      )
    )
    (fun proof3: (∀ x, q x) => (
      (fun val: α => Or.inr (proof3 val))
    ))
  )

/- Why isn't the reverse implication  derivable? For starters, we can't use the
  elim rule the same way we've used it here. We would need to get the inner ∀
  and then use the elim rule for p val ∨ q val, where val is some
  term of type α. It's then impossible to prove (∀ x, p x) ∨ (∀ x, q x) from
  this, because the type of x will always have been selected, but we want to
  be able to select it. The proof will never typecheck-/
--example : ∀ x, p x ∨ q x → (∀ x, p x) ∨ (∀ x, q x) :=
--  (fun val: α =>
--    (fun proof1 : ∀ x, p x ∨ q x => (proof1 val).elim
--      (fun proof2: p val => Or.inl proof2)
--      (fun proof3: q val => Or.inr proof3)
--    )
--  )
