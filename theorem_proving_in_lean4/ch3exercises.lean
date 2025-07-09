variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h: p ∧ q => (And.intro (And.right h) (And.left h)))
    (fun h: q ∧ p => (And.intro (And.right h) (And.left h)))

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
  -- First we need a proof of q to prove that q ∨ p
  (fun h: p ∨ q => (Or.elim h
    (fun hp: p => (Or.inr hp))
    (fun hq: q => (Or.inl hq))
    ))
  (fun h: q ∨ p => (Or.elim h
    (fun hq: q => (Or.inr hq))
    (fun hp: p => (Or.inl hp))
    ))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h: (p ∧ q) ∧ r => (And.intro
      h.left.left
      (And.intro (h.left.right)
        h.right
      )))
    (fun h: p ∧ (q ∧ r) => (And.intro
      (And.intro h.left
        h.right.left)
      h.right.right
    ))

/- First we need Or.elim ((p ∨ q) ∨ r) ((p ∨ q) -> (p ∨ (q ∨ r)) (r → (p ∨ (q ∨ r)))-/
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
  (fun h: (p ∨ q) ∨ r => Or.elim h
    -- (p ∨ q) → (p ∨ (q ∨ r))
    (fun hpq: (p ∨ q) => Or.elim hpq
      (fun hp : p => Or.inl hp)
      (fun hq : q => (Or.inr
        (Or.inl hq))))
    (fun hr : r => (Or.inr (Or.inr hr)))
  )
  -- r → (p ∨ (q ∨ r))
  (fun h : p ∨ (q ∨ r) => Or.elim h
    (fun hp  : p => Or.inl (Or.inl hp))
    (fun hqr : q ∨ r => Or.elim hqr
      (fun hq: q => Or.inl (Or.inr hq))
      (fun hr : r => Or.inr hr)
    )
  )

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) => (Or.elim h.right
     (fun hq : q => Or.inl
      (And.intro
       (And.left h)
        hq
      )
      )
     (fun hr : r => Or.inr
       (And.intro
        (And.left h) hr
       )
     )
    ))
    (fun h : (p ∧ q) ∨ (p ∧ r) => Or.elim h
      (fun hpq: p ∧ q => And.intro
        (And.left hpq)
        (Or.inl (And.right hpq))
      )
      (fun hpr: p ∧ r => And.intro
        (And.left hpr)
        (Or.inr (And.right hpr))
      )
    )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
  (fun hpqr: p ∨ (q ∧ r) => Or.elim hpqr
   (fun hp: p => And.intro
    (Or.inl hp)
    (Or.inl hp)
   )
   (fun hqr : q ∧ r => And.intro
    (Or.inr (And.left hqr))
    (Or.inr (And.right hqr))
   )
  )
  (fun hpqr : (p ∨ q) ∧ (p ∨ r) => Or.elim hpqr.left
    (fun hp : p => Or.inl hp)
    (fun hq : q => Or.elim hpqr.right
      (fun hp: p => Or.inl hp)
      (fun hr: r => Or.inr (And.intro
       hq
       hr)
    ))
  )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun hpqr : (p → (q → r)) =>
      (fun hpq: p ∧ q => hpqr
       (And.left hpq)
       (And.right hpq)
    ))
    (fun hpqr : (p ∧ q → r) =>
      (fun hp: p =>
       (fun hq: q =>
        hpqr (And.intro hp hq)
       )
      )
    )


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun hpqr: (p ∨ q) → r => And.intro
      (fun hp: p => hpqr (Or.inl hp))
      (fun hq: q => hpqr (Or.inr hq))
    )
    (fun hpqr: (p → r) ∧ (q → r) =>
      (fun hpq: (p ∨ q) => Or.elim hpq
        (fun hp: p => hpqr.left hp)
        (fun hq: q => hpqr.right hq)
      )
    )

/- For ¬ (p ∨ q) → ¬p ∧ ¬q, we can safely assume that p and q are false, and thus
¬ p is true and ¬ q is true, which leads to (¬ p ∧ ¬ q) being true. -/
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
  (fun hnpq: ¬(p ∨ q) => And.intro
    (fun hp: p => hnpq (Or.inl hp))
    (fun hq: q => hnpq (Or.inr hq))
  )
  (fun hnpnq: ¬p ∧ ¬q =>
    (fun hpq: p ∨ q => Or.elim hpq
      (fun hp: p => (hnpnq.left.elim hp))
      (fun hq: q => (hnpnq.right.elim hq))
    )
  )

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun hnpq : ¬p ∨ ¬q =>
    fun hpq : p ∧ q =>
      (Or.elim hnpq
        (fun np: ¬p => np hpq.left)
        (fun nq: ¬q => nq hpq.right)
      )

example : ¬(p ∧ ¬p) :=
  (fun hp : p ∧ ¬p =>
    (And.right hp)
    (And.left hp))

example : p ∧ ¬q → ¬(p → q) :=
  (fun hpnq: p ∧ ¬q =>
    (fun hpq : p → q =>
      hpnq.right
        (hpq (And.left hpnq))
    )
  )

example : ¬p → (p → q) :=
  (fun hnp: ¬p =>
    (fun hpq: p =>
      False.elim (hnp hpq)
    )
  )

example : (¬p ∨ q) → (p → q) := (
  (fun hpq: ¬p ∨ q => Or.elim hpq
    (fun hnp: ¬p => (fun hp: p => False.elim (hnp hp)))
    (fun hq:  q =>
      (fun _: p =>
        hq
      )
    )
  )
)

example : p ∨ False ↔ p :=
  Iff.intro
    (fun hpf: p ∨ False => Or.elim hpf
      (fun hp: p => hp)
      (fun hf: False => hf.elim)
    )
    (fun hp: p => Or.inl hp)

example : p ∧ False ↔ False :=
  Iff.intro
    (fun hpf: p ∧ False => hpf.right.elim)
    (fun hf: False => False.elim hf)

example : (p → q) → (¬q → ¬p) :=
  (fun hpq: p → q =>
      (fun hnq: ¬q =>
        (fun hp: p =>
          hnq.elim (hpq hp)
        )
      )
  )
