open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  (fun hpqr: p → q ∨ r => (em p).elim
    (fun hp: p => Or.elim (hpqr hp)
      (fun hq: q => Or.inl (fun _: p => hq))
      (fun hr: r => Or.inr (fun _: p => hr))
    )
    (fun hnp: ¬p => Or.inl (fun hp: p => absurd hp hnp))
  )

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  (fun hnpq: ¬(p ∧ q) => (em p).elim
    (fun hp: p => ((em q).elim
      (fun hq: q => absurd (And.intro hp hq) hnpq)
      (fun hnq: ¬q => (Or.inr hnq))
    ))
    (fun hnp: ¬p => Or.inl hnp)
  )

theorem NotPImplPToQ {r s: Prop} (hns: ¬s): s → r :=
  (fun hs: s =>
    False.elim (hns hs)
  )

example : ¬(p → q) → p ∧ ¬q :=
  (fun hnpq: ¬(p → q) => (em p).elim
    (fun hp: p => ((em q).elim
      (fun hq: q => absurd (fun _: p => hq) hnpq)
      (fun hnq: ¬q => And.intro hp hnq)
    ))
    /- So how do we prove it? We assume that a proof of ¬p exists, and
    from that we must derive a contradiction. We also have a proof
    of ¬(p → q). If we can prove p → q from ¬p, then it follows from the
    assumption of ¬(p → q) an absurdity and thus what we want can be
    concluded-/
    (fun hnp: ¬p =>
      have hptoq: p → q := (fun hp: p => False.elim (hnp hp))
      absurd hptoq hnpq
      --(absurd (NotPImplPToQ hnp) hnpq)
    )
  )

example : (p → q) → (¬p ∨ q) :=
  (fun hptoq: p → q => ((em p).elim
    (fun hp: p => Or.inr (hptoq hp))
    (fun hnp: ¬p => Or.inl hnp)
  ))

example : (¬q → ¬p) → (p → q) :=
  --have hptoq: p → q := (fun hnp: ¬p => (fun hp: p => False.elim (hnp hp)))

  (fun hnqtonp: ¬q → ¬p => ((em q).elim
    (fun hq: q => (em p).elim
      (fun _: p => (fun _: p => hq))
      (fun hnp: ¬p => (NotPImplPToQ hnp))
    )
    (fun hnq: ¬q =>
      NotPImplPToQ (hnqtonp hnq)
    )
  ))

-- Asking us to prove excluded middle, what a bad boy
example : p ∨ ¬p := em p
theorem Np {r s: Prop} (hnr: ¬r) : r → s :=
  (fun hr: r => False.elim (hnr hr))

example : (((p → q) → p) → p) :=
  (fun h1: ((p → q) -> p) => (em p).elim
    (fun hp: p => (em q).elim
      (fun hq: q => h1 (fun _: p => hq))
      (fun _: ¬q => hp)
    )
    (fun hnp: ¬p => h1 (Np hnp))
  )

example : ¬(p ↔ ¬p) :=
  (fun h1 : p ↔ ¬p =>
    have hnp: ¬p := (fun hp: p => ((h1.mp hp) hp))
    hnp (h1.mpr hnp)
  )
