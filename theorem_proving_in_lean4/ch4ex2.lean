variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) :=
  (fun vart: α =>
    Iff.intro
      (fun prfTrm1: (∀ _ : α, r) =>
        prfTrm1 vart
      )
      (fun prfTrm2: r =>
        (fun _ : α => prfTrm2)
      )
  )

open Classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun prfTrm1: (∀x, p x ∨ r) => (em r).elim
      (fun rTrue1: r => Or.inr rTrue1)
      -- Todo apply prfTrm1 to a type and use elim. Since
      -- rFalse, when the proof of r is yielded we can use contradiction
      -- When a proof of p α is given, how to prove that forall x, p x?
      -- Well, r can't be assumed because it's false. Thus, given an
      -- α, we do elim?
      (fun rFalse: ¬r =>
        have allPrf: ∀x, p x := (fun val: α => (prfTrm1 val).elim
          (fun Allpx: p val => Allpx)
          (fun rTrue2: r => False.elim (rFalse rTrue2))
        )
        Or.inl allPrf
      )
    )

    (fun prfTrm2: (∀ x, p x) ∨ r => prfTrm2.elim
      (fun prfTrm3: ∀ x, p x =>
        (fun val: α => Or.inl (prfTrm3 val))
      )
      (fun prfTrm4: r =>
        (fun _: α => Or.inr prfTrm4)
      )
    )

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun prfTrm1: (∀ x, r → p x) =>
      (fun rProof: r => (fun val: α =>
        ((prfTrm1 val) rProof)
      )
      )
    )
    (fun prfTrm2: (r → ∀ x, p x) => (fun gnrcType: α =>
      (fun rProof: r =>
        (prfTrm2 rProof)
          gnrcType
      )
      )
    )
