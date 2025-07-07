open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r :=
  (fun prop1: (∃ _: α, r) => prop1.elim
    (fun _: α =>
      (fun rProof: r => rProof)
    )
  )

example (a : α) : r → (∃ _ : α, r) :=
  (fun rProof: r => Exists.intro
    a
    rProof
  )

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun pxAr: ∃x, p x ∧ r =>
      (Exists.elim  pxAr (fun w: α =>
        (fun pxArpxArw: p w ∧ r =>
          have existsProof: ∃ x, p x := Exists.intro w (pxArpxArw).left
          And.intro existsProof pxArpxArw.right
        ))

      )
    )

    /- -/
    (fun exPxAr: (∃x, p x) ∧ r => (Exists.elim
        (exPxAr.left)
        (fun val: α =>
          (fun pVal: p val =>
            have andProof : p val ∧ r := And.intro (pVal) exPxAr.right
            Exists.intro val andProof
          )
        )
    ))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    /- We do this by contradiction. Assuming that ∃x, ¬p x, we are led to a
    statement that can't be true. Thus it must be false(e.g. ¬(∃x, ¬p x)) -/
    (fun hAll: ∀x, p x => (fun existsVal: ∃x, ¬p x =>
      Exists.elim existsVal
        (fun val: α =>
          (fun valProp: ¬p val => valProp (hAll val)))
      )
    )

    /- How to prove this? We must show that this is the same as saying that
    ∀x, p x. Suppose then that there exists an x such that ¬p x. From this we
    have a contradiction for notEx. Would that work?-/
    (fun notEx: ¬(∃x, ¬p x) => (fun val: α =>
        have nPval: p val := byContradiction (fun exNpx: ¬(p val) =>
          have XEx: ∃x, ¬p x := Exists.intro val exNpx
          notEx XEx
        )
        nPval
    ))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    /- I think assume that ∀x, ¬p x here will lead inevitably to a contradiction,
    so we do it and then obtain from Exists.elim a proof of p val -/
    (fun eX: ∃ x, p x => (fun contrVal: ∀x, ¬p x => (
          Exists.elim
            eX
            (fun val1: α => (fun pVal1: p val1 => (contrVal val1) pVal1))
        )
      )
    )
    /- We assume that there doesn't exist a value x such that ∃x, p x. That is,
    ¬(∃x, p x). Then we should be led to a contradiction, right?-/
    (fun nAllX: ¬(∀x, ¬p x) => byContradiction (fun notEx: ¬(∃x, p x) =>
       nAllX (fun val: α =>
        (fun valp: p val =>
          have exProof: ∃x, p x := Exists.intro val valp
          (notEx exProof)
        )
      ))
    )

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  ⟨
    /- We can try supposing that p val is true for some generic val.
    This will lead to us being able to use Exists.intro to conclude that
    ∃x, p x is true, which will be a contradiction-/
    (fun nExVal: ¬ ∃ x, p x => (fun val: α =>
      (fun pVal: p val =>
        nExVal (Exists.intro val pVal)
      ))
    ),
    (fun allNpx: ∀ x, ¬ p x => (fun exPx: ∃x, p x =>
      Exists.elim
        exPx
        (fun val: α => (fun pVal: p val => (allNpx val) pVal))
    )

    )
  ⟩
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  ⟨
    (fun nAllx: ¬ ∀ x, p x => byContradiction (fun nEx: ¬(∃ x, ¬ p x) =>
        nAllx (fun val: α =>
          have pVal: p val := byContradiction (fun npVal: ¬ p val =>
            have xExnp: ∃x, ¬p x := Exists.intro val npVal
            nEx xExnp
          )
          pVal
        )
      )
    ),
    (fun ExNpx: ∃ x, ¬ p x => (fun Allpx: ∀ x, p x =>
      have np := Exists.elim
        ExNpx
        (fun val: α => (fun nPval: ¬p val => nPval (Allpx val)))
      np
    ))
  ⟩

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  ⟨
    (fun allX: ∀ x, p x → r => (fun exPx: ∃ x, p x =>
      Exists.elim
        exPx
        (fun val: α => (fun pVal: p val => (allX val) pVal))
    )),
    (fun exPxTr: (∃ x, p x) → r => (fun val: α =>
      (fun pVal: p val =>
        have exPx: ∃ x, p x := Exists.intro val pVal
        exPxTr exPx
      )
    ))
  ⟩

/- This proof was provided by the book. Unfortunately i don't really have much time
  to reprove it-/
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  ⟨
    (fun eXrTp: ∃ x, r → p x => (fun rPrf: r =>
        let ⟨w, rTpw⟩ := eXrTp
        ⟨w, rTpw rPrf⟩
    )),
    /- To prove this, we use intro and then prove that r → p val-/
    (fun rtExPx: r → ∃ x, p x => byCases
      (fun rPrf: r =>
        let ⟨w, hw⟩ := rtExPx rPrf
        --⟨w, fun _ => hw⟩
        Exists.intro w (fun _ => hw)
      )
      (fun nrPrf: ¬r => Exists.intro
        a
        (fun rPrf: r => absurd rPrf nrPrf)
      )
    )
  ⟩
