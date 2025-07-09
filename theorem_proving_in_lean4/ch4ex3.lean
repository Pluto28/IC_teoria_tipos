open Classical

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  ((em (shaves barber barber)).elim
    (fun shavesHimself: shaves barber barber =>
      (((h barber).mp shavesHimself)
        shavesHimself)
    )
    (fun notShavesHimself: ¬(shaves barber barber) =>
      notShavesHimself ((h barber).mpr
        notShavesHimself)
    )
  )
