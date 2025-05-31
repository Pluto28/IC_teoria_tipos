
variable {p q : Prop}
variable (hp : p)

--theorem t5 : q → p := fun (hq : q) =>

theorem t6 : q → p := fun (hq : q) => hp
