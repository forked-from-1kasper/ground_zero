namespace ground_zero.algebra

universe u
class magma (α : Type u) :=
(m : α → α → α)

class pointed_magma (α : Type u) extends magma α :=
(e : α)

end ground_zero.algebra