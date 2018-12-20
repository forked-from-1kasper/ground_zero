namespace ground_zero.theorems.functions

universe u

def idfun {α : Sort u} : α → α :=
λ a, a

def swap {α β γ : Sort u} (f : α → β → γ) : β → α → γ :=
λ b a, f a b

end ground_zero.theorems.functions