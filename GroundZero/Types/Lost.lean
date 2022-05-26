import GroundZero.Types.Equiv

namespace GroundZero.Types

universe u

hott def uninhabitedType {α : Type u} (f : α → 𝟎) : α ≃ 𝟎 :=
begin
  apply Sigma.mk f; apply Qinv.toBiinv;
  apply Sigma.mk (@Proto.Empty.elim α);
  apply Prod.mk <;> intro x;
  induction x; induction f x
end

inductive Lost (α : Type u)
| cons : α → Lost α → Lost α

namespace Lost

hott def code {α : Type u} : Lost α → 𝟎
| cons head tail => code tail

hott def isZero {α : Type u} : Lost α ≃ 𝟎 :=
uninhabitedType code

end Lost

end GroundZero.Types