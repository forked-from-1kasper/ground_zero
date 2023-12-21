import GroundZero.Types.Equiv

namespace GroundZero.Types

universe u

hott definition uninhabitedType {A : Type u} (f : A → 𝟎) : A ≃ 𝟎 :=
begin
  apply Sigma.mk f; apply Qinv.toBiinv;
  apply Sigma.mk (@Proto.Empty.elim A);
  apply Prod.mk <;> intro x;
  induction x; induction f x
end

inductive Lost (A : Type u)
| cons : A → Lost A → Lost A

namespace Lost

hott definition code {A : Type u} : Lost A → 𝟎
| cons x xs => code xs

hott definition isZero {A : Type u} : Lost A ≃ 𝟎 :=
uninhabitedType code

end Lost

end GroundZero.Types
