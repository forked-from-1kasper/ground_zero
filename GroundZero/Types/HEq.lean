import GroundZero.Types.Equiv

namespace GroundZero.Types.HEq

universe u v

hott def inclusion {α : Type u} {a b : α} (p : a = b) : HEq a b :=
begin induction p; apply HEq.refl end

hott def map {α : Type u} {β : α → Type v} {a b : α}
  (f : Π x, β x) (p : a = b) : HEq (f a) (f b) :=
begin induction p; apply HEq.refl end

hott def onlyRefl {α : Type u} {a b : α} (p : a = b) : HEq p (idp a) :=
begin induction p; apply HEq.refl end

hott def eqSubstHEq {α : Type u} {π : α → Type v}
  {a b : α} (p : a = b) (x : π a) :
  HEq x (Types.Equiv.subst p x) :=
begin induction p; apply HEq.refl end

hott def fromPathover {α : Type u} {π : α → Type v}
  {a b : α} (p : a = b) {u : π a} {v : π b} (q : u =[p] v) : HEq u v :=
begin induction p; induction q; apply HEq.refl end

end GroundZero.Types.HEq