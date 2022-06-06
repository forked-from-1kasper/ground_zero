import GroundZero.Types.Equiv

namespace GroundZero.Types.HEq

universe u v

hott def inclusion {A : Type u} {a b : A} (p : a = b) : HEq a b :=
begin induction p; apply HEq.refl end

hott def map {A : Type u} {β : A → Type v} {a b : A}
  (f : Π x, β x) (p : a = b) : HEq (f a) (f b) :=
begin induction p; apply HEq.refl end

hott def onlyRefl {A : Type u} {a b : A} (p : a = b) : HEq p (idp a) :=
begin induction p; apply HEq.refl end

hott def eqSubstHEq {A : Type u} {B : A → Type v}
  {a b : A} (p : a = b) (x : B a) :
  HEq x (Types.Equiv.subst p x) :=
begin induction p; apply HEq.refl end

hott def fromPathover {A : Type u} {B : A → Type v}
  {a b : A} (p : a = b) {u : B a} {v : B b} (q : u =[p] v) : HEq u v :=
begin induction p; induction q; apply HEq.refl end

end GroundZero.Types.HEq