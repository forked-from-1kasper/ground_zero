import GroundZero.Types.Equiv

open GroundZero.Types.Equiv (transport)

namespace GroundZero.Types.HEq

universe u v

hott definition inclusion {A : Type u} {a b : A} (p : a = b) : HEq a b :=
begin induction p; apply HEq.refl end

hott definition map {A : Type u} {B : A → Type v} {a b : A}
  (f : Π x, B x) (p : a = b) : HEq (f a) (f b) :=
begin induction p; apply HEq.refl end

hott definition onlyRefl {A : Type u} {a b : A} (p : a = b) : HEq p (idp a) :=
begin induction p; apply HEq.refl end

hott definition eqSubstHEq {A : Type u} {B : A → Type v} {a b : A}
  (p : a = b) (x : B a) : HEq x (transport B p x) :=
begin induction p; apply HEq.refl end

hott definition fromPathover {A : Type u} {B : A → Type v} {a b : A}
  (p : a = b) {u : B a} {v : B b} (q : u =[p] v) : HEq u v :=
begin induction p; induction q; apply HEq.refl end

end GroundZero.Types.HEq
