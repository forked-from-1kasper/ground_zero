import GroundZero.HITs.Circle

open GroundZero.Types.Id (ap)
open GroundZero

namespace GroundZero.HITs
open GroundZero.Types GroundZero.HITs.Interval

universe u v

hott definition M : S¹ → Type := Circle.rec I (ua Interval.twist)
hott definition moebius := Σ b, M b

hott definition cylinder := S¹ × I

hott definition C : S¹ → Type := Circle.rec I (idp I)
hott definition cylinder' := Σ b, C b

hott definition C.const : Π x, C x = I :=
begin
  intro x; induction x; reflexivity; change _ = _;
  transitivity; apply Equiv.transportOverContrMap;
  transitivity; apply ap (· ⬝ idp I);
  transitivity; apply Id.mapInv; apply ap;
  apply Circle.recβrule₂; reflexivity
end

hott definition cylEqv : cylinder' ≃ cylinder :=
begin
  transitivity;
  { apply Equiv.idtoeqv; apply ap;
    apply Theorems.funext; exact C.const };
  { apply Sigma.const }
end

end GroundZero.HITs
