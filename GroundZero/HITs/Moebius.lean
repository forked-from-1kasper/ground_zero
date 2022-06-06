import GroundZero.HITs.Circle
open GroundZero

namespace GroundZero.HITs
open GroundZero.Types GroundZero.HITs.Interval

universe u v

def M : S¹ → Type := Circle.rec I (ua Interval.twist)
def moebius := Σ b, M b

def cylinder := S¹ × I

def C : S¹ → Type := Circle.rec I (idp I)
def cylinder' := Σ b, C b

noncomputable hott def C.const : Π x, C x = I :=
begin
  intro x; induction x; reflexivity; change _ = _;
  transitivity; apply Equiv.transportOverContrMap;
  transitivity; apply Id.map (· ⬝ idp I);
  transitivity; apply Id.mapInv; apply Id.map;
  apply Circle.recβrule₂; reflexivity
end

noncomputable hott def cylEqv : cylinder' ≃ cylinder :=
begin
  transitivity;
  { apply Equiv.idtoeqv; apply Id.map;
    apply Theorems.funext; exact C.const };
  { apply Sigma.const }
end

end GroundZero.HITs