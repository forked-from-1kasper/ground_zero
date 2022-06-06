import GroundZero.Algebra.Group.Basic
open GroundZero.Structures
open GroundZero.Types
open GroundZero

namespace GroundZero.Algebra
universe u v u' v' w

namespace Group
  variable {G : Pregroup} [Algebra.group G]

  local infixl:70 (priority := high) " * " => G.φ
  local postfix:max (priority := high) "⁻¹" => G.ι
  local notation "e" => G.e

  def P.carrier (G : Pregroup) := ℕ → G.carrier

  hott def P.hset (G : Pregroup) : hset (P.carrier G) :=
  begin apply piHset; intro; apply G.hset end

  section
    variable {H : Pregroup}

    def P.mul : P.carrier H → P.carrier H → P.carrier H :=
    λ f g n, H.φ (f n) (g n)

    def P.one : P.carrier H := λ _, H.e
    def P.inv : P.carrier H → P.carrier H :=
    λ f n, H.ι (f n)
  end

  hott def P (G : Pregroup) : Pregroup :=
  @Pregroup.intro (P.carrier G) (P.hset G) P.mul P.inv P.one

  instance P.semigroup : semigroup (P G).magma :=
  ⟨begin intros a b c; apply Theorems.funext; intro; apply G.mulAssoc end⟩

  instance P.monoid : monoid (P G).premonoid :=
  begin
    apply monoid.mk; exact P.semigroup;
    { intro; apply Theorems.funext; intro; apply G.oneMul };
    { intro; apply Theorems.funext; intro; apply G.mulOne }
  end

  instance P.group : Algebra.group (P G) :=
  ⟨P.monoid, begin intro; fapply Theorems.funext; intro; apply G.mulLeftInv end⟩

  instance P.abelian (G : Pregroup) [abelian G] : abelian (P G) :=
  ⟨begin intros f g; fapply Theorems.funext; intro; fapply abelian.mulComm end⟩

  hott def P.unitSqr (H : Π x, x * x = e) (x : P.carrier G) : P.mul x x = P.one :=
  begin fapply Theorems.funext; intro; apply H end

  hott def P₂ := P Z₂

  hott def P₂.periodic : Π (x : P₂.carrier), P.mul x x = P.one :=
  P.unitSqr (λ | false => Id.refl | true => Id.refl)
end Group

end GroundZero.Algebra