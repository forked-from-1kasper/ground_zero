import GroundZero.HITs.Coequalizer
import GroundZero.Theorems.UA

open GroundZero.Types.Equiv
open GroundZero.Types
open GroundZero (ua)

namespace GroundZero.HITs
universe u v w

section
  variable {A : Type u} {B : Type v} (f g : A → B)
           (C : B → Type w) (D : Π x, C (f x) ≃ C (g x))

  def Flattening := @Coeq (Σ x, C (f x)) (Σ x, C x)
    (λ w, ⟨f w.1, w.2⟩) (λ w, ⟨g w.1, (D w.1).1 w.2⟩)

  hott def P : Coeq f g → Type w :=
  Coeq.rec (Type w) C (λ x, ua (D x))
end

namespace Flattening
  variable {A : Type u} {B : Type v} {f g : A → B}
           {C : B → Type w} {D : Π x, C (f x) ≃ C (g x)}

  hott def iota (x : B) (c : C x) : Flattening f g C D :=
  Coeq.iota ⟨x, c⟩

  hott def resp (x : A) (y : C (f x)) : @Id (Flattening f g C D) (iota (f x) y) (iota (g x) ((D x).1 y)) :=
  @Coeq.resp (Σ x, C (f x)) (Σ x, C x) (λ w, ⟨f w.1, w.2⟩) (λ w, ⟨g w.1, (D w.1).1 w.2⟩) ⟨x, y⟩

  hott def iotaφ : Π x, C x → Σ x, P f g C D x :=
  λ x y, ⟨Coeq.iota x, y⟩

  noncomputable hott def respφ (x : A) (y : C (f x)) :
    @Id (Σ x, P f g C D x) (iotaφ (f x) y) (iotaφ (g x) ((D x).1 y)) :=
  begin
    fapply Sigma.prod; apply Coeq.resp;
    transitivity; apply transportToTransportconst;
    transitivity; apply @Id.map _ _ (Id.map (P f g C D) (Coeq.resp x)) _ (transportconst · y);
    apply Coeq.recβrule (Type w) C (λ x, ua (D x)) x; apply GroundZero.ua.transportRule
  end

  noncomputable hott def sec : Flattening f g C D → Σ x, P f g C D x :=
  begin fapply Coeq.rec; intro w; apply iotaφ w.1 w.2; intro w; apply respφ w.1 w.2 end
end Flattening

end GroundZero.HITs