import ground_zero.HITs.coequalizer ground_zero.theorems.ua
open ground_zero.types.equiv ground_zero.types
open ground_zero (ua)

hott theory

namespace ground_zero.HITs
universes u v w

section
  variables {α : Type u} {β : Type v} (f g : α → β)
            (C : β → Type w) (D : Π x, C (f x) ≃ C (g x))

  def flattening := @coeq (Σ x, C (f x)) (Σ x, C x)
    (λ w, ⟨f w.1, w.2⟩) (λ w, ⟨g w.1, (D w.1).1 w.2⟩)

  @[hott] def P : coeq f g → Type w :=
  coeq.rec (Type w) C (λ x, ua (D x))
end

namespace flattening
  variables {α : Type u} {β : Type v} {f g : α → β}
            {C : β → Type w} {D : Π x, C (f x) ≃ C (g x)}

  @[hott] def iota (x : β) (c : C x) : flattening f g C D :=
  coeq.iota ⟨x, c⟩

  @[hott] def resp (x : α) (y : C (f x)) :
    iota (f x) y = iota (g x) ((D x).1 y) :> flattening f g C D :=
  @coeq.resp (Σ x, C (f x)) (Σ x, C x)
    (λ w, ⟨f w.1, w.2⟩) (λ w, ⟨g w.1, (D w.1).1 w.2⟩) ⟨x, y⟩

  @[hott] def iotaφ : Π x, C x → Σ x, P f g C D x :=
  λ x y, ⟨coeq.iota x, y⟩

  @[hott] noncomputable def respφ (x : α) (y : C (f x)) :
    iotaφ (f x) y = iotaφ (g x) ((D x).1 y) :> Σ x, P f g C D x :=
  begin
    fapply sigma.prod, apply coeq.resp,
    transitivity, apply equiv.transport_to_transportconst,
    transitivity, apply Id.map (λ p, transportconst p y),
    change Id.map (coeq.rec (Type w) C (λ x, ua (D x))) (coeq.resp x) = _,
    apply coeq.recβrule, apply ground_zero.ua.transportconst_rule
  end

  @[hott] noncomputable def sec : flattening f g C D → Σ x, P f g C D x :=
  begin fapply coeq.rec, intro w, apply iotaφ w.1 w.2, intro w, apply respφ w.1 w.2 end

  @[hott] def ret : Π x, P f g C D x → flattening f g C D :=
  begin
    fapply coeq.ind (λ x, P f g C D x → flattening f g C D), apply iota,
    intro x, change _ = _, transitivity, apply transport_impl (P f g C D) (λ _, flattening f g C D),
    apply ground_zero.theorems.funext, intro ω, transitivity, apply transport_over_const_family,
    
  end

  @[hott] def lem : (Σ x, P f g C D x) ≃ flattening f g C D :=
  begin
    fapply sigma.mk,
  end
end flattening

end ground_zero.HITs