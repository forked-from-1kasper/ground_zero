import ground_zero.types.heq
open ground_zero.types

hott theory

/-
  The unit interval I as Higher Inductive Type.
  Proof of functional extensionality from it.
  * HoTT 6.3

  It is primitive HIT.
  * HoTT, chapter 6, exercise 6.13
-/

namespace ground_zero.HITs
universes u v w

inductive I.rel : bool → bool → Prop
| mk (a b : bool) : I.rel a b

def I : Type := quot I.rel
abbreviation interval := I

namespace interval

  def discrete : bool → I := quot.mk rel
  def i₀ : I := discrete ff
  def i₁ : I := discrete tt

  @[safe] def seg : i₀ = i₁ := ground_zero.support.inclusion $ quot.sound (rel.mk ff tt)

  instance : has_zero I := ⟨i₀⟩
  instance : has_one I := ⟨i₁⟩

  abbreviation left := i₀
  abbreviation right := i₁

  abbreviation zero := i₀
  abbreviation one := i₁

  @[safe] def ind {π : I → Type u} (b₀ : π i₀) (b₁ : π i₁)
    (s : b₀ =[seg] b₁) (x : I) : π x :=
  begin
    fapply quot.hrec_on x,
    { intro b, cases b, exact b₀, exact b₁ },
    { intros,
      cases a; cases b,
      { reflexivity },
      { simp, apply heq.from_pathover, exact s },
      { simp, symmetry,
        apply heq.from_pathover, exact s },
      { reflexivity } }
  end

  @[hott, inline]
  def rec {β : Type u} (b₀ : β) (b₁ : β)
    (s : b₀ = b₁ :> β) : I → β :=
  ind b₀ b₁ (equiv.pathover_of_eq seg s)

  axiom indβrule {π : I → Type u} (b₀ : π i₀) (b₁ : π i₁)
    (s : b₀ =[seg] b₁) : equiv.apd (ind b₀ b₁ s) seg = s

  @[hott] noncomputable def recβrule {π : Type u} (b₀ b₁ : π)
    (s : b₀ = b₁) : rec b₀ b₁ s # seg = s :=
  begin
    apply equiv.pathover_of_eq_inj seg, transitivity,
    symmetry, apply equiv.apd_over_constant_family,
    transitivity, apply indβrule, reflexivity
  end

  @[hott] def homotopy {α : Type u} {β : α → Type v} {f g : Π x, β x}
    (p : f ~ g) (x : α) : I → β x :=
  interval.rec (f x) (g x) (p x)

  @[hott] def funext {α : Type u} {β : α → Type v}
    {f g : Π x, β x} (p : f ~ g) : f = g :=
  @Id.map I (Π x, β x) 0 1 (function.swap (homotopy p)) interval.seg

  @[hott] def happly {α : Type u} {β : α → Type v}
    {f g : Π x, β x} (p : f = g) : f ~ g :=
  equiv.transport (λ g, f ~ g) p (equiv.homotopy.id f)

  @[hott] def map_happly {α β γ : Type u} {a b : α} {c : β} (f : α → β → γ)
    (p : a = b) : (λ x, f x c) # p = happly (f # p) c :=
  begin induction p, trivial end
end interval
end ground_zero.HITs