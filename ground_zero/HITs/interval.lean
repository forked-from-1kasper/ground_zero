import ground_zero.HITs.generalized ground_zero.structures
open ground_zero.HITs ground_zero.structures

hott theory

/-
  The unit interval I as Higher Inductive Type.
  Proof of functional extensionality from it.
  * HoTT 6.3

  It is defined as the propositional trunc of bool.
  * HoTT, chapter 6, exercise 6.13
-/

namespace ground_zero
namespace HITs

notation [parsing_only] `𝟐` := bool

def I := {𝟐}
abbreviation interval := I

namespace interval
  universes u v

  def i₀ : I := generalized.incl ff
  def i₁ : I := generalized.incl tt

  def seg : i₀ = i₁ := generalized.glue ff tt
  def seg_inv : i₁ = i₀ := generalized.glue tt ff

  def discrete : bool → I := generalized.incl

  instance : has_zero I := ⟨i₀⟩
  instance : has_one I := ⟨i₁⟩

  abbreviation left := i₀
  abbreviation right := i₁

  abbreviation zero := i₀
  abbreviation one := i₁

  @[inline, recursor 4]
  def rec {β : Sort u} (b₀ : β) (b₁ : β)
    (s : b₀ = b₁ :> β) : I → β :=
  let f (b : bool) : singl b₀ :=
    bool.rec (singl.trivial_loop b₀) ⟨b₁, s⟩ b in
  singl.point ∘ generalized.rec f (begin intros, apply singl.singl_prop end)

  def lift {β : Sort u} (f : bool → β) (H : prop β) : I → β :=
  generalized.rec f (begin intros, apply H end)

  /- β i₀ and β i₁ are Prop’s,
     so s : b₀ = b₁ is trivial -/
  def prop_rec {β : I → Prop} (b₀ : β i₀) (b₁ : β i₁) :
    Π (x : I), β x := begin
    intros, refine quot.ind _ x, intros,
    induction a, apply b₀, apply b₁
  end

  def hrec (β : I → Sort u)
    (b₀ : β 0) (b₁ : β 1) (s : b₀ == b₁)
    (x : I) : β x :=
  quot.hrec_on x
    (λ i, bool.rec_on i b₀ b₁)
    (λ a b _,
      begin simp, induction a; induction b; simp,
            apply s, symmetry, apply s end)

  def ind {π : I → Sort u} (b₀ : π i₀) (b₁ : π i₁)
    (s : b₀ =[seg] b₁) (x : I) : π x := begin
    refine quot.hrec_on x _ _,
    { intro b, cases b, exact b₀, exact b₁ },
    { intros,
      cases a; cases b,
      { reflexivity },
      { simp, apply types.heq.from_pathover, exact s },
      { simp, symmetry,
        apply types.heq.from_pathover, exact s },
      { reflexivity } }
  end

  def interval_contr : contr I := begin
    existsi i₁,
    fapply ind,
    { exact seg⁻¹ }, { reflexivity },
    { apply types.equiv.pathover_from_trans,
      apply types.eq.inv_comp }
  end

  def interval_prop : prop I :=
  contr_impl_prop interval_contr

  def seg_inv_comp : seg ⬝ seg⁻¹ = types.eq.rfl :=
  by apply prop_is_set interval_prop

  def homotopy {α : Sort u} {β : Sort v} {f g : α → β}
    (p : f ~ g) (x : α) : I → β :=
  rec (f x) (g x) (p x)

  def funext {α : Sort u} {β : Sort v} {f g : α → β}
    (p : f ~ g) : f = g :> α → β :=
  let lem := function.swap (homotopy p)
  in lem # seg

  def dfunext {α : Sort u} {β : α → Sort v}
    {f g : Π x, β x}
    (p : f ~ g) : f = g :> Π x, β x :=
  let lem := λ i x, rec (f x) (g x) (p x) i
  in lem # seg

  def homotopy_from_path {α : Sort u} {β : α → Sort v}
    {f g : Π (x : α), β x} (p : f = g) : f ~ g :=
  begin induction p, apply types.equiv.homotopy.id end

  def neg : I → I :=
  lift (discrete ∘ bnot) interval_prop
  prefix `−`:80 := neg
  instance : has_neg I := ⟨neg⟩

  def bool_to_interval (f : bool → bool → bool) (a b : I) : I :=
  lift (λ a, lift (discrete ∘ f a) interval_prop b) interval_prop a

  def min (a b : I) : I :=
  lift (begin intro x, cases x, exact i₀, exact a end)
        interval_prop b

  def max (a b : I) : I :=
  lift (begin intro x, cases x, exact a, exact i₁ end)
        interval_prop b

  notation r `∧`:70 s := min r s
  notation r `∨`:70 s := max r s
end interval

end HITs
end ground_zero