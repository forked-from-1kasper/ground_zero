import ground_zero.HITs.trunc
open ground_zero.HITs.trunc ground_zero.structures

/-
  The unit interval I as Higher Inductive Type.
  Proof of functional extensionality from it.
  * HoTT 6.3

  It is defined as the propositional truncation of bool.
  * HoTT, chapter 6, exercise 6.13
-/

namespace ground_zero
namespace HITs

def I := ∥bool∥
abbreviation interval := I

namespace interval
  universes u v

  def i₀ : I := trunc.elem ff
  def i₁ : I := trunc.elem tt
  def seg : i₀ = i₁ :> I := trunc.uniq i₀ i₁

  abbreviation zero := i₀
  abbreviation one := i₁

  @[inline, recursor 4]
  def rec {β : Sort u} (b₀ : β) (b₁ : β)
    (s : b₀ = b₁ :> β) : I → β :=
  let f (b : bool) : singl b₀ :=
    bool.rec (singl.trivial_loop b₀) ⟨b₁, s⟩ b in
  singl.point ∘ trunc.rec f

  /- β i₀ and β i₁ are Prop’s,
     so s : b₀ = b₁ is trivial -/
  def hrec {β : I → Prop} (b₀ : β i₀) (b₁ : β i₁) :
    Π (x : I), β x := begin
    intros, refine trunc.ind _ _ x, intros,
    { induction a, apply b₀, apply b₁ },
    { intros, trivial }
  end

  def ind {π : I → Sort u} (b₀ : π i₀) (b₁ : π i₁)
    (s : b₀ =[seg] b₁) : Π (x : I), π x := begin
    intro x, refine quot.hrec_on x _ _,
    { intro b, cases b, exact b₀, exact b₁ },
    { intros, induction s,
      cases a; cases b,
      { reflexivity },
      { simp, apply types.heq.eq_subst_heq },
      { simp, symmetry, apply types.heq.eq_subst_heq },
      { reflexivity } }
  end

  def homotopy {α : Sort u} {β : Sort v} {f g : α → β}
    (p : f ~ g) (x : α) : I → β :=
  rec (f x) (g x) (p x)

  def funext {α : Sort u} {β : Sort v} {f g : α → β}
    (p : f ~ g) : f = g :> (α → β) :=
  function.swap (homotopy p) # seg

  def dfunext {α : Sort u} {β : α → Sort v}
    {f g : Π (x : α), β x}
    (p : f ~ g) : f = g :> _ :=
  (λ i x, rec (f x) (g x) (p x) i) # seg

  def homotopy_from_path {α : Sort u} {β : α → Sort v}
    {f g : Π (x : α), β x} (p : f = g :> _) : f ~ g :=
  begin induction p, apply types.equiv.homotopy.id end

  instance : prop I := ⟨trunc.uniq⟩
  instance trunc_functions {α : Type u} : prop (∥α∥ → ∥α∥) :=
  ⟨begin intros, apply funext, intro x, apply trunc.uniq end⟩

  def neg : I → I :=
  trunc.rec (trunc.elem ∘ bnot)
  prefix `−`:20 := neg

  def bool_to_interval (f : bool → bool → bool) (a b : I) : I :=
  trunc.rec (λ a, trunc.rec (trunc.elem ∘ f a) b) a

  def min (a b : I) : I :=
  trunc.rec (begin intro x, cases x, exact i₀, exact a end) b

  def max (a b : I) : I :=
  trunc.rec (begin intro x, cases x, exact a, exact i₁ end) b

  notation r `∧`:70 s := min r s
  notation r `∨`:70 s := max r s
end interval

end HITs
end ground_zero