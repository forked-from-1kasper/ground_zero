import ground_zero.trunc ground_zero.heq
open ground_zero.trunc ground_zero.structures

namespace ground_zero

def 𝕀 := ∥bool∥
abbreviation interval := 𝕀

namespace interval
  universes u v

  def i₀ : 𝕀 := trunc.elem ff
  def i₁ : 𝕀 := trunc.elem tt
  def seg : i₀ = i₁ :> 𝕀 := trunc.uniq i₀ i₁

  abbreviation zero := i₀
  abbreviation one := i₁

  @[inline, recursor 4]
  def rec {β : Sort u} (b₀ : β) (b₁ : β)
    (s : b₀ = b₁ :> β) : 𝕀 → β :=
  let f (b : bool) : singl b₀ :=
    bool.rec (singl.trivial_loop b₀) ⟨b₁, s⟩ b in
  singl.point ∘ trunc.rec f

  /- β i₀ and β i₁ are Prop,
     so s : b₀ = b₁ is trivial -/
  def hrec {β : 𝕀 → Prop} (b₀ : β i₀) (b₁ : β i₁) :
    Π (x : 𝕀), β x := begin
    intros, apply trunc.ind, intros,
    induction a, apply b₀, apply b₁
  end

  def ind {π : 𝕀 → Sort u} (b₀ : π i₀) (b₁ : π i₁)
    (s : b₀ =[seg] b₁) : Π (x : 𝕀), π x := begin
    intro x, refine quot.hrec_on x _ _,
    { intro b, cases b, exact b₀, exact b₁ },
    { intros, induction s,
      cases a; cases b,
      { reflexivity },
      { simp, apply heq.eq_subst_heq },
      { simp, symmetry, apply heq.eq_subst_heq },
      { reflexivity } }
  end

  def homotopy {α : Sort u} {β : Sort v} {f g : α → β}
    (p : f ~ g) (x : α) : 𝕀 → β :=
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
  begin induction p, apply equiv.homotopy.id end

  instance : prop 𝕀 := ⟨trunc.uniq⟩
  instance trunc_functions {α : Type u} : prop (∥α∥ → ∥α∥) :=
  ⟨begin intros, apply funext, intro x, apply trunc.uniq end⟩

  def neg : 𝕀 → 𝕀 :=
  trunc.rec (trunc.elem ∘ bnot)
  prefix `−`:20 := neg

  def bool_to_interval (f : bool → bool → bool) (a b : 𝕀) : 𝕀 :=
  trunc.rec (λ a, trunc.rec (trunc.elem ∘ f a) b) a

  def min (a b : 𝕀) : 𝕀 :=
  trunc.rec (begin intro x, cases x, exact i₀, exact a end) b

  def max : 𝕀 → 𝕀 → 𝕀 := bool_to_interval bor

  notation r `∧`:70 s := min r s
  notation r `∨`:70 s := max r s
end interval

end ground_zero