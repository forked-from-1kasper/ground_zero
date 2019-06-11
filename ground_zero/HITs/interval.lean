import ground_zero.structures ground_zero.types.heq
open ground_zero.structures

hott theory

/-
  The unit interval I as Higher Inductive Type.
  Proof of functional extensionality from it.
  * HoTT 6.3

  It is primitive HIT.
  * HoTT, chapter 6, exercise 6.13
-/

namespace ground_zero
namespace HITs

inductive I.rel : bool → bool → Prop
| mk (a b : bool) : I.rel a b

def I : Type := quot I.rel
abbreviation interval := I

namespace interval
  universes u v

  def discrete : bool → I := quot.mk rel
  def i₀ : I := discrete ff
  def i₁ : I := discrete tt

  def seg : i₀ = i₁ := support.inclusion $ quot.sound (rel.mk ff tt)
  def seg_inv : i₁ = i₀ := support.inclusion $ quot.sound (rel.mk tt ff)

  instance : has_zero I := ⟨i₀⟩
  instance : has_one I := ⟨i₁⟩

  abbreviation left := i₀
  abbreviation right := i₁

  abbreviation zero := i₀
  abbreviation one := i₁

  /- β i₀ and β i₁ are Prop’s,
     so s : b₀ = b₁ is trivial -/
  def prop_rec {β : I → Prop} (b₀ : β i₀) (b₁ : β i₁) :
    Π (x : I), β x := begin
    intros, refine quot.ind _ x, intro b,
    cases b, exact b₀, exact b₁
  end

  def hrec (β : I → Sort u)
    (b₀ : β 0) (b₁ : β 1) (s : b₀ == b₁)
    (x : I) : β x := begin
    fapply quot.hrec_on x,
    { intro b, cases b, exact b₀, exact b₁ },
    { intros a b R, cases a; cases b,
      { trivial },
      { exact s },
      { symmetry, exact s },
      { trivial } }
  end

  def ind {π : I → Sort u} (b₀ : π i₀) (b₁ : π i₁)
    (s : b₀ =[seg] b₁) (x : I) : π x := begin
    fapply quot.hrec_on x,
    { intro b, cases b, exact b₀, exact b₁ },
    { intros,
      cases a; cases b,
      { reflexivity },
      { simp, apply types.heq.from_pathover, exact s },
      { simp, symmetry,
        apply types.heq.from_pathover, exact s },
      { reflexivity } }
  end

  @[inline, recursor 4]
  def rec {β : Sort u} (b₀ : β) (b₁ : β)
    (s : b₀ = b₁ :> β) : I → β :=
  ind b₀ b₁ (types.dep_path.pathover_of_eq seg s)

  def lift {β : Sort u} (f : bool → β) (H : prop β) : I → β :=
  begin fapply rec, exact f ff, exact f tt, apply H end

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

  def lifting_property {α : Sort u} {β : Sort v} (p : α → β) :=
  Π (x : α) (f : I → β), p x = f 0 → Σ' (g : I → α), x = g 0

  def fibration {α : Sort u} (β : α → Sort v) (x : Σ' x, β x) : α := x.fst

  def lifting {α : Sort u} {β : α → Sort v} {x : α} (u : β x)
    (f : I → α) (h : x = f 0) : I → (Σ' x, β x) :=
  let b₀ := types.equiv.subst h u in
  let b₁ := types.equiv.transport (β ∘ f) seg b₀ in
  λ i, ⟨f i, @interval.ind (β ∘ f) b₀ b₁ (types.equiv.path_over_subst types.eq.rfl) i⟩

  lemma prod {α : Sort u} {β : α → Sort v} {u v : psigma β}
    (h : u.fst = v.fst) (g : types.equiv.subst h u.snd = v.snd) : u = v := begin
    cases u with x u, cases v with y v,
    fapply types.equiv.transport (λ (v : β y), ⟨x, u⟩ = ⟨y, v⟩ :> psigma β),
    exact g,
    apply @types.eq.rec α x (λ (y : α) (h : x = y),
      ⟨x, u⟩ = ⟨y, types.equiv.subst h u⟩ :> psigma β),
    trivial
  end

  theorem type_family {α : Sort u} (β : α → Sort v) :
    lifting_property (fibration β) := begin
    intros x f h, cases x with x u, existsi lifting u f h,
    fapply prod, exact h, trivial
  end
end interval

end HITs
end ground_zero