import ground_zero.structures
open ground_zero.structures ground_zero.types
open ground_zero.theorems (funext)

hott theory

namespace ground_zero
universes u v w

namespace HITs
namespace interval
  @[safe] def seg_inv : i₁ = i₀ := support.inclusion $ quot.sound (I.rel.mk tt ff)

  /- β i₀ and β i₁ are Prop’s,
     so s : b₀ = b₁ is trivial -/
  def prop_rec {β : I → Prop} (b₀ : β i₀) (b₁ : β i₁) :
    Π (x : I), β x := begin
    intros, refine quot.ind _ x, intro b,
    cases b, exact b₀, exact b₁
  end

  def hrec (β : I → Type u)
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

  @[hott] def lift {β : Type u} (f : bool → β) (H : prop β) : I → β :=
  begin fapply rec, exact f ff, exact f tt, apply H end

  @[hott] def contr_left : Π i, i₀ = i :=
  interval.ind types.Id.refl seg (begin
    apply types.equiv.pathover_from_trans,
    apply types.Id.refl_left
  end)

  @[hott] def contr_right : Π i, i₁ = i :=
  interval.ind seg⁻¹ types.Id.refl (begin
    apply types.equiv.pathover_from_trans,
    apply types.Id.inv_comp
  end)

  @[hott] def interval_contr : contr I := ⟨i₁, contr_right⟩

  @[hott] def interval_prop : prop I :=
  contr_impl_prop interval_contr

  @[hott] def seg_inv_comp : seg ⬝ seg⁻¹ = types.Id.refl :=
  by apply prop_is_set interval_prop

  @[hott] def transport_over_hmtpy {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β) (g₁ g₂ : β → γ) (h : α → γ)
    (p : g₁ = g₂) (H : g₁ ∘ f ~ h) (x : α) :
    equiv.transport (λ (g : β → γ), g ∘ f ~ h) p H x =
    @equiv.transport (β → γ) (λ (g : β → γ), g (f x) = h x) g₁ g₂ p (H x) :=
  begin apply happly, apply equiv.transport_over_pi end

  @[hott] def bool_to_interval (f : bool → bool → bool) (a b : I) : I :=
  lift (λ a, lift (discrete ∘ f a) interval_prop b) interval_prop a

  @[hott] def neg : I → I := interval.rec i₁ i₀ seg⁻¹
  instance : has_neg I := ⟨neg⟩

  @[hott] def min (a b : I) : I :=
  lift (begin intro x, cases x, exact i₀, exact a end)
        interval_prop b

  @[hott] def max (a b : I) : I :=
  lift (begin intro x, cases x, exact a, exact i₁ end)
        interval_prop b

  notation r `∧`:70 s := min r s
  notation r `∨`:70 s := max r s

  @[hott] def elim {α : Type u} {a b : α} (p : a = b) : I → α := rec a b p
  @[hott] def lam  {α : Type u} (f : I → α) : f 0 = f 1 := f # seg

  @[hott] def conn_and {α : Type u} {a b : α}
    (p : a = b) : Π i, a = elim p i :=
  λ i, lam (λ j, elim p (i ∧ j))

  @[hott] def cong {α : Type u} {β : Type v} {a b : α}
    (f : α → β) (p : a = b) : f a = f b :=
  lam (λ i, f (elim p i))

  @[hott] noncomputable def cong_refl {α : Type u} {β : Type v}
    {a : α} (f : α → β) : cong f (idp a) = idp (f a) := begin
    transitivity, apply types.equiv.map_over_comp,
    transitivity, apply Id.map, apply recβrule, trivial
  end

  @[hott] noncomputable def map_eq_cong {α : Type u} {β : Type v} {a b : α}
    (f : α → β) (p : a = b) : f # p = cong f p :=
  begin induction p, symmetry, apply cong_refl end

  @[hott] noncomputable def neg_neg : Π x, neg (neg x) = x :=
  interval.ind Id.refl Id.refl (calc
    equiv.transport (λ x, neg (neg x) = x) seg (idp i₀) =
    (@Id.map I I i₁ i₀ (neg ∘ neg) seg⁻¹) ⬝ idp i₀ ⬝ seg :
      by apply equiv.transport_over_involution
    ... = neg # (neg # seg⁻¹) ⬝ idp i₀ ⬝ seg :
      begin apply Id.map (λ p, p ⬝ idp i₀ ⬝ seg),
            apply equiv.map_over_comp end
    ... = neg # (neg # seg)⁻¹ ⬝ idp i₀ ⬝ seg :
      begin apply Id.map (λ p, p ⬝ idp i₀ ⬝ seg),
            apply Id.map, apply Id.map_inv end
    ... = neg # seg⁻¹⁻¹ ⬝ idp i₀ ⬝ seg :
      begin apply Id.map (λ p, p ⬝ idp i₀ ⬝ seg),
            apply Id.map, apply Id.map ground_zero.types.Id.symm,
            apply interval.recβrule end
    ... = neg # seg ⬝ idp i₀ ⬝ seg :
      begin apply Id.map (λ (p : i₀ = i₁), neg # p ⬝ idp i₀ ⬝ seg),
            apply Id.inv_inv end
    ... = seg⁻¹ ⬝ idp i₀ ⬝ seg :
      begin apply Id.map (λ p, p ⬝ idp i₀ ⬝ seg),
            apply interval.recβrule end
    ... = seg⁻¹ ⬝ seg :
      begin apply Id.map (λ p, p ⬝ seg),
            apply Id.refl_right end
    ... = idp i₁ : by apply Id.inv_comp)

  @[hott] def neg_neg' (x : I) : neg (neg x) = x :=
  (conn_and seg⁻¹ (neg x))⁻¹ ⬝ contr_right x

  @[hott] noncomputable def twist : I ≃ I :=
  ⟨neg, ⟨⟨neg, neg_neg⟩, ⟨neg, neg_neg⟩⟩⟩

  @[hott] noncomputable def line_rec {α : Type u} (p : I → α) :
    interval.rec (p 0) (p 1) (p # seg) = p :> I → α := begin
    apply theorems.funext, intro x, fapply interval.ind _ _ _ x,
    { refl }, { refl },
    { apply ground_zero.types.Id.trans,
      apply equiv.transport_over_hmtpy,
      transitivity, { apply Id.map ( ⬝ p # seg), apply Id.refl_right },
      transitivity,
      { apply Id.map (⬝ p # seg), transitivity,
        { apply Id.map_inv },
        { apply Id.map, apply interval.recβrule } },
      transitivity, { apply Id.map, symmetry, apply Id.map_inv p },
      transitivity, { symmetry, apply equiv.map_functoriality p },
      transitivity, { apply Id.map, apply Id.inv_comp },
      trivial }
  end

  @[hott] noncomputable def transport_over_seg {α : Type u} (π : α → Type v)
    {a b : α} (p : a = b :> α) (u : π a) :
    @equiv.transport I (λ (i : I), π (interval.elim p i))
      0 1 interval.seg u = equiv.subst p u :> π b := begin
    transitivity, apply equiv.transport_comp,
    transitivity, apply Id.map (λ p, equiv.subst p u),
    apply interval.recβrule, trivial
  end

  @[hott] noncomputable def transportconst_with_seg
    {α β : Type u} (p : α = β) (x : α) :
    @equiv.transport I (interval.elim p) 0 1 interval.seg x =
      equiv.subst p x :> β := begin
    transitivity, apply equiv.transport_to_transportconst,
    transitivity, apply Id.map (λ p, equiv.transportconst p x),
    apply interval.recβrule, induction p, trivial
  end
end interval

end HITs
end ground_zero