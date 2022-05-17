import ground_zero.algebra.group.factor
open ground_zero.types.equiv (biinv transport)
open ground_zero.types.Id (map)
open ground_zero.structures
open ground_zero.types
open ground_zero.proto
open ground_zero

/-
  Trivial group, symmetric group, cyclic group Z₂,
  dihedral group D₃, alternating group A₃ as its subgroup.
  * https://en.wikipedia.org/wiki/Trivial_group
  * https://en.wikipedia.org/wiki/Symmetric_group
  * https://en.wikipedia.org/wiki/Cyclic_group
  * https://en.wikipedia.org/wiki/Dihedral_group_of_order_6
  * https://en.wikipedia.org/wiki/Alternating_group

  Z₂ ≅ D₃\A₃ proof.
-/

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group
  inductive D₃.carrier
  | R₀ | R₁ | R₂
  | S₀ | S₁ | S₂
  open D₃.carrier

  @[hott] def D₃.inv : D₃.carrier → D₃.carrier
  | R₀ := R₀ | R₁ := R₂ | R₂ := R₁
  | S₀ := S₀ | S₁ := S₁ | S₂ := S₂

  @[hott] def D₃.mul : D₃.carrier → D₃.carrier → D₃.carrier
  | R₀ R₀ := R₀ | R₀ R₁ := R₁ | R₀ R₂ := R₂
  | R₀ S₀ := S₀ | R₀ S₁ := S₁ | R₀ S₂ := S₂
  | R₁ R₀ := R₁ | R₁ R₁ := R₂ | R₁ R₂ := R₀
  | R₁ S₀ := S₁ | R₁ S₁ := S₂ | R₁ S₂ := S₀
  | R₂ R₀ := R₂ | R₂ R₁ := R₀ | R₂ R₂ := R₁
  | R₂ S₀ := S₂ | R₂ S₁ := S₀ | R₂ S₂ := S₁
  | S₀ R₀ := S₀ | S₀ R₁ := S₂ | S₀ R₂ := S₁
  | S₀ S₀ := R₀ | S₀ S₁ := R₂ | S₀ S₂ := R₁
  | S₁ R₀ := S₁ | S₁ R₁ := S₀ | S₁ R₂ := S₂
  | S₁ S₀ := R₁ | S₁ S₁ := R₀ | S₁ S₂ := R₂
  | S₂ R₀ := S₂ | S₂ R₁ := S₁ | S₂ R₂ := S₀
  | S₂ S₀ := R₂ | S₂ S₁ := R₁ | S₂ S₂ := R₀

  @[hott] instance D₃.has_one : has_one D₃.carrier := ⟨R₀⟩
  @[hott] instance D₃.has_inv : has_inv D₃.carrier := ⟨D₃.inv⟩
  @[hott] instance D₃.has_mul : has_mul D₃.carrier := ⟨D₃.mul⟩

  def D₃.elim {β : Type u} : β → β → β → β → β → β → D₃.carrier → β :=
  @D₃.carrier.rec (λ _, β)

  @[hott] def D₃ : pregroup :=
  begin
    fapply pregroup.intro, exact D₃.carrier,
    apply Hedberg, intros x y, induction x; induction y;
    try { apply sum.inl, refl },
    repeat { apply sum.inr, intro p, apply ff_neq_tt, symmetry },
    repeat { apply (D₃.elim tt ff ff ff ff ff) # p },
    repeat { apply (D₃.elim ff tt ff ff ff ff) # p },
    repeat { apply (D₃.elim ff ff tt ff ff ff) # p },
    repeat { apply (D₃.elim ff ff ff tt ff ff) # p },
    repeat { apply (D₃.elim ff ff ff ff ff tt) # p },
    repeat { apply (D₃.elim ff ff ff ff tt ff) # p },
    exact D₃.mul, exact D₃.inv, exact R₀
  end

  @[hott] instance D₃.semigroup : semigroup D₃.magma :=
  ⟨begin intros a b c, induction a; induction b; induction c; trivial end⟩

  @[hott] instance D₃.monoid : monoid D₃.premonoid :=
  ⟨D₃.semigroup,
    begin intro a; induction a; trivial end,
    begin intro a; induction a; trivial end⟩

  @[hott] instance D₃.group : group D₃ :=
  ⟨D₃.monoid, begin intro a, induction a; trivial end⟩

  @[hott] def A₃.set : D₃.subset :=
  ⟨D₃.elim 𝟏 𝟏 𝟏 𝟎 𝟎 𝟎, begin
    intros x, induction x,
    repeat { apply ground_zero.structures.unit_is_prop },
    repeat { apply ground_zero.structures.empty_is_prop }
  end⟩

  @[hott] def A₃ : D₃.subgroup :=
  begin
    fapply pregroup.subgroup.mk, exact A₃.set,
    { apply ★ },
    { intros a b p q, induction a; induction b;
      induction p; induction q; apply ★ },
    { intros a p, induction a; induction p; apply ★ }
  end

  @[hott] instance A₃.normal : D₃ ⊵ A₃ :=
  begin
    split, intros g h p; induction g; induction h;
    induction p; apply ★
  end

  def D₃.inj : D₃.carrier → factor_left D₃ A₃ := @factor.incl D₃ _ A₃ _

  @[hott] def Z₂.encode : Z₂.carrier → factor_left D₃ A₃
  | ff := D₃.inj R₀
  | tt := D₃.inj S₀

  @[hott] def Z₂.decode : factor_left D₃ A₃ → Z₂.carrier :=
  begin
    fapply ground_zero.HITs.quotient.rec,
    { exact D₃.elim ff ff ff tt tt tt },
    { intros x y H; induction x; induction y; induction H; trivial },
    { intros a b, apply Z₂.set }
  end

  @[hott] noncomputable def Z₂.iso : Z₂ ≅ D₃\A₃ :=
  begin
    fapply mkiso, exact Z₂.encode,
    { intros x y, induction x; induction y; trivial },
    split; existsi Z₂.decode,
    { intro x, induction x; trivial },
    { fapply HITs.quotient.ind,
      { intro x, induction x; apply HITs.quotient.sound; exact ★ },
      { intros x y H, apply HITs.quotient.set },
      { intro x, apply structures.prop_is_set,
        apply HITs.quotient.set } }
  end
end group

end ground_zero.algebra