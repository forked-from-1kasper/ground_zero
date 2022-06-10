import GroundZero.Algebra.Group.Factor
open GroundZero.Types.Equiv (biinv transport)
open GroundZero.Types.Id (map)
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Proto
open GroundZero

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

namespace GroundZero.Algebra

namespace Group
  inductive D₃.carrier
  | R₀ | R₁ | R₂
  | S₀ | S₁ | S₂
  attribute [eliminator] D₃.carrier.casesOn

  open D₃.carrier

  hott def D₃.inv : D₃.carrier → D₃.carrier
  | R₀ => R₀ | R₁ => R₂ | R₂ => R₁
  | S₀ => S₀ | S₁ => S₁ | S₂ => S₂

  hott def D₃.mul : D₃.carrier → D₃.carrier → D₃.carrier
  | R₀, R₀ => R₀ | R₀, R₁ => R₁ | R₀, R₂ => R₂
  | R₀, S₀ => S₀ | R₀, S₁ => S₁ | R₀, S₂ => S₂
  | R₁, R₀ => R₁ | R₁, R₁ => R₂ | R₁, R₂ => R₀
  | R₁, S₀ => S₁ | R₁, S₁ => S₂ | R₁, S₂ => S₀
  | R₂, R₀ => R₂ | R₂, R₁ => R₀ | R₂, R₂ => R₁
  | R₂, S₀ => S₂ | R₂, S₁ => S₀ | R₂, S₂ => S₁
  | S₀, R₀ => S₀ | S₀, R₁ => S₂ | S₀, R₂ => S₁
  | S₀, S₀ => R₀ | S₀, S₁ => R₂ | S₀, S₂ => R₁
  | S₁, R₀ => S₁ | S₁, R₁ => S₀ | S₁, R₂ => S₂
  | S₁, S₀ => R₁ | S₁, S₁ => R₀ | S₁, S₂ => R₂
  | S₂, R₀ => S₂ | S₂, R₁ => S₁ | S₂, R₂ => S₀
  | S₂, S₀ => R₂ | S₂, S₁ => R₁ | S₂, S₂ => R₀

  instance D₃.hasOne : OfNat D₃.carrier (Nat.succ Nat.zero) := ⟨R₀⟩
  instance D₃.hasMul : Mul D₃.carrier := ⟨D₃.mul⟩

  def D₃.elim {β : Type u} (b₁ b₂ b₃ b₄ b₅ b₆ : β) (d : D₃.carrier) : β :=
  @D₃.carrier.casesOn (λ _, β) d b₁ b₂ b₃ b₄ b₅ b₆

  hott def D₃ : Group :=
  begin
    fapply Group.intro; exact D₃.carrier; apply Hedberg;
    intros x y; induction x <;> induction y <;>
    (first | apply Sum.inl; reflexivity |
      apply Sum.inr; intro H; apply ffNeqTt; symmetry; first
      | apply Id.map (D₃.elim true  false false false false false) H
      | apply Id.map (D₃.elim false true  false false false false) H
      | apply Id.map (D₃.elim false false true  false false false) H
      | apply Id.map (D₃.elim false false false true  false false) H
      | apply Id.map (D₃.elim false false false false false true)  H
      | apply Id.map (D₃.elim false false false false true  false) H);
    exact D₃.mul; exact D₃.inv; exact R₀;
    { intro a b c; induction a <;> induction b <;> induction c <;> reflexivity };
    repeat { intro a; induction a <;> reflexivity }
  end

  hott def A₃.set : D₃.subset :=
  ⟨D₃.elim 𝟏 𝟏 𝟏 𝟎 𝟎 𝟎, begin
    intro (x : D₃.carrier); induction x <;>
    first | apply Structures.unitIsProp
          | apply Structures.emptyIsProp
  end⟩

  hott def A₃ : D₃.normal :=
  ⟨begin
    fapply Group.subgroup.mk; exact A₃.set; apply ★;
    { intro (a : D₃.carrier) (b : D₃.carrier) p q;
      induction a <;> induction b <;>
      (first | induction p using Unit.casesOn
             | induction p using Proto.Empty.casesOn) <;>
      (first | induction q using Unit.casesOn
             | induction q using Proto.Empty.casesOn) <;> apply ★ };
    { intro (a : D₃.carrier) p <;> induction a <;>
      (first | induction p using Unit.casesOn
             | induction p using Proto.Empty.casesOn) <;> apply ★ }
  end,
  begin
    intro (g : D₃.carrier) (h : D₃.carrier) p;
    induction g <;> induction h <;>
    (first | induction p using Unit.casesOn
           | induction p using Proto.Empty.casesOn) <;> apply ★
  end⟩

  def D₃.inj : D₃.carrier → factorLeft D₃ A₃ := @Factor.incl D₃ A₃

  hott def Z₂.encode : Z₂.carrier → factorLeft D₃ A₃
  | false => D₃.inj R₀
  | true  => D₃.inj S₀

  hott def Z₂.decode : factorLeft D₃ A₃ → Z₂.carrier :=
  begin
    fapply GroundZero.HITs.Quotient.rec;
    exact D₃.elim false false false true true true;
    intros x y H <;> induction x <;> induction y <;>
    induction H <;> reflexivity; apply Z₂.set
  end

  noncomputable hott def Z₂.iso : Z₂ ≅ D₃\A₃ :=
  begin
    fapply mkiso; exact Z₂.encode;
    { intros x y; induction x <;> induction y <;> reflexivity };
    apply Prod.mk <;> existsi Z₂.decode;
    { intro x; induction x <;> reflexivity };
    { fapply HITs.Quotient.ind;
      { intro x; induction x <;> apply HITs.Quotient.sound <;> exact ★ };
      { intros x y H; apply HITs.Quotient.set };
      { intro; apply Structures.propIsSet;
        apply HITs.Quotient.set } }
  end
end Group

end GroundZero.Algebra