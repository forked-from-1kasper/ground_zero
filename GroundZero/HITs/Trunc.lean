import GroundZero.HITs.Merely

open GroundZero.HITs.Interval (happly funext)
open GroundZero.Structures.hlevel (succ)
open GroundZero.Types.Id (ap)
open GroundZero.Proto (idfun)
open GroundZero.Structures
open GroundZero.Types

namespace GroundZero.HITs
universe u v w

private structure Trunc.aux (n : ℕ₋₂) (A : Type u) := (val : A)

attribute [nothott] Trunc.aux Trunc.aux.mk Trunc.aux.recOn Trunc.aux.rec Trunc.aux.val

def Trunc : ℕ₋₂ → Type u → Type u
| −2,            A => 𝟏
| −1,            A => ∥A∥
| succ (succ n), A => Trunc.aux n A

namespace Trunc
  variable {A : Type u} {n : ℕ₋₂}

  def elem : Π {n : ℕ₋₂} (x : A), Trunc n A
  | −2,            _ => ★
  | −1,            x => Merely.elem x
  | succ (succ n), x => @Trunc.aux.mk n A x

  opaque uniq (n : ℕ₋₂) : is-n-type (Trunc n A) :=
  match n with
  | −2            => unitIsContr
  | −1            => Merely.hprop
  | succ (succ n) => λ _ _, propIsNType (λ _ _, trustCoherence) n

  @[eliminator] def ind {B : Trunc n A → Type v} (elemπ : Π x, B (elem x))
    (uniqπ : Π x, is-n-type (B x)) : Π x, B x :=
  match n with
  | −2            => λ x, (uniqπ x).1
  | −1            => Merely.ind elemπ (λ _, minusOneEqvProp.forward (uniqπ _))
  | succ (succ n) => λ (Trunc.aux.mk x), elemπ x

  attribute [hottAxiom] Trunc elem uniq ind

  attribute [irreducible] Trunc

  notation "∥" A "∥₋₂" => Trunc −2 A
  notation "∥" A "∥₋₁" => Trunc −1 A

  macro:max "∥" A:term "∥" n:subscript : term => do
    `(Trunc $(← Meta.Notation.parseSubscript n) $A)

  macro "|" x:term "|" n:subscript : term => do
    `(@Trunc.elem _ $(← Meta.Notation.parseSubscript n) $x)

  hott lemma indβrule {B : ∥A∥ₙ → Type v} (elemπ : Π x, B (elem x))
    (uniqπ : Π x, is-n-type (B x)) (x : A) : ind elemπ uniqπ (elem x) = elemπ x :=
  begin
    match n with | −2 => _ | −1 => _ | succ (succ n) => _;
    apply (uniqπ (elem x)).2; reflexivity; reflexivity
  end

  section
    variable {B : Type v} (elemπ : A → B) (uniqπ : is-n-type B)

    hott def rec : ∥A∥ₙ → B := @ind A n (λ _, B) elemπ (λ _, uniqπ)

    hott corollary recβrule (x : A) : rec elemπ uniqπ (elem x) = elemπ x :=
    by apply indβrule
  end

  hott def elemClose {B : Type v} (G : is-n-type B)
    (f g : ∥A∥ₙ → B) (H : f ∘ elem = g ∘ elem) : f = g :=
  begin
    apply Theorems.funext; fapply ind <;> intro x;
    { exact ap (λ (f : A → B), f x) H };
    { apply hlevel.cumulative; assumption }
  end

  hott def nthTrunc (H : is-n-type A) : A ≃ ∥A∥ₙ :=
  begin
    existsi elem; apply Prod.mk <;> existsi rec id H;
    { intro; apply recβrule; };
    { apply Interval.happly; apply elemClose; apply uniq;
      apply Theorems.funext; intro; apply ap elem; apply recβrule; }
  end

  hott def setEquiv {A : Type u} (H : hset A) : A ≃ ∥A∥₀ :=
  begin apply nthTrunc; apply zeroEqvSet.left; assumption end

  hott def ap {A : Type u} {B : Type v} {n : ℕ₋₂} (f : A → B) : ∥A∥ₙ → ∥B∥ₙ :=
  rec (elem ∘ f) (uniq n)

  hott def ap₂ {A : Type u} {B : Type v} {C : Type w}
    {n : ℕ₋₂} (f : A → B → C) : ∥A∥ₙ → ∥B∥ₙ → ∥C∥ₙ :=
  rec (ap ∘ f) (piRespectsNType n (λ _, uniq n))

  hott lemma idmap {A : Type u} {n : ℕ₋₂} : ap idfun ~ @idfun ∥A∥ₙ :=
  begin
    fapply ind; intro; apply recβrule; intro;
    apply hlevel.cumulative; apply uniq
  end

  hott lemma apCom {A : Type u} {B : Type v} {C : Type w} {n : ℕ₋₂}
    (f : B → C) (g : A → B) : ap f ∘ ap g ~ @ap A C n (f ∘ g) :=
  begin
    fapply ind; intro; transitivity; apply Id.ap (ap _);
    apply recβrule; transitivity; apply recβrule; symmetry;
    apply recβrule; intro; apply hlevel.cumulative; apply uniq
  end

  hott theorem respectsEquiv {A : Type u} {B : Type v} {n : ℕ₋₂} (φ : A ≃ B) : ∥A∥ₙ ≃ ∥B∥ₙ :=
  ⟨ap φ.forward, (⟨ap φ.left,  (apCom _ _).trans ((happly (Id.ap ap (funext φ.leftForward))).trans  idmap)⟩,
                  ⟨ap φ.right, (apCom _ _).trans ((happly (Id.ap ap (funext φ.forwardRight))).trans idmap)⟩)⟩
end Trunc

end GroundZero.HITs
