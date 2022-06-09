import GroundZero.HITs.Generalized
import GroundZero.HITs.Colimit
import GroundZero.Structures

open GroundZero.Types.Equiv (subst apd pathoverFromTrans)
open GroundZero.Structures (prop contr lemContr)
open GroundZero.Types.Id
open GroundZero.Types

namespace GroundZero.HITs
universe u v w

/-
  Propositional truncation is colimit of a following sequence:
    A → {A} → {{A}} → ...

  * https://github.com/fpvandoorn/leansnippets/blob/master/truncation.hlean
  * https://github.com/fpvandoorn/leansnippets/blob/master/cpp.hlean (we use this proof here)
  * https://homotopytypetheory.org/2015/07/28/constructing-the-propositional-truncation-using-nonrecursive-hits/
  * https://homotopytypetheory.org/2016/01/08/colimits-in-hott/
  * https://arxiv.org/pdf/1512.02274
-/

def Merely (A : Type u) :=
Colimit (Generalized.rep A) (Generalized.dep A)

notation "∥" A "∥" => Merely A

namespace Merely
  def elem {A : Type u} (x : A) : ∥A∥ :=
  Colimit.inclusion 0 x

  section
    variable {A : Type u} {B : ∥A∥ → Type v} (elemπ : Π x, B (elem x)) (uniqπ : Π x, prop (B x))

    hott def resp : Π (n : ℕ) (x : Generalized.rep A n), B (Colimit.incl x)
    | Nat.zero,   x => elemπ x
    | Nat.succ n, w => @Generalized.ind _ (λ x, B (Colimit.inclusion (n + 1) x))
                         (λ x, subst (Colimit.glue x)⁻¹ (resp n x))
                         (λ a b, uniqπ _ _ _) w

    hott def ind : Π x, B x :=
    begin intro x; fapply Colimit.ind; apply resp elemπ uniqπ; intros; apply uniqπ end
  end

  attribute [eliminator] ind

  hott def rec {A : Type u} {B : Type v} (H : prop B) (f : A → B) : ∥A∥ → B :=
  ind f (λ _, H)

  hott def weakUniq {A : Type u} (x y : A) : @Types.Id ∥A∥ (elem x) (elem y) :=
  begin
    transitivity; { symmetry; apply Colimit.glue }; symmetry;
    transitivity; { symmetry; apply Colimit.glue };
    apply map; apply Generalized.glue
  end

  hott def incl {A : Type u} {n : ℕ} :=
  @Colimit.incl (Generalized.rep A) (Generalized.dep A) n

  hott def glue {A : Type u} {n : ℕ} {x : Generalized.rep A n} :
    incl (Generalized.dep A n x) = incl x :=
  Colimit.glue x

  hott def exactNth {A : Type u} (a : A) : Π n, Generalized.rep A n
  | Nat.zero   => a
  | Nat.succ n => Generalized.dep A n (exactNth a n)

  hott def nthGlue {A : Type u} (a : A) : Π n, incl (exactNth a n) = @incl A 0 a
  | Nat.zero   => idp _
  | Nat.succ n => Colimit.glue (exactNth a n) ⬝ nthGlue a n

  hott def inclUniq {A : Type u} {n : ℕ} (a b : Generalized.rep A n) : incl a = incl b :=
  calc incl a = incl (Generalized.dep A n a) : glue⁻¹
          ... = incl (Generalized.dep A n b) : Id.map incl (Generalized.glue a b)
          ... = incl b                       : glue

  hott def inclZeroEqIncl {A : Type u} {n : ℕ} (x : A)
    (y : Generalized.rep A n) : @incl A 0 x = incl y :=
  calc @incl A 0 x = incl (exactNth x n) : (nthGlue x n)⁻¹
               ... = incl y              : inclUniq (exactNth x n) y

  hott def weaklyConstantAp {A : Type u} {B : Type v} (f : A → B)
    {a b : A} (p q : a = b) (H : Π a b, f a = f b) : Id.map f p = Id.map f q :=
  let L : Π {u v : A} (r : u = v), (H a u)⁻¹ ⬝ H a v = Id.map f r :=
  begin intros u v r; induction r; apply Types.Id.invComp end; (L p)⁻¹ ⬝ L q

  hott def congClose {A : Type u} {n : ℕ} {a b : Generalized.rep A n} (p : a = b) :
    glue⁻¹ ⬝ Id.map incl (Id.map (Generalized.dep A n) p) ⬝ glue = Id.map incl p :=
  begin
    induction p; transitivity; { symmetry; apply Id.assoc };
    apply Equiv.rewriteComp; symmetry; apply Id.reflRight
  end

  hott def congOverPath {A : Type u} {n : ℕ} {a b : Generalized.rep A n}
    (p q : a = b) : Id.map incl p = Id.map incl q :=
  weaklyConstantAp incl p q inclUniq

  hott def glueClose {A : Type u} {n : ℕ} {a b : Generalized.rep A n} :
      glue⁻¹ ⬝ Id.map incl (Generalized.glue (Generalized.dep A n a) (Generalized.dep A n b)) ⬝ glue
    = Id.map incl (Generalized.glue a b) :=
  begin
    symmetry; transitivity; { symmetry; apply @congClose A (n + 1) _ _ (Generalized.glue a b) };
    apply map (· ⬝ glue); apply map; apply congOverPath
  end

  hott def inclUniqClose {A : Type u} {n : ℕ} (a b : Generalized.rep A n) :
    glue⁻¹ ⬝ inclUniq (Generalized.dep A n a) (Generalized.dep A n b) ⬝ glue = inclUniq a b :=
  Id.map (· ⬝ glue) (Id.map _ glueClose)

  hott def uniq {A : Type u} : prop ∥A∥ :=
  begin
    apply lemContr; fapply ind;
    { intro x; existsi elem x; fapply Colimit.ind <;> intros n y;
      { apply inclZeroEqIncl };
      { apply pathoverFromTrans; symmetry; transitivity;
        apply Id.map (_ ⬝ ·); symmetry; apply inclUniqClose;
        symmetry; transitivity; apply Id.map (· ⬝ _ ⬝ _); apply Id.explodeInv;
        -- TODO: use “iterate” here
        transitivity; symmetry; apply Id.assoc;
        transitivity; symmetry; apply Id.assoc;
        apply Id.map ((nthGlue x n)⁻¹ ⬝ ·); apply Id.assoc } };
    { intro x; apply Structures.contrIsProp }
  end

  hott def lift {A : Type u} {B : Type v} (f : A → B) : ∥A∥ → ∥B∥ :=
  rec uniq (elem ∘ f)

  hott def rec₂ {A : Type u} {B : Type v} {γ : Type w} (H : prop γ)
    (φ : A → B → γ) : ∥A∥ → ∥B∥ → γ :=
  @rec A (∥B∥ → γ) (Structures.implProp H) (rec H ∘ φ)

  hott def lift₂ {A : Type u} {B : Type v} {γ : Type w}
    (φ : A → B → γ) : ∥A∥ → ∥B∥ → ∥γ∥ :=
  rec₂ uniq (λ a b, elem (φ a b))

  hott def equivIffTrunc {A B : Type u}
    (f : A → B) (g : B → A) : ∥A∥ ≃ ∥B∥ :=
  ⟨lift f, (⟨lift g, λ _, uniq _ _⟩, ⟨lift g, λ _, uniq _ _⟩)⟩

  def diag {A : Type u} (a : A) : A × A := ⟨a, a⟩

  hott def productIdentity {A : Type u} : ∥A∥ ≃ ∥A × A∥ :=
  equivIffTrunc diag Prod.fst

  hott def uninhabitedImpliesTruncUninhabited {A : Type u} : ¬A → ¬∥A∥ :=
  rec Structures.emptyIsProp
end Merely

end GroundZero.HITs