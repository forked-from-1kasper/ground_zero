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
    α → {α} → {{α}} → ...

  * https://github.com/fpvandoorn/leansnippets/blob/master/truncation.hlean
  * https://github.com/fpvandoorn/leansnippets/blob/master/cpp.hlean (we use this proof here)
  * https://homotopytypetheory.org/2015/07/28/constructing-the-propositional-truncation-using-nonrecursive-hits/
  * https://homotopytypetheory.org/2016/01/08/colimits-in-hott/
  * https://arxiv.org/pdf/1512.02274
-/

def Merely (α : Type u) :=
Colimit (Generalized.rep α) (Generalized.dep α)

notation "∥" α "∥" => Merely α

namespace Merely
  def elem {α : Type u} (x : α) : ∥α∥ :=
  Colimit.inclusion 0 x

  section
    variable {α : Type u} {π : ∥α∥ → Type v} (elemπ : Π x, π (elem x)) (uniqπ : Π x, prop (π x))

    hott def resp : Π (n : ℕ) (x : Generalized.rep α n), π (Colimit.incl x)
    | Nat.zero,   x => elemπ x
    | Nat.succ n, w => @Generalized.ind _ (λ x, π (Colimit.inclusion (n + 1) x))
                         (λ x, subst (Colimit.glue x)⁻¹ (resp n x))
                         (λ a b, uniqπ _ _ _) w

    hott def ind : Π x, π x :=
    begin intro x; fapply Colimit.ind; apply resp elemπ uniqπ; intros; apply uniqπ end
  end

  attribute [eliminator] ind

  hott def rec {α : Type u} {β : Type v} (H : prop β) (f : α → β) : ∥α∥ → β :=
  ind f (λ _, H)

  hott def weakUniq {α : Type u} (x y : α) : @Types.Id ∥α∥ (elem x) (elem y) :=
  begin
    transitivity; { symmetry; apply Colimit.glue }; symmetry;
    transitivity; { symmetry; apply Colimit.glue };
    apply map; apply Generalized.glue
  end

  hott def incl {α : Type u} {n : ℕ} :=
  @Colimit.incl (Generalized.rep α) (Generalized.dep α) n

  hott def glue {α : Type u} {n : ℕ} {x : Generalized.rep α n} :
    incl (Generalized.dep α n x) = incl x :=
  Colimit.glue x

  hott def exactNth {α : Type u} (a : α) : Π n, Generalized.rep α n
  | Nat.zero   => a
  | Nat.succ n => Generalized.dep α n (exactNth a n)

  hott def nthGlue {α : Type u} (a : α) : Π n, incl (exactNth a n) = @incl α 0 a
  | Nat.zero   => idp _
  | Nat.succ n => Colimit.glue (exactNth a n) ⬝ nthGlue a n

  hott def inclUniq {α : Type u} {n : ℕ} (a b : Generalized.rep α n) : incl a = incl b :=
  calc incl a = incl (Generalized.dep α n a) : glue⁻¹
          ... = incl (Generalized.dep α n b) : Id.map incl (Generalized.glue a b)
          ... = incl b                       : glue

  hott def inclZeroEqIncl {α : Type u} {n : ℕ} (x : α)
    (y : Generalized.rep α n) : @incl α 0 x = incl y :=
  calc @incl α 0 x = incl (exactNth x n) : (nthGlue x n)⁻¹
               ... = incl y              : inclUniq (exactNth x n) y

  hott def weaklyConstantAp {α : Type u} {β : Type v} (f : α → β)
    {a b : α} (p q : a = b) (H : Π a b, f a = f b) : Id.map f p = Id.map f q :=
  let L : Π {u v : α} (r : u = v), (H a u)⁻¹ ⬝ H a v = Id.map f r :=
  begin intros u v r; induction r; apply Types.Id.invComp end; (L p)⁻¹ ⬝ L q

  hott def congClose {α : Type u} {n : ℕ} {a b : Generalized.rep α n} (p : a = b) :
    glue⁻¹ ⬝ Id.map incl (Id.map (Generalized.dep α n) p) ⬝ glue = Id.map incl p :=
  begin
    induction p; transitivity; { symmetry; apply Id.assoc };
    apply Equiv.rewriteComp; symmetry; apply Id.reflRight
  end

  hott def congOverPath {α : Type u} {n : ℕ} {a b : Generalized.rep α n}
    (p q : a = b) : Id.map incl p = Id.map incl q :=
  weaklyConstantAp incl p q inclUniq

  hott def glueClose {α : Type u} {n : ℕ} {a b : Generalized.rep α n} :
      glue⁻¹ ⬝ Id.map incl (Generalized.glue (Generalized.dep α n a) (Generalized.dep α n b)) ⬝ glue
    = Id.map incl (Generalized.glue a b) :=
  begin
    symmetry; transitivity; { symmetry; apply @congClose α (n + 1) _ _ (Generalized.glue a b) };
    apply map (· ⬝ glue); apply map; apply congOverPath
  end

  hott def inclUniqClose {α : Type u} {n : ℕ} (a b : Generalized.rep α n) :
    glue⁻¹ ⬝ inclUniq (Generalized.dep α n a) (Generalized.dep α n b) ⬝ glue = inclUniq a b :=
  Id.map (· ⬝ glue) (Id.map _ glueClose)

  hott def uniq {α : Type u} : prop ∥α∥ :=
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

  hott def lift {α : Type u} {β : Type v} (f : α → β) : ∥α∥ → ∥β∥ :=
  rec uniq (elem ∘ f)

  hott def rec₂ {α : Type u} {β : Type v} {γ : Type w} (H : prop γ)
    (φ : α → β → γ) : ∥α∥ → ∥β∥ → γ :=
  @rec α (∥β∥ → γ) (Structures.implProp H) (rec H ∘ φ)

  hott def lift₂ {α : Type u} {β : Type v} {γ : Type w}
    (φ : α → β → γ) : ∥α∥ → ∥β∥ → ∥γ∥ :=
  rec₂ uniq (λ a b, elem (φ a b))

  hott def equivIffTrunc {α β : Type u}
    (f : α → β) (g : β → α) : ∥α∥ ≃ ∥β∥ :=
  ⟨lift f, (⟨lift g, λ _, uniq _ _⟩, ⟨lift g, λ _, uniq _ _⟩)⟩

  def diag {α : Type u} (a : α) : α × α := ⟨a, a⟩

  hott def productIdentity {α : Type u} : ∥α∥ ≃ ∥α × α∥ :=
  equivIffTrunc diag Prod.fst

  hott def uninhabitedImpliesTruncUninhabited {α : Type u} : ¬α → ¬∥α∥ :=
  rec Structures.emptyIsProp
end Merely

end GroundZero.HITs