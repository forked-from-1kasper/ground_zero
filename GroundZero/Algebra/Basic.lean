import GroundZero.Types.Ens

open GroundZero.Types GroundZero.Structures
open GroundZero.HITs.Interval (happly)
open GroundZero.Types.Equiv
open GroundZero

/-
  Magma, semigroup, monoid, group, abelian group.
  * HoTT 6.11
-/

namespace GroundZero.Algebra
  universe u v u' v' w

  hott def zeroeqv {A : Type u} (H : hset A) : 0-Type :=
  ⟨A, zeroEqvSet.left H⟩

  macro "propauto" : tactic =>
    `(repeat { apply piProp; intro }; apply p)

  def algop (deg : ℕ) (A : Type u) :=
  vect A deg → A

  def algrel (deg : ℕ) (A : Type u) :=
  vect A deg → Ω

  section
    variable {ι : Type u} {υ : Type v} (deg : ι + υ → ℕ)

    def Algebra (A : Type w) :=
    (Π i, algop  (deg (Sum.inl i)) A) × -- Algebraic operations
    (Π i, algrel (deg (Sum.inr i)) A)   -- relations

    def Alg := Σ (A : 0-Type), Algebra deg A.1

    noncomputable hott def Algebra.hset {A : Type w} (H : hset A) : hset (Algebra deg A) :=
    begin
      apply prodHset;
      { apply piHset; intro; apply piHset; intro; apply H };
      { apply piHset; intro; apply piHset; intro; apply Theorems.Equiv.propsetIsSet }
    end
  end

  section
    variable {ι : Type u} {υ : Type v} {deg : ι + υ → ℕ}

    section
      variable (A : Alg deg)
      def Alg.carrier := A.1.1
      def Alg.op      := A.2.1
      def Alg.rel     := A.2.2
      def Alg.zero    := A.1
      def Alg.subset  := Ens A.carrier
      def Alg.univ    := Ens.univ A.carrier

      hott def Alg.hset : hset A.carrier :=
      zeroEqvSet.forward A.1.2
    end

    def mapping (Γ Λ : Alg deg) :=
    Γ.carrier → Λ.carrier

    infix:51 " →ᴬ " => mapping

    hott def respects {Γ Λ : Alg deg} (f : Γ.carrier → Λ.carrier) :=
    (Π i v, f (Γ.op i v) = Λ.op i (v.map f)) ×
    (Π i v, Γ.rel i v = Λ.rel i (v.map f))

    noncomputable hott def respects.prop {Γ Λ : Alg deg}
      (f : Γ →ᴬ Λ) : prop (respects f) :=
    begin
      apply productProp <;> apply piProp <;> intro <;> apply piProp <;> intro;
      apply Alg.hset; apply Theorems.Equiv.propsetIsSet
    end

    hott def respects.comp {Γ Λ Δ : Alg deg} {f : Γ →ᴬ Λ} {g : Λ →ᴬ Δ} :
      respects g → respects f → respects (g ∘ f) :=
    begin
      intros p q; apply Prod.mk <;> intros;
      { transitivity; apply Id.map g; apply q.1;
        transitivity; apply p.1;
        apply Id.map; apply vect.comp };
      { transitivity; apply q.2;
        transitivity; apply p.2;
        apply Id.map; apply vect.comp }
    end

    hott def Hom (Γ Λ : Alg deg) :=
    Σ (φ : Γ →ᴬ Λ), respects φ

    def Hom.ap {Γ Λ : Alg deg} : Hom Γ Λ → (Γ →ᴬ Λ) := Sigma.fst

    def Hom.comp {Γ Λ Δ : Alg deg} (g : Hom Λ Δ) (f : Hom Γ Λ) : Hom Γ Δ :=
    ⟨g.1 ∘ f.1, respects.comp g.2 f.2⟩

    infix:60 " ⋅ " => Hom.comp

    hott def Hom.id (Γ : Alg deg) : Hom Γ Γ :=
    begin
      existsi Proto.idfun; apply Prod.mk <;> intros i v <;> symmetry;
      apply Id.map (Γ.op i);  apply vect.id;
      apply Id.map (Γ.rel i); apply vect.id
    end

    noncomputable hott def Hom.funext {Γ Λ : Alg deg} :
      Π {f g : Hom Γ Λ}, f.ap ~ g.ap → f = g :=
    begin
      intro ⟨f, F⟩ ⟨g, G⟩ p; fapply Sigma.prod;
      apply Theorems.funext; exact p; apply respects.prop
    end

    hott def idhom {Γ Λ : Alg deg} {f g : Hom Γ Λ} : f = g → f.ap ~ g.ap :=
    begin intro p; induction p; apply Homotopy.id end

    noncomputable hott def Hom.hset {Γ Λ : Alg deg} : hset (Hom Γ Λ) :=
    begin
      fapply hsetRespectsSigma;
      { apply piHset; intro; apply Λ.hset };
      { intro f; apply propIsSet; apply respects.prop }
    end

    hott def Iso (Γ Λ : Alg deg) :=
    Σ (φ : Γ →ᴬ Λ), respects φ × biinv φ

    def Iso.ap {Γ Λ : Alg deg} : Iso Γ Λ → (Γ →ᴬ Λ) := Sigma.fst

    def Iso.eqv {Γ Λ : Alg deg} : Iso Γ Λ → Γ.carrier ≃ Λ.carrier :=
    λ φ, ⟨φ.ap, φ.2.2⟩

    hott def Iso.ofEquiv {Γ Λ : Alg deg} : Π (φ : Γ.carrier ≃ Λ.carrier), respects φ.1 → Iso Γ Λ :=
    λ ⟨φ, q⟩ p, ⟨φ, (p, q)⟩

    hott def Iso.ofHom {Γ Λ : Alg deg} : Π (φ : Hom Γ Λ), biinv φ.ap → Iso Γ Λ :=
    λ ⟨φ, p⟩ q, ⟨φ, (p, q)⟩

    noncomputable hott def Iso.ext {Γ Λ : Alg deg} {φ ψ : Iso Γ Λ} : φ.ap ~ ψ.ap → φ = ψ :=
    begin
      intro p; fapply Sigma.prod; apply Theorems.funext p;
      apply productProp; apply respects.prop;
      apply Theorems.Equiv.biinvProp
    end

    noncomputable hott def Iso.eqIffEqEqv {Γ Λ : Alg deg} (φ ψ : Iso Γ Λ) : φ.eqv = ψ.eqv → φ = ψ :=
    begin intro p; apply Iso.ext; apply happly; apply Id.map Sigma.fst p end

    hott def Iso.hom {Γ Λ : Alg deg} (φ : Iso Γ Λ) : Hom Γ Λ :=
    ⟨φ.ap, φ.2.1⟩

    noncomputable hott def Iso.hset {Γ Λ : Alg deg} : hset (Iso Γ Λ) :=
    begin
      apply hsetRespectsSigma;
      { apply piHset; intro; apply Λ.hset };
      { intro x; apply propIsSet;
        apply productProp; apply respects.prop;
        apply Theorems.Equiv.biinvProp }
    end

    hott def Iso.refl (Γ : Alg deg) : Iso Γ Γ :=
    begin
      fapply Iso.ofEquiv; reflexivity; apply Prod.mk <;> intros i v;
      { apply Id.map (Γ.op i);  symmetry; apply vect.id };
      { apply Id.map (Γ.rel i); symmetry; apply vect.id }
    end

    hott def Iso.symm {Γ Λ : Alg deg} : Iso Γ Λ → Iso Λ Γ :=
    begin
      intro f; have μ := Equiv.forwardLeft f.eqv;
      existsi f.eqv.left; apply Prod.mk;
      { apply Prod.mk <;> intros i v;
        { symmetry; transitivity; { symmetry; apply f.eqv.leftForward };
          transitivity; apply Id.map f.eqv.left; apply f.2.1.1;
          apply Id.map (f.eqv.left ∘ Λ.op i); transitivity;
          apply vect.comp; apply vect.idfunc; apply μ };
        { transitivity; apply Id.map (Λ.rel i);
          transitivity; symmetry; apply vect.idfunc (f.ap ∘ f.eqv.left);
          apply μ; symmetry; apply vect.comp; symmetry; apply f.2.1.2 } };
      { apply Prod.mk <;> existsi f.ap; apply μ; apply f.eqv.leftForward }
    end

    hott def Iso.trans {Γ Λ Δ : Alg deg} : Iso Γ Λ → Iso Λ Δ → Iso Γ Δ :=
    begin
      intros f g; existsi g.ap ∘ f.ap; apply Prod.mk;
      { apply respects.comp; exact g.2.1; exact f.2.1 };
      { apply Equiv.biinvTrans; exact f.2.2; exact g.2.2 }
    end

    instance : @Reflexive  (Alg deg) Iso := ⟨Iso.refl⟩
    instance : @Symmetric  (Alg deg) Iso := ⟨@Iso.symm _ _ _⟩
    instance : @Transitive (Alg deg) Iso := ⟨@Iso.trans _ _ _⟩

    hott def Algebra.ext {A B : Type w} (p : A = B) :
      Π (Γ : Algebra deg A) (Λ : Algebra deg B),
        (Π i, Γ.1 i =[p] Λ.1 i) → (Π i, Γ.2 i =[p] Λ.2 i) → Γ =[p] Λ :=
    begin
      intro ⟨Γ₁, Γ₂⟩ ⟨Λ₁, Λ₂⟩ ε δ; induction p;
      apply Product.prod <;> apply Theorems.funext <;>
      intro; apply ε; apply δ
    end

    hott def transportOverZeroPath : Π {A B : 0-Type} (C : Type u → Type v) (p : A.1 = B.1) (u : C A.1),
      transport (C ∘ Sigma.fst) (zeroPath p) u = @transport (Type u) C A.1 B.1 p u :=
    begin
      intro ⟨A, F⟩ ⟨B, G⟩ C (p : A = B) u; induction p;
      have ρ : F = G := ntypeIsProp 0 F G; induction ρ;
      transitivity; apply Equiv.transportToTransportconst; transitivity;
      apply Id.map (λ p, transportconst (Id.map (C ∘ Sigma.fst) p) u);
      apply zeroPathRefl; reflexivity
    end

    hott def Alg.ext {Γ Λ : Alg deg} (p : Γ.carrier = Λ.carrier)
      (μ : Π i, Γ.op i  =[algop  (deg (Sum.inl i)), p] Λ.op i)
      (η : Π i, Γ.rel i =[algrel (deg (Sum.inr i)), p] Λ.rel i) : Γ = Λ :=
    begin
      fapply Sigma.prod; apply zeroPath; exact p;
      transitivity; apply transportOverZeroPath (Algebra deg) p;
      apply Algebra.ext <;> assumption
    end

    noncomputable hott def equivCompSubst {A B : Type u} (φ : A ≃ B) :
      φ.1 ∘ transportconst (ua φ)⁻¹ = id :=
    begin
      apply Theorems.funext; intro x;
      transitivity; apply Id.map φ.1;
      transitivity; apply Equiv.substOverInvPath;
      apply ua.transportInvRule;
      apply Equiv.forwardLeft
    end

    noncomputable hott def uaPreservesOp {Γ Λ : Alg deg} :
      Π (φ : Iso Γ Λ) (i : ι), Γ.op i =[ua φ.eqv] Λ.op i :=
    begin
      intro ⟨φ, (p, q)⟩ i; apply Id.trans;
      apply transportOverFunctor (λ A, vect A (deg (Sum.inl i))) id;
      apply Theorems.funext; intro v;
      transitivity; apply ua.transportRule;
      transitivity; apply p.1; apply Id.map;
      transitivity; apply vect.subst;
      transitivity; apply Id.map (vect.map · v);
      apply equivCompSubst ⟨φ, q⟩; apply vect.id
    end

    noncomputable hott def uaPreservesRel {Γ Λ : Alg deg} :
      Π (φ : Iso Γ Λ) (i : υ), Γ.rel i =[algrel (deg (Sum.inr i)), ua φ.eqv] Λ.rel i :=
    begin
      intro ⟨φ, (p, q)⟩ i; apply Id.trans;
      apply transportOverFunctor (λ A, vect A (deg (Sum.inr i))) (λ _, Ω);
      apply Theorems.funext; intro v;
      transitivity; apply Id.map (subst (ua ⟨φ, q⟩));
      transitivity; apply p.2; apply Id.map (Λ.rel i);
      transitivity; apply vect.subst;
      transitivity; apply Id.map (vect.map · v);
      apply equivCompSubst ⟨φ, q⟩; apply vect.id; change transport _ _ _ = _;
      transitivity; apply Equiv.transportToTransportconst;
      transitivity; apply Id.map (transportconst · (Λ.rel i v));
      apply constmap; reflexivity
    end

    noncomputable hott def Alg.ua {Γ Λ : Alg deg} (φ : Iso Γ Λ) : Γ = Λ :=
    Alg.ext (GroundZero.ua φ.eqv) (uaPreservesOp φ) (uaPreservesRel φ)

    hott def Alg.eqcar {Γ Λ : Alg deg} : Γ = Λ → Γ.carrier = Λ.carrier :=
    λ p, @Id.map (0-Type) (Type _) _ _ Sigma.fst (Id.map Sigma.fst p)

    noncomputable hott def Alg.uaext : Π {Γ Λ : Alg deg} (φ : Iso Γ Λ), GroundZero.ua φ.eqv = Alg.eqcar (Alg.ua φ) :=
    begin
      intro ⟨⟨A, f⟩, (Γ₁, Γ₂)⟩ ⟨⟨B, g⟩, (Λ₁, Λ₂)⟩ φ;
      symmetry; change Id.map _ _ = _; transitivity; apply Id.map;
      apply Sigma.mapFstOverProd; apply Sigma.mapFstOverProd
    end

    noncomputable hott def Alg.inj {Γ Λ : Alg deg} {φ ψ : Iso Γ Λ} (p : Alg.ua φ = Alg.ua ψ) : φ = ψ :=
    begin
      apply Iso.eqIffEqEqv; transitivity; symmetry; apply ua.uaβrule;
      transitivity; apply Id.map; apply Alg.uaext;
      transitivity; apply Id.map (Equiv.idtoeqv ∘ Alg.eqcar);
      exact p; transitivity; apply Id.map Equiv.idtoeqv;
      symmetry; apply Alg.uaext; apply ua.uaβrule
    end

    hott def Alg.id {Γ Λ : Alg deg} (p : Γ = Λ) : Iso Γ Λ :=
    begin induction p; reflexivity end

    hott def transportOverProd {A : Type u} {B : A → Type v} {u v : Sigma B}
      (p₁ p₂ : u.1 = v.1) (q : Equiv.subst p₁ u.2 = v.2) (ε : p₁ = p₂) :
      Sigma.prod p₁ q = Sigma.prod p₂ (@transport (u.1 = v.1)
        (λ p, Equiv.subst p u.2 = v.2) p₁ p₂ ε q) :=
    begin induction ε; reflexivity end

    noncomputable hott def Alg.uaβrefl {Γ : Alg deg} : Alg.ua (Iso.refl Γ) = Id.refl :=
    begin
      change Alg.ext _ _ _ = _;
      change Sigma.prod _ _ = _;
      transitivity; apply transportOverProd;
      transitivity; transitivity; apply transportOverProd;
      apply ua.reflOnUa; apply Id.map (Sigma.prod Id.refl);
      change _ = Id.refl; apply propIsSet;
      apply ntypeIsProp; apply Sigma.prodRefl;
      transitivity; apply Id.map (Sigma.prod Id.refl);
      change _ = Id.refl; apply Algebra.hset;
      apply zeroEqvSet.forward Γ.1.2;
      apply Sigma.prodRefl
    end

    noncomputable hott def Alg.rinv {Γ Λ : Alg deg} (p : Γ = Λ) : Alg.ua (Alg.id p) = p :=
    begin induction p; apply Alg.uaβrefl end

    noncomputable hott def Alg.linv {Γ Λ : Alg deg} {φ : Iso Γ Λ} : Alg.id (Alg.ua φ) = φ :=
    begin apply Alg.inj; apply Alg.rinv end

    /--
      Related:

      “Universal Algebra in HoTT”
      Andreas Lynge and Bas Spitters
      * https://github.com/andreaslyn/hott-classes
      * http://www.ii.uib.no/~bezem/abstracts/TYPES_2019_paper_7

      “Isomorphism is equality”
      Thierry Coquand, Nils Anders Danielsson
      * https://www.sciencedirect.com/science/article/pii/S0019357713000694

      “Universal Algebra in UniMath”
      Gianluca Amato, Marco Maggesi, Maurizio Parton, Cosimo Perini Brogi
      * https://hott-uf.github.io/2020/HoTTUF_2020_paper_13.pdf

      “Formalization of universal Algebra in Agda”
      Emmanuel Gunther, Alejandro Gadea, and Miguel Pagano
      * https://www.sciencedirect.com/science/article/pii/S1571066118300768

      “Universal Algebra in type theory”
      Venanzio Capretta
      * https://link.springer.com/chapter/10.1007/3-540-48256-3_10
    -/
    noncomputable hott def Alg.univalence {Γ Λ : Alg deg} : Iso Γ Λ ≃ (Γ = Λ) :=
    begin existsi Alg.ua; apply Prod.mk <;> existsi Alg.id; apply Alg.linv; apply Alg.rinv end
  end

  hott def Magma : Type (u + 1) :=
  @Alg.{0, 0, u, 0} 𝟏 ⊥ (λ _, 2)

  namespace Magma
    hott def intro {A : Type u} (H : hset A) (φ : A → A → A) : Magma :=
    ⟨zeroeqv H, (λ _ (a, b, _), φ a b, λ i, nomatch i)⟩

    def φ (M : Magma) : M.carrier → M.carrier → M.carrier :=
    λ x y, M.op ★ (x, y, ★)

    hott def isCommutative (M : Magma) :=
    Π a b, M.φ a b = M.φ b a

    hott def isAssociative (M : Magma) :=
    Π a b c, M.φ (M.φ a b) c = M.φ a (M.φ b c)

    hott def isLeftUnital (M : Magma) :=
    Σ e, Π a, M.φ e a = a

    hott def isRightUnital (M : Magma) :=
    Σ e, Π a, M.φ a e = a

    hott def isUnital (M : Magma) :=
    Σ e, Π a, M.φ e a = a × M.φ a e = a 

    hott def isLeftInvertible (M : Magma) (e : M.carrier) :=
    Σ (ι : M →ᴬ M), Π a, M.φ (ι a) a = e

    hott def isRightInvertible (M : Magma) (e : M.carrier) :=
    Σ (ι : M →ᴬ M), Π a, M.φ a (ι a) = e

    hott def isGroup (M : Magma) :=
    M.isAssociative × Σ (w : M.isUnital), M.isLeftInvertible w.1

    hott def unitalProp (M : Magma) : prop M.isUnital :=
    begin
      intro w₁ w₂; fapply Sigma.prod; transitivity;
      symmetry; apply (w₂.2 w₁.1).1; apply (w₁.2 _).2;
      apply piProp; intro; apply productProp <;> apply M.hset
    end

    hott def assocProp (M : Magma) : prop M.isAssociative :=
    begin
      apply piProp; intro;
      apply piProp; intro;
      apply piProp; intro;
      apply M.hset
    end
  end Magma

  namespace Premonoid
    def signature : 𝟐 + ⊥ → ℕ
    | Sum.inl false => 0
    | Sum.inl true  => 2
  end Premonoid

  def Premonoid : Type (u + 1) :=
  Alg.{0, 0, u, 0} Premonoid.signature

  namespace Premonoid
    def e (M : Premonoid) : M.carrier :=
    M.op false ★

    def φ (M : Premonoid) : M.carrier → M.carrier → M.carrier :=
    λ x y, M.op true (x, y, ★)

    hott def magma (M : Premonoid) : Magma :=
    begin
      existsi M.1; apply Prod.mk;
      { intro; exact M.op true };
      { intro x; apply nomatch x }
    end
  end Premonoid

  namespace Pregroup
    inductive Arity : Type
    | nullary | unary | binary
    open Arity

    def signature : Arity + ⊥ → ℕ
    | Sum.inl nullary => 0
    | Sum.inl unary   => 1
    | Sum.inl binary  => 2
  end Pregroup

  def Pregroup : Type (u + 1) :=
  Alg.{0, 0, u, 0} Pregroup.signature

  namespace Pregroup
    hott def intro {A : Type u} (H : hset A)
      (φ : A → A → A) (ι : A → A) (e : A) : Pregroup :=
    ⟨zeroeqv H, (λ | Arity.nullary => λ _, e
                   | Arity.unary   => λ (a, _), ι a
                   | Arity.binary  => λ (a, b, _), φ a b,
                 λ i, nomatch i)⟩

    def e (G : Pregroup) : G.carrier :=
    G.op Arity.nullary ★

    def ι (G : Pregroup) : G →ᴬ G :=
    λ x, G.op Arity.unary (x, ★)

    def φ (G : Pregroup) : G.carrier → G.carrier → G.carrier :=
    λ x y, G.op Arity.binary (x, y, ★)

    hott def magma (G : Pregroup) : Magma :=
    begin
      existsi G.1; apply Prod.mk;
      { intro; exact G.op Arity.binary };
      { intro x; apply nomatch x }
    end

    hott def premonoid (G : Pregroup) : Premonoid :=
    begin
      existsi G.1; apply Prod.mk;
      { exact λ | false => G.op Arity.nullary
                | true  => G.op Arity.binary };
      { intro x; apply nomatch x }
    end

    variable (G : Pregroup)

    hott def isAssociative :=
    Π a b c, G.φ (G.φ a b) c = G.φ a (G.φ b c)

    hott def isLeftUnital  := Π a, G.φ G.e a = a
    hott def isRightUnital := Π a, G.φ a G.e = a

    hott def isLeftInvertible := Π a, G.φ (G.ι a) a = G.e

    hott def isCommutative := Π a b, G.φ a b = G.φ b a

    hott def isGroup := G.isAssociative × G.isLeftUnital × G.isRightUnital × G.isLeftInvertible

    hott def isAbelian := G.isGroup × G.isCommutative
  end Pregroup

  hott def Group := Σ (M : Magma), M.isGroup

  namespace Group
    variable (G : Group)

    hott def carrier := G.1.carrier
    hott def subset  := G.1.subset
    hott def hset    := G.1.hset
    hott def magma   := G.1

    hott def φ := G.1.φ
    hott def e := G.2.2.1.1
    hott def ι := G.2.2.2.1

    hott def mulAssoc : Π a b c, G.φ (G.φ a b) c = G.φ a (G.φ b c) := G.2.1

    hott def oneMul (a : G.carrier) : G.φ G.e a = a := (G.2.2.1.2 a).1
    hott def mulOne (a : G.carrier) : G.φ a G.e = a := (G.2.2.1.2 a).2

    hott def mulLeftInv : Π a, G.φ (G.ι a) a = G.e := G.2.2.2.2

    hott def isCommutative := G.1.isCommutative

    hott def Hom (G H : Group) := Algebra.Hom G.1 H.1

    hott def intro {A : Type u} (H : Structures.hset A)
      (φ : A → A → A) (ι : A → A) (e : A)
      (α : Π a b c, φ (φ a b) c = φ a (φ b c))
      (β₁ : Π a, φ e a = a) (β₂ : Π a, φ a e = a)
      (γ : Π a, φ (ι a) a = e) : Group :=
    ⟨Magma.intro H φ, (α, ⟨⟨e, λ a, (β₁ a, β₂ a)⟩, ⟨ι, γ⟩⟩)⟩
  end Group

  hott def Abelian := Σ (M : Magma), M.isGroup × M.isCommutative

  namespace Abelian
    variable (G : Abelian)

    hott def carrier := G.1.carrier
    hott def subset  := G.1.subset
    hott def hset    := G.1.hset
    hott def magma   := G.1

    hott def group : Group := ⟨G.1, G.2.1⟩

    hott def φ := G.1.φ
    hott def e := G.2.1.2.1.1
    hott def ι := G.2.1.2.2.1

    hott def mulAssoc : Π a b c, G.φ (G.φ a b) c = G.φ a (G.φ b c) := G.2.1.1

    hott def oneMul (a : G.carrier) : G.φ G.e a = a := (G.2.1.2.1.2 a).1
    hott def mulOne (a : G.carrier) : G.φ a G.e = a := (G.2.1.2.1.2 a).2

    hott def mulLeftInv : Π a, G.φ (G.ι a) a = G.e := G.2.1.2.2.2

    hott def mulComm : Π a b, G.φ a b = G.φ b a := G.2.2

    hott def Hom (G H : Abelian) := Algebra.Hom G.1 H.1

    hott def intro {A : Type u} (H : Structures.hset A)
      (φ : A → A → A) (ι : A → A) (e : A)
      (α : Π a b c, φ (φ a b) c = φ a (φ b c))
      (β₁ : Π a, φ e a = a) (β₂ : Π a, φ a e = a)
      (γ : Π a, φ (ι a) a = e) (δ : Π a b, φ a b = φ b a) : Abelian :=
    ⟨Magma.intro H φ, ((α, ⟨⟨e, λ a, (β₁ a, β₂ a)⟩, ⟨ι, γ⟩⟩), δ)⟩
  end Abelian

  notation:51 A " ≅ " B => Iso A.1 B.1
end GroundZero.Algebra