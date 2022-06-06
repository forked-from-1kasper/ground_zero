import GroundZero.Algebra.Group.Symmetric
import GroundZero.HITs.Quotient
open GroundZero.Structures
open GroundZero.Types
open GroundZero

namespace GroundZero.Algebra
universe u v w

namespace Group
  hott def leftAction (G : Pregroup) (α : Type u) :=
  Σ (φ : G.carrier → α → α), (Π x, φ G.e x = x) × (Π g h x, φ g (φ h x) = φ (G.φ g h) x)
  infix:20 " ⮎ " => leftAction

  hott def leftAction.id {G : Pregroup} {α : Type u} (H : hset α)
    (φ ψ : G ⮎ α) (p : φ.1 ~ ψ.1) : φ = ψ :=
  begin
    fapply Sigma.prod; apply Theorems.funext; exact p;
    apply productProp; apply piProp; intro; apply H;
    apply piProp; intro; apply piProp; intro; apply piProp; intro; apply H
  end

  hott def rightAction (G : Pregroup) (α : Type u) :=
  Σ (φ : α → G.carrier → α), (Π x, φ x G.e = x) × (Π g h x, φ (φ x g) h = φ x (G.φ g h))
  infix:20 " ⮌ " => rightAction

  variable {G : Pregroup} [Algebra.group G]

  section
    variable {α : Type u} 

    hott def rightAction.associated : (G ⮎ α) → (G ⮌ α) :=
    λ ⟨φ, (p, q)⟩, ⟨λ x g, φ (G.ι g) x, (begin
      intro x; transitivity; apply Id.map (φ · x);
      symmetry; apply unitInv; apply p
    end, begin
      intros g h x; transitivity;
      apply q; apply Id.map (φ · x);
      symmetry; apply invExplode
    end)⟩

    def orbit (φ : G ⮎ α) (x : α) :=
    GroundZero.Algebra.im (φ.1 · x)

    def Orb (φ : G ⮎ α) (x : α) :=
    (orbit φ x).subtype

    def orbitᵣ (φ : G ⮌ α) (x : α) :=
    GroundZero.Algebra.im (φ.1 x)

    def Orbᵣ (φ : G ⮌ α) (x : α) :=
    (orbitᵣ φ x).subtype
  end

  hott def S.ap {α : 0-Type} : S α ⮎ α.1 :=
  ⟨λ f x, f.1 x, (idp, λ ⟨g, G⟩ ⟨h, G⟩ x, idp (g (h x)))⟩

  hott def leftAction.cut {α : Type u} (φ : G.subgroup) :
    (G ⮎ α) → (Subgroup G φ ⮎ α) :=
  λ ⟨φ, (p, q)⟩, ⟨λ ⟨g, G⟩ x, φ g x, (p, λ ⟨g, G⟩ ⟨h, G⟩, q g h)⟩

  hott def leftAction.eqv {α : Type u} (φ : G ⮎ α) (n m : α) :=
  ∥(Σ g, φ.1 g n = m)∥

  hott def leftAction.refl {α : Type u} (φ : G ⮎ α) {a : α} : φ.eqv a a :=
  begin apply HITs.Merely.elem; existsi G.e; apply φ.2.1 end

  hott def leftAction.symm {α : Type u} (φ : G ⮎ α)
    {a b : α} : φ.eqv a b → φ.eqv b a :=
  begin
    apply HITs.Merely.lift;
    intro ⟨g, p⟩; existsi G.ι g;
    transitivity; apply Id.map; exact Id.inv p;
    transitivity; apply φ.2.2;
    transitivity; apply Id.map (φ.1 · a);
    apply G.mulLeftInv; apply φ.2.1
  end

  hott def leftAction.trans {α : Type u} (φ : G ⮎ α)
    {a b c : α} : φ.eqv a b → φ.eqv b c → φ.eqv a c :=
  begin
    apply HITs.Merely.lift₂; intro ⟨g, p⟩ ⟨h, q⟩;
    existsi G.φ h g; transitivity; symmetry; apply φ.2.2;
    transitivity; apply Id.map; exact p; exact q
  end

  hott def leftAction.rel {α : Type u} (φ : G ⮎ α) : hrel α :=
  λ n m, ⟨φ.eqv n m, HITs.Merely.uniq⟩

  hott def leftAction.eqrel {α : Type u} (φ : G ⮎ α) : eqrel α :=
  ⟨leftAction.rel φ, (λ _, φ.refl, λ _ _, φ.symm, λ _ _ _, φ.trans)⟩

  hott def orbit.subset {α : Type u} (φ : G ⮎ α) {a b : α}
    (p : φ.eqv a b) : orbit φ a ⊆ orbit φ b :=
  begin intros c G; apply φ.trans; apply φ.symm p; exact G end

  hott def Orbits {α : Type u} (φ : G ⮎ α) :=
  HITs.Quotient φ.eqrel

  hott def transitive {α : Type u} (φ : G ⮎ α) :=
  Π a b, ∥(Σ g, φ.fst g a = b)∥

  hott def free {α : Type u} (φ : G ⮎ α) :=
  Π x g h, φ.fst g x = φ.fst h x → g = h

  hott def regular {α : Type u} (φ : G ⮎ α) :=
  Π a b, contr (Σ g, φ.fst g a = b)

  inductive Marked (α : Type u) (β : Type v)
  | elem : α → Marked α β
  | comp : β → Marked α β → Marked α β

  section
    private structure Fga.aux (α : Type u) (G : Pregroup) :=
    (val : Marked α G.carrier)

    def Fga (α : Type u) (G : Pregroup) := Fga.aux α G
  end

  namespace Fga
    variable {α : Type u}
    attribute [nothott] Fga.aux.recOn Fga.aux.rec aux.val

    hott def elem : α → Fga α G := aux.mk ∘ Marked.elem

    @[hottAxiom] def φ (g : G.carrier) (x : Fga α G) :=
    aux.mk (Marked.comp g x.val)

    axiom unit  : Π (x : Fga α G), φ G.e x = x
    axiom assoc : Π g h, Π (x : Fga α G), φ g (φ h x) = φ (G.φ g h) x

    axiom ens : hset (Fga α G)

    section
      variable (ψ : G ⮎ α)

      def rec.aux (H : hset α) : Marked α G.carrier → α
      | Marked.elem x   => x
      | Marked.comp g x => ψ.1 g (aux H x)

      @[hottAxiom] def rec (H : hset α) : Fga α G → α := rec.aux ψ H ∘ @aux.val α G
    end

    noncomputable hott def act : G ⮎ Fga α G :=
    ⟨φ, (unit, assoc)⟩
  end Fga

  hott def pact {α : Type u} : G ⮎ G.carrier × α :=
  ⟨λ g ⟨h, x⟩, (G.φ g h, x),
   (λ ⟨g, x⟩, Product.prod (G.oneMul g) (idp x),
    λ g h ⟨f, x⟩, Product.prod (Id.inv (G.mulAssoc g h f)) (idp x))⟩

  hott def regular.mk {α : Type u} (H : hset α)
    (φ : G ⮎ α) : transitive φ → free φ → regular φ :=
  begin
    intros f g a b; fapply HITs.Merely.rec _ _ (f a b);
    { apply contrIsProp };
    { intro p; existsi p;
      intro q; fapply Sigma.prod;
      { apply g a; transitivity; exact p.2;
        symmetry; exact q.2 };
      { apply H } }
  end

  hott def regular.elim {α : Type u}
    (φ : G ⮎ α) : regular φ → transitive φ × free φ :=
  begin
    intro H; apply Prod.mk;
    { intros a b; apply HITs.Merely.elem; exact (H a b).1 };
    { intros x g h p;
      apply @Id.map (Σ g, φ.fst g x = φ.fst h x) G.carrier
                    ⟨g, p⟩ ⟨h, Id.refl⟩ Sigma.fst;
      apply contrImplProp; apply H }
  end

  hott def regularIsProp {α : Type u} (φ : G ⮎ α) : prop (regular φ) :=
  begin apply piProp; intro; apply piProp; intro; apply contrIsProp end

  hott def transitiveIsProp {α : Type u} (φ : G ⮎ α) : prop (transitive φ) :=
  begin apply piProp; intro; apply piProp; intro; apply HITs.Merely.uniq end

  hott def freeIsProp {α : Type u} (φ : G ⮎ α) : prop (free φ) :=
  begin apply piProp; intro; apply piProp; intro; apply piProp; intro; apply piProp; intro; apply G.hset end

  hott def regular.eqv {α : Type u} (H : hset α)
    (φ : G ⮎ α) : regular φ ≃ transitive φ × free φ :=
  begin
    apply propEquivLemma; apply regularIsProp;
    apply productProp; apply transitiveIsProp; apply freeIsProp;
    apply regular.elim; intro w; apply regular.mk H φ w.1 w.2
  end
end Group

end GroundZero.Algebra