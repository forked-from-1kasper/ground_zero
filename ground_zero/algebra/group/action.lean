import ground_zero.HITs.quotient ground_zero.algebra.group.symmetric
open ground_zero.structures
open ground_zero.types
open ground_zero

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group
  @[hott] def left_action (G : pregroup) (α : Type u) :=
  Σ (φ : G.carrier → α → α), (Π x, φ G.e x = x) × (Π g h x, φ g (φ h x) = φ (G.φ g h) x)
  infix ` ⮎ `:20 := left_action

  @[hott] def left_action.id {G : pregroup} {α : Type u} (H : hset α)
    (φ ψ : G ⮎ α) : φ.fst ~ ψ.fst → φ = ψ :=
  begin
    intro p, induction φ with φ p₁, induction ψ with ψ p₂,
    fapply sigma.prod, apply theorems.funext, exact p, apply product_prop;
    { repeat { apply pi_prop, intro }, apply H }
  end

  @[hott] def right_action (G : pregroup) (α : Type u) :=
  Σ (φ : α → G.carrier → α), (Π x, φ x G.e = x) × (Π g h x, φ (φ x g) h = φ x (G.φ g h))
  infix ` ⮌ `:20 := right_action

  variables {G : pregroup} [group G]

  section
    variable {α : Type u} 

    @[hott] def right_action.associated : (G ⮎ α) → (G ⮌ α) :=
    λ ⟨φ, (p, q)⟩, ⟨λ x g, φ (G.ι g) x, (begin
      intro x, transitivity, apply Id.map (λ g, φ g x),
      symmetry, apply unit_inv, apply p
    end, begin
      intros g h x, transitivity,
      apply q, apply Id.map (λ g, φ g x),
      symmetry, apply inv_explode
    end)⟩

    def orbit (φ : G ⮎ α) (x : α) :=
    ground_zero.algebra.im (λ g, φ.fst g x)

    def Orb (φ : G ⮎ α) (x : α) :=
    (orbit φ x).subtype

    def orbitᵣ (φ : G ⮌ α) (x : α) :=
    ground_zero.algebra.im (φ.fst x)

    def Orbᵣ (φ : G ⮌ α) (x : α) :=
    (orbitᵣ φ x).subtype
  end

  @[hott] def S.ap {α : 0-Type} : S α ⮎ α.fst :=
  ⟨λ f x, f.fst x, (idp, λ ⟨g, G⟩ ⟨h, G⟩ x, idp (g (h x)))⟩

  @[hott] def left_action.cut {α : Type u} (φ : G.subgroup) :
    (G ⮎ α) → (Subgroup G φ ⮎ α) :=
  λ ⟨φ, (p, q)⟩, ⟨λ ⟨g, G⟩ x, φ g x, (p, λ ⟨g, G⟩ ⟨h, G⟩, q g h)⟩

  @[hott] def left_action.eqv {α : Type u} (φ : G ⮎ α) (n m : α) :=
  ∥(Σ g, φ.fst g n = m)∥

  @[hott] def left_action.refl {α : Type u} (φ : G ⮎ α) {a : α} : φ.eqv a a :=
  begin apply HITs.merely.elem, existsi G.e, apply φ.snd.fst end

  @[hott] def left_action.symm {α : Type u} (φ : G ⮎ α)
    {a b : α} : φ.eqv a b → φ.eqv b a :=
  begin
    apply HITs.merely.lift,
    intro p, induction p with g p, existsi G.ι g,
    transitivity, apply Id.map, exact Id.inv p,
    transitivity, apply φ.snd.snd,
    transitivity, apply Id.map (λ g, φ.fst g a),
    apply mul_left_inv, apply φ.snd.fst
  end

  @[hott] def left_action.trans {α : Type u} (φ : G ⮎ α)
    {a b c : α} : φ.eqv a b → φ.eqv b c → φ.eqv a c :=
  begin
    apply HITs.merely.lift₂, intros p q,
    induction p with g p, induction q with h q,
    existsi G.φ h g, transitivity, symmetry, apply φ.snd.snd,
    transitivity, apply Id.map, exact p, exact q
  end

  @[hott] def left_action.rel {α : Type u} (φ : G ⮎ α) : hrel α :=
  λ n m, ⟨φ.eqv n m, HITs.merely.uniq⟩

  @[hott] def left_action.eqrel {α : Type u} (φ : G ⮎ α) : eqrel α :=
  ⟨left_action.rel φ, (λ _, φ.refl, λ _ _, φ.symm, λ _ _ _, φ.trans)⟩

  @[hott] def orbit.subset {α : Type u} (φ : G ⮎ α) {a b : α}
    (p : φ.eqv a b) : orbit φ a ⊆ orbit φ b :=
  begin
    intro c, change φ.eqv a c → φ.eqv b c,
    intro q, apply φ.trans, apply φ.symm p, exact q
  end

  @[hott] def Orbits {α : Type u} (φ : G ⮎ α) :=
  HITs.quotient φ.eqrel

  @[hott] def transitive {α : Type u} (φ : G ⮎ α) :=
  Π a b, ∥(Σ g, φ.fst g a = b)∥

  @[hott] def free {α : Type u} (φ : G ⮎ α) :=
  Π x g h, φ.fst g x = φ.fst h x → g = h

  @[hott] def regular {α : Type u} (φ : G ⮎ α) :=
  Π a b, contr (Σ g, φ.fst g a = b)

  inductive marked (α : Type u) (β : Type v)
  | elem : α → marked
  | comp : β → marked → marked

  section
    private structure fga.aux (α : Type u) (G : pregroup) :=
    (val : marked α G.carrier)

    def fga (α : Type u) (G : pregroup) := fga.aux α G
  end

  namespace fga
    variables {α : Type u}
    attribute [nothott] fga.aux.rec_on fga.aux.rec aux.val

    @[hott] def elem : α → fga α G := aux.mk ∘ marked.elem
    @[safe] def φ (g : G.carrier) (x : fga α G) :=
    aux.mk (marked.comp g x.val)

    axiom unit  : Π (x : fga α G), φ G.e x = x
    axiom assoc : Π g h, Π (x : fga α G), φ g (φ h x) = φ (G.φ g h) x

    axiom ens : hset (fga α G)

    section
      variables (ψ : G ⮎ α) (H : hset α)
      include H

      def rec.aux : marked α G.carrier → α
      |  (marked.elem a)  := a
      | (marked.comp g x) := ψ.fst g (rec.aux x)
      @[safe] def rec : fga α G → α := rec.aux ψ (λ _ _, H) ∘ aux.val
    end

    @[hott] noncomputable def act : G ⮎ fga α G :=
    ⟨φ, (unit, assoc)⟩
  end fga

  @[hott] def pact {α : Type u} : G ⮎ G.carrier × α :=
  ⟨λ g ⟨h, x⟩, (G.φ g h, x),
   (λ ⟨g, x⟩, product.prod (G.one_mul g) (idp x),
    λ g h ⟨f, x⟩, product.prod (Id.inv (G.mul_assoc g h f)) (idp x))⟩

  @[hott] def regular.mk {α : Type u} (H : hset α)
    (φ : G ⮎ α) : transitive φ → free φ → regular φ :=
  begin
    intros f g a b, fapply HITs.merely.rec _ _ (f a b),
    { apply contr_is_prop },
    { intro p, existsi p,
      intro q, fapply sigma.prod,
      { apply g a, transitivity, exact p.snd,
        symmetry, exact q.snd },
      { apply H } }
  end

  @[hott] def regular.elim {α : Type u}
    (φ : G ⮎ α) : regular φ → transitive φ × free φ :=
  begin
    intro H, split,
    { intros a b, apply HITs.merely.elem,
      exact (H a b).point },
    { intros x g h p,
      apply @Id.map (Σ g, φ.fst g x = φ.fst h x) G.carrier
                    ⟨g, p⟩ ⟨h, Id.refl⟩ sigma.fst,
      apply contr_impl_prop, apply H }
  end

  @[hott] def regular.eqv {α : Type u} (H : hset α)
    (φ : G ⮎ α) : regular φ ≃ transitive φ × free φ :=
  begin
    apply prop_equiv_lemma,
    { repeat { apply pi_prop, intro },
      apply contr_is_prop },
    { apply product_prop;
      repeat { apply pi_prop, intro },
      { apply HITs.merely.uniq },
      { apply G.hset } },
    { apply regular.elim },
    { intro x, induction x,
      apply regular.mk; assumption }
  end
end group

end ground_zero.algebra