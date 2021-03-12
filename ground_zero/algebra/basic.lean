import ground_zero.types.ens
open ground_zero.types ground_zero.structures
open ground_zero.types.equiv (biinv transport)
open ground_zero (ua vect vect.id vect.idfunc vect.map vect.subst vect.comp)

hott theory

/-
  Magma, semigroup, monoid, group, abelian group.
  * HoTT 6.11
-/

namespace ground_zero.algebra
  universes u v u' v' w

  def zeroeqv {α : Type u} (H : hset α) : 0-Type :=
  ⟨α, zero_eqv_set.left (λ _ _, H)⟩

  meta def propauto :=
  `[ repeat { apply pi_prop, intro }, apply p ]

  def algop (deg : ℕ) (α : Type u) :=
  vect α deg → α

  def algrel (deg : ℕ) (α : Type u) :=
  vect α deg → propset

  section
    variables {ι : Type u} {υ : Type v} (deg : ι + υ → ℕ)

    def algebra (α : Type w) :=
    (Π i, algop  (deg (sum.inl i)) α) × -- algebraic operations
    (Π i, algrel (deg (sum.inr i)) α)   -- relations

    def Alg := Σ (α : 0-Type), algebra deg α.fst
  end

  section
    variables {ι : Type u} {υ : Type v} {deg : ι + υ → ℕ}

    section
      variable (A : Alg deg)
      def Alg.carrier := A.fst.fst
      def Alg.op      := A.snd.fst
      def Alg.rel     := A.snd.snd
      def Alg.zero    := A.fst
      def Alg.subset  := ens A.carrier
      def Alg.univ    := ens.univ A.carrier

      def Alg.hset : hset A.carrier :=
      λ _ _, zero_eqv_set.forward A.fst.snd
    end

    def respects {Γ Λ : Alg deg} (f : Γ.carrier → Λ.carrier) :=
    (Π i v, f (Γ.op i v) = Λ.op i (v.map f)) ×
    (Π i v, Γ.rel i v = Λ.rel i (v.map f))

    @[hott] noncomputable def respects.prop {Γ Λ : Alg deg}
      (f : Γ.carrier → Λ.carrier) : prop (respects f) :=
    begin
      apply product_prop; apply pi_prop; intros i; apply pi_prop; intros v,
      apply Alg.hset, apply ground_zero.theorems.prop.propset_is_set
    end

    @[hott] def respects.comp {Γ Λ Δ : Alg deg}
      {f : Γ.carrier → Λ.carrier} {g : Λ.carrier → Δ.carrier} :
      respects g → respects f → respects (g ∘ f) :=
    begin
      intros p q, split; intros i v,
      { transitivity, apply Id.map g, apply q.fst,
        transitivity, apply p.fst,
        apply Id.map, apply vect.comp },
      { transitivity, apply q.snd,
        transitivity, apply p.snd,
        apply Id.map, apply vect.comp }
    end

    def homo (Γ Λ : Alg deg) :=
    Σ (φ : Γ.carrier → Λ.carrier), respects φ
    infix ` ⤳ `:20 := homo

    def homo.comp {Γ Λ Δ : Alg deg} (g : Λ ⤳ Δ) (f : Γ ⤳ Λ) : Γ ⤳ Δ :=
    ⟨g.fst ∘ f.fst, respects.comp g.snd f.snd⟩

    infix ` ⋅ `:60 := homo.comp

    @[hott] def homo.id (Γ : Alg deg) : Γ ⤳ Γ :=
    begin
      existsi id, split; intros i v; symmetry,
      apply Id.map (Γ.op i),  apply vect.id,
      apply Id.map (Γ.rel i), apply vect.id
    end

    @[hott] noncomputable def homo.funext {Γ Λ : Alg deg}
      {f g : Γ ⤳ Λ} : f.fst ~ g.fst → f = g :=
    begin
      intro p, induction f with f F, induction g with g G, fapply sigma.prod,
      apply ground_zero.theorems.funext, exact p, apply respects.prop
    end

    @[hott] def idhomo {Γ Λ : Alg deg} {f g : Γ ⤳ Λ} : f = g → f.fst ~ g.fst :=
    begin intro p, induction p, reflexivity end

    @[hott] noncomputable def homo.hset {Γ Λ : Alg deg} : hset (Γ ⤳ Λ) :=
    begin
      fapply hset_respects_sigma,
      { apply pi_hset, intros x a b, apply Λ.hset },
      { intro f, apply prop_is_set, apply respects.prop }
    end

    def iso (Γ Λ : Alg deg) :=
    Σ (φ : Γ.carrier → Λ.carrier), respects φ × biinv φ
    infix ` ≅ `:25 := iso

    def iso.eqv {Γ Λ : Alg deg} : Γ ≅ Λ → Γ.carrier ≃ Λ.carrier :=
    λ φ, ⟨φ.fst, φ.snd.snd⟩

    @[hott] def iso.of_equiv {Γ Λ : Alg deg} :
      Π (φ : Γ.carrier ≃ Λ.carrier), respects φ.fst → Γ ≅ Λ
    | ⟨φ, q⟩ p := ⟨φ, (p, q)⟩

    @[hott] noncomputable def iso.ext {Γ Λ : Alg deg} (φ ψ : Γ ≅ Λ) : φ.fst ~ ψ.fst → φ = ψ :=
    begin
      intro p, fapply sigma.prod, apply ground_zero.theorems.funext p,
      apply product_prop, apply respects.prop,
      apply ground_zero.theorems.prop.biinv_prop
    end

    @[hott] def iso.homo {Γ Λ : Alg deg} (φ : Γ ≅ Λ) : Γ ⤳ Λ :=
    ⟨φ.fst, φ.snd.fst⟩

    @[hott] noncomputable def iso.hset {Γ Λ : Alg deg} : hset (Γ ≅ Λ) :=
    begin
      apply hset_respects_sigma,
      { apply pi_hset, intros x a b, apply Λ.hset },
      { intro x, apply prop_is_set,
        apply product_prop, apply respects.prop,
        apply ground_zero.theorems.prop.biinv_prop }
    end

    @[hott, refl] def iso.refl (Γ : Alg deg) : Γ ≅ Γ :=
    begin
      fapply iso.of_equiv, reflexivity, split; intros i v,
      { apply Id.map (Γ.op i),  symmetry, apply vect.id },
      { apply Id.map (Γ.rel i), symmetry, apply vect.id }
    end

    @[hott, symm] def iso.symm {Γ Λ : Alg deg} : Γ ≅ Λ → Λ ≅ Γ :=
    begin
      intro f, have μ := equiv.forward_left f.eqv,
      existsi f.eqv.left, split,
      { split; intros i v,
        { symmetry, transitivity, { symmetry, apply f.eqv.left_forward },
          transitivity, apply Id.map f.eqv.left, apply f.snd.fst.fst,
          apply Id.map (f.eqv.left ∘ Λ.op i), transitivity,
          apply vect.comp, apply vect.idfunc, apply μ },
        { transitivity, apply Id.map (Λ.rel i),
          transitivity, symmetry, apply vect.idfunc (f.fst ∘ f.eqv.left),
          apply μ, symmetry, apply vect.comp, symmetry, apply f.snd.fst.snd } },
      { split; existsi f.fst, apply μ, apply f.eqv.left_forward }
    end

    @[hott, trans] def iso.trans {Γ Λ Δ : Alg deg} : Γ ≅ Λ → Λ ≅ Δ → Γ ≅ Δ :=
    begin
      intros f g, existsi g.fst ∘ f.fst, split,
      { apply respects.comp, exact g.snd.fst, exact f.snd.fst },
      { apply equiv.biinv_trans, exact f.snd.snd, exact g.snd.snd }
    end

    @[hott] def Alg.ext : Π {Γ Λ : Alg deg},
      Π (p : Γ.carrier = Λ.carrier),
      (Π i, Γ.op i  =[algop  (deg (sum.inl i)), p] Λ.op i) →
      (Π i, Γ.rel i =[algrel (deg (sum.inr i)), p] Λ.rel i) → Γ = Λ
    | ⟨⟨α, f⟩, (Γ₁, Γ₂)⟩ ⟨⟨β, g⟩, (Λ₁, Λ₂)⟩ :=
    begin
      intros p μ η, change α = β at p, induction p,
      have ρ : f = g := ntype_is_prop 0 f g, induction ρ,
      apply Id.map, apply product.prod;
      apply ground_zero.theorems.funext; intro x,
      apply μ, apply η
    end

    @[hott] noncomputable def Alg.extβrule :
      Π Γ, @Alg.ext ι υ deg Γ Γ Id.refl (λ _, Id.refl) (λ _, Id.refl) = Id.refl :=
    λ ⟨⟨α, f⟩, (Γ₁, Γ₂)⟩,
    begin
      apply @transport (f = f)
        (λ p, @Id.rec _ f
          (λ g (ρ : f = g),
            Π (Λ₁ : Π i, algop (deg (sum.inl i)) α)
              (Λ₂ : Π i, algrel (deg (sum.inr i)) α),
            (Π i, Γ₁ i = Λ₁ i) → (Π i, Γ₂ i = Λ₂ i) →
            @Id (Alg deg) ⟨⟨α, f⟩, (Γ₁, Γ₂)⟩ ⟨⟨α, g⟩, (Λ₁, Λ₂)⟩)
          (λ Λ₁ Λ₂ μ η, Id.map (λ (Γ : algebra deg α), ⟨⟨α, f⟩, Γ⟩)
            (product.prod (ground_zero.theorems.funext μ)
                          (ground_zero.theorems.funext η)))
          f p Γ₁ Γ₂ (λ _, Id.refl) (λ _, Id.refl) = Id.refl)
        Id.refl (ntype_is_prop 0 f f),
      apply prop_is_set, apply ntype_is_prop 0,
      change Id.map _ _ = _, transitivity, apply Id.map,
      change _ = product.prod Id.refl Id.refl, apply equiv.bimap,
      { apply pi_hset, intro i, apply pi_hset, intro v,
        apply zero_eqv_set.forward, exact f },
      { apply pi_hset, intro i, apply pi_hset, intro v,
        apply ground_zero.theorems.prop.propset_is_set },
      reflexivity
    end

    @[hott] noncomputable def equiv_comp_subst {α β : Type u} (φ : α ≃ β) :
      φ.fst ∘ equiv.subst (ua φ)⁻¹ = id :=
    begin
      apply ground_zero.theorems.funext,
      intro x, transitivity, apply Id.map φ.fst,
      transitivity, apply equiv.subst_over_inv_path,
      apply ground_zero.ua.transport_inv_rule,
      apply equiv.forward_left
    end

    @[hott] noncomputable def ua_preserves_op {Γ Λ : Alg deg}
      (φ : Γ ≅ Λ) (i : ι) : Γ.op i =[ua φ.eqv] Λ.op i :=
    begin
      induction φ with φ H, induction H with p q,
      apply Id.trans, apply equiv.transport_over_functor
        (λ α, vect α (deg (sum.inl i))) id,
      apply ground_zero.theorems.funext, intro v,
      transitivity, apply ground_zero.ua.transport_rule,
      transitivity, apply p.fst, apply Id.map,
      transitivity, apply vect.subst,
      transitivity, apply Id.map (λ f, vect.map f v),
      apply equiv_comp_subst ⟨φ, q⟩, apply vect.id
    end

    @[hott] noncomputable def ua_preserves_rel {Γ Λ : Alg deg} (φ : Γ ≅ Λ)
      (i : υ) : Γ.rel i =[algrel (deg (sum.inr i)), ua φ.eqv] Λ.rel i :=
    begin
      induction φ with φ H, induction H with p q,
      apply Id.trans, apply equiv.transport_over_functor
        (λ α, vect α (deg (sum.inr i))) (λ _, propset),
      apply ground_zero.theorems.funext, intro v,
      transitivity, apply Id.map (equiv.subst (ua ⟨φ, q⟩)),
      transitivity, apply p.snd, apply Id.map (Λ.rel i),
      transitivity, apply vect.subst,
      transitivity, apply Id.map (λ f, vect.map f v),
      apply equiv_comp_subst ⟨φ, q⟩, apply vect.id,
      transitivity, apply equiv.transport_to_transportconst,
      transitivity, apply Id.map (λ p, equiv.transportconst p (Λ.rel i v)),
      apply equiv.constmap, reflexivity
    end

    @[hott] noncomputable def Alg.ua {Γ Λ : Alg deg} (φ : Γ ≅ Λ) : Γ = Λ :=
    begin
      fapply Alg.ext, apply ua φ.eqv,
      apply ua_preserves_op, apply ua_preserves_rel
    end

    @[hott] def Alg.id {Γ Λ : Alg deg} (p : Γ = Λ) : Γ ≅ Λ :=
    begin induction p, reflexivity end

    def magma : Type (u + 1) :=
    @Alg.{0 0 u 0} (𝟏 : Type) ⊥ (λ _, 2)

    namespace magma
      def φ (M : magma) : M.carrier → M.carrier → M.carrier :=
      λ x y, M.op ★ (x, y, ★)
    end magma

    class commutative (M : magma) :=
    (mul_comm : Π a b, M.φ a b = M.φ b a)

    class semigroup (M : magma) :=
    (mul_assoc : Π a b c, M.φ (M.φ a b) c = M.φ a (M.φ b c))

    namespace premonoid
      def signature : 𝟐 + ⊥ → ℕ
      | (sum.inl ff) := 0
      | (sum.inl tt) := 2
    end premonoid

    def premonoid : Type (u + 1) :=
    Alg.{0 0 u 0} premonoid.signature

    namespace premonoid
      def e (M : premonoid) : M.carrier :=
      M.op ff ★

      def φ (M : premonoid) : M.carrier → M.carrier → M.carrier :=
      λ x y, M.op tt (x, y, ★)

      @[hott] def magma (M : premonoid) : magma :=
      begin
        existsi M.fst, split,
        { intro b, exact M.op tt },
        { intro x, cases x }
      end
    end premonoid

    class monoid (M : premonoid) :=
    (is_semigroup : semigroup M.magma)
    (one_mul      : Π a, M.φ M.e a = a)
    (mul_one      : Π a, M.φ a M.e = a)

    namespace pregroup
      inductive arity : Type
      | nullary | unary | binary
      open arity

      def signature : arity + ⊥ → ℕ
      | (sum.inl nullary) := 0
      | (sum.inl unary)   := 1
      | (sum.inl binary)  := 2
    end pregroup

    def pregroup : Type (u + 1) :=
    Alg.{0 0 u 0} pregroup.signature

    namespace pregroup
      @[hott] def intro {α : Type u} (H : hset α)
        (φ : α → α → α) (ι : α → α) (e : α) : pregroup :=
      begin
        existsi zeroeqv (λ _ _, H), split; intro i; induction i,
        exact (λ _, e), exact (λ ⟨a, _⟩, ι a), exact (λ ⟨a, b, _⟩, φ a b)
      end

      def e (G : pregroup) : G.carrier :=
      G.op arity.nullary ★

      def ι (G : pregroup) : G.carrier → G.carrier :=
      λ x, G.op arity.unary (x, ★)

      def φ (G : pregroup) : G.carrier → G.carrier → G.carrier :=
      λ x y, G.op arity.binary (x, y, ★)

      @[hott] def magma (G : pregroup) : magma :=
      begin
        existsi G.fst, split,
        { intro b, exact G.op arity.binary },
        { intro x, cases x }
      end

      @[hott] def premonoid (G : pregroup) : premonoid :=
      begin
        existsi G.fst, split,
        { intro b, cases b,
          exact G.op arity.nullary,
          exact G.op arity.binary },
        { intro x, cases x }
      end
    end pregroup

    class group (G : pregroup) :=
    (is_monoid    : monoid G.premonoid)
    (mul_left_inv : Π a, G.φ (G.ι a) a = G.e)

    class abelian (G : pregroup) extends group G :=
    (mul_comm : Π a b, G.φ a b = G.φ b a)

    namespace pregroup
      variables (G : pregroup) [group G]

      @[hott] def mul_assoc : Π a b c, G.φ (G.φ a b) c = G.φ a (G.φ b c) :=
      group.is_monoid.is_semigroup.mul_assoc

      @[hott] def one_mul : Π a, G.φ G.e a = a :=
      group.is_monoid.one_mul

      @[hott] def mul_one : Π a, G.φ a G.e = a :=
      group.is_monoid.mul_one

      @[hott] def mul_left_inv : Π a, G.φ (G.ι a) a = G.e :=
      group.mul_left_inv
    end pregroup

    @[hott] def pregroup.mul_comm (G : pregroup) [abelian G] :
      Π a b, G.φ a b = G.φ b a :=
    abelian.mul_comm
  end

end ground_zero.algebra