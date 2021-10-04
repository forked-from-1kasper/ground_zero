import ground_zero.types.ens
open ground_zero.HITs.interval (happly)
open ground_zero.types ground_zero.structures
open ground_zero.types.equiv (biinv transport transportconst)
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

    @[hott] noncomputable def algebra.hset {α : Type w} (H : hset α) : hset (algebra deg α) :=
    begin
      apply prod_hset,
      { apply pi_hset, intro, apply pi_hset, intro, intros a b, apply H },
      { apply pi_hset, intro, apply pi_hset,
        intro, apply ground_zero.theorems.prop.propset_is_set },
    end
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

    abbreviation mapping (Γ Λ : Alg deg) :=
    Γ.carrier → Λ.carrier

    infix ` →ᴬ `:20 := mapping

    def respects {Γ Λ : Alg deg} (f : Γ.carrier → Λ.carrier) :=
    (Π i v, f (Γ.op i v) = Λ.op i (v.map f)) ×
    (Π i v, Γ.rel i v = Λ.rel i (v.map f))

    @[hott] noncomputable def respects.prop {Γ Λ : Alg deg}
      (f : Γ →ᴬ Λ) : prop (respects f) :=
    begin
      apply product_prop; apply pi_prop; intros i; apply pi_prop; intros v,
      apply Alg.hset, apply ground_zero.theorems.prop.propset_is_set
    end

    @[hott] def respects.comp {Γ Λ Δ : Alg deg} {f : Γ →ᴬ Λ} {g : Λ →ᴬ Δ} :
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
    Σ (φ : Γ →ᴬ Λ), respects φ
    infix ` ⤳ `:20 := homo

    abbreviation homo.ap {Γ Λ : Alg deg} : (Γ ⤳ Λ) → (Γ →ᴬ Λ) := sigma.fst

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
      {f g : Γ ⤳ Λ} : f.ap ~ g.ap → f = g :=
    begin
      intro p, induction f with f F, induction g with g G, fapply sigma.prod,
      apply ground_zero.theorems.funext, exact p, apply respects.prop
    end

    @[hott] def idhomo {Γ Λ : Alg deg} {f g : Γ ⤳ Λ} : f = g → f.ap ~ g.ap :=
    begin intro p, induction p, reflexivity end

    @[hott] noncomputable def homo.hset {Γ Λ : Alg deg} : hset (Γ ⤳ Λ) :=
    begin
      fapply hset_respects_sigma,
      { apply pi_hset, intros x a b, apply Λ.hset },
      { intro f, apply prop_is_set, apply respects.prop }
    end

    def iso (Γ Λ : Alg deg) :=
    Σ (φ : Γ →ᴬ Λ), respects φ × biinv φ
    infix ` ≅ `:25 := iso

    abbreviation iso.ap {Γ Λ : Alg deg} : Γ ≅ Λ → (Γ →ᴬ Λ) := sigma.fst

    def iso.eqv {Γ Λ : Alg deg} : Γ ≅ Λ → Γ.carrier ≃ Λ.carrier :=
    λ φ, ⟨φ.ap, φ.snd.snd⟩

    @[hott] def iso.of_equiv {Γ Λ : Alg deg} :
      Π (φ : Γ.carrier ≃ Λ.carrier), respects φ.fst → Γ ≅ Λ
    | ⟨φ, q⟩ p := ⟨φ, (p, q)⟩

    @[hott] def iso.of_homo {Γ Λ : Alg deg} :
      Π (φ : Γ ⤳ Λ), biinv φ.ap → Γ ≅ Λ
    | ⟨φ, p⟩ q := ⟨φ, (p, q)⟩

    @[hott] noncomputable def iso.ext {Γ Λ : Alg deg} (φ ψ : Γ ≅ Λ) : φ.ap ~ ψ.ap → φ = ψ :=
    begin
      intro p, fapply sigma.prod, apply ground_zero.theorems.funext p,
      apply product_prop, apply respects.prop,
      apply ground_zero.theorems.prop.biinv_prop
    end

    @[hott] noncomputable def iso.eq_iff_eq_eqv {Γ Λ : Alg deg} (φ ψ : Γ ≅ Λ) : φ.eqv = ψ.eqv → φ = ψ :=
    begin intro p, apply iso.ext, apply happly, apply sigma.fst # p end

    @[hott] def iso.homo {Γ Λ : Alg deg} (φ : Γ ≅ Λ) : Γ ⤳ Λ :=
    ⟨φ.ap, φ.snd.fst⟩

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
          transitivity, symmetry, apply vect.idfunc (f.ap ∘ f.eqv.left),
          apply μ, symmetry, apply vect.comp, symmetry, apply f.snd.fst.snd } },
      { split; existsi f.ap, apply μ, apply f.eqv.left_forward }
    end

    @[hott, trans] def iso.trans {Γ Λ Δ : Alg deg} : Γ ≅ Λ → Λ ≅ Δ → Γ ≅ Δ :=
    begin
      intros f g, existsi g.ap ∘ f.ap, split,
      { apply respects.comp, exact g.snd.fst, exact f.snd.fst },
      { apply equiv.biinv_trans, exact f.snd.snd, exact g.snd.snd }
    end

    @[hott] def algebra.ext {α β : Type w}
      (p : α = β) (Γ : algebra deg α) (Λ : algebra deg β)
      (ε : Π i, Γ.fst i =[p] Λ.fst i) (δ : Π i, Γ.snd i =[p] Λ.snd i) : 
      Γ =[p] Λ :=
    begin
      induction Γ with Γ₁ Γ₂, induction Λ with Λ₁ Λ₂,
      induction p, apply product.prod;
      apply ground_zero.theorems.funext;
      intro x, apply ε, apply δ
    end

    @[hott] def transport_over_zero_path {α β : 0-Type} (π : Type u → Type v)
      (p : α.fst = β.fst) (u : π α.fst) :
       transport (π ∘ sigma.fst) (zero_path p) u =
      @transport (Type u) π α.fst β.fst p u :=
    begin
      induction α with α f, induction β with β g, change α = β at p, induction p,
      have ρ : f = g := ntype_is_prop 0 f g, induction ρ,
      transitivity, apply equiv.transport_to_transportconst, transitivity,
      apply Id.map (λ p, transportconst (Id.map (π ∘ sigma.fst) p) u),
      apply zero_path_refl, reflexivity
    end

    @[hott] def Alg.ext {Γ Λ : Alg deg} (p : Γ.carrier = Λ.carrier)
      (μ : Π i, Γ.op i  =[algop  (deg (sum.inl i)), p] Λ.op i)
      (η : Π i, Γ.rel i =[algrel (deg (sum.inr i)), p] Λ.rel i) : Γ = Λ :=
    begin
      fapply sigma.prod, apply zero_path, exact p,
      transitivity, apply transport_over_zero_path,
      apply algebra.ext; assumption
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
    Alg.ext (ua φ.eqv) (ua_preserves_op φ) (ua_preserves_rel φ)

    @[hott] def Alg.eqcar {Γ Λ : Alg deg} : Γ = Λ → Γ.carrier = Λ.carrier :=
    λ p, @Id.map (0-Type) (Type _) _ _ sigma.fst (sigma.fst # p)

    @[hott] noncomputable def Alg.uaext :
      Π {Γ Λ : Alg deg} (φ : Γ ≅ Λ), ua φ.eqv = Alg.eqcar (Alg.ua φ)
    | ⟨⟨α, f⟩, (Γ₁, Γ₂)⟩ ⟨⟨β, g⟩, (Λ₁, Λ₂)⟩ := begin
      intro φ, symmetry, transitivity, change Id.map _ _ = _, apply Id.map,
      apply sigma.map_fst_over_prod, apply sigma.map_fst_over_prod
    end

    @[hott] noncomputable def Alg.inj {Γ Λ : Alg deg} {φ ψ : Γ ≅ Λ}
      (p : Alg.ua φ = Alg.ua ψ) : φ = ψ :=
    begin
      apply iso.eq_iff_eq_eqv, transitivity, symmetry, apply ground_zero.ua.uaβrule,
      transitivity, apply Id.map, apply Alg.uaext,
      transitivity, apply Id.map (equiv.idtoeqv ∘ Alg.eqcar),
      exact p, transitivity, apply Id.map equiv.idtoeqv,
      symmetry, apply Alg.uaext, apply ground_zero.ua.uaβrule
    end

    @[hott] def Alg.id {Γ Λ : Alg deg} (p : Γ = Λ) : Γ ≅ Λ :=
    begin induction p, reflexivity end

    @[hott] def transport_over_prod {α : Type u} {β : α → Type v} {u v : sigma β}
      (p₁ p₂ : u.fst = v.fst) (q : equiv.subst p₁ u.snd = v.snd) (ε : p₁ = p₂) :
      sigma.prod p₁ q = sigma.prod p₂ (@transport (u.fst = v.fst)
        (λ p, equiv.subst p u.snd = v.snd) p₁ p₂ ε q) :=
    begin induction ε, reflexivity end

    @[hott] noncomputable def Alg.uaβrefl {Γ : Alg deg} : Alg.ua (iso.refl Γ) = Id.refl :=
    begin
      change Alg.ext _ _ _ = _, change sigma.prod _ _ = _,
      transitivity, apply transport_over_prod,
      transitivity, change sigma.prod _ _ = _,
      transitivity, apply transport_over_prod,
      apply ground_zero.ua.refl_on_ua,
      apply Id.map (sigma.prod Id.refl),
      change _ = Id.refl, apply prop_is_set,
      apply ntype_is_prop, apply sigma.prod_refl,
      transitivity, apply Id.map (sigma.prod Id.refl),
      change _ = Id.refl, apply algebra.hset,
      intros a b, apply zero_eqv_set.forward Γ.fst.snd,
      apply sigma.prod_refl
    end

    @[hott] noncomputable def Alg.rinv {Γ Λ : Alg deg} (p : Γ = Λ) : Alg.ua (Alg.id p) = p :=
    begin induction p, apply Alg.uaβrefl end

    @[hott] noncomputable def Alg.linv {Γ Λ : Alg deg} {φ : Γ ≅ Λ} :
      Alg.id (Alg.ua φ) = φ :=
    begin apply Alg.inj, apply Alg.rinv end

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

      “Formalization of universal algebra in Agda”
      Emmanuel Gunther, Alejandro Gadea, and Miguel Pagano
      * https://www.sciencedirect.com/science/article/pii/S1571066118300768

      “Universal algebra in type theory”
      Venanzio Capretta
      * https://link.springer.com/chapter/10.1007/3-540-48256-3_10
    -/
    @[hott] noncomputable def Alg.univalence {Γ Λ : Alg deg} : (Γ ≅ Λ) ≃ (Γ = Λ) :=
    begin existsi Alg.ua, split; existsi Alg.id, apply Alg.linv, apply Alg.rinv end

    def magma : Type (u + 1) :=
    @Alg.{0 0 u 0} 𝟏 ⊥ (λ _, 2)

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

      def ι (G : pregroup) : G →ᴬ G :=
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