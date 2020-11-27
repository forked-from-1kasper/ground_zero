import ground_zero.algebra.group
open ground_zero.algebra.group
open ground_zero.types.equiv
open ground_zero.structures
open ground_zero.types
open ground_zero.HITs
open ground_zero

hott theory

universes u v

namespace ground_zero.algebra
  /- Generalized Musical Intervals and Transformations
     David Lewin, 1987
  -/

  /- Generalized Interval System and Its Applications, Minseon Song
     https://www.whitman.edu/documents/Academics/Mathematics/2014/songm.pdf
  -/

  /- Conceptualizing Music Through Mathematics And
     The Generalized Interval Systen
     http://www.math.uchicago.edu/~may/VIGRE/VIGRE2006/PAPERS/Sternberg.pdf
  -/
  structure gis (M : Type u) (G : group) :=
  (ι     : M → M → G.carrier)
  (trans : Π x y z, G.φ (ι x y) (ι y z) = ι x z)
  (full  : Π g x, contr (Σ y, ι x y = g))

  def rga (M : Type u) (G : group) :=
  Σ (φ : G ⮎ M), regular φ

  namespace gis
    variables {M : Type u} {G : group} (L : gis M G)
    include L

    local infix ` * ` := G.φ
    local postfix ⁻¹ := G.inv

    @[hott] def neut : Π x, L.ι x x = G.e :=
    begin intro x, apply group.unit_of_sqr, apply L.trans end

    @[hott] def inv : Π x y, (L.ι x y)⁻¹ = L.ι y x :=
    begin
      intros x y, apply group.inv_eq_of_mul_eq_one,
      transitivity, apply L.trans, apply gis.neut
    end

    @[hott] def inv_trans (x y z : M) : (L.ι x y)⁻¹ * (L.ι x z) = L.ι y z :=
    begin transitivity, apply Id.map (* L.ι x z), apply inv, apply L.trans end

    @[hott] def trans_inv (x y z : M) : (L.ι x y) * (L.ι z y)⁻¹ = L.ι x z :=
    begin transitivity, apply Id.map, apply inv, apply L.trans end

    @[hott] def propι : Π g x, prop (Σ y, L.ι x y = g) :=
    λ g x, contr_impl_prop (L.full g x)

    @[hott] def fixι : Π g x, Σ y, L.ι x y = g :=
    λ g x, (L.full g x).point

    @[hott] def zero {x y : M} : L.ι x y = G.e → x = y :=
    begin
      intro p, symmetry,
      have m := L.propι (L.ι x y) x ⟨y, Id.refl⟩ ⟨x, L.neut x ⬝ Id.inv p⟩,
      apply Id.map sigma.fst m
    end

    @[hott] def injιᵣ {x y z : M} : L.ι z x = L.ι z y → x = y :=
    begin
      intro p, apply L.zero,
      transitivity, symmetry, apply L.trans x z y,
      transitivity, apply Id.map, exact Id.inv p,
      transitivity, apply L.trans, apply neut
    end

    @[hott] def injιₗ {x y z : M} : L.ι x z = L.ι y z → x = y :=
    begin
      intro p, apply L.injιᵣ, apply group.inv_inj,
      transitivity, apply inv, symmetry,
      transitivity, apply inv,
      exact Id.inv p
    end

    @[hott] def injεᵣ (x y z : M) (H : hset M) :
      L.ι z x = L.ι z y ≃ x = y :=
    begin
      apply prop_equiv_lemma,
      { apply G.set }, { apply H }, { exact injιᵣ L },
      { intro p, induction p, reflexivity }
    end

    omit L
    @[hott] def prod {M₁ : Type u} {M₂ : Type v} {G H : group} :
      gis M₁ G → gis M₂ H → gis (M₁ × M₂) (G × H) :=
    begin
      intros L K, fapply gis.mk,
      { intros m₁ m₂, fapply prod.intro,
        exact L.ι m₁.fst m₂.fst,
        exact K.ι m₁.snd m₂.snd },
      { intros x y z, fapply product.prod,
        apply L.trans, apply K.trans },
      { intros g x, induction g with g₁ g₂, fapply contr.mk,
        { fapply sigma.mk,
          { fapply prod.intro,
            exact (L.fixι g₁ x.fst).fst,
            exact (K.fixι g₂ x.snd).fst },
          fapply product.prod,
          { apply (L.fixι g₁ x.fst).snd },
          { apply (K.fixι g₂ x.snd).snd } },
        { intro p, induction p with p v,
          induction p with p₁ p₂, fapply sigma.prod,
          { fapply product.prod,
            apply Id.map sigma.fst ((L.full g₁ x.fst).intro ⟨p₁, Id.map prod.fst v⟩),
            apply Id.map sigma.fst ((K.full g₂ x.snd).intro ⟨p₂, Id.map prod.snd v⟩) },
          { apply group.prod_hset; intros p q,
            apply G.set, apply H.set } } }
    end
    notation L × K := prod L K

    @[hott] def octave.hrel (φ : G.subset) : hrel M :=
    λ a b, ⟨L.ι a b ∈ φ, ens.prop _ φ⟩

    include L
    @[hott] def octave (φ : G.subset) [G ≥ φ] : eqrel M :=
    begin
      existsi octave.hrel L φ, split,
      { intro a, apply transport (∈ φ),
        exact Id.inv (L.neut a),
        apply group.is_subgroup.unit }, split,
      { intros a b p, apply transport (∈ φ),
        apply L.inv, apply group.is_subgroup.inv,
        exact p },
      { intros a b c p q, apply transport (∈ φ),
        apply L.trans a b c, apply group.is_subgroup.mul;
        assumption }
    end

    -- Transposition
    @[hott] def τ (i : G.carrier) : M → M :=
    λ x, (L.fixι i x).fst

    @[hott] def τ.lawful : Π i x, L.ι x (L.τ i x) = i :=
    λ i x, (L.fixι i x).snd

    @[hott] def τ.comp : Π i j x, L.τ i (L.τ j x) = L.τ (j * i) x :=
    begin
      intros i j x, apply @injιᵣ M G L _ _ x,
      transitivity, symmetry, apply L.trans, exact L.τ j x,
      transitivity, apply bimap; apply τ.lawful,
      symmetry, apply τ.lawful
    end

    @[hott] def τ.id : Π x, L.τ G.e x = x :=
    begin
      intro x, apply @injιᵣ M G L _ _ x,
      transitivity, apply τ.lawful,
      symmetry, apply L.neut
    end

    @[hott] def τ.biinv (i : G.carrier) : biinv (L.τ i) :=
    begin
      split; existsi L.τ i⁻¹;
      { intro x, transitivity, apply τ.comp,
        transitivity, apply Id.map (λ g, L.τ g x),
        apply group.mul_left_inv <|> apply group.mul_right_inv,
        apply τ.id }
    end

    @[hott] def τ.tauto {a b : M} : L.τ (L.ι a b) a = b :=
    begin apply @injιᵣ M G L _ _ a, apply τ.lawful end

    @[hott] def τ.inj {g h : G.carrier} (x : M) (p : L.τ g x = L.τ h x) : g = h :=
    Id.inv (τ.lawful L g x) ⬝ (Id.map (L.ι x) p) ⬝ (τ.lawful L h x)

    @[hott] def τ.act : Gᵒᵖ ⮎ M :=
    ⟨L.τ, (τ.id L, τ.comp L)⟩

    @[hott] def τ.reg (H : hset M) : regular (τ.act L) :=
    begin
      intros a b, fapply contr.mk,
      { existsi L.ι a b, apply τ.tauto },
      { intros p, induction p with g p,
        fapply sigma.prod,
        { apply τ.inj L a, transitivity,
          apply τ.tauto, exact Id.inv p },
        { apply H } }
    end

    @[hott] def preserving (f : M → M) :=
    Π x y, L.ι (f x) (f y) = L.ι x y

    @[hott] def reversing (f : M → M) :=
    Π x y, L.ι (f x) (f y) = L.ι y x

    @[hott] def preserving.comm {f : M → M} {i : G.carrier}
      (H : preserving L f) : L.τ i ∘ f ~ f ∘ L.τ i :=
    begin
      intro x, apply @injιᵣ M G L _ _ (f x),
      transitivity, apply τ.lawful,
      symmetry, transitivity, apply H,
      apply τ.lawful
    end

    @[hott] def preserving.abelian (m : M)
      (H : Π i, preserving L (L.τ i)) : abelian G :=
    begin
      split, intros i j, apply τ.inj L m,
      transitivity, { symmetry, apply τ.comp },
      symmetry, transitivity, { symmetry, apply τ.comp },
      apply preserving.comm, apply H
    end

    @[hott] def preserving.id : preserving L id :=
    λ x y, idp (L.ι x y)

    @[hott] def reversing.acomm {f : M → M} {i : G.carrier}
      (H : reversing L f) : L.τ i⁻¹ ∘ f ~ f ∘ L.τ i :=
    begin
      intro x, apply @injιᵣ M G L _ _ (f x),
      transitivity, apply τ.lawful,
      symmetry, transitivity, apply H,
      transitivity, symmetry, apply inv,
      apply Id.map, apply τ.lawful
    end

    @[hott] def reversing.acommᵣ {f : M → M} {i : G.carrier}
      (H : reversing L f) : L.τ i ∘ f ~ f ∘ L.τ i⁻¹ :=
    begin
      apply transport (λ j, L.τ j ∘ f ~ f ∘ L.τ i⁻¹),
      apply inv_inv, apply reversing.acomm L H
    end

    @[hott] def reversing.unit_sqr (m : M)
      (H : Π i, reversing L (L.τ i)) : Π i, i * i = G.e :=
    begin
      intros i, apply τ.inj L m,
      transitivity, { symmetry, apply τ.comp },
      transitivity, apply reversing.acommᵣ, apply H,
      transitivity, apply τ.comp, apply Id.map (λ i, L.τ i m),
      apply mul_left_inv
    end

    @[hott] def reversing.abelian (m : M)
      (H : Π i, reversing L (L.τ i)) : abelian G :=
    group.sqr_unit_impls_abelian (reversing.unit_sqr L m H)

    @[hott] def π (i : G.carrier) (a b : M) : M :=
    (L.fixι (G.φ i (L.ι a b)) a).fst

    @[hott] def π.lawful {i : G.carrier} (a b : M) :
      L.ι a (L.π i a b) = G.φ i (L.ι a b) :=
    (L.fixι (G.φ i (L.ι a b)) a).snd

    @[hott] def τ.mul_right {i : G.carrier} (a b : M) :
      L.ι a (L.τ i b) = G.φ (L.ι a b) i :=
    begin
      transitivity, { symmetry, apply L.trans _ b _ },
      apply Id.map, apply τ.lawful
    end

    @[hott] def π.conjugate {i : G.carrier} (a b : M) :
      L.ι a (L.π i⁻¹ a (L.τ i b)) = conjugate (L.ι a b) i :=
    begin
      transitivity, { apply π.lawful },
      transitivity, { apply Id.map (G.φ i⁻¹), apply τ.mul_right },
      symmetry, apply G.mul_assoc
    end

    @[hott] def π.preserving {i : G.carrier}
      (x : M) : preserving L (L.π i x) :=
    begin
      intros a b, transitivity, { symmetry, apply L.trans _ x },
      transitivity, apply Id.map, apply π.lawful,
      transitivity, apply Id.map (* i * L.ι x b),
      transitivity, symmetry, apply inv,
      transitivity, { apply Id.map, apply π.lawful },
      apply inv_explode, transitivity, apply G.mul_assoc,
      transitivity, apply Id.map,
      transitivity, symmetry, apply G.mul_assoc,
      transitivity, apply Id.map (* L.ι x b), apply mul_left_inv,
      apply G.one_mul, apply inv_trans
    end

    @[hott] def π.uniq₁ {f : M → M} (H : preserving L f)
      (m : M) : L.π (L.ι m (f m)) (f m) ~ f :=
    begin
      intro n, apply @injιᵣ M G L _ _ (f m),
      transitivity, apply π.lawful,
      transitivity, apply trans,
      symmetry, apply H
    end

    @[hott] def π.uniq₂ {f : M → M} (H : preserving L f)
      (m : M) : L.π (L.ι m (f m)) m ~ f :=
    begin
      intro n, apply @injιᵣ M G L _ _ m,
      transitivity, apply π.lawful,
      symmetry, transitivity,
      { symmetry, apply L.trans _ (f m) _ },
      apply Id.map, apply H
    end

    @[hott] def τ.abelian_impl_preserving [abelian G] :
      Π i, preserving L (L.τ i) :=
    begin
      intros i a b,
      transitivity, { symmetry, apply L.trans _ a },
      transitivity, apply Id.map (* L.ι a (L.τ i b)),
      transitivity, { symmetry, apply inv },
      apply Id.map, apply τ.lawful,
      transitivity, apply Id.map (G.φ i⁻¹),
      transitivity, { symmetry, apply L.trans _ b },
      transitivity, apply abelian.mul_comm,
      apply Id.map (* L.ι a b), apply τ.lawful,
      transitivity, { symmetry, apply G.mul_assoc },
      transitivity, apply Id.map (* L.ι a b),
      apply mul_left_inv, apply G.one_mul
    end

    @[hott] def τ.π [abelian G] (m : M) : Π i, L.π i m ~ L.τ i :=
    begin
      intro i, apply transport (λ j, L.π j m ~ L.τ i),
      apply τ.lawful L i m, apply π.uniq₂,
      apply τ.abelian_impl_preserving
    end

    @[hott] def π.comp (i j : G.carrier) {m : M} :
      L.π i m ∘ L.π j m ~ L.π (i * j) m :=
    begin
      intro n, apply @injιᵣ M G L _ _ m,
      transitivity, apply π.lawful,
      transitivity, apply Id.map (G.φ i), apply π.lawful,
      symmetry, transitivity, apply π.lawful,
      apply G.mul_assoc
    end

    @[hott] def π.id (m : M) : L.π G.e m ~ id :=
    begin
      intro n, apply @injιᵣ M G L _ _ m,
      transitivity, apply π.lawful,
      apply G.one_mul
    end

    @[hott] def π.biinv (i : G.carrier) (m : M) : biinv (L.π i m) :=
    begin
      split; existsi L.π i⁻¹ m;
      { intro x, transitivity, apply π.comp,
        transitivity, apply Id.map (λ g, L.π g m x),
        apply group.mul_left_inv <|> apply group.mul_right_inv,
        apply π.id }
    end

    @[hott] def preserving.biinv {f : M → M}
      (H : preserving L f) (m : M) : biinv f :=
    transport biinv (theorems.funext (π.uniq₂ L H m)) (π.biinv L _ m)

    @[hott] def ρ (u v : M) : M → M :=
    λ x, (L.fixι (L.ι x u) v).fst

    @[hott] def ρ.lawful (u v x : M) : L.ι v (L.ρ u v x) = L.ι x u :=
    (L.fixι (L.ι x u) v).snd

    @[hott] def ρ.ι (u v a b : M) : L.ι a (L.ρ u v b) = L.ι a v * L.ι b u :=
    begin
      transitivity, { symmetry, apply L.trans _ v _ },
      apply Id.map, apply ρ.lawful
    end

    section
      variables {f h : M → M}
      @[hott] def reversing.comp₁ (F : reversing L f) (H : preserving L h) :
        reversing L (f ∘ h) :=
      begin intros x y, transitivity, apply F, apply H end

      @[hott] def reversing.comp₂ (F : preserving L f) (H : reversing L h) :
        reversing L (f ∘ h) :=
      begin intros x y, transitivity, apply F, apply H end

      @[hott] def reversing.comp₃ (F : reversing L f) (H : reversing L h) :
        preserving L (f ∘ h) :=
      begin intros x y, transitivity, apply F, apply H end

      @[hott] def reversing.comp₄ (F : preserving L f) (H : preserving L h) :
        preserving L (f ∘ h) :=
      begin intros x y, transitivity, apply F, apply H end
    end

    section
      variables {f : M ≃ M}

      @[hott] def preserving.inv₁ :
        preserving L f.forward → preserving L f.left :=
      begin
        intros H a b, transitivity, { symmetry, apply H }, apply bimap;
        { apply qinv.rinv_inv, apply f.forward_right, apply f.left_forward }
      end

      @[hott] def preserving.inv₂ :
        preserving L f.forward → preserving L f.right :=
      begin
        intros H a b, transitivity, { symmetry, apply H },
        apply bimap; apply f.forward_right
      end

      @[hott] def reversing.inv₁ :
        reversing L f.forward → reversing L f.left :=
      begin
        intros H a b, transitivity, { symmetry, apply H }, apply bimap;
        { apply qinv.rinv_inv, apply f.forward_right, apply f.left_forward }
      end

      @[hott] def reversing.inv₂ :
        reversing L f.forward → reversing L f.right :=
      begin
        intros H a b, transitivity, { symmetry, apply H },
        apply bimap; apply f.forward_right
      end
    end

    omit L
    @[hott] def rga.decode (H : hset M) : gis M G → rga M Gᵒᵖ :=
    λ L, ⟨τ.act L, τ.reg L (λ _ _, H)⟩

    @[hott] def rga.encode : rga M Gᵒᵖ → gis M G :=
    λ ⟨φ, H⟩, ⟨λ a b, (H a b).point.fst, begin
      intros x y z, apply (regular.elim φ H).snd x,
      transitivity, symmetry, apply φ.snd.snd,
      transitivity, apply Id.map, apply (H x y).point.snd,
      transitivity, apply (H y z).point.snd,
      symmetry, apply (H x z).point.snd
    end, begin
      intros g x, fapply contr.mk,
      { existsi φ.fst g x, apply (regular.elim φ H).snd x,
        apply (H _ _).point.snd },
      { intro p, induction p with y p, fapply sigma.prod,
        { transitivity, apply Id.map (λ g, φ.fst g x),
          exact Id.inv p, apply (H x y).point.snd },
        { apply G.set } }
    end⟩

    @[hott] def gis.id (L K : gis M G) : L.ι ~ K.ι → L = K :=
    begin
      intro p', induction L with φ₁ p₁ q₁,
      induction K with φ₂ p₂ q₂,
      have p := theorems.funext p',
      change φ₁ = φ₂ at p, induction p,
      have q : p₁ = p₂ := begin
        repeat { apply pi_prop, intro },
        apply G.set
      end,
      have r : q₁ = q₂ := begin
        repeat { apply pi_prop, intro },
        apply contr_is_prop
      end,
      induction q, induction r,
      reflexivity
    end

    @[hott] def rga.eqv (H : hset M) : rga M Gᵒᵖ ≃ gis M G := begin
      existsi rga.encode, split; existsi rga.decode (λ _ _, H),
      { intro p, induction p with φ q, fapply sigma.prod,
        { fapply left_action.id, intros a b, apply H,
          intro x, apply theorems.funext, intro m,
          reflexivity },
        { repeat { apply pi_prop, intro }, apply contr_is_prop } },
      { intro p, apply gis.id, reflexivity }
    end
  end gis

  -- In case of α = {C, C♯, D, D♯, E, F, ...},
  -- this is 12 ordered notes
  abbreviation P (α : 0-Type) := α ≃₀ α

  def L (α : Type u) := Σ n, finite n → α

  def L.length {α : Type u} : L α → ℕ := sigma.fst
  def L.nth {α : Type u} (xs : L α) : finite xs.length → α := xs.snd

  @[hott] def L.all {α : Type u} (π : α → propset)
    (xs : L α) : propset :=
  ⟨Π n, (π (xs.nth n)).fst, begin
    apply pi_prop, intro x,
    apply (π _).snd
  end⟩

  -- Set of (12 × n) ordered notes, where n ∈ ℕ
  def M (α : 0-Type) := L (P α).fst

  -- Set of *all* tone row transformations
  abbreviation T (α : 0-Type) := S (P α)

  section
    variables {α : 0-Type} (φ : (T α).subset) [T α ≥ φ]

    -- Tone row transformations in terms of φ ≤ T α
    def tr := (@S.ap (α ≃₀ α)).cut φ

    -- Set of tone rows
    def R := Orbits (tr φ)

    def M.dodecaphonic (xs : M α) (r : (P α).fst) : propset :=
    xs.all (λ x, ⟨x ∈ orbit (tr φ) r, ens.prop x _⟩)
  end
end ground_zero.algebra