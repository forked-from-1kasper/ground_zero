import GroundZero.Algebra.Group.Product
import GroundZero.Algebra.Group.Action

open GroundZero.Algebra.Group
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types
open GroundZero.HITs
open GroundZero

universe u v w

namespace GroundZero.Algebra
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

  structure gis (M : Type u) (G : Group) :=
  (ι     : M → M → G.carrier)
  (trans : Π x y z, G.φ (ι x y) (ι y z) = ι x z)
  (full  : Π g x, contr (Σ y, ι x y = g))

  def rga (M : Type u) (G : Group) :=
  Σ (φ : G ⮎ M), regular φ

  namespace gis
    section
      variable {M : Type u} {N : Type v} {G : Group}
      variable (L : gis M G) (K : gis N G)
      variable (f : M → N)

      def preserving := Π x y, K.ι (f x) (f y) = L.ι x y
      def reversing  := Π x y, K.ι (f x) (f y) = L.ι y x
    end

    section
      variable {A : Type u} {B : Type v} {C : Type w} {G : Group}
      variable (L : gis A G) (K : gis B G) (N : gis C G)
      variable {f : B → C} {h : A → B}

      hott def reversing.comp₁ (F : reversing K N f) (H : preserving L K h) :
        reversing L N (f ∘ h) :=
      begin intros x y; transitivity; apply F; apply H end

      hott def reversing.comp₂ (F : preserving K N f) (H : reversing L K h) :
        reversing L N (f ∘ h) :=
      begin intros x y; transitivity; apply F; apply H end

      hott def reversing.comp₃ (F : reversing K N f) (H : reversing L K h) :
        preserving L N (f ∘ h) :=
      begin intros x y; transitivity; apply F; apply H end

      hott def reversing.comp₄ (F : preserving K N f) (H : preserving L K h) :
        preserving L N (f ∘ h) :=
      begin intros x y; transitivity; apply F; apply H end
    end

    variable {M : Type u} {G : Group} (L : gis M G)

    local infixl:70 " * " => G.φ
    local postfix:max (priority := high) "⁻¹" => G.ι

    hott def neut : Π x, L.ι x x = G.e :=
    begin intro; apply Group.unitOfSqr; apply L.trans end

    hott def neut₂ (x y : M) : L.ι x x = L.ι y y :=
    neut L x ⬝ Id.inv (neut L y)

    hott def inv : Π x y, (L.ι x y)⁻¹ = L.ι y x :=
    begin
      intros x y; apply Group.invEqOfMulEqOne;
      transitivity; apply L.trans; apply gis.neut
    end

    hott def invTrans (x y z : M) : (L.ι x y)⁻¹ * (L.ι x z) = L.ι y z :=
    begin transitivity; apply Id.map (G.φ · (L.ι x z)); apply inv; apply L.trans end

    hott def transInv (x y z : M) : (L.ι x y) * (L.ι z y)⁻¹ = L.ι x z :=
    begin transitivity; apply Id.map; apply inv; apply L.trans end

    hott def propι : Π g x, prop (Σ y, L.ι x y = g) :=
    λ g x, contrImplProp (L.full g x)

    hott def fixι : Π g x, Σ y, L.ι x y = g :=
    λ g x, (L.full g x).1

    hott def zero {x y : M} (p : L.ι x y = G.e) : x = y :=
    let q := L.propι (L.ι x y) x ⟨y, Id.refl⟩ ⟨x, L.neut x ⬝ Id.inv p⟩;
    Id.map Sigma.fst (Id.inv q)

    hott def injιᵣ {x y z : M} : L.ι z x = L.ι z y → x = y :=
    begin
      intro p; apply L.zero;
      transitivity; symmetry; apply L.trans x z y;
      transitivity; apply Id.map; exact Id.inv p;
      transitivity; apply L.trans; apply neut
    end

    hott def injιₗ {x y z : M} : L.ι x z = L.ι y z → x = y :=
    begin
      intro p; apply L.injιᵣ; apply Group.invInj;
      transitivity; apply inv; symmetry;
      transitivity; apply inv;
      exact Id.inv p
    end

    hott def injεᵣ (x y z : M) (H : hset M) :
      L.ι z x = L.ι z y ≃ x = y :=
    begin
      apply propEquivLemma; apply G.hset; apply H;
      exact injιᵣ L; intro p; induction p; reflexivity
    end

    hott def prod {M₁ : Type u} {M₂ : Type v} {G H : Group} : gis M₁ G → gis M₂ H → gis (M₁ × M₂) (G × H) :=
    begin
      intros L K; fapply gis.mk;
      { intros m₁ m₂; fapply Prod.mk;
        exact L.ι m₁.1 m₂.1; exact K.ι m₁.2 m₂.2 };
      { intros x y z; fapply Product.prod;
        apply L.trans; apply K.trans };
      { intro (g₁, g₂) x; fapply Sigma.mk;
        { fapply Sigma.mk;
          { fapply Prod.mk;
            exact (L.fixι g₁ x.1).1;
            exact (K.fixι g₂ x.2).1 };
          fapply Product.prod;
          { apply (L.fixι g₁ x.1).2 };
          { apply (K.fixι g₂ x.2).2 } };
        { intro ⟨(p₁, p₂), v⟩; fapply Sigma.prod;
          { fapply Product.prod;
            apply Id.map Sigma.fst ((L.full g₁ x.1).2 ⟨p₁, Id.map Prod.fst v⟩);
            apply Id.map Sigma.fst ((K.full g₂ x.2).2 ⟨p₂, Id.map Prod.snd v⟩) };
          { apply Structures.prodHset; apply G.hset; apply H.hset } } }
    end

    hott def octave.hrel (φ : G.subset) : hrel M :=
    λ a b, ⟨L.ι a b ∈ φ, Ens.prop (L.ι a b) φ⟩

    hott def octave (φ : G.subgroup) : eqrel M :=
    begin
      existsi octave.hrel L φ.set; apply Prod.mk;
      { intro a; apply transport (· ∈ φ.set);
        exact Id.inv (L.neut a); apply φ.unit }; apply Prod.mk;
      { intros a b p; apply transport (· ∈ φ.set);
        apply L.inv; apply φ.inv; exact p };
      { intros a b c p q; apply transport (· ∈ φ.set);
        apply L.trans a b c; apply φ.mul <;> assumption }
    end

    hott def oct (φ : G.subgroup) := HITs.Quotient (octave L φ)

    hott def normal (φ : G.normal) {a₁ a₂ b₁ b₂ : M}
      (p : L.ι a₁ b₁ ∈ φ.set) (q : L.ι a₂ b₂ ∈ φ.set) : G.φ (L.ι a₁ a₂)⁻¹ (L.ι b₁ b₂) ∈ φ.set :=
    begin
      apply transport (· ∈ φ.set); symmetry;
      transitivity; apply Id.map (G.φ _);
      symmetry; apply G.oneMul; transitivity;
      apply Id.map; apply Id.map (G.φ · (L.ι b₁ b₂));
      symmetry; apply G.mulLeftInv (L.ι a₂ b₁);
      transitivity; apply Id.map; apply G.mulAssoc;
      symmetry; apply G.mulAssoc; apply φ.1.mul;
      { apply transport (· ∈ φ.set); apply invExplode; apply φ.1.inv;
        apply transport (· ∈ φ.set); symmetry; apply Id.map (G.φ · (L.ι a₁ a₂));
        transitivity; symmetry; apply L.trans a₂ a₁; apply Id.map (G.φ · (L.ι a₁ b₁));
        symmetry; apply inv; apply isNormalSubgroup.conj φ.2; exact p };
      { apply φ.2; apply transport (· ∈ φ.set); symmetry;
        apply Id.map (G.φ · (L.ι a₂ b₁)); transitivity; symmetry; apply L.trans b₁ a₂;
        apply Id.map (G.φ · (L.ι a₂ b₂)); symmetry; apply inv;
        apply isNormalSubgroup.conj φ.2; exact q }
    end

    -- Transposition
    hott def τ (i : G.carrier) : M → M :=
    λ x, (L.fixι i x).1

    hott def τ.lawful : Π i x, L.ι x (L.τ i x) = i :=
    λ i x, (L.fixι i x).2

    hott def τ.comp : Π i j x, L.τ i (L.τ j x) = L.τ (j * i) x :=
    begin
      intros i j x; apply @injιᵣ M G L _ _ x;
      transitivity; symmetry; apply L.trans; exact L.τ j x;
      transitivity; apply bimap <;> apply τ.lawful;
      symmetry; apply τ.lawful
    end

    hott def τ.id : Π x, L.τ G.e x = x :=
    begin
      intro x; apply @injιᵣ M G L _ _ x;
      transitivity; apply τ.lawful;
      symmetry; apply L.neut
    end

    hott def τ.biinv (i : G.carrier) : biinv (L.τ i) :=
    begin
      apply Prod.mk <;> existsi L.τ i⁻¹ <;>
      { intro x; transitivity; apply τ.comp;
        transitivity; apply Id.map (L.τ · x);
        first | apply G.mulLeftInv | apply Group.mulRightInv;
        apply τ.id }
    end

    hott def τ.tauto {a b : M} : L.τ (L.ι a b) a = b :=
    begin apply @injιᵣ M G L _ _ a; apply τ.lawful end

    hott def τ.inj {g h : G.carrier} (x : M) (p : L.τ g x = L.τ h x) : g = h :=
    Id.inv (τ.lawful L g x) ⬝ (Id.map (L.ι x) p) ⬝ (τ.lawful L h x)

    hott def τ.act : Gᵒᵖ ⮎ M :=
    ⟨L.τ, (τ.id L, τ.comp L)⟩

    hott def τ.reg (H : hset M) : regular (τ.act L) :=
    begin
      intros a b; fapply Sigma.mk;
      { existsi L.ι a b; apply τ.tauto };
      { intro ⟨g, p⟩; fapply Sigma.prod;
        { apply τ.inj L a; transitivity;
          apply τ.tauto; exact Id.inv p };
        { apply H } }
    end

    hott def preserving.comm {f : M → M} {i : G.carrier}
      (H : preserving L L f) : L.τ i ∘ f ~ f ∘ L.τ i :=
    begin
      intro x; apply @injιᵣ M G L _ _ (f x);
      transitivity; apply τ.lawful;
      symmetry; transitivity; apply H;
      apply τ.lawful
    end

    hott def preserving.abelian (m : M) (H : Π i, preserving L L (L.τ i)) : G.isCommutative :=
    begin
      intros i j; apply τ.inj L m;
      transitivity; { symmetry; apply τ.comp };
      symmetry; transitivity; { symmetry; apply τ.comp };
      apply preserving.comm; apply H
    end

    hott def preserving.id : preserving L L id :=
    λ x y, idp (L.ι x y)

    hott def reversing.acomm {f : M → M} {i : G.carrier}
      (H : reversing L L f) : L.τ i⁻¹ ∘ f ~ f ∘ L.τ i :=
    begin
      intro x; apply @injιᵣ M G L _ _ (f x);
      transitivity; apply τ.lawful;
      symmetry; transitivity; apply H;
      transitivity; symmetry; apply inv;
      apply Id.map; apply τ.lawful
    end

    hott def reversing.acommᵣ {f : M → M} {i : G.carrier}
      (H : reversing L L f) : L.τ i ∘ f ~ f ∘ L.τ i⁻¹ :=
    begin
      apply transport (λ j, L.τ j ∘ f ~ f ∘ L.τ i⁻¹);
      apply invInv; apply reversing.acomm L H
    end

    hott def reversing.unitSqr (m : M)
      (H : Π i, reversing L L (L.τ i)) : Π i, G.φ i i = G.e :=
    begin
      intros i; apply τ.inj L m;
      transitivity; { symmetry; apply τ.comp };
      transitivity; apply reversing.acommᵣ; apply H;
      transitivity; apply τ.comp; apply Id.map (L.τ · m);
      apply G.mulLeftInv
    end

    hott def reversing.abelian (m : M)
      (H : Π i, reversing L L (L.τ i)) : G.isCommutative :=
    Group.sqrUnitImplsAbelian (reversing.unitSqr L m H)

    hott def π (i : G.carrier) (a b : M) : M :=
    (L.fixι (G.φ i (L.ι a b)) a).fst

    hott def π.lawful {i : G.carrier} (a b : M) :
      L.ι a (L.π i a b) = G.φ i (L.ι a b) :=
    (L.fixι (G.φ i (L.ι a b)) a).snd

    hott def τ.mulRight {i : G.carrier} (a b : M) :
      L.ι a (L.τ i b) = G.φ (L.ι a b) i :=
    begin
      transitivity; { symmetry; apply L.trans _ b _ };
      apply Id.map; apply τ.lawful
    end

    hott def π.conjugate {i : G.carrier} (a b : M) :
      L.ι a (L.π i⁻¹ a (L.τ i b)) = Group.conjugate (L.ι a b) i :=
    begin
      transitivity; { apply π.lawful };
      transitivity; { apply Id.map (G.φ i⁻¹); apply τ.mulRight };
      symmetry; apply G.mulAssoc
    end

    hott def π.preserving {i : G.carrier} (x : M) : preserving L L (L.π i x) :=
    begin
      intros a b; transitivity; { symmetry; apply L.trans _ x };
      transitivity; apply Id.map; apply π.lawful;
      transitivity; apply Id.map (G.φ · _);
      transitivity; symmetry; apply inv;
      transitivity; { apply Id.map; apply π.lawful };
      apply invExplode; transitivity; apply G.mulAssoc;
      transitivity; apply Id.map;
      transitivity; symmetry; apply G.mulAssoc;
      transitivity; apply Id.map (G.φ · _);
      apply G.mulLeftInv; apply G.oneMul; apply invTrans
    end

    hott def π.uniq₁ {f : M → M} (H : gis.preserving L L f)
      (m : M) : L.π (L.ι m (f m)) (f m) ~ f :=
    begin
      intro n; apply @injιᵣ M G L _ _ (f m);
      transitivity; apply π.lawful;
      transitivity; apply trans;
      symmetry; apply H
    end

    hott def π.uniq₂ {f : M → M} (H : gis.preserving L L f)
      (m : M) : L.π (L.ι m (f m)) m ~ f :=
    begin
      intro n; apply @injιᵣ M G L _ _ m;
      transitivity; apply π.lawful;
      symmetry; transitivity;
      symmetry; apply L.trans _ (f m) _;
      apply Id.map; apply H
    end

    hott def τ.abelianImplPreserving (ρ : G.isCommutative) :
      Π i, preserving L L (L.τ i) :=
    begin
      intros i a b;
      transitivity; symmetry; apply L.trans _ a;
      transitivity; apply Id.map (G.φ · _);
      transitivity; symmetry; apply inv;
      apply Id.map; apply τ.lawful;
      transitivity; apply Id.map (G.φ i⁻¹);
      transitivity; symmetry; apply L.trans _ b;
      transitivity; apply ρ;
      apply Id.map (G.φ · _); apply τ.lawful;
      transitivity; symmetry; apply G.mulAssoc;
      transitivity; apply Id.map (G.φ · _);
      apply G.mulLeftInv; apply G.oneMul
    end

    hott def τ.π (ρ : G.isCommutative) (m : M) : Π i, L.π i m ~ L.τ i :=
    begin
      intro i; apply transport (λ j, L.π j m ~ L.τ i);
      apply τ.lawful L i m; apply π.uniq₂;
      apply τ.abelianImplPreserving _ ρ
    end

    hott def π.comp (i j : G.carrier) {m : M} :
      L.π i m ∘ L.π j m ~ L.π (i * j) m :=
    begin
      intro n; apply @injιᵣ M G L _ _ m;
      transitivity; apply π.lawful;
      transitivity; apply Id.map (G.φ i); apply π.lawful;
      symmetry; transitivity; apply π.lawful; apply G.mulAssoc
    end

    hott def π.id (m : M) : L.π G.e m ~ id :=
    begin
      intro n; apply @injιᵣ M G L _ _ m;
      transitivity; apply π.lawful; apply G.oneMul
    end

    hott def π.biinv (i : G.carrier) (m : M) : biinv (L.π i m) :=
    begin
      apply Prod.mk <;> existsi L.π i⁻¹ m <;>
      { intro x; transitivity; apply π.comp;
        transitivity apply Id.map (L.π · m x);
        first | apply G.mulLeftInv | apply Group.mulRightInv;
        apply π.id }
    end

    hott def preserving.biinv {f : M → M}
      (H : preserving L L f) (m : M) : biinv f :=
    transport Equiv.biinv (Theorems.funext (π.uniq₂ L H m))
      (π.biinv L (L.ι m (f m)) m)

    hott def ρ (u v : M) : M → M :=
    λ x, (L.fixι (L.ι x u) v).fst

    hott def ρ.lawful (u v x : M) : L.ι v (L.ρ u v x) = L.ι x u :=
    (L.fixι (L.ι x u) v).snd

    hott def ρ.ι (u v a b : M) : L.ι a (L.ρ u v b) = L.ι a v * L.ι b u :=
    begin
      transitivity; symmetry; apply L.trans _ v _;
      apply Id.map; apply ρ.lawful
    end

    hott def ρ.inv (u v : M) : ρ L u v ∘ ρ L v u ~ id :=
    begin
      intro m; apply @injιᵣ M G L _ _ m;
      transitivity; apply ρ.ι;
      transitivity; apply Id.map (G.φ (L.ι m v));
      transitivity; symmetry; apply gis.inv;
      transitivity; apply Id.map; apply ρ.ι;
      apply Group.invExplode;
      transitivity; symmetry; apply G.mulAssoc;
      transitivity; apply Id.map (G.φ · _);
      apply Group.mulRightInv;
      transitivity; apply G.oneMul;
      transitivity; apply gis.inv; apply neut₂
    end

    hott def ρ.biinv (u v : M) : biinv (ρ L u v) :=
    begin apply Prod.mk <;> existsi ρ L v u <;> apply ρ.inv end

    section
      variable {A : Type u} {B : Type v} {H : Group}
      variable (N : gis A H) (K : gis B H)
      variable {f : A ≃ B}

      hott def preserving.inv₁ :
        preserving N K f.forward → preserving K N f.left :=
      begin
        intros H a b; transitivity; symmetry; apply H;
        apply bimap <;> apply f.forwardLeft
      end

      hott def preserving.inv₂ :
        preserving N K f.forward → preserving K N f.right :=
      begin
        intros H a b; transitivity; symmetry; apply H;
        apply bimap <;> apply f.forwardRight
      end

      hott def reversing.inv₁ :
        reversing N K f.forward → reversing K N f.left :=
      begin
        intros H a b; transitivity; symmetry; apply H;
        apply bimap <;> apply f.forwardLeft
      end

      hott def reversing.inv₂ :
        reversing N K f.forward → reversing K N f.right :=
      begin
        intros H a b; transitivity; symmetry; apply H;
        apply bimap <;> apply f.forwardRight
      end
    end

    hott def rga.decode (H : hset M) : gis M G → rga M Gᵒᵖ :=
    λ L, ⟨τ.act L, τ.reg L H⟩

    hott def rga.encode : rga M Gᵒᵖ → gis M G :=
    λ ⟨φ, H⟩, ⟨λ a b, (H a b).1.1, begin
      intros x y z; apply (regular.elim φ H).2 x;
      transitivity; symmetry; apply φ.2.2;
      transitivity; apply Id.map; apply (H x y).1.2;
      transitivity; apply (H y z).1.2;
      symmetry; apply (H x z).1.2
    end, begin
      intros g x; fapply Sigma.mk;
      { existsi φ.1 g x; apply (regular.elim φ H).2 x;
        apply (H _ _).1.2 };
      { intro ⟨y, p⟩; fapply Sigma.prod;
        { transitivity; apply Id.map (φ.1 · x);
          exact Id.inv p; apply (H x y).1.2 };
        { apply G.hset } }
    end⟩

    hott def gis.id : Π (L K : gis M G), L.ι ~ K.ι → L = K :=
    begin
      intro ⟨φ₁, p₁, q₁⟩ ⟨φ₂, p₂, q₂⟩ p';
      let p : φ₁ = φ₂ := Theorems.funext p';
      induction p;
      let q : p₁ = p₂ := begin
        -- repeat?
        apply piProp; intro;
        apply piProp; intro;
        apply piProp; intro;
        apply G.hset
      end;
      have r : q₁ = q₂ := begin
        apply piProp; intro;
        apply piProp; intro;
        apply contrIsProp
      end;
      induction q; induction r; reflexivity
    end

    hott def rga.eqv (H : hset M) : rga M Gᵒᵖ ≃ gis M G :=
    begin
      existsi rga.encode; apply Prod.mk <;> existsi rga.decode H;
      { intro ⟨φ, p⟩; fapply Sigma.prod;
        { fapply leftAction.id; intros a b; apply H;
          intro; apply Theorems.funext; intro; reflexivity };
        apply piProp; intro; apply piProp; intro; apply contrIsProp };
      { intro; apply gis.id; reflexivity }
    end

    noncomputable hott def rga.eqv' (G : Group)
      (H : hset M) : rga M G ≃ gis M G :=
    @transport Group (λ H, @rga M H ≃ gis M G) Gᵒᵖ G
      (Id.inv (Iso.ua Op.iso)) (rga.eqv H)

    hott def reversing.ι (f : M → M) (H : reversing L L f) :
      Π a b, L.ι a (f b) = L.ι a (f a) * (L.ι a b)⁻¹ :=
    begin
      intros a b; transitivity; symmetry; apply L.trans a (f a);
      apply Id.map (G.φ (L.ι a (f a))); transitivity;
      apply H; symmetry; apply inv
    end

    hott def reversing.desc (f : M → M) (H : reversing L L f)
      (m : M) : ρ L m (f m) ~ f :=
    begin
      intro n; apply @injιᵣ M G L _ _ n;
      transitivity; apply ρ.ι;
      transitivity; apply Id.map (G.φ · _);
      apply reversing.ι L f H;
      symmetry; apply Group.cancelLeft
    end

    hott def reversing.biinv {f : M → M}
      (H : reversing L L f) (m : M) : biinv f :=
    transport Equiv.biinv (Theorems.funext (reversing.desc L f H m)) (ρ.biinv L m (f m))
  end gis

  namespace Dodecaphony

  -- In case of A = {C, C♯, D, D♯, E, F, ...},
  -- this is 12 ordered notes
  abbrev P (A : 0-Type) := A ≃₀ A

  def L (A : Type u) := Σ n, Finite n → A

  def L.length {A : Type u} : L A → ℕ := Sigma.fst
  def L.nth {A : Type u} (xs : L A) : Finite xs.length → A := xs.snd

  hott def L.all {A : Type u} (π : A → propset)
    (xs : L A) : propset :=
  ⟨Π n, (π (xs.nth n)).fst, begin apply piProp; intro; apply (π _).2 end⟩

  -- Set of (12 × n) ordered notes, where n ∈ ℕ
  def M (A : 0-Type) := L (P A)

  def Tr (A : 0-Type) :=
  zeroeqv (Theorems.Equiv.zeroEquiv.hset A A)

  -- Set of *all* tone row transformations
  abbrev T (A : 0-Type) := S (Tr A)

  section
    variable {A : 0-Type} (φ : (T A).subgroup)

    -- Tone row transformations in terms of φ ≤ T A
    def tr := (@S.ap (Tr A)).cut φ

    -- Set of tone rows
    def R := Orbits (tr φ)

    def M.dodecaphonic (xs : M A) (r : P A) : propset :=
    xs.all (λ x, ⟨x ∈ orbit (tr φ) r, Ens.prop x _⟩)

    noncomputable hott def R.dodecaphonic (xs : M A) (r : R φ) : propset :=
    begin
      fapply HITs.Quotient.rec _ _ _ r;
      { exact M.dodecaphonic φ xs };
      { intros x y p; fapply Theorems.Equiv.propset.Id;
        apply GroundZero.ua; apply equivFunext;
        intro z; apply propEquivLemma;
        change prop (_ ∈ orbit (tr φ) x); apply Ens.prop;
        change prop (_ ∈ orbit (tr φ) y); apply Ens.prop;
        apply orbit.subset; exact p;
        apply orbit.subset; apply leftAction.symm; exact p };
      { apply Theorems.Equiv.propsetIsSet }
    end
  end

  end Dodecaphony
end GroundZero.Algebra