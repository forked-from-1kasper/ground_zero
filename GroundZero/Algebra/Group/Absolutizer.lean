import GroundZero.Algebra.Group.Basic
import GroundZero.HITs.Setquot

open GroundZero.Types.Id (ap)
open GroundZero.Types
open GroundZero.HITs
open GroundZero

namespace GroundZero.Algebra
universe u v u' v' w

namespace Group
  variable {G : Group}

  hott def «Sosnitsky construction» (G : Group) :=
  @Relquot G.carrier
    ⟨λ g h, ⟨∥(g = h) + (g = G.ι h)∥, HITs.Merely.uniq⟩,
    begin
      apply Prod.mk;
      { intro; apply HITs.Merely.elem; left; reflexivity }; apply Prod.mk;
      { intros a b; apply HITs.Merely.lift; intro p;
        match p with | Sum.inl u => _ | Sum.inr v => _;
        { left; exact Id.inv u };
        { right; transitivity; symmetry; apply invInv;
          apply ap; exact Id.inv v } };
      { intros a b c; apply HITs.Merely.lift₂;
        intros p q; match p, q with
        | Sum.inl p₁, Sum.inl q₁ => { left;  exact p₁ ⬝ q₁ }
        | Sum.inl p₁, Sum.inr q₂ => { right; exact p₁ ⬝ q₂ }
        | Sum.inr p₂, Sum.inl q₁ => { right; exact p₂ ⬝ ap _ q₁ }
        | Sum.inr p₂, Sum.inr q₂ => { left;  exact p₂ ⬝ ap _ q₂ ⬝ invInv _ } }
    end⟩

  notation "⌈" G "⌉" => «Sosnitsky construction» G

  hott def Absolutizer (G : Group.{u}) :=
  Σ (φ : ⌈G⌉ → G.carrier), φ ∘ Relquot.elem ∘ φ ~ φ

  section
    variable (φ : Absolutizer G)
    def Absolutizer.ap := φ.fst ∘ Relquot.elem

    hott def Absolutizer.idem : φ.ap ∘ φ.ap ~ φ.ap :=
    λ x, φ.snd (Relquot.elem x)

    hott def Absolutizer.even : φ.ap ∘ G.ι ~ φ.ap :=
    begin
      intro; apply Id.ap φ.1; apply Relquot.sound;
      apply HITs.Merely.elem; right; reflexivity
    end

    hott def Absolutizer.inv : Absolutizer G :=
    ⟨G.ι ∘ φ.fst,
    begin
      intro; apply Id.ap G.ι;
      transitivity; apply φ.even; apply φ.2
    end⟩

    hott def Absolutizer.comp₁ : φ.ap ∘ φ.inv.ap ~ φ.ap :=
    begin intro; transitivity; apply φ.even; apply φ.idem end

    hott def Absolutizer.comp₂ : φ.inv.ap ∘ φ.ap ~ φ.inv.ap :=
    begin intro x; apply Id.ap G.ι; apply φ.idem end

    hott def Absolutizer.mul : ⌈G⌉ → ⌈G⌉ → ⌈G⌉ :=
    begin
      fapply Relquot.lift₂;
      { intros a b; apply Relquot.elem; exact G.φ (φ.ap a) (φ.ap b) };
      { apply Relquot.set };
      { intro a₁ a₂ b₁ b₂ (p : ∥_∥); induction p;
        { case elemπ p =>
          intro (q : ∥_∥); induction q;
          { case elemπ q =>
            apply Id.ap Relquot.elem; apply Equiv.bimap;
            { induction p using Sum.casesOn;
              { apply Id.ap; assumption };
              { transitivity; apply Id.ap; assumption;
                apply Absolutizer.even } };
            { induction q using Sum.casesOn;
              { apply Id.ap; assumption };
              { transitivity; apply Id.ap; assumption;
                apply Absolutizer.even } } };
          apply Relquot.set };
        apply Structures.piProp; intro; apply Relquot.set }
    end

    hott def Absolutizer.one : ⌈G⌉ :=
    Relquot.elem G.e
  end
end Group

end GroundZero.Algebra
