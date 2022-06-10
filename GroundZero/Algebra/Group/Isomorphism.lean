import GroundZero.Algebra.Group.Symmetric
import GroundZero.Algebra.Group.Factor

open GroundZero.Types.Equiv (biinv transport)
open GroundZero.Types.Id (map)
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Proto
open GroundZero

/-
  First isomorphism theorem: Im φ ≅ G\ker φ.
  * https://en.wikipedia.org/wiki/Fundamental_theorem_on_homomorphisms
  * https://en.wikipedia.org/wiki/First_isomorphism_theorem#Theorem_A

  Cayley’s theorem.
  * https://en.wikipedia.org/wiki/Cayley's_theorem
-/

namespace GroundZero.Algebra

namespace Group
  variable {G : Group}

  section
    variable {H : Group}

    hott def ker.encode {φ : Hom G H} : factorLeft G (ker φ) → im.carrier φ :=
    begin
      fapply HITs.Quotient.rec;
      { intro x; existsi φ.fst x;
        apply HITs.Merely.elem; existsi x; reflexivity };
      { intro x y (p : _ = _); fapply Sigma.prod; transitivity;
        symmetry; apply invInv; apply invEqOfMulEqOne; transitivity;
        { apply map (H.φ · (φ.1 y)); symmetry; apply homoInv };
        transitivity; { symmetry; apply homoMul }; apply p;
        apply HITs.Merely.uniq };
      { apply Ens.hset; apply H.hset }
    end

    noncomputable hott def ker.encodeInj {φ : Hom G H} :
      Π (x y : factorLeft G (ker φ)), ker.encode x = ker.encode y → x = y :=
    begin
      fapply @HITs.Quotient.indProp _ _ (λ x, Π y, ker.encode x = ker.encode y → x = y) <;> intro x;
      { fapply @HITs.Quotient.indProp _ _ (λ y, ker.encode _ = ker.encode y → _ = y) <;> intro y;
        { intro p; apply HITs.Quotient.sound;
          change _ = _; transitivity; apply homoMul;
          transitivity; apply Id.map (H.φ · (φ.1 y));
          apply homoInv; apply mulEqOneOfInvEq;
          transitivity; apply invInv;
          apply (Sigma.sigmaEqOfEq p).1 };
        { apply implProp; apply HITs.Quotient.set } };
      { apply piProp; intro; apply implProp; apply HITs.Quotient.set }
    end

    hott def ker.incl {φ : Hom G H} : G.carrier → factorLeft G (ker φ) :=
    Factor.incl

    noncomputable hott def ker.decodeSigma {φ : Hom G H} :
      Π (x : im.carrier φ), fib ker.encode x :=
    begin
      intro ⟨x, (p : ∥_∥)⟩; induction p; case elemπ z =>
      { existsi ker.incl z.1; fapply Types.Sigma.prod;
        apply z.2; apply HITs.Merely.uniq };
      case uniqπ p q =>
      { fapply Types.Sigma.prod;
        { apply ker.encodeInj; transitivity;
          exact p.2; symmetry; exact q.2 };
        { apply Ens.hset; apply H.hset } }
    end

    noncomputable hott def ker.decode {φ : Hom G H}
      (x : im.carrier φ) : factorLeft G (ker φ) :=
    (ker.decodeSigma x).1

    abbrev Im (φ : Hom G H) : Group :=
    Subgroup H (im φ)

    -- First isomorphism theorem.
    noncomputable hott def firstIsoTheorem {φ : Hom G H} : Im φ ≅ G\ker φ :=
    begin
      fapply mkiso; exact ker.decode;
      { intro ⟨a, (A : ∥_∥)⟩ ⟨b, (B : ∥_∥)⟩; induction A; induction B;
        reflexivity; apply HITs.Quotient.set; apply HITs.Quotient.set };
      apply Prod.mk <;> existsi ker.encode;
      { intro x; apply (ker.decodeSigma x).2 };
      { fapply GroundZero.HITs.Quotient.indProp; intro;
        reflexivity; intro; apply HITs.Quotient.set }
    end
  end

  noncomputable hott def S.iso : Im (S.univ G) ≅ G :=
  begin
    fapply Iso.trans firstIsoTheorem;
    apply Iso.symm; fapply Iso.trans triv.factor;
    apply Factor.iso S.univ.ker.decode S.univ.ker.encode
  end

  hott def Hom.id.encode : G.carrier → im.carrier (Hom.id G.1) :=
  λ x, ⟨x, HITs.Merely.elem ⟨x, idp x⟩⟩

  hott def Hom.id.decode : im.carrier (Hom.id G.1) → G.carrier :=
  Sigma.fst

  hott def Hom.id.iso : G ≅ Im (Hom.id G.1) :=
  begin
    fapply mkiso; exact Hom.id.encode;
    { intros a b; fapply Sigma.prod;
      reflexivity; apply Ens.prop };
    apply Prod.mk <;> existsi Hom.id.decode;
    { intro; reflexivity };
    { intro; fapply Sigma.prod;
      reflexivity; apply Ens.prop }
  end

  -- Cayley’s theorem
  noncomputable hott def Cayley : Σ (φ : subgroup (S G.1.zero)), Subgroup (S G.1.zero) φ ≅ G :=
  ⟨im (S.univ G), S.iso⟩
end Group

end GroundZero.Algebra