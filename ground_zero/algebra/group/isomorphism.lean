import ground_zero.algebra.group.factor ground_zero.algebra.group.symmetric
open ground_zero.types.equiv (biinv transport)
open ground_zero.types.Id (map)
open ground_zero.structures
open ground_zero.types
open ground_zero.proto
open ground_zero

/-
  First isomorphism theorem: Im φ ≅ G\ker φ.
  * https://en.wikipedia.org/wiki/Fundamental_theorem_on_homomorphisms
  * https://en.wikipedia.org/wiki/First_isomorphism_theorem#Theorem_A

  Cayley’s theorem.
  * https://en.wikipedia.org/wiki/Cayley's_theorem
-/

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group
  variables {G : pregroup} [group G]
  local infix ` * ` := G.φ

  section
    variables {H : pregroup} [group H]
    local infix ` × `:50 := H.φ

    @[hott] def ker.encode {φ : G ⤳ H} : factor_left G (ker φ) → im.carrier φ :=
    begin
      fapply HITs.quotient.rec,
      { intro x, existsi φ.fst x, apply HITs.merely.elem,
        existsi x, trivial },
      { intros x y p, fapply sigma.prod,
        change _ = _ at p, transitivity,
        { symmetry, apply inv_inv },
        apply inv_eq_of_mul_eq_one, transitivity,
        { apply map (× φ.fst y), symmetry, apply homo_inv },
        transitivity, { symmetry, apply homo_mul }, apply p,
        apply HITs.merely.uniq },
      { apply ens.hset, intros a b, apply H.hset }
    end

    @[hott] noncomputable def ker.encode_inj {φ : G ⤳ H} :
      Π (x y : factor_left G (ker φ)),
        ker.encode x = ker.encode y → x = y :=
    begin
      intros x y, fapply ground_zero.HITs.quotient.ind_prop _ _ x; clear x; intro x,
      { fapply ground_zero.HITs.quotient.ind_prop _ _ y; clear y; intro y,
        { intro p, apply ground_zero.HITs.quotient.sound,
          change _ = _, transitivity, apply homo_mul,
          transitivity, { apply Id.map (× φ.fst y), apply homo_inv },
          apply mul_eq_one_of_inv_eq,
          transitivity, apply inv_inv,
          apply (sigma.sigma_eq_of_eq p).fst },
        { apply impl_prop, apply HITs.quotient.set } },
      { apply impl_prop, apply HITs.quotient.set }
    end

    @[hott] def ker.incl {φ : G ⤳ H} : G.carrier → factor_left G (ker φ) :=
    factor.incl

    @[hott] noncomputable def ker.decode_sigma {φ : G ⤳ H} :
      Π (x : im.carrier φ), fib ker.encode x :=
    begin
      intro x, induction x with x p,
      fapply ground_zero.HITs.merely.ind _ _ p; intro z,
      { induction z with z q, existsi ker.incl z,
        fapply ground_zero.types.sigma.prod, apply q,
        apply HITs.merely.uniq },
      { intros u v, induction u with u q, induction v with v G,
        fapply ground_zero.types.sigma.prod,
        { apply ker.encode_inj, transitivity, exact q,
          symmetry, exact G },
        { apply ens.hset, intros a b, apply H.hset } }
    end

    @[hott] noncomputable def ker.decode {φ : G ⤳ H}
      (x : im.carrier φ) : factor_left G (ker φ) :=
    (ker.decode_sigma x).fst

    abbreviation Im (φ : G ⤳ H) : pregroup :=
    Subgroup H (im φ)

    -- First isomorphism theorem.
    @[hott] noncomputable def first_iso_theorem
      {φ : G ⤳ H} : Im φ ≅ G\ker φ :=
    begin
      fapply mkiso, exact ker.decode,
      { intros a b, induction a with a A, induction b with b B,
        change ∥_∥ at A, change ∥_∥ at B,
        fapply ground_zero.HITs.merely.ind _ _ A; clear A; intro A,
        { fapply ground_zero.HITs.merely.ind _ _ B; clear B; intro B,
          { induction A, induction B, reflexivity },
          { apply HITs.quotient.set } },
        { apply HITs.quotient.set } },
      split; existsi ker.encode,
      { intro x, apply (ker.decode_sigma x).snd },
      { fapply ground_zero.HITs.quotient.ind_prop; intro x,
        { trivial }, { apply HITs.quotient.set } }
    end
  end

  @[hott] noncomputable def S.iso : Im (S.univ G) ≅ G :=
  begin
    fapply iso.trans first_iso_theorem,
    symmetry, fapply iso.trans triv.factor,
    apply factor.iso S.univ.ker.decode S.univ.ker.encode
  end

  open ground_zero.algebra.pregroup (subgroup)

  -- Cayley’s theorem
  @[hott] noncomputable def Cayley :
    Σ (φ : subgroup (S G.zero)), Subgroup (S G.zero) φ ≅ G :=
  ⟨im (S.univ G), S.iso⟩

  @[hott] def homo.id.encode :
    G.carrier → im.carrier (homo.id G) :=
  λ x, ⟨x, HITs.merely.elem ⟨x, idp x⟩⟩

  @[hott] def homo.id.decode : im.carrier (homo.id G) → G.carrier :=
  sigma.fst

  @[hott] def homo.id.iso : G ≅ Im (homo.id G) :=
  begin
    fapply mkiso, exact homo.id.encode,
    { intros a b, fapply sigma.prod,
      reflexivity, apply ens.prop },
    split; existsi homo.id.decode,
    { intro x, reflexivity }, assumption,
    { intro x, induction x with x H,
      fapply sigma.prod, reflexivity,
      apply ens.prop }, assumption
  end
end group

end ground_zero.algebra