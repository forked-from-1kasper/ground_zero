import ground_zero.HITs.circle
open ground_zero.theorems (funext)
open ground_zero.HITs.circle
open ground_zero.structures
open ground_zero.types.Id
open ground_zero.types

/-
  Homotopical reals R.
  * HoTT 8.1.5
-/

namespace ground_zero.HITs
universes u v w

hott theory
local notation ℤ := integer

inductive reals.rel : ℤ → ℤ → Type
| glue (x : ℤ) : reals.rel x (integer.succ x)
def reals := graph reals.rel
notation `R` := reals

namespace reals
  def elem : ℤ → R := graph.elem
  @[hott] def glue (z : ℤ) : elem z = elem (integer.succ z) :> R :=
  graph.line (rel.glue z)

  @[hott] def ind {π : R → Type u} (cz : Π x, π (elem x))
    (sz : Π z, cz z =[glue z] cz (integer.succ z)) (u : R) : π u := begin
    fapply graph.ind, exact cz,
    { intros u v H, induction H, apply sz }
  end

  @[hott] noncomputable def indβrule {π : R → Type u}
    (cz : Π x, π (elem x))
    (sz : Π z, cz z =[glue z] cz (integer.succ z))
    (z : ℤ) : equiv.apd (ind cz sz) (glue z) = sz z :=
  by apply graph.indβrule

  @[hott] def rec {π : Type u} (cz : ℤ → π)
    (sz : Π z, cz z = cz (integer.succ z) :> π) : R → π :=
  ind cz (λ x, equiv.pathover_of_eq (glue x) (sz x))

  @[hott] noncomputable def recβrule {π : Type u} (cz : ℤ → π)
    (sz : Π z, cz z = cz (integer.succ z) :> π) (z : ℤ) :
    rec cz sz # (glue z) = sz z := begin
    apply equiv.pathover_of_eq_inj (glue z), transitivity,
    symmetry, apply equiv.apd_over_constant_family,
    transitivity, apply indβrule, reflexivity
  end

  @[hott] def positive : Π n, elem 0 = elem (integer.pos n) :> R
  |    0    := idp (elem 0)
  | (n + 1) := positive n ⬝ glue (integer.pos n)

  @[hott] def negative : Π n, elem 0 = elem (integer.neg n) :> R
  |    0    := (glue (integer.neg 0))⁻¹
  | (n + 1) := negative n ⬝ (glue $ integer.neg (n + 1))⁻¹

  @[hott] def center : Π z, elem 0 = elem z :> R
  | (integer.pos n) := positive n
  | (integer.neg n) := negative n

  @[hott] def vect (u v : ℤ) : elem u = elem v :> R :=
  (center u)⁻¹ ⬝ center v

  @[hott] def contr : ground_zero.structures.contr R :=
  { point := elem 0,
    intro := @ind (λ x, elem 0 = x :> R) center (begin
      intro z, apply Id.trans,
      apply equiv.transport_composition,
      induction z,
      { trivial },
      { induction z with z ih,
        { apply Id.inv_comp },
        { transitivity, symmetry, apply Id.assoc,
          transitivity, apply Id.map, apply Id.inv_comp,
          transitivity, apply Id.refl_right,
          reflexivity } }
    end) }

  @[hott] def dist : Π (u v : R), u = v :> R :=
  ground_zero.structures.contr_impl_prop contr

  @[hott] def lift (f : ℤ → ℤ) : R → R :=
  rec (elem ∘ f) (begin intros, apply dist end)

  @[hott] def operator (f : ℤ → ℤ → ℤ) : R → R → R :=
  rec (λ x, rec (elem ∘ f x) (begin intros, apply dist end))
    (begin intros, apply ground_zero.theorems.funext, intro x, apply dist end)

  instance : has_coe integer R := ⟨elem⟩

  instance : has_zero R := ⟨elem 0⟩
  instance : has_one R := ⟨elem 1⟩

  @[hott] def cis : R → S¹ := rec (λ _, base) (λ _, loop)

  @[hott] def helix_over_cis (x : R) : helix (cis x) = ℤ :=
  begin change _ = helix (cis 0), apply map (helix ∘ cis), apply dist end

  /-
            ≃
       S¹ ←–––– R/τℤ
       ↑          ↑
   eⁱ⁻ |          |
       |          |
       R ════════ R
  -/
  @[hott] noncomputable def Euler := calc
    fib cis base ≃ (Σ (x : R), circle.base = cis x) :
                   sigma.hmtpy_inv_eqv cis (λ _, circle.base)
             ... = (Σ (x : R), helix (cis x)) :
                   sigma # (funext (λ x, ground_zero.ua (circle.family (cis x))))
             ... = (Σ (x : R), ℤ) : sigma # (funext helix_over_cis)
             ... ≃ R × ℤ : sigma.const R ℤ
             ... ≃ 𝟏 × ℤ : ground_zero.ua.product_equiv₃
                             (contr_equiv_unit contr) (equiv.id ℤ)
             ... ≃ ℤ : prod_unit_equiv ℤ
end reals

def complex := R × R
notation `C` := complex

namespace complex
  def inj (x : R) : C := ⟨x, 0⟩

  abbreviation Re : C → R := prod.pr₁
  abbreviation Im : C → R := prod.pr₂
end complex

end ground_zero.HITs