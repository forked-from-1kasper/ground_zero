import ground_zero.theorems.functions
import ground_zero.HITs.circle
open ground_zero.theorems.functions (injective)
open ground_zero.types.equiv (transport)
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
    (sz : Π z, cz z =[glue z] cz (integer.succ z)) (u : R) : π u :=
  begin
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
    rec cz sz # (glue z) = sz z := 
  begin
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

  @[hott] def contractible : contr R :=
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
  ground_zero.structures.contr_impl_prop contractible

  @[hott] def lift (f : ℤ → ℤ) : R → R :=
  rec (elem ∘ f) (begin intros, apply dist end)

  @[hott] def operator (f : ℤ → ℤ → ℤ) : R → R → R :=
  rec (λ x, rec (elem ∘ f x) (begin intros, apply dist end))
    (begin intros, apply ground_zero.theorems.funext, intro x, apply dist end)

  instance : has_coe integer R := ⟨elem⟩

  instance : has_zero R := ⟨elem 0⟩
  instance : has_one R := ⟨elem 1⟩

  section
    variables {α : Type⁎} (H : prop α.space)
    variables (φ : Map⁎ α ⟨S¹, base⟩)
    include H

    @[hott] def helix_over_homo (x : α.space) : helix (φ.ap x) = ℤ :=
    begin
      transitivity, apply map (helix ∘ φ.ap),
      apply H x α.point, change _ = helix base,
      apply map helix, apply φ.id
    end

    @[hott] noncomputable def fib_of_homo (x : S¹) := calc
      fib φ.ap x ≃ (Σ z, φ.ap z = x) :
        equiv.id (fib φ.ap x)
             ... = (Σ z, φ.ap α.point = x) :
        sigma # (funext (λ z, (λ u, φ.ap u = x) # (H z α.point)))
             ... = (Σ z, base = x) :
        sigma # (funext (λ _, (= x) # φ.id))
             ... = (Σ z, helix x) :
        sigma # (funext (λ z, ground_zero.ua (circle.family x)))
             ... ≃ α.space × (helix x) :
        sigma.const α.space (helix x)
             ... ≃ 𝟏 × (helix x) :
        ground_zero.ua.product_equiv₃
          (contr_equiv_unit ⟨α.point, H α.point⟩)
          (equiv.id (helix x))
             ... ≃ helix x :
        prod_unit_equiv (helix x)

    @[hott] noncomputable def ker_of_homo : fib φ.ap base ≃ ℤ :=
    fib_of_homo H φ base
  end

  /-
            ≃
       S¹ ←–––– R/τℤ
       ↑          ↑
   eⁱ⁻ |          |
       |          |
       R ════════ R
  -/
  @[hott] def cis : R → S¹ := rec (λ _, base) (λ _, loop)

  @[hott] noncomputable def Euler : fib cis base ≃ ℤ :=
  @ker_of_homo ⟨R, 0⟩ dist ⟨cis, idp base⟩

  -- Another (more tricky) proof, but it does not use R contractibility
  @[hott] noncomputable def helix_over_cis (x : R) : helix (cis x) = ℤ :=
  begin
    fapply ind _ _ x; clear x,
    { intro x, exact (integer.shift x)⁻¹ },
    { intro z, change _ = _,
      let p := integer.shift z, calc
            equiv.transport (λ x, helix (cis x) = ℤ) (glue z) (integer.shift z)⁻¹
          = @Id.map R Type _ _ (helix ∘ cis) (glue z)⁻¹ ⬝ (integer.shift z)⁻¹ :
        by apply equiv.transport_over_contr_map
      ... = (Id.map (helix ∘ cis) (glue z))⁻¹ ⬝ (integer.shift z)⁻¹ :
        begin apply Id.map (⬝ p⁻¹), apply Id.map_inv end
      ... = (helix # (cis # (glue z)))⁻¹ ⬝ (integer.shift z)⁻¹ :
        begin apply Id.map (λ q, inv q ⬝ p⁻¹),
              apply equiv.map_over_comp end
      ... = (helix # loop)⁻¹ ⬝ (integer.shift z)⁻¹ :
        begin apply Id.map (λ q, inv q ⬝ p⁻¹),
              apply Id.map, apply recβrule end
      ... = integer.succ_path⁻¹ ⬝ (integer.shift z)⁻¹ :
        begin apply Id.map (λ q, inv q ⬝ p⁻¹),
              apply circle.recβrule₂ end
      ... = (integer.shift z ⬝ integer.succ_path)⁻¹ :
        begin symmetry, apply Id.explode_inv end
      ... = (integer.shift (integer.succ z))⁻¹ :
        begin apply Id.map, apply integer.shift_comp end }
  end

  @[hott] def phi_eqv_base_impl_contr {α : Type u} {x : α}
    (H : Π (φ : α → S¹), φ x = base) : contr S¹ :=
  ⟨base, λ y, (H (λ _, y))⁻¹⟩

  @[hott] def phi_neq_base_impl_false {α : Type u} {x : α}
    (φ : α → S¹) : ¬¬(φ x = base) :=
  begin
    fapply @circle.ind (λ b, ¬¬(b = base)) _ _ (φ x),
    { intro p, apply p, reflexivity },
    { change _ = _, apply impl_prop empty_is_prop }
  end

  @[hott] def lem_inf_impl_dneg_inf (H : LEM∞)
    {α : Type u} : ¬¬α → α :=
  begin
    intro p, cases H α with u v,
    { assumption }, { cases p v }
  end

  @[hott] noncomputable def circle_not_hset : ¬(hset S¹) :=
  begin intro H, apply circle.loop_neq_refl, apply H end

  @[hott] noncomputable def lem_inf_disproved : LEM∞ → 𝟎 :=
  begin
    intro H, apply circle_not_hset, apply prop_is_set,
    apply contr_impl_prop,
    apply phi_eqv_base_impl_contr,
    intro φ, apply lem_inf_impl_dneg_inf H,
    apply phi_neq_base_impl_false φ,
    exact R, exact 0
  end

  @[hott] def zero.decode {α : Type u} (f : 𝟏 → α) : α := f ★
  @[hott] def zero.encode {α : Type u} (x : α) : 𝟏 → α := λ _, x

  @[hott] def zero.desc {α : Type u} : (𝟏 → α) ≃ α :=
  begin
    existsi zero.decode, split; existsi zero.encode,
    { intro f, apply ground_zero.theorems.funext,
      intro x, induction x, trivial },
    { intro x, trivial }
  end

  @[hott] noncomputable def cis_family : (R → S¹) ≃ S¹ :=
  @transport Type (λ α, (α → S¹) ≃ S¹) 𝟏 R
    (Id.symm $ ground_zero.ua (contr_equiv_unit contractible)) zero.desc

  @[hott] def countable (α : Type u) :=
  ∥(Σ (f : α → ℕ), injective f)∥

  @[hott] noncomputable def circle_uncountable : ¬(countable S¹) :=
  begin
    fapply ground_zero.HITs.merely.rec, apply empty_is_prop,
    intro p, cases p with f p, apply circle_not_hset,
    apply prop_is_set, intros x y, apply p,
    { fapply circle.ind _ _ x,
      { fapply circle.ind _ _ y,
        { reflexivity },
        { apply ground_zero.theorems.nat.nat_is_set } },
      { apply ground_zero.theorems.nat.nat_is_set } }
  end
end reals

def complex := R × R
notation `C` := complex

namespace complex
  def inj (x : R) : C := ⟨x, 0⟩

  abbreviation Re : C → R := prod.pr₁
  abbreviation Im : C → R := prod.pr₂
end complex

end ground_zero.HITs