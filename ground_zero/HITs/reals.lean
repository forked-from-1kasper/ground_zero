import ground_zero.HITs.circle
open ground_zero.types.eq
open ground_zero.HITs.circle
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
  def glue (z : ℤ) : elem z = elem (integer.succ z) :> R :=
  graph.line (rel.glue z)

  def ind {π : R → Type u} (cz : Π x, π (elem x))
    (sz : Π z, cz z =[glue z] cz (integer.succ z))
    (u : R) : π u := begin
    fapply graph.ind, exact cz,
    { intros u v H, cases H, apply sz }
  end

  def rec {π : Type u} (cz : ℤ → π)
    (sz : Π z, cz z = cz (integer.succ z) :> π) : R → π :=
  ind cz (λ x, equiv.pathover_of_eq (glue x) (sz x))

  def positive : Π n, elem 0 = elem (integer.pos n) :> R
  | 0 := ground_zero.types.eq.refl (elem 0)
  | (n + 1) := positive n ⬝ glue (integer.pos n)

  def negative : Π n, elem 0 = elem (integer.neg n) :> R
  | 0 := (glue (integer.neg 0))⁻¹
  | (n + 1) := negative n ⬝ (glue $ integer.neg (n + 1))⁻¹

  def center : Π z, elem 0 = elem z :> R
  | (integer.pos n) := positive n
  | (integer.neg n) := negative n

  def vect (u v : ℤ) : elem u = elem v :> R :=
  (center u)⁻¹ ⬝ center v

  def contr : ground_zero.structures.contr R :=
  { point := elem 0,
    intro := @ind (λ x, elem 0 = x :> R) center (begin
      intro z, apply ground_zero.types.eq.trans,
      apply equiv.transport_composition,
      induction z,
      { trivial },
      { induction z with z ih,
        { apply eq.inv_comp },
        { transitivity, symmetry, apply eq.assoc,
          transitivity, apply eq.map, apply eq.inv_comp,
          transitivity, apply eq.refl_right,
          reflexivity } }
    end) }

  def dist : Π (u v : R), u = v :> R :=
  ground_zero.structures.contr_impl_prop contr

  def lift (f : ℤ → ℤ) : R → R :=
  rec (elem ∘ f) (begin intros, apply dist end)

  def operator (f : ℤ → ℤ → ℤ) : R → R → R :=
  rec (λ x, rec (elem ∘ f x) (begin intros, apply dist end))
    (begin intros, apply interval.funext, intro x, apply dist end)

  instance : has_neg R := ⟨lift integer.negate⟩

  instance : has_add R := ⟨operator integer.add⟩
  instance : has_sub R := ⟨operator integer.sub⟩
  instance : has_mul R := ⟨operator integer.mul⟩

  instance : has_coe integer R := ⟨elem⟩

  instance : has_zero R := ⟨elem 0⟩
  instance : has_one R := ⟨elem 1⟩

  def cis : R → S¹ := rec (λ _, base) (λ _, loop)
end reals

def complex := R × R
notation `C` := complex

namespace complex
  def inj (x : R) : C := ⟨x, 0⟩

  def add : C → C → C
  | ⟨a, b⟩ ⟨c, d⟩ := ⟨a + c, b + d⟩
  instance : has_add C := ⟨add⟩

  def mul : C → C → C
  | ⟨a, b⟩ ⟨c, d⟩ := ⟨a * c - b * d, a * d + b * c⟩
  instance : has_mul C := ⟨mul⟩

  def neg : C → C
  | ⟨a, b⟩ := ⟨-a, -b⟩
  instance : has_neg C := ⟨neg⟩

  instance : has_coe R C := ⟨inj⟩
  instance : has_zero C := ⟨inj 0⟩
  instance : has_one C := ⟨inj 1⟩

  def i : C := ⟨0, 1⟩
  example : i * i = -1 := by trivial

  def conj : C → C
  | ⟨a, b⟩ := ⟨a, -b⟩

  abbreviation Re : C → R := prod.pr₁
  abbreviation Im : C → R := prod.pr₂
end complex

end ground_zero.HITs