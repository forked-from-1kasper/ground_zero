import GroundZero.HITs.Quotient
open GroundZero.Types.Equiv (pathoverOfEq)

/-
  Sequential Colimit.
  * https://homotopytypetheory.org/2016/01/08/Colimits-in-hott/
-/

namespace GroundZero.HITs
universe u v

inductive Colimit.core (A : ℕ → Type u)
  (f : Π (n : ℕ), A n → A (n + 1))
| incl {n : ℕ} : A n → core A f

inductive Colimit.rel (A : ℕ → Type u) (f : Π (n : ℕ), A n → A (n + 1)) :
  Colimit.core A f → Colimit.core A f → Type u
| glue (n : ℕ) (x : A n) : rel A f (core.incl (f n x)) (core.incl x)

hott definition Colimit (A : ℕ → Type u) (f : Π (n : ℕ), A n → A (n + 1)) :=
Quotient (Colimit.rel A f)

namespace Colimit
  variable {A : ℕ → Type u} {f : Π (n : ℕ), A n → A (n + 1)}

  hott definition incl {n : ℕ} (x : A n) : Colimit A f :=
  Quotient.elem (core.incl x)

  hott definition inclusion (n : ℕ) : A n → Colimit A f := incl

  hott definition glue {n : ℕ} (x : A n) : incl (f n x) = @incl A f n x :=
  Quotient.line (Colimit.rel.glue n x)

  hott definition ind {B : Colimit A f → Type v} (inclπ : Π (n : ℕ) (x : A n), B (incl x))
    (glueπ : Π (n : ℕ) (x : A n), inclπ (n + 1) (f n x) =[glue x] inclπ n x) : Π x, B x :=
  begin
    intro x; fapply Quotient.ind;
    { intro (core.incl x); apply inclπ };
    { intros u v H; induction H; apply glueπ }
  end

  attribute [eliminator] ind

  hott definition rec {B : Type v} (inclπ : Π (n : ℕ), A n → B)
    (glueπ : Π (n : ℕ) (x : A n), inclπ (n + 1) (f n x) = inclπ n x) : Colimit A f → B :=
  ind @inclπ (λ n x, pathoverOfEq (glue x) (glueπ n x))
end Colimit

end GroundZero.HITs
