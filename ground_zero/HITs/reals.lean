import ground_zero.HITs.circle ground_zero.HITs.interval
open ground_zero.types.eq (renaming refl -> idp)
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

  def ind {π : R → Sort u} (cz : Π x, π (elem x))
    (sz : Π z, cz z =[glue z] cz (integer.succ z))
    (u : R) : π u := begin
    fapply graph.ind, exact cz,
    { intros u v H, cases H, apply sz }
  end

  def rec {π : Sort u} (cz : ℤ → π)
    (sz : Π z, cz z = cz (integer.succ z) :> π) : R → π :=
  ind cz (λ x, dep_path.pathover_of_eq (glue x) (sz x))

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
      intro z, apply equiv.path_over_subst,
      transitivity, apply equiv.transport_composition,
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

  def turn : Π (x : S¹), x = x :=
  circle.ind circle.loop (begin
    apply equiv.path_over_subst,
    transitivity, apply equiv.transport_inv_comp_comp,
    transitivity, apply eq.map (⬝ loop),
    apply eq.inv_comp, apply eq.refl_left
  end)

  def μ : S¹ → S¹ → S¹ :=
  circle.rec id (interval.funext turn)

  def inv : S¹ → S¹ :=
  circle.rec base loop⁻¹

  noncomputable def inv_inv (x : S¹) : inv (inv x) = x :=
  let invₚ := @eq.map S¹ S¹ base base (inv ∘ inv) in
  begin
    fapply circle.ind _ _ x; clear x,
    { reflexivity },
    { apply equiv.path_over_subst, calc
        equiv.transport (λ x, inv (inv x) = x) loop eq.rfl =
                              invₚ loop⁻¹ ⬝ eq.rfl ⬝ loop :
      by apply equiv.transport_over_involution
        ... = invₚ loop⁻¹ ⬝ (eq.rfl ⬝ loop) :
      begin symmetry, apply eq.assoc end
        ... = inv # (inv # loop⁻¹) ⬝ loop :
      begin apply eq.map (⬝ loop), apply equiv.map_over_comp end
        ... = inv # (inv # loop)⁻¹ ⬝ loop :
      begin apply eq.map (⬝ loop),
            apply eq.map, apply eq.map_inv end
        ... = inv # loop⁻¹⁻¹ ⬝ loop :
      begin apply eq.map (⬝ loop),
            apply eq.map, apply eq.map,
            apply circle.recβrule₂ end
        ... = inv # loop ⬝ loop :
      begin apply eq.map (⬝ loop),
            apply eq.map, apply eq.inv_inv end
        ... = loop⁻¹ ⬝ loop :
      begin apply eq.map (⬝ loop), apply circle.recβrule₂ end
        ... = eq.rfl : by apply eq.inv_comp }
  end

  def S {α β γ : Sort u} (f : α → β → γ) (g : α → β) := λ x, f x (g x)
  def fixed {α : Sort u} (f : α → α) (x : α) := f x = x

  def transport_over_subst {α : Sort u} {a b : α}
    (f : α → α → α) (g : α → α) (p : a = b) (q : S f g a = a) :
    equiv.transport (fixed (S f g)) p q =
    (@eq.map α α b a (S f g) p⁻¹) ⬝ q ⬝ p := begin
    induction p, symmetry,
    transitivity, apply eq.refl_left (q ⬝ idp a),
    apply eq.refl_right
  end

  def bimap {α β γ : Sort u} {a b : α} {a' b' : β}
    (f : α → β → γ) (p : a = b) (q : a' = b') : f a a' = f b b' :=
  begin induction p, induction q, reflexivity end

  def map_over_subst {α : Sort u} {a b : α}
    (f : α → α → α) (g : α → α) (p : a = b) :
    (S f g # p) = @bimap α α α a b (g a) (g b) f p (g # p) :=
  begin induction p, reflexivity end

  def function_map {α β γ : Sort u} {a b : α} {a' b' : β}
    (f : α → β → γ) (p : f a = f b) (q : a' = b') : f a a' = f b b' :=
  begin induction q, apply eq.map (λ (f : β → γ), f a'), exact p end

  def bimap_inv {α : Sort u} {a b : α}
    (f : α → α → α) (p : a = b) :
    bimap f p p⁻¹ = {!!} :=
  sorry

  noncomputable def mul_inv (x : S¹) : base = (S μ inv) x := begin
    fapply circle.ind _ _ x; clear x,
    { exact circle.loop },
    { apply equiv.path_over_subst,
      transitivity, apply equiv.transport_comp,
      transitivity, apply equiv.transport_composition,
      transitivity, apply eq.map, apply map_over_subst,
      transitivity, apply eq.map, apply eq.map, apply circle.recβrule₂,
      admit }
  end

  def associator {α : Sort u} (μ : α → α → α) (a b : α) :=
  λ x, μ (μ x a) b = μ x (μ a b)

  def transport_over_associator {α : Sort u} {u v a b : α} (μ : α → α → α)
    (p : u = v) (q : associator μ a b u) :
    equiv.transport (associator μ a b) p q =
    @eq.map α α v u (λ x, μ (μ x a) b) p⁻¹ ⬝ q ⬝
      (λ x, μ x (μ a b)) # p := begin
    induction p, symmetry, change _ = q,
    transitivity, apply eq.refl_left, apply eq.refl_right
  end

  def mul_assoc (x y z : S¹) : μ (μ x y) z = μ x (μ y z) := begin
    fapply circle.ind _ _ x; clear x,
    { reflexivity },
    { apply equiv.path_over_subst,
      transitivity, apply transport_over_associator,
      transitivity, apply eq.map (⬝ eq.map (λ (x : S¹), μ x (μ y z)) loop),
      apply eq.refl_right,
      transitivity, apply eq.map (⬝ eq.map (λ (x : S¹), μ x (μ y z)) loop),
      apply eq.map_inv, apply equiv.rewrite_comp,
      symmetry, transitivity, apply eq.refl_right,
      admit }
  end

  def kernel := fib cis base

  def integer_add_succ (x y : ℤ) : x + integer.succ y = integer.succ (x + y) := begin
    induction x; induction y,
    { trivial },
    { admit },
    { admit },
    { admit }
  end

  def power_succ (x : ℤ) : circle.power (integer.succ x) = circle.power x ⬝ circle.loop := begin
    induction x,
    { trivial },
    { induction x with x ih,
      { symmetry, apply eq.inv_comp },
      { symmetry, transitivity, symmetry, apply eq.assoc,
        transitivity, apply eq.map (ground_zero.types.eq.trans _),
        apply eq.inv_comp circle.loop, transitivity,
        apply eq.refl_right, reflexivity } }
  end

  noncomputable def indβrule {π : R → Sort u} (cz : Π x, π (elem x))
    (sz : Π z, cz z =[glue z] cz (integer.succ z))
    (z : ℤ) : dep_path.apd (ind cz sz) (glue z) = sz z :=
  by apply graph.indβrule

  --def glue_transport {π : R → Type u} (f : Π x, π (elem x)) (x : ℤ) :
  --  equiv.subst (glue x) (f x) = f (integer.succ x) := begin
  --  admit
  --end

  def subst_on_refl (x y : R) (p : x = y) :
    equiv.transport (λ x, x = x) (cis # p) (idp (cis x)) = idp (cis y) :=
  begin induction p, trivial end

  def cis_homomorphism (x y : R) : cis (x + y) = μ (cis x) (cis y) := begin
    fapply ind _ _ x; clear x; intro x,
    change _ = cis y, apply eq.map, apply dist,
    apply equiv.path_over_subst,
    admit
  end

  def integer_succ_add (x y : ℤ) : integer.succ x + y = integer.succ (x + y) := begin
    admit
  end

  def f' (x : R) : circle.helix (cis x) → Ω¹(S¹) := begin
    fapply ind _ _ x; clear x,
    { intros x y, exact circle.power (x + y) },
    { intros, apply equiv.path_over_subst,
      admit }
  end

  def f : (Σ' (x : R), circle.helix (cis x)) → Ω¹(S¹)
  | ⟨x, h⟩ := f' x h

  def g (p : Ω¹(S¹)) : Σ' x, circle.helix (cis x) :=
  ⟨0, circle.winding p⟩

  lemma lem1 : (Σ' (x : R), circle.helix (cis x)) ≃ Ω¹(S¹) := begin
    existsi f, split; existsi g,
    { intro p, simp, cases p with x p,
      unfold f, unfold f', unfold g,
      fapply sigma.prod, apply dist,
      admit },
    { intro p, simp, unfold g, unfold f, unfold f',
      
      admit }
  end

  /-
    (Σ' (x : S¹), helix x) ≃
    (Σ' (x : S¹), base = x)

    (Σ' (x : R), cis x = circle.base) =
    (Σ' (x : R), circle.base = cis x) ≃
    (Σ' (x : R), helix (cis x))

    helix (cis x) = ℤ
  -/

  noncomputable def total_group {α : Sort u} (f : α → S¹) (x : α) : ℤ = helix (f x) := begin
    fapply @circle.ind (λ x, ℤ = helix x) _ _ (f x),
    { refl },
    { apply equiv.path_over_subst,
      transitivity, apply equiv.transport_comp,
      transitivity, apply eq.map (λ p, equiv.subst p (idp ℤ)),
      apply circle.recβrule₂,
      transitivity, apply equiv.transport_composition,
      admit }
  end

  def helix_over_cis (x : R) : ℤ = helix (cis x) :=
  begin
    fapply ind _ _ x; clear x,
    { intro x, reflexivity },
    { intro z, apply equiv.path_over_subst,
      admit }
  end

  /-
            ≃
       S¹ ←–––– R/τℤ
       ↑          ↑
   eⁱ⁻ |          |
       |          |
       R ════════ R
  -/
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

  abbreviation Re : C → R := product.pr₁
  abbreviation Im : C → R := product.pr₂
end complex

end ground_zero.HITs