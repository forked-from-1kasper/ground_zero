import ground_zero.HITs.merely
open ground_zero.types

hott theory

namespace ground_zero.theorems.logic
  universe u

  -- individuals
  variable {ι : Type u}

  inductive wff (ι : Type u)
  | P        : (ι → wff) → wff -- positive
  | «forall» : (ι → wff) → wff -- for all
  | G        : ι → wff         -- god-like
  | impl     : wff → wff → wff -- implication
  | box      : wff → wff       -- necessary
  | false    : wff             -- falsehood
  open wff (P G)

  -- property
  def prop (ι : Type u) := ι → wff ι

  notation `⋀` binders `, ` r:(scoped φ, wff.«forall» φ) := r

  infixr ` ⇒ `:20 := wff.impl
  prefix `□`:90 := wff.box

  notation `⊥` := wff.false

  def not (φ : wff ι) := φ ⇒ ⊥
  prefix `¬` := not

  def diam (φ : wff ι) := ¬□¬φ
  prefix `◇`:90 := diam

  def «exists» (φ : prop ι) := ¬⋀ x, ¬φ x
  notation `⋁` binders `, ` r:(scoped φ, «exists» φ) := r

  def or (φ ψ : wff ι) := ¬φ ⇒ ψ
  notation φ ` ∨ ` ψ := or φ ψ

  def and (φ ψ : wff ι) := ¬(φ ⇒ ¬ψ)
  notation φ ` ∧ ` ψ := and φ ψ

  def iff (φ ψ : wff ι) := (φ ⇒ ψ) ∧ (ψ ⇒ φ)
  infix ` ⇔ `:20 := iff

  def subset (φ ψ : prop ι) :=
  ⋀ x, φ x ⇒ ψ x
  infix ⊆ := subset

  def equal (φ ψ : prop ι) :=
  ⋀ x, φ x ⇔ ψ x
  infix ` ≡ ` := equal

  def compl (φ : prop ι) : prop ι := λ x, ¬φ x
  prefix `¬` := compl

  inductive deriv : wff ι → Type u
  -- classical propositional calculus
  | mp   : Π φ ψ, deriv (φ ⇒ ψ) → deriv φ → deriv ψ
  | ak   : Π φ ψ, deriv (φ ⇒ ψ ⇒ φ)
  | ac   : Π φ ψ, deriv ((¬φ ⇒ ¬ψ) ⇒ (ψ ⇒ φ))
  | as   : Π φ ψ ξ, deriv ((φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ))
  -- classical predicate logic
  | gen  : Π (φ : prop ι), (Π x, deriv (φ x)) → deriv (⋀ x, φ x)
  | ap   : Π (x : ι) (φ : prop ι), deriv ((⋀ y, φ y) ⇒ φ x)
  | dis  : Π (φ ψ : prop ι), deriv ((⋀ x, φ x ⇒ ψ x) ⇒ (⋀ x, φ x) ⇒ (⋀ y, ψ y))
  | triv : Π (x φ : wff ι), deriv (φ ⇒ ⋀ x, φ)
  -- S5 modal logic
  | nec  : Π φ, deriv φ → deriv □φ
  | K    : Π φ ψ, deriv (□(φ ⇒ ψ) ⇒ □φ ⇒ □ψ)
  | T    : Π φ, deriv (□φ ⇒ φ)
  | «5»  : Π φ, deriv (◇φ ⇒ □◇φ)
  -- ontological logic
  | gd₁  : Π x, (Π (φ : prop ι), deriv (□(φ x) ⇔ P φ)) → deriv (G x)
  | gd₂  : Π (x : ι) (φ : prop ι), deriv (G x ⇒ P φ ⇔ □(φ x))
  | wkc  : Π (φ ψ : prop ι), deriv (□(φ ≡ ψ) ⇒ P φ ⇔ P ψ)
  | pimp : Π (φ ψ : prop ι), deriv (P φ ⇒ □(φ ⊆ ψ) ⇒ ¬(P ¬ψ))
  | gp   : deriv (P G)
  open deriv

  prefix `⊢ `:10 := deriv
  local prefix `⊢ `:10 := @deriv ι

  @[hott] def I (φ : wff ι) : ⊢ φ ⇒ φ :=
  begin
    apply mp, apply mp, apply as φ (φ ⇒ φ) φ,
    apply ak, apply ak
  end

  def lem (φ : wff ι) : ⊢ φ ∨ ¬φ :=
  I ¬φ

  def true : wff ι := ¬⊥
  notation `⊤` := true

  @[hott] def true.intro : ⊢ ⊤ :=
  I ⊥

  @[hott] def mp₂ (φ ψ ξ : wff ι) : (⊢ φ ⇒ ψ ⇒ ξ) → (⊢ φ) → (⊢ ψ) → (⊢ ξ) :=
  begin
    intros p q r, apply mp ψ, apply mp φ,
    exact p, exact q, exact r
  end

  @[hott] def impl.intro (φ ψ : wff ι) (h : ⊢ ψ) : ⊢ φ ⇒ ψ :=
  begin apply mp, apply ak, assumption end

  @[hott] def S {φ ψ ξ : wff ι} (f : ⊢ φ ⇒ ψ ⇒ ξ) (g : ⊢ φ ⇒ ψ) : ⊢ φ ⇒ ξ :=
  begin apply mp₂, apply as φ ψ ξ, exact f, exact g end

  @[hott] def AS {φ ψ ξ : wff ι} (f : ⊢ φ ⇒ ψ ⇒ ξ) : ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ ξ) :=
  begin apply mp, apply as, exact f end

  -- https://en.wikipedia.org/wiki/Hypothetical_syllogism#Proof
  @[hott] def impl.comp (φ ψ ξ : wff ι) : ⊢ (ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ) :=
  begin
    apply mp ((ψ ⇒ ξ) ⇒ (φ ⇒ ψ ⇒ ξ)),
    apply AS, apply impl.intro,
    apply as, apply ak
  end

  @[hott] def hypsyll (φ ψ ξ : wff ι) : (⊢ ψ ⇒ ξ) → (⊢ φ ⇒ ψ) → (⊢ φ ⇒ ξ) :=
  begin apply mp₂, apply impl.comp end

  -- https://en.wikipedia.org/wiki/Hilbert_system#Some_useful_theorems_and_their_proofs
  @[hott] def impl.symm (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ψ ⇒ ξ) ⇒ (ψ ⇒ φ ⇒ ξ) :=
  begin
    apply mp ((φ ⇒ ψ ⇒ ξ) ⇒ (ψ ⇒ φ ⇒ ψ)),
    apply mp ((φ ⇒ ψ ⇒ ξ) ⇒ (ψ ⇒ φ ⇒ ψ) ⇒ (ψ ⇒ φ ⇒ ξ)),
    apply as, apply hypsyll _ ((φ ⇒ ψ) ⇒ (φ ⇒ ξ)) _,
    apply impl.comp, apply as, apply impl.intro, apply ak
  end

  @[hott] def impl.trans (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ ξ) ⇒ (φ ⇒ ξ) :=
  begin apply mp, apply impl.symm, apply impl.comp end

  @[hott] def impl.symm₂ (φ ψ ξ ζ : wff ι) : ⊢ (φ ⇒ ψ ⇒ ζ ⇒ ξ) ⇒ (ζ ⇒ ψ ⇒ φ ⇒ ξ) :=
  begin
    apply hypsyll, apply impl.symm,
    fapply hypsyll, exact (ψ ⇒ φ ⇒ ζ ⇒ ξ),
    apply mp, apply impl.comp,
    apply impl.symm, apply impl.symm
  end

  @[hott] def impl.apply (φ ψ : wff ι) : ⊢ φ ⇒ (φ ⇒ ψ) ⇒ ψ :=
  begin apply mp, apply impl.symm, apply I end

  @[hott] def dneg.intro (φ : wff ι) : ⊢ φ ⇒ ¬¬φ :=
  by apply impl.apply

  @[hott] def dneg.elim (φ : wff ι) : ⊢ ¬¬φ ⇒ φ :=
  begin apply mp, apply ac, apply dneg.intro end

  @[hott] def explode (φ : wff ι) : ⊢ ⊥ ⇒ φ :=
  begin
    apply mp, apply ac,
    apply impl.intro, apply true.intro
  end

  @[hott] def contradiction (φ ψ : wff ι) : ⊢ φ ⇒ ¬φ ⇒ ψ :=
  begin
    apply mp, apply impl.symm,
    apply AS, apply impl.intro, apply explode
  end

  @[hott] def contraposition (φ ψ : wff ι) : ⊢ (φ ⇒ ψ) ⇒ (¬ψ ⇒ ¬φ) :=
  begin apply mp, apply impl.symm, apply impl.comp end

  @[hott] def contraposition₁ (φ ψ : wff ι) : ⊢ (φ ⇒ ¬ψ) ⇒ ψ ⇒ ¬φ :=
  begin
    apply hypsyll, apply ac,
    apply mp, apply impl.trans, apply dneg.elim
  end

  @[hott] def contraposition₂ (φ ψ : wff ι) : ⊢ (¬φ ⇒ ψ) ⇒ ¬ψ ⇒ φ :=
  begin
    apply hypsyll, apply ac,
    apply mp, apply impl.comp, apply dneg.intro
  end

  @[hott] def or.swap (φ ψ : wff ι) : ⊢ φ ∨ ψ ⇒ ψ ∨ φ :=
  begin
    apply hypsyll, apply ac,
    apply AS, apply impl.intro, apply dneg.intro
  end

  @[hott] def or.inl (φ ψ : wff ι) : ⊢ φ ⇒ φ ∨ ψ :=
  by apply contradiction

  @[hott] def or.inr (φ ψ : wff ι) : ⊢ ψ ⇒ φ ∨ ψ :=
  begin apply hypsyll, apply or.swap, apply or.inl end

  @[hott] def and.intro (φ ψ : wff ι) : ⊢ φ ⇒ ψ ⇒ φ ∧ ψ :=
  begin
    apply mp, apply impl.symm,
    apply mp, apply impl.symm₂, apply I
  end

  @[hott] def and.symm (φ ψ : wff ι) : ⊢ φ ∧ ψ ⇒ ψ ∧ φ :=
  begin apply mp, apply contraposition, apply contraposition₁ end

  @[hott] def and.pr₁ (φ ψ : wff ι) : ⊢ φ ∧ ψ ⇒ φ :=
  begin
    apply mp, apply contraposition₂,
    apply mp, apply impl.symm, apply contradiction
  end

  @[hott] def and.pr₂ (φ ψ : wff ι) : ⊢ φ ∧ ψ ⇒ ψ :=
  begin apply hypsyll, apply and.pr₁, exact φ, apply and.symm end

  @[hott] def iff.intro (φ ψ : wff ι) (f : ⊢ φ ⇒ ψ) (g : ⊢ ψ ⇒ φ) : ⊢ φ ⇔ ψ :=
  begin apply mp₂, apply and.intro, exact f, exact g end

  @[hott] def iff.left {φ ψ : wff ι} (H : ⊢ φ ⇔ ψ) : ⊢ φ ⇒ ψ :=
  begin apply mp, apply and.pr₁, exact (ψ ⇒ φ), exact H end

  @[hott] def iff.right {φ ψ : wff ι} (H : ⊢ φ ⇔ ψ) : ⊢ ψ ⇒ φ :=
  begin apply mp, apply and.pr₂, exact (φ ⇒ ψ), exact H end

  @[hott] def iff.symm {φ ψ : wff ι} (H : ⊢ φ ⇔ ψ) : ⊢ ψ ⇔ φ :=
  begin apply mp, apply and.symm, exact H end

  @[hott] def iff.antcdtsubst {φ ψ ξ : wff ι} (f : ⊢ φ ⇔ ψ) (g : ⊢ ξ ⇒ φ) : ⊢ ξ ⇒ ψ :=
  begin apply hypsyll, apply iff.left f, exact g end

  @[hott] def iff.consqsubst {φ ψ ξ : wff ι} (f : ⊢ φ ⇔ ψ) (g : ⊢ φ ⇒ ξ) : ⊢ ψ ⇒ ξ :=
  begin apply hypsyll, exact g, apply iff.right f end

  @[hott] def iff.antcdtiff {φ ψ ξ : wff ι} (H : ⊢ φ ⇔ ψ) : ⊢ (ξ ⇒ φ) ⇔ (ξ ⇒ ψ) :=
  begin
    apply iff.intro, apply mp, apply impl.comp, apply iff.left H,
    apply mp, apply impl.comp, apply iff.right H
  end

  @[hott] def iff.consqiff {φ ψ ξ : wff ι} (H : ⊢ φ ⇔ ψ) : ⊢ (φ ⇒ ξ) ⇔ (ψ ⇒ ξ) :=
  begin
    apply iff.intro, apply mp, apply impl.trans, apply iff.right H,
    apply mp, apply impl.trans, apply iff.left H
  end

  @[hott] def dneg (φ : wff ι) : ⊢ φ ⇔ ¬¬φ :=
  begin apply iff.intro, apply dneg.intro, apply dneg.elim end

  @[hott] def contrapos₁ (φ ψ : wff ι) : ⊢ (φ ⇒ ψ) ⇔ (¬ψ ⇒ ¬φ) :=
  begin apply iff.intro, apply contraposition, apply ac end

  @[hott] def contrapos₂ (φ ψ : wff ι) : ⊢ (φ ⇒ ¬ψ) ⇔ (ψ ⇒ ¬φ) :=
  begin apply iff.intro; apply contraposition₁ end

  @[hott] def dedup (φ ψ : wff ι) : ⊢ (φ ⇒ φ ⇒ ψ) ⇒ (φ ⇒ ψ) :=
  begin apply mp, apply mp, apply impl.symm, apply as, apply I end

  @[hott] def dup (φ ψ : wff ι) : ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ φ ⇒ ψ) :=
  by apply ak

  @[hott] def impl.negdef₁ (φ ψ : wff ι) : ⊢ ¬(φ ⇒ ψ) ⇒ (φ ∧ ¬ψ) :=
  begin
    apply mp, apply contraposition,
    apply mp, apply impl.comp, apply dneg.elim
  end

  @[hott] def impl.negdef₂ (φ ψ : wff ι) : ⊢ (φ ∧ ¬ψ) ⇒ ¬(φ ⇒ ψ) :=
  begin
    apply mp, apply contraposition,
    apply mp, apply impl.comp, apply dneg.intro
  end

  @[hott] def impl.negdef (φ ψ : wff ι) : ⊢ ¬(φ ⇒ ψ) ⇔ (φ ∧ ¬ψ) :=
  begin apply iff.intro, apply impl.negdef₁, apply impl.negdef₂ end

  @[hott] def rot₁ (φ ψ ξ : wff ι) : ⊢ (¬ξ ⇒ φ ⇒ ¬ψ) ⇒ (φ ⇒ ψ ⇒ ξ) :=
  begin
    apply hypsyll, apply mp, apply impl.comp,
    exact (¬ξ ⇒ ¬ψ), apply ac, apply impl.symm
  end

  @[hott] def rot₂ (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ψ ⇒ ξ) ⇒ (¬ξ ⇒ φ ⇒ ¬ψ) :=
  begin
    apply hypsyll, apply impl.symm,
    apply mp, apply impl.comp,
    apply contraposition
  end

  @[hott] def curry (φ ψ ξ : wff ι) : ⊢ (φ ∧ ψ ⇒ ξ) ⇒ (φ ⇒ ψ ⇒ ξ) :=
  begin apply hypsyll, apply rot₁, apply contraposition₂ end

  @[hott] def uncurry (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ψ ⇒ ξ) ⇒ (φ ∧ ψ ⇒ ξ) :=
  begin apply hypsyll, apply contraposition₂, apply rot₂ end

  @[hott] def boximpl (φ ψ : wff ι) (H : ⊢ φ ⇒ ψ) : ⊢ □φ ⇒ □ψ :=
  begin apply mp, apply K, apply nec, exact H end

  @[hott] def boxcongr (φ ψ : wff ι) (H : ⊢ φ ⇔ ψ) : ⊢ □φ ⇔ □ψ :=
  begin apply iff.intro; apply boximpl, apply iff.left H, apply iff.right H end

  @[hott] def negiff (φ ψ : wff ι) (H : ⊢ φ ⇔ ψ) : ⊢ ¬φ ⇔ ¬ψ :=
  begin
    apply iff.intro, apply mp, apply contraposition, apply iff.right H,
    apply mp, apply contraposition, apply iff.left H
  end

  @[hott] def impl.comp₃ (φ ψ ξ θ : wff ι) : ⊢ (φ ⇒ ψ ⇒ ξ) ⇒ (θ ⇒ φ) ⇒ (θ ⇒ ψ) ⇒ (θ ⇒ ξ) :=
  begin
    apply mp, apply impl.symm, apply mp, apply curry,
    apply hypsyll, apply as, apply mp, apply uncurry, apply impl.trans
  end

  @[hott] def and.impl (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ ξ) ⇒ (φ ⇒ ψ ∧ ξ) :=
  begin apply mp, apply impl.comp₃, apply and.intro end

  @[hott] def prodpimp (φ ψ : prop ι) : ⊢ P φ ∧ □(φ ⊆ ψ) ⇒ ¬(P ¬ψ) :=
  begin apply mp, apply uncurry, apply pimp end

  @[hott] def impl.pr₁ (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ψ ∧ ξ) ⇒ (φ ⇒ ψ) :=
  begin apply mp, apply impl.comp, apply and.pr₁ end

  @[hott] def impl.pr₂ (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ψ ∧ ξ) ⇒ (φ ⇒ ξ) :=
  begin apply mp, apply impl.comp, apply and.pr₂ end

  @[hott] def subset.refl (φ : prop ι) : ⊢ φ ⊆ φ :=
  begin apply gen, intro x, apply I end

  @[hott] def prop.dneg (φ : prop ι) : ⊢ (¬¬φ) ≡ φ :=
  begin apply gen, intro x, apply iff.symm, apply dneg end

  @[hott] def thm1 (φ : prop ι) : ⊢ P φ ⇒ ◇ ⋁ x, φ x :=
  begin
    apply mp, apply ac, apply iff.consqsubst, apply dneg,
    apply iff.consqsubst, apply boxcongr, apply dneg,
    apply iff.antcdtsubst, apply negiff, apply mp, apply wkc,
    exact ¬¬φ, apply nec, apply prop.dneg,
    apply hypsyll, apply prodpimp, exact G,
    apply mp₂, apply and.impl, apply impl.intro, apply gp,
    apply mp, apply K, apply nec,
    apply mp, apply dis, apply gen, intro x, apply ak
  end

  @[hott] def perfneg (φ : prop ι) : ⊢ P φ ⇒ ¬(P ¬φ) :=
  begin
    apply hypsyll, apply prodpimp φ φ,
    apply mp, apply mp, apply impl.symm, apply and.intro,
    apply nec, apply subset.refl
  end

  @[hott] def thm2 : ⊢ ◇ ⋁ x, G x :=
  begin apply mp, apply thm1, apply gp end

  @[hott] def thm3 (x : ι) : ⊢ G x ⇒ □G x :=
  begin
    apply mp₂, apply as, exact P G,
    apply mp, apply impl.pr₁, exact (□G x ⇒ P G),
    apply gd₂, apply impl.intro, apply gp
  end
end ground_zero.theorems.logic