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

  def compl (φ : prop ι) : prop ι := λ x, ¬φ x
  prefix `¬` := compl

  inductive deriv : wff ι → Type u
  -- classical propositional calculus
  | mp  : Π φ ψ, deriv (φ ⇒ ψ) → deriv φ → deriv ψ
  | nec : Π φ, deriv φ → deriv □φ
  | ak  : Π φ ψ, deriv (φ ⇒ ψ ⇒ φ)
  | as  : Π φ ψ ξ, deriv ((φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ))
  | ac  : Π φ ψ, deriv ((¬φ ⇒ ¬ψ) ⇒ (ψ ⇒ φ))
  -- classical predicate logic
  | ap  : Π x (φ : prop ι), deriv ((⋀ y, φ y) ⇒ φ x)
  | dis : Π (φ ψ : prop ι), deriv ((⋀ x, φ x ⇒ ψ x) ⇒ (⋀ x, φ x) ⇒ (⋀ y, ψ y))
  -- S5 modal logic
  | K   : Π φ ψ, deriv (□(φ ⇒ ψ) ⇒ □φ ⇒ □ψ)
  | T   : Π φ, deriv (□φ ⇒ φ)
  | «5» : Π φ, deriv (◇φ ⇒ □◇φ)
  -- ontological logic
  | ps  : Π (φ ψ : prop ι), deriv (P φ ∧ □(φ ⊆ ψ) ⇒ ¬(P ¬ψ))
  | gp  : deriv (P G)
  open deriv

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

  @[hott] def iff.antcdtsubst {φ ψ ξ : wff ι} (f : ⊢ φ ⇔ ψ) (g : ⊢ ξ ⇒ φ) : ⊢ ξ ⇒ ψ :=
  begin apply hypsyll, apply iff.left f, exact g end

  @[hott] def iff.consqsubst {φ ψ ξ : wff ι} (f : ⊢ φ ⇔ ψ) (g : ⊢ φ ⇒ ξ) : ⊢ ψ ⇒ ξ :=
  begin apply hypsyll, exact g, apply iff.right f end

  @[hott] def dneg (φ : wff ι) : ⊢ φ ⇔ ¬¬φ :=
  begin apply iff.intro, apply dneg.intro, apply dneg.elim end

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
end ground_zero.theorems.logic