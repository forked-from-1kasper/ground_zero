import ground_zero.HITs.merely
open ground_zero.types

hott theory

namespace ground_zero.theorems.logic
  universe u

  inductive wff
  | impl  : wff → wff → wff
  | box   : wff → wff
  | false : wff

  infixr ` ⇒ `:20 := wff.impl
  prefix `□`:90 := wff.box

  notation `⊥` := wff.false

  def not (φ : wff) := φ ⇒ ⊥
  prefix `¬` := not

  def diam (φ : wff) := ¬□¬φ
  prefix `◇`:90 := diam

  namespace S5
    inductive deriv : wff → Type
    | mp  : Π φ ψ, deriv (φ ⇒ ψ) → deriv φ → deriv ψ
    | nec : Π φ, deriv φ → deriv □φ
    | ak  : Π φ ψ, deriv (φ ⇒ ψ ⇒ φ)
    | as  : Π φ ψ ξ, deriv ((φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ))
    | ac  : Π φ ψ, deriv ((¬φ ⇒ ¬ψ) ⇒ (ψ ⇒ φ))
    | K   : Π φ ψ, deriv (□(φ ⇒ ψ) ⇒ □φ ⇒ □ψ)
    | T   : Π φ, deriv (□φ ⇒ φ)
    | «5» : Π φ, deriv (◇φ ⇒ □◇φ)
  end S5

  prefix `⊢₅ `:10 := S5.deriv

  @[hott] def I (φ : wff) : ⊢₅ φ ⇒ φ :=
  begin
    apply S5.deriv.mp,
    { apply S5.deriv.mp,
      apply S5.deriv.as φ (φ ⇒ φ) φ,
      apply S5.deriv.ak },
    apply S5.deriv.ak
  end

  def or (φ ψ : wff) := ¬φ ⇒ ψ
  notation φ ` ∨ ` ψ := or φ ψ

  def lem (φ : wff) : ⊢₅ φ ∨ ¬φ :=
  I ¬φ

  def true : wff := ¬⊥
  notation `⊤` := true

  @[hott] def true.intro : ⊢₅ ⊤ :=
  I ⊥

  @[hott] def mp₂ (φ ψ ξ : wff) : (⊢₅ φ ⇒ ψ ⇒ ξ) → (⊢₅ φ) → (⊢₅ ψ) → (⊢₅ ξ) :=
  begin
    intros p q r, apply S5.deriv.mp ψ, apply S5.deriv.mp φ,
    exact p, exact q, exact r
  end

  @[hott] def impl.intro (φ ψ : wff) (h : ⊢₅ ψ) : ⊢₅ φ ⇒ ψ :=
  begin apply S5.deriv.mp, apply S5.deriv.ak, assumption end

  @[hott] def S {φ ψ ξ : wff} (f : ⊢₅ φ ⇒ ψ ⇒ ξ) (g : ⊢₅ φ ⇒ ψ) : ⊢₅ φ ⇒ ξ :=
  begin apply mp₂, apply S5.deriv.as φ ψ ξ, exact f, exact g end

  @[hott] def AS {φ ψ ξ : wff} (f : ⊢₅ φ ⇒ ψ ⇒ ξ) : ⊢₅ (φ ⇒ ψ) ⇒ (φ ⇒ ξ) :=
  begin apply S5.deriv.mp, apply S5.deriv.as, exact f end

  -- https://en.wikipedia.org/wiki/Hypothetical_syllogism#Proof
  @[hott] def impl.comp (φ ψ ξ : wff) : ⊢₅ (ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ) :=
  begin
    apply S5.deriv.mp ((ψ ⇒ ξ) ⇒ (φ ⇒ ψ ⇒ ξ)),
    apply AS, apply impl.intro,
    apply S5.deriv.as, apply S5.deriv.ak
  end

  @[hott] def hypsyll (φ ψ ξ : wff) : (⊢₅ ψ ⇒ ξ) → (⊢₅ φ ⇒ ψ) → (⊢₅ φ ⇒ ξ) :=
  begin apply mp₂, apply impl.comp end

  -- https://en.wikipedia.org/wiki/Hilbert_system#Some_useful_theorems_and_their_proofs
  @[hott] def impl.symm (φ ψ ξ : wff) : ⊢₅ (φ ⇒ ψ ⇒ ξ) ⇒ (ψ ⇒ φ ⇒ ξ) :=
  begin
    apply S5.deriv.mp ((φ ⇒ ψ ⇒ ξ) ⇒ (ψ ⇒ φ ⇒ ψ)),
    apply S5.deriv.mp ((φ ⇒ ψ ⇒ ξ) ⇒ (ψ ⇒ φ ⇒ ψ) ⇒ (ψ ⇒ φ ⇒ ξ)),
    apply S5.deriv.as, apply hypsyll _ ((φ ⇒ ψ) ⇒ (φ ⇒ ξ)) _,
    apply impl.comp, apply S5.deriv.as, apply impl.intro, apply S5.deriv.ak
  end

  @[hott] def impl.trans (φ ψ ξ : wff) : ⊢₅ (φ ⇒ ψ) ⇒ (ψ ⇒ ξ) ⇒ (φ ⇒ ξ) :=
  begin apply S5.deriv.mp, apply impl.symm, apply impl.comp end

  @[hott] def impl.symm₂ (φ ψ ξ ζ : wff) : ⊢₅ (φ ⇒ ψ ⇒ ζ ⇒ ξ) ⇒ (ζ ⇒ ψ ⇒ φ ⇒ ξ) :=
  begin
    apply hypsyll, apply impl.symm,
    fapply hypsyll, exact (ψ ⇒ φ ⇒ ζ ⇒ ξ),
    apply S5.deriv.mp, apply impl.comp,
    apply impl.symm, apply impl.symm
  end

  @[hott] def impl.apply (φ ψ : wff) : ⊢₅ φ ⇒ (φ ⇒ ψ) ⇒ ψ :=
  begin apply S5.deriv.mp, apply impl.symm, apply I end

  @[hott] def dneg.intro (φ : wff) : ⊢₅ φ ⇒ ¬¬φ :=
  by apply impl.apply

  @[hott] def dneg.elim (φ : wff) : ⊢₅ ¬¬φ ⇒ φ :=
  begin apply S5.deriv.mp, apply S5.deriv.ac, apply dneg.intro end

  @[hott] def explode (φ : wff) : ⊢₅ ⊥ ⇒ φ :=
  begin
    apply S5.deriv.mp, apply S5.deriv.ac,
    apply impl.intro, apply true.intro
  end

  @[hott] def contradiction (φ ψ : wff) : ⊢₅ φ ⇒ ¬φ ⇒ ψ :=
  begin
    apply S5.deriv.mp, apply impl.symm,
    apply AS, apply impl.intro, apply explode
  end

  @[hott] def contraposition (φ ψ : wff) : ⊢₅ (φ ⇒ ψ) ⇒ (¬ψ ⇒ ¬φ) :=
  begin apply S5.deriv.mp, apply impl.symm, apply impl.comp end

  @[hott] def contraposition₁ (φ ψ : wff) : ⊢₅ (φ ⇒ ¬ψ) ⇒ ψ ⇒ ¬φ :=
  begin
    apply hypsyll, apply S5.deriv.ac,
    apply S5.deriv.mp, apply impl.trans, apply dneg.elim
  end

  @[hott] def contraposition₂ (φ ψ : wff) : ⊢₅ (¬φ ⇒ ψ) ⇒ ¬ψ ⇒ φ :=
  begin
    apply hypsyll, apply S5.deriv.ac,
    apply S5.deriv.mp, apply impl.comp, apply dneg.intro
  end

  @[hott] def or.swap (φ ψ : wff) : ⊢₅ φ ∨ ψ ⇒ ψ ∨ φ :=
  begin
    apply hypsyll, apply S5.deriv.ac,
    apply AS, apply impl.intro, apply dneg.intro
  end

  @[hott] def or.inl (φ ψ : wff) : ⊢₅ φ ⇒ φ ∨ ψ :=
  by apply contradiction

  @[hott] def or.inr (φ ψ : wff) : ⊢₅ ψ ⇒ φ ∨ ψ :=
  begin apply hypsyll, apply or.swap, apply or.inl end

  def and (φ ψ : wff) := ¬(φ ⇒ ¬ψ)
  notation φ ` ∧ ` ψ := and φ ψ

  @[hott] def and.intro (φ ψ : wff) : ⊢₅ φ ⇒ ψ ⇒ φ ∧ ψ :=
  begin
    apply S5.deriv.mp, apply impl.symm,
    apply S5.deriv.mp, apply impl.symm₂, apply I
  end

  @[hott] def and.symm (φ ψ : wff) : ⊢₅ φ ∧ ψ ⇒ ψ ∧ φ :=
  begin apply S5.deriv.mp, apply contraposition, apply contraposition₁ end

  @[hott] def and.pr₁ (φ ψ : wff) : ⊢₅ φ ∧ ψ ⇒ φ :=
  begin
    apply S5.deriv.mp, apply contraposition₂,
    apply S5.deriv.mp, apply impl.symm, apply contradiction
  end

  @[hott] def and.pr₂ (φ ψ : wff) : ⊢₅ φ ∧ ψ ⇒ ψ :=
  begin apply hypsyll, apply and.pr₁, exact φ, apply and.symm end

  def iff (φ ψ : wff) := (φ ⇒ ψ) ∧ (ψ ⇒ φ)
  infix ` ⇔ `:20 := iff

  @[hott] def iff.intro (φ ψ : wff) (f : ⊢₅ φ ⇒ ψ) (g : ⊢₅ ψ ⇒ φ) : ⊢₅ φ ⇔ ψ :=
  begin apply mp₂, apply and.intro, exact f, exact g end

  @[hott] def dneg (φ : wff) : ⊢₅ φ ⇔ ¬¬φ :=
  begin apply iff.intro, apply dneg.intro, apply dneg.elim end

  @[hott] def dedup (φ ψ : wff) : ⊢₅ (φ ⇒ φ ⇒ ψ) ⇒ (φ ⇒ ψ) :=
  begin
    apply S5.deriv.mp,
    apply S5.deriv.mp, apply impl.symm,
    apply S5.deriv.as, apply I
  end

  @[hott] def dup (φ ψ : wff) : ⊢₅ (φ ⇒ ψ) ⇒ (φ ⇒ φ ⇒ ψ) :=
  by apply S5.deriv.ak
end ground_zero.theorems.logic