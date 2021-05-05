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

  inductive deriv : wff → Type
  | mp  : Π φ ψ, deriv (φ ⇒ ψ) → deriv φ → deriv ψ
  | nec : Π φ, deriv φ → deriv □φ
  | ak  : Π φ ψ, deriv (φ ⇒ ψ ⇒ φ)
  | as  : Π φ ψ ξ, deriv ((φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ))
  | ac  : Π φ ψ, deriv ((¬φ ⇒ ¬ψ) ⇒ (ψ ⇒ φ))
  | K   : Π φ ψ, deriv (□(φ ⇒ ψ) ⇒ □φ ⇒ □ψ)
  | T   : Π φ, deriv (□φ ⇒ φ)
  | «5» : Π φ, deriv (◇φ ⇒ □◇φ)
  open deriv

  prefix `⊢ `:10 := deriv

  @[hott] def I (φ : wff) : ⊢ φ ⇒ φ :=
  begin
    apply mp, apply mp, apply as φ (φ ⇒ φ) φ,
    apply ak, apply ak
  end

  def or (φ ψ : wff) := ¬φ ⇒ ψ
  notation φ ` ∨ ` ψ := or φ ψ

  def lem (φ : wff) : ⊢ φ ∨ ¬φ :=
  I ¬φ

  def true : wff := ¬⊥
  notation `⊤` := true

  @[hott] def true.intro : ⊢ ⊤ :=
  I ⊥

  @[hott] def mp₂ (φ ψ ξ : wff) : (⊢ φ ⇒ ψ ⇒ ξ) → (⊢ φ) → (⊢ ψ) → (⊢ ξ) :=
  begin
    intros p q r, apply mp ψ, apply mp φ,
    exact p, exact q, exact r
  end

  @[hott] def impl.intro (φ ψ : wff) (h : ⊢ ψ) : ⊢ φ ⇒ ψ :=
  begin apply mp, apply ak, assumption end

  @[hott] def S {φ ψ ξ : wff} (f : ⊢ φ ⇒ ψ ⇒ ξ) (g : ⊢ φ ⇒ ψ) : ⊢ φ ⇒ ξ :=
  begin apply mp₂, apply as φ ψ ξ, exact f, exact g end

  @[hott] def AS {φ ψ ξ : wff} (f : ⊢ φ ⇒ ψ ⇒ ξ) : ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ ξ) :=
  begin apply mp, apply as, exact f end

  -- https://en.wikipedia.org/wiki/Hypothetical_syllogism#Proof
  @[hott] def impl.comp (φ ψ ξ : wff) : ⊢ (ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ) :=
  begin
    apply mp ((ψ ⇒ ξ) ⇒ (φ ⇒ ψ ⇒ ξ)),
    apply AS, apply impl.intro,
    apply as, apply ak
  end

  @[hott] def hypsyll (φ ψ ξ : wff) : (⊢ ψ ⇒ ξ) → (⊢ φ ⇒ ψ) → (⊢ φ ⇒ ξ) :=
  begin apply mp₂, apply impl.comp end

  -- https://en.wikipedia.org/wiki/Hilbert_system#Some_useful_theorems_and_their_proofs
  @[hott] def impl.symm (φ ψ ξ : wff) : ⊢ (φ ⇒ ψ ⇒ ξ) ⇒ (ψ ⇒ φ ⇒ ξ) :=
  begin
    apply mp ((φ ⇒ ψ ⇒ ξ) ⇒ (ψ ⇒ φ ⇒ ψ)),
    apply mp ((φ ⇒ ψ ⇒ ξ) ⇒ (ψ ⇒ φ ⇒ ψ) ⇒ (ψ ⇒ φ ⇒ ξ)),
    apply as, apply hypsyll _ ((φ ⇒ ψ) ⇒ (φ ⇒ ξ)) _,
    apply impl.comp, apply as, apply impl.intro, apply ak
  end

  @[hott] def impl.trans (φ ψ ξ : wff) : ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ ξ) ⇒ (φ ⇒ ξ) :=
  begin apply mp, apply impl.symm, apply impl.comp end

  @[hott] def impl.symm₂ (φ ψ ξ ζ : wff) : ⊢ (φ ⇒ ψ ⇒ ζ ⇒ ξ) ⇒ (ζ ⇒ ψ ⇒ φ ⇒ ξ) :=
  begin
    apply hypsyll, apply impl.symm,
    fapply hypsyll, exact (ψ ⇒ φ ⇒ ζ ⇒ ξ),
    apply mp, apply impl.comp,
    apply impl.symm, apply impl.symm
  end

  @[hott] def impl.apply (φ ψ : wff) : ⊢ φ ⇒ (φ ⇒ ψ) ⇒ ψ :=
  begin apply mp, apply impl.symm, apply I end

  @[hott] def dneg.intro (φ : wff) : ⊢ φ ⇒ ¬¬φ :=
  by apply impl.apply

  @[hott] def dneg.elim (φ : wff) : ⊢ ¬¬φ ⇒ φ :=
  begin apply mp, apply ac, apply dneg.intro end

  @[hott] def explode (φ : wff) : ⊢ ⊥ ⇒ φ :=
  begin
    apply mp, apply ac,
    apply impl.intro, apply true.intro
  end

  @[hott] def contradiction (φ ψ : wff) : ⊢ φ ⇒ ¬φ ⇒ ψ :=
  begin
    apply mp, apply impl.symm,
    apply AS, apply impl.intro, apply explode
  end

  @[hott] def contraposition (φ ψ : wff) : ⊢ (φ ⇒ ψ) ⇒ (¬ψ ⇒ ¬φ) :=
  begin apply mp, apply impl.symm, apply impl.comp end

  @[hott] def contraposition₁ (φ ψ : wff) : ⊢ (φ ⇒ ¬ψ) ⇒ ψ ⇒ ¬φ :=
  begin
    apply hypsyll, apply ac,
    apply mp, apply impl.trans, apply dneg.elim
  end

  @[hott] def contraposition₂ (φ ψ : wff) : ⊢ (¬φ ⇒ ψ) ⇒ ¬ψ ⇒ φ :=
  begin
    apply hypsyll, apply ac,
    apply mp, apply impl.comp, apply dneg.intro
  end

  @[hott] def or.swap (φ ψ : wff) : ⊢ φ ∨ ψ ⇒ ψ ∨ φ :=
  begin
    apply hypsyll, apply ac,
    apply AS, apply impl.intro, apply dneg.intro
  end

  @[hott] def or.inl (φ ψ : wff) : ⊢ φ ⇒ φ ∨ ψ :=
  by apply contradiction

  @[hott] def or.inr (φ ψ : wff) : ⊢ ψ ⇒ φ ∨ ψ :=
  begin apply hypsyll, apply or.swap, apply or.inl end

  def and (φ ψ : wff) := ¬(φ ⇒ ¬ψ)
  notation φ ` ∧ ` ψ := and φ ψ

  @[hott] def and.intro (φ ψ : wff) : ⊢ φ ⇒ ψ ⇒ φ ∧ ψ :=
  begin
    apply mp, apply impl.symm,
    apply mp, apply impl.symm₂, apply I
  end

  @[hott] def and.symm (φ ψ : wff) : ⊢ φ ∧ ψ ⇒ ψ ∧ φ :=
  begin apply mp, apply contraposition, apply contraposition₁ end

  @[hott] def and.pr₁ (φ ψ : wff) : ⊢ φ ∧ ψ ⇒ φ :=
  begin
    apply mp, apply contraposition₂,
    apply mp, apply impl.symm, apply contradiction
  end

  @[hott] def and.pr₂ (φ ψ : wff) : ⊢ φ ∧ ψ ⇒ ψ :=
  begin apply hypsyll, apply and.pr₁, exact φ, apply and.symm end

  def iff (φ ψ : wff) := (φ ⇒ ψ) ∧ (ψ ⇒ φ)
  infix ` ⇔ `:20 := iff

  @[hott] def iff.intro (φ ψ : wff) (f : ⊢ φ ⇒ ψ) (g : ⊢ ψ ⇒ φ) : ⊢ φ ⇔ ψ :=
  begin apply mp₂, apply and.intro, exact f, exact g end

  @[hott] def iff.left {φ ψ : wff} (H : ⊢ φ ⇔ ψ) : ⊢ φ ⇒ ψ :=
  begin apply mp, apply and.pr₁, exact (ψ ⇒ φ), exact H end

  @[hott] def iff.right {φ ψ : wff} (H : ⊢ φ ⇔ ψ) : ⊢ ψ ⇒ φ :=
  begin apply mp, apply and.pr₂, exact (φ ⇒ ψ), exact H end

  @[hott] def iff.antcdtsubst {φ ψ ξ : wff} (f : ⊢ φ ⇔ ψ) (g : ⊢ ξ ⇒ φ) : ⊢ ξ ⇒ ψ :=
  begin apply hypsyll, apply iff.left f, exact g end

  @[hott] def iff.consqsubst {φ ψ ξ : wff} (f : ⊢ φ ⇔ ψ) (g : ⊢ φ ⇒ ξ) : ⊢ ψ ⇒ ξ :=
  begin apply hypsyll, exact g, apply iff.right f end

  @[hott] def dneg (φ : wff) : ⊢ φ ⇔ ¬¬φ :=
  begin apply iff.intro, apply dneg.intro, apply dneg.elim end

  @[hott] def dedup (φ ψ : wff) : ⊢ (φ ⇒ φ ⇒ ψ) ⇒ (φ ⇒ ψ) :=
  begin apply mp, apply mp, apply impl.symm, apply as, apply I end

  @[hott] def dup (φ ψ : wff) : ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ φ ⇒ ψ) :=
  by apply ak

  @[hott] def impl.negdef₁ (φ ψ : wff) : ⊢ ¬(φ ⇒ ψ) ⇒ (φ ∧ ¬ψ) :=
  begin
    apply mp, apply contraposition,
    apply mp, apply impl.comp, apply dneg.elim
  end

  @[hott] def impl.negdef₂ (φ ψ : wff) : ⊢ (φ ∧ ¬ψ) ⇒ ¬(φ ⇒ ψ) :=
  begin
    apply mp, apply contraposition,
    apply mp, apply impl.comp, apply dneg.intro
  end

  @[hott] def impl.negdef (φ ψ : wff) : ⊢ ¬(φ ⇒ ψ) ⇔ (φ ∧ ¬ψ) :=
  begin apply iff.intro, apply impl.negdef₁, apply impl.negdef₂ end

  @[hott] def rot₁ (φ ψ ξ : wff) : ⊢ (¬ξ ⇒ φ ⇒ ¬ψ) ⇒ (φ ⇒ ψ ⇒ ξ) :=
  begin
    apply hypsyll, apply mp, apply impl.comp,
    exact (¬ξ ⇒ ¬ψ), apply ac, apply impl.symm
  end

  @[hott] def rot₂ (φ ψ ξ : wff) : ⊢ (φ ⇒ ψ ⇒ ξ) ⇒ (¬ξ ⇒ φ ⇒ ¬ψ) :=
  begin
    apply hypsyll, apply impl.symm,
    apply mp, apply impl.comp,
    apply contraposition
  end

  @[hott] def curry (φ ψ ξ : wff) : ⊢ (φ ∧ ψ ⇒ ξ) ⇒ (φ ⇒ ψ ⇒ ξ) :=
  begin apply hypsyll, apply rot₁, apply contraposition₂ end

  @[hott] def uncurry (φ ψ ξ : wff) : ⊢ (φ ⇒ ψ ⇒ ξ) ⇒ (φ ∧ ψ ⇒ ξ) :=
  begin apply hypsyll, apply contraposition₂, apply rot₂ end
end ground_zero.theorems.logic