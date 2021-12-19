import ground_zero.structures

open ground_zero ground_zero.types
open ground_zero.types.equiv
open ground_zero.proto

open ground_zero.structures (prop contr)

universes u v w k
hott theory

-- exercise 2.1

section
  variables {α : Type u} {a b c : α}

  @[hott] def trans₁ (p : a = b) (q : b = c) : a = c :=
  begin induction p, induction q, reflexivity end

  infixl ` ⬝₁ `:99 := trans₁

  @[hott] def trans₂ (p : a = b) (q : b = c) : a = c :=
  begin induction p, exact q end

  infixl ` ⬝₂ `:99 := trans₂

  @[hott] def trans₃ (p : a = b) (q : b = c) : a = c :=
  begin induction q, exact p end

  infixl ` ⬝₃ `:99 := trans₃

  @[hott] def eq₁₂ (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₂ q :=
  begin induction p, induction q, reflexivity end

  @[hott] def eq₂₃ (p : a = b) (q : b = c) : p ⬝₂ q = p ⬝₃ q :=
  begin induction p, induction q, reflexivity end

  @[hott] def eq₁₃ (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₃ q :=
  begin induction p, induction q, reflexivity end
end

-- exercise 2.2

section
  variables {A : Type u} {a b c : A} (p : a = b) (q : b = c)

  @[hott] example : eq₁₂ p q ⬝ eq₂₃ p q = eq₁₃ p q :=
  begin induction p, induction q, reflexivity end
end
