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

  @[hott] def trans₂ (p : a = b) (q : b = c) : a = c :=
  begin induction p, exact q end

  @[hott] def trans₃ (p : a = b) (q : b = c) : a = c :=
  begin induction q, exact p end

  @[hott] example (p : a = b) (q : b = c) : trans₁ p q = trans₂ p q :=
  begin induction p, induction q, reflexivity end

  @[hott] example (p : a = b) (q : b = c) : trans₂ p q = trans₃ p q :=
  begin induction p, induction q, reflexivity end
end