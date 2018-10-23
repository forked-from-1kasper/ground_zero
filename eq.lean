namespace ground_zero

universes u v

theorem K {α : Sort u} {a b : α} (p q : a = b) : p = q :=
by trivial

inductive eq {α : Sort u} (a : α) : α → Sort u
| refl : eq a
attribute [refl] eq.refl


local infix ` = ` := eq
notation a ` = ` b ` :> ` α := @eq α a b

/- fails!
theorem K₁ {α : Sort u} {a b : α} (p q : a = b :> α) :
  p = q :> (a = b :> α) :=
by trivial
-/

namespace eq
  def rfl {α : Sort u} {a : α} : a = a :> α := eq.refl a

  @[trans] def trans {α : Sort u} {a b c : α}
    (p : a = b :> α) (q : b = c :> α) : a = c :> α := begin
    induction p, assumption
  end

  @[symm] def symm {α : Sort u} {a b : α} (p : a = b :> α) :
    b = a :> α := begin
    induction p, reflexivity
  end

  infix ⬝ := trans
  postfix ⁻¹ := symm

  def map {α : Sort u} {β : Sort v} {a b : α}
    (f : α → β) (p : a = b :> α) : f a = f b :> β :=
  begin induction p, reflexivity end
  infix # := map

  structure pointed :=
  (α : Sort u) (a : α)

  def loop_space (X : pointed) : pointed :=
  { α := X.a = X.a :> X.α,
    a := eq.refl X.a }

  def iterated_loop_space : pointed → ℕ → pointed
  | X 0 := X
  | X (n+1) := iterated_loop_space (loop_space X) n
  notation `Ω` `[` n `]` X := iterated_loop_space X n
end eq

namespace not
  notation `¬` a := a → empty
end not

end ground_zero