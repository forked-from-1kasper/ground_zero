import ground_zero.types.eq

namespace ground_zero.types
universes u v

inductive dep_path {α : Sort u} (π : α → Sort v) :
  Π {a b : α} (p : a = b :> α) (u : π a) (v : π b), Sort (max u v)
| refl (a : α) (u : π a) : dep_path (eq.refl a) u u
attribute [refl] dep_path.refl

notation u ` =[` P `,` p `] ` v := dep_path P p u v
notation u ` =[` p `] ` v := dep_path _ p u v

namespace dep_path
  def apd {α : Sort u} {β : α → Sort v} {a b : α}
    (f : Π (x : α), β x) (p : a = b :> α) :
    f a =[p] f b :=
  begin induction p, reflexivity end

  def pathover_of_eq {α : Sort u} {β : Sort v}
    {a b : α} {a' b' : β}
    (p : a = b :> α) (q : a' = b' :> β) : a' =[p] b' :=
  begin induction p, induction q, trivial end

  @[symm] def symm {α : Sort u} {β : α → Sort v} {a b : α}
    (p : a = b :> α) {u : β a} {v : β b}
    (q : u =[p] v) : v =[p⁻¹] u :=
  begin induction q, reflexivity end

  @[trans] def dep_trans {α : Sort u} {π : α → Sort v}
    {a b c : α} {p : a = b :> α} {q : b = c :> α}
    {u : π a} {v : π b} {w : π c}
    (r : u =[p] v) (s : v =[q] w):
    u =[p ⬝ q] w :=
  begin induction r, induction s, reflexivity end
  infix ` ⬝' `:40 := dep_trans

  def dep_homotopy {α : Sort u} {β γ : α → Sort v}
    {a b : α} (p : a = b :> α)
    (f : Π x, β a → γ x) (g : Π x, β b → γ x) :=
  Π (x : β a) (y : β b) (q : x =[p] y) (z : α), f z x =[p] g z y
end dep_path

end ground_zero.types