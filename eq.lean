import ground_zero.structures
open ground_zero.structures (contr)

namespace ground_zero.eq
  universes u v
  infix ⬝ := eq.trans
  postfix ⁻¹ := eq.symm

  def map {α : Sort u} {β : Sort v} {a b : α}
    (f : α → β) (p : a = b) : f a = f b :=
  begin induction p, reflexivity end

  -- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/tiny-library.html
  -- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/hsetfunext.html
  def singl {α : Sort u} (a : α) :=
  Σ' (b : α), a = b

  def end_point {α : Sort u} {a : α} : singl a → α :=
  psigma.fst

  def trivial_loop {α : Sort u} (a : α) : singl a :=
  ⟨a, eq.refl a⟩

  def path_from_trivial_loop {α : Sort u} {a b : α}
    (r : a = b) : trivial_loop a = ⟨b, r⟩ :=
  begin induction r, trivial end

  instance signl_contr {α : Sort u} (a : α) : contr (singl a) :=
  { point := trivial_loop a,
    intro := λ t, (path_from_trivial_loop t.snd) ⬝
                  (psigma.eq (by trivial) (by trivial)) }

end ground_zero.eq

namespace ground_zero.not
  notation `¬` a := a → empty
end ground_zero.not