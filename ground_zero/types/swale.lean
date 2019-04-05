namespace ground_zero.types

universes u v w

class has_mem (α : Sort u) (γ : Sort v) :=
(mem : α → γ → Sort w)
infix ` ∈ ` := has_mem.mem

def swale (α : Sort u) := α → Sort v
namespace swale
  abbreviation mk {α : Sort u} (f : α → Sort v) : swale α := f

  def membership {α : Sort u} (x : α) (s : swale α) := s x
  instance {α : Sort u} : has_mem α (swale α) := ⟨membership⟩

  notation `{` binder ` | ` r:(scoped P, mk P) `}` := r

  inductive bottom : Sort u
  def empty (α : Sort u) : swale α := { x | bottom }
end swale

end ground_zero.types