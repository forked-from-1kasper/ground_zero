namespace ground_zero.types

universes u v w

class has_mem (α : Sort u) (β : Sort v) :=
(mem : α → β → Sort w)
infix ` ∈ ` := has_mem.mem

def swale (α : Sort u) := α → Sort v
namespace swale
  abbreviation mk {α : Sort u} (f : α → Sort v) : swale α := f

  def membership {α : Sort u} (x : α) (s : swale α) := s x
  instance {α : Sort u} : has_mem α (swale α) := ⟨membership⟩

  inductive bottom : Sort u
  def empty (α : Sort u) : swale α := λ _, bottom
end swale

end ground_zero.types