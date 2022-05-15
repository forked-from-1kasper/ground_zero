import ground_zero.HITs.graph
open ground_zero.types.equiv

hott theory

namespace ground_zero.HITs
universes u v w

section
  variables {α : Type u} {β : Type v} (f g : α → β)

  inductive coeq.rel : β → β → Type (max u v)
  | intro : Π x, coeq.rel (f x) (g x)

  def coeq := graph (coeq.rel f g)
end

namespace coeq
  variables {α : Type u} {β : Type v} {f g : α → β}

  @[hott] def iota : β → coeq f g := graph.elem
  @[hott] def resp : Π (x : α), iota (f x) = iota (g x) :> coeq f g :=
  λ x, graph.line (coeq.rel.intro x)

  @[hott] def ind (π : coeq f g → Type w) (i : Π x, π (iota x))
    (ρ : Π x, i (f x) =[resp x] i (g x)) : Π x, π x :=
  begin fapply graph.ind, apply i, intros x y H, induction H, apply ρ end

  @[hott] noncomputable def indβrule (π : coeq f g → Type w) (i : Π x, π (iota x))
    (ρ : Π x, i (f x) =[resp x] i (g x)) (x : α) : apd (ind π i ρ) (resp x) = ρ x :=
  by apply graph.indβrule

  @[hott] def rec (π : Type w) (i : β → π) (ρ : Π x, i (f x) = i (g x)) : coeq f g → π :=
  ind (λ _, π) i (λ x, pathover_of_eq (resp x) (ρ x))

  @[hott] noncomputable def recβrule (π : Type w) (i : β → π)
    (ρ : Π x, i (f x) = i (g x)) : Π x, (rec π i ρ) # (resp x) = ρ x :=
  begin
    intro x, apply pathover_of_eq_inj (resp x),
    transitivity, symmetry, apply apd_over_constant_family,
    transitivity, apply indβrule, reflexivity
  end
end coeq

end ground_zero.HITs