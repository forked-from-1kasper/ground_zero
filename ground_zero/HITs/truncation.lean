import ground_zero.HITs.colimit ground_zero.HITs.generalized
import ground_zero.structures
open ground_zero.types.equiv (subst path_over_subst)
open ground_zero.structures (prop contr lem_contr lem_prop)

namespace ground_zero.HITs
hott theory

universes u v

/-
  Propositionally truncation is colimit of a following sequence:
    α → {α} → {{α}} → ...

  * https://github.com/fpvandoorn/leansnippets/blob/master/truncation.hlean
  * https://github.com/fpvandoorn/leansnippets/blob/master/cpp.hlean
  * https://homotopytypetheory.org/2015/07/28/constructing-the-propositional-truncation-using-nonrecursive-hits/
  * https://homotopytypetheory.org/2016/01/08/colimits-in-hott/
-/
def truncation (α : Sort u) :=
colimit (generalized.repeat α) (generalized.dep α)

notation `∥` α `∥` := truncation α

namespace truncation
  def elem {α : Sort u} (x : α) : ∥α∥ :=
  colimit.inclusion 0 x

  def ind {α : Sort u} {π : ∥α∥ → Sort v}
    (elemπ : Π x, π (elem x))
    (uniqπ : Π x, prop (π x)) : Π x, π x := begin
    fapply colimit.ind,
    { intros, induction n with n ih,
      { apply elemπ },
      { refine generalized.ind _ _ x,
        { clear x, intro x,
          apply subst (colimit.glue x)⁻¹ (ih x), },
        { intros, apply path_over_subst,
          apply uniqπ } } },
    { intros, apply path_over_subst, apply uniqπ }
  end

  def rec {α : Sort u} {β : Sort v} (h : prop β)
    (f : α → β) : ∥α∥ → β :=
  ind f (λ _, h)

  def weak_uniq {α : Sort u} (x y : α) : elem x = elem y :> ∥α∥ := begin
    transitivity, { symmetry, apply colimit.glue }, symmetry,
    transitivity, { symmetry, apply colimit.glue },
    apply ground_zero.types.eq.map, apply generalized.glue
  end
end truncation

end ground_zero.HITs