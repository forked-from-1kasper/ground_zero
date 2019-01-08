import ground_zero.HITs.colimit ground_zero.HITs.generalized
import ground_zero.structures
open ground_zero.support (renaming truncation -> hint)
open ground_zero.types.equiv (subst path_over_subst apd pathover_from_trans)
open ground_zero.types.eq (cong)
open ground_zero.structures (prop contr lem_contr)

namespace ground_zero.HITs
hott theory

universes u v

/-
  Propositional truncation is colimit of a following sequence:
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

  abbreviation incl {α : Sort u} (n : ℕ) :=
  @colimit.incl (generalized.repeat α) (generalized.dep α) n

  def exact_nth {α : Sort u} (a : α) : Π n, generalized.repeat α n
  | 0 := a
  | (n + 1) := generalized.dep α n (exact_nth n)

  def nth_glue {α : Sort u} (a : α) : Π n,
    incl n (exact_nth a n) = incl 0 a
  | 0 := by reflexivity
  | (n + 1) := colimit.glue (exact_nth a n) ⬝ nth_glue n

  def incl_zero_eq_incl {α : Sort u} {n : ℕ} (x : α)
    (y : generalized.repeat α n) : incl 0 x = incl n y :=
  calc incl 0 x = incl n (exact_nth x n) : (nth_glue x n)⁻¹
            ... = incl (n + 1) (generalized.dep α n _) : (colimit.glue _)⁻¹
            ... = incl (n + 1) (generalized.dep α n y)
                : incl (n + 1) # (generalized.glue _ y)
            ... = incl n y : colimit.glue y

  def uniq {α : Sort u} : prop ∥α∥ := begin
    apply lem_contr, fapply ind,
    { intro x, existsi elem x, fapply colimit.ind; intros n y,
      { apply incl_zero_eq_incl },
      { simp, unfold incl_zero_eq_incl, unfold nth_glue,
        admit } },
    { intro x, apply ground_zero.structures.contr_is_prop }
  end

  def lift {α β : Type u} (f : α → β) : ∥α∥ → ∥β∥ :=
  rec uniq (elem ∘ f)

  theorem equiv_iff_trunc {α β : Type u}
    (f : α → β) (g : β → α) : ∥α∥ ≃ ∥β∥ := begin
    existsi lift f, split; existsi lift g;
    { intro x, apply uniq }
  end

  def double {α : Type u} (a : α) : α × α := ⟨a, a⟩
  theorem product_identity {α : Type u} :
    ∥α∥ ≃ ∥α × α∥ := begin
    apply equiv_iff_trunc, exact double,
    intro x, cases x with u v, exact u
  end

  def uninhabited_implies_trunc_uninhabited {α : Sort u}
    (p : α → empty) : ∥α∥ → empty :=
  rec ground_zero.structures.empty_is_prop p
end truncation

end ground_zero.HITs