import ground_zero.HITs.colimit ground_zero.HITs.generalized
import ground_zero.structures
open ground_zero.types.equiv (subst apd pathover_from_trans)
open ground_zero.types.eq (cong inv)
open ground_zero.structures (prop contr lem_contr)

namespace ground_zero.HITs
hott theory

universes u v w

/-
  Propositional truncation is colimit of a following sequence:
    α → {α} → {{α}} → ...

  * https://github.com/fpvandoorn/leansnippets/blob/master/truncation.hlean
  * https://github.com/fpvandoorn/leansnippets/blob/master/cpp.hlean
    (we use this proof here)
  * https://homotopytypetheory.org/2015/07/28/constructing-the-propositional-truncation-using-nonrecursive-hits/
  * https://homotopytypetheory.org/2016/01/08/colimits-in-hott/
  * https://arxiv.org/pdf/1512.02274
-/
def merely (α : Type u) :=
colimit (generalized.repeat α) (generalized.dep α)

notation `∥` α `∥` := merely α

namespace merely
  def elem {α : Type u} (x : α) : ∥α∥ :=
  colimit.inclusion 0 x

  notation `|` a `|` := elem a

  @[hott] def ind {α : Type u} {π : ∥α∥ → Type v}
    (elemπ : Π x, π (elem x))
    (uniqπ : Π x, prop (π x)) : Π x, π x := begin
    fapply colimit.ind,
    { intros, induction n with n ih,
      { apply elemπ },
      { refine generalized.ind _ _ x,
        { clear x, intro x, apply subst,
          symmetry, apply colimit.glue, apply ih },
        { intros, apply uniqπ } } },
    { intros, apply uniqπ }
  end

  @[hott] def rec {α : Type u} {β : Type v} (h : prop β)
    (f : α → β) : ∥α∥ → β :=
  ind f (λ _, h)

  @[hott] def weak_uniq {α : Type u} (x y : α) : elem x = elem y :> ∥α∥ := begin
    transitivity, { symmetry, apply colimit.glue }, symmetry,
    transitivity, { symmetry, apply colimit.glue },
    apply ground_zero.types.eq.map, apply generalized.glue
  end

  abbreviation incl {α : Type u} {n : ℕ} :=
  @colimit.incl (generalized.repeat α) (generalized.dep α) n

  abbreviation glue {α : Type u} {n : ℕ} {x : generalized.repeat α n} :
    incl (generalized.dep α n x) = incl x :=
  colimit.glue x

  @[hott] def exact_nth {α : Type u} (a : α) : Π n, generalized.repeat α n
  | 0 := a
  | (n + 1) := generalized.dep α n (exact_nth n)

  @[hott] def nth_glue {α : Type u} (a : α) : Π n,
    incl (exact_nth a n) = @incl α 0 a
  | 0 := by reflexivity
  | (n + 1) := colimit.glue (exact_nth a n) ⬝ nth_glue n

  @[hott] def incl_uniq {α : Type u} {n : ℕ} (a b : generalized.repeat α n) :
    incl a = incl b :=
  calc incl a = incl (generalized.dep α n a) : glue⁻¹
          ... = incl (generalized.dep α n b) : incl # (generalized.glue a b)
          ... = incl b : glue

  @[hott] def incl_zero_eq_incl {α : Type u} {n : ℕ} (x : α)
    (y : generalized.repeat α n) : @incl α 0 x = incl y :=
  calc @incl α 0 x = incl (exact_nth x n) : (nth_glue x n)⁻¹
               ... = incl y : incl_uniq (exact_nth x n) y

  @[hott] def weakly_constant_ap {α : Type u} {β : Type v} (f : α → β)
    {a b : α} (p q : a = b) (H : Π (a b : α), f a = f b) : f # p = f # q :=
  let L : Π {u v : α} {r : u = v}, (H a u)⁻¹ ⬝ H a v = f # r :=
  begin intros, induction r, apply ground_zero.types.eq.inv_comp end in
  L⁻¹ ⬝ L

  @[hott] def cong_close {α : Type u} {n : ℕ} {a b : generalized.repeat α n} (p : a = b) :
    inv glue ⬝ incl # (generalized.dep α n # p) ⬝ glue = incl # p := begin
    induction p, transitivity,
    { symmetry, apply ground_zero.types.eq.assoc },
    apply ground_zero.types.equiv.rewrite_comp, symmetry,
    apply ground_zero.types.eq.refl_right
  end

  @[hott] def cong_over_path {α : Type u} {n : ℕ} {a b : generalized.repeat α n}
    (p q : a = b) : incl # p = incl # q :=
  weakly_constant_ap incl p q incl_uniq

  @[hott] def glue_close {α : Type u} {n : ℕ} {a b : generalized.repeat α n} :
    inv glue ⬝ incl # (generalized.glue (generalized.dep α n a)
                                        (generalized.dep α n b)) ⬝ glue =
    incl # (generalized.glue a b) := begin
    symmetry, transitivity,
    { symmetry, exact cong_close (generalized.glue a b) },
    apply cong (λ p, p ⬝ glue), apply cong,
    apply cong_over_path
  end

  @[hott] def incl_uniq_close {α : Type u} {n : ℕ} (a b : generalized.repeat α n) :
    inv glue ⬝ incl_uniq (generalized.dep α n a) (generalized.dep α n b) ⬝ glue =
    incl_uniq a b := begin
    apply cong (λ p, p ⬝ glue), apply cong,
    apply glue_close
  end

  @[hott] def uniq {α : Type u} : prop ∥α∥ := begin
    apply lem_contr, fapply ind,
    { intro x, existsi elem x, fapply colimit.ind; intros n y,
      { apply incl_zero_eq_incl },
      { apply pathover_from_trans,
        symmetry, transitivity,
        { symmetry, apply cong (λ p, (nth_glue x n)⁻¹ ⬝ p),
          apply incl_uniq_close },
        symmetry, transitivity, apply cong
          (λ p, p ⬝ incl_uniq (exact_nth x (n + 1)) (generalized.dep α n y) ⬝
                    colimit.glue y),
        apply ground_zero.types.eq.explode_inv,
        repeat { transitivity, symmetry, apply ground_zero.types.eq.assoc },
        apply cong (λ p, (nth_glue x n)⁻¹ ⬝ p),
        apply ground_zero.types.eq.assoc } },
    { intro x, apply ground_zero.structures.contr_is_prop }
  end

  @[hott] def lift {α : Type u} {β : Type v} (f : α → β) : ∥α∥ → ∥β∥ :=
  rec uniq (elem ∘ f)

  @[hott] def lift₂ {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β → γ) : ∥α∥ → ∥β∥ → ∥γ∥ := begin
    fapply @rec α (∥β∥ → ∥γ∥),
    { apply ground_zero.structures.impl_prop, apply uniq },
    { intro a, fapply rec, apply uniq,
      intro b, apply elem, exact f a b }
  end

  @[hott] theorem equiv_iff_trunc {α β : Type u}
    (f : α → β) (g : β → α) : ∥α∥ ≃ ∥β∥ := begin
    existsi lift f, split; existsi lift g;
    { intro x, apply uniq }
  end

  def double {α : Type u} (a : α) : α × α := ⟨a, a⟩
  @[hott] theorem product_identity {α : Type u} :
    ∥α∥ ≃ ∥α × α∥ := begin
    apply equiv_iff_trunc, exact double,
    intro x, cases x with u v, exact u
  end

  @[hott] def uninhabited_implies_trunc_uninhabited {α : Type u} : ¬α → ¬∥α∥ :=
  rec ground_zero.structures.empty_is_prop
end merely

end ground_zero.HITs