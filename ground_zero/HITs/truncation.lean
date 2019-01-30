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
    (we use this proof here)
  * https://homotopytypetheory.org/2015/07/28/constructing-the-propositional-truncation-using-nonrecursive-hits/
  * https://homotopytypetheory.org/2016/01/08/colimits-in-hott/
-/
def truncation (α : Sort u) :=
colimit (generalized.repeat α) (generalized.dep α)

notation `∥` α `∥` := truncation α

namespace truncation
  def elem {α : Sort u} (x : α) : ∥α∥ :=
  colimit.inclusion 0 x

  notation `|` a `|` := elem a

  def ind {α : Sort u} {π : ∥α∥ → Sort v}
    (elemπ : Π x, π (elem x))
    (uniqπ : Π x, prop (π x)) : Π x, π x := begin
    fapply colimit.ind,
    { intros, induction n with n ih,
      { apply elemπ },
      { refine generalized.ind _ _ x,
        { clear x, intro x,
          apply subst (colimit.glue x)⁻¹ (ih x) },
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

  abbreviation incl {α : Sort u} {n : ℕ} :=
  @colimit.incl (generalized.repeat α) (generalized.dep α) n

  abbreviation glue {α : Sort u} {n : ℕ} {x : generalized.repeat α n} :
    incl (generalized.dep α n x) = incl x :=
  colimit.glue x

  def exact_nth {α : Sort u} (a : α) : Π n, generalized.repeat α n
  | 0 := a
  | (n + 1) := generalized.dep α n (exact_nth n)

  def nth_glue {α : Sort u} (a : α) : Π n,
    incl (exact_nth a n) = @incl α 0 a
  | 0 := by reflexivity
  | (n + 1) := colimit.glue (exact_nth a n) ⬝ nth_glue n

  def incl_uniq {α : Sort u} {n : ℕ} (a b : generalized.repeat α n) :
    incl a = incl b :=
  calc incl a = incl (generalized.dep α n a) : glue⁻¹
          ... = incl (generalized.dep α n b) : incl # (generalized.glue a b)
          ... = incl b : glue

  def incl_zero_eq_incl {α : Sort u} {n : ℕ} (x : α)
    (y : generalized.repeat α n) : @incl α 0 x = incl y :=
  calc @incl α 0 x = incl (exact_nth x n) : (nth_glue x n)⁻¹
               ... = incl y : incl_uniq (exact_nth x n) y

  def weakly_constant_ap {α : Sort u} {β : Sort v} (f : α → β)
    {a b : α} (p q : a = b) (H : Π (a b : α), f a = f b) : f # p = f # q :=
  let L : Π {u v : α} {r : u = v}, (H a u)⁻¹ ⬝ H a v = f # r :=
  begin intros, induction r, apply ground_zero.types.eq.inv_comp end in
  L⁻¹ ⬝ L

  def cong_close {α : Sort u} {n : ℕ} {a b : generalized.repeat α n} (p : a = b) :
    glue⁻¹ ⬝ incl # (generalized.dep α n # p) ⬝ glue = incl # p := begin
    induction p,
    rw ←hint (ground_zero.types.eq.assoc _ _ _),
    apply ground_zero.types.equiv.rewrite_comp, symmetry,
    apply ground_zero.types.eq.refl_right
  end

  def cong_over_path {α : Sort u} {n : ℕ} {a b : generalized.repeat α n}
    (p q : a = b) : incl # p = incl # q :=
  weakly_constant_ap incl p q incl_uniq

  def glue_close {α : Sort u} {n : ℕ} {a b : generalized.repeat α n} :
    glue⁻¹ ⬝ incl # (generalized.glue (generalized.dep α n a)
                                      (generalized.dep α n b)) ⬝ glue =
    incl # (generalized.glue a b) := begin
    symmetry, transitivity,
    { symmetry, exact cong_close (generalized.glue a b) },
    apply cong (λ p, p ⬝ glue), apply cong,
    apply cong_over_path
  end

  def incl_uniq_close {α : Sort u} {n : ℕ} (a b : generalized.repeat α n) :
    glue⁻¹ ⬝ incl_uniq (generalized.dep α n a) (generalized.dep α n b) ⬝ glue =
    incl_uniq a b := begin
    unfold incl_uniq, apply cong (λ p, p ⬝ glue), apply cong,
    apply glue_close
  end

  def uniq {α : Sort u} : prop ∥α∥ := begin
    apply lem_contr, fapply ind,
    { intro x, existsi elem x, fapply colimit.ind; intros n y,
      { apply incl_zero_eq_incl },
      { simp, unfold incl_zero_eq_incl, unfold nth_glue,
        apply pathover_from_trans,
        symmetry, transitivity,
        { symmetry, apply cong, apply incl_uniq_close },
        rw hint (ground_zero.types.eq.explode_inv _ _),
        repeat { rw ←hint (ground_zero.types.eq.assoc _ _ _) },
        apply cong (λ p, (nth_glue x n)⁻¹ ⬝ p),
        unfold incl_uniq, trivial } },
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

def surj {α : Sort u} {β : Sort v} (f : α → β) :=
Π (b : β), ∥ground_zero.types.fib f b∥

def embedding {α : Sort u} {β : Sort v} (f : α → β) :=
Π (x y : α), ground_zero.types.equiv.biinv (λ (p : x = y), f # p)

end ground_zero.HITs