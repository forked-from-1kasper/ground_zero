import GroundZero.Theorems.Equiv
import GroundZero.HITs.Trunc

open GroundZero.HITs.Interval (happly)
open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types
open GroundZero.HITs

universe u v

namespace GroundZero
namespace Theorems

hott def conn {A : Type u} {B : Type v} (n : ℕ₋₂) (f : A → B) :=
Π (b : B), contr ∥fib f b∥ₙ

hott def isConnected (n : ℕ₋₂) (A : Type u) :=
contr ∥A∥ₙ

notation "is-" n "-connected" => isConnected n

namespace Connectedness
  hott proposition isProp {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B} : prop (conn n f) :=
  begin apply piProp; intro; apply contrIsProp end

  -- HoTT Book Lemma 7.5.14
  hott lemma isQinv {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B} (c : conn n f) : @qinv ∥A∥ₙ ∥B∥ₙ (Trunc.lift f) :=
  begin
    fapply Sigma.mk; apply Trunc.rec; intro b; exact Trunc.lift Sigma.fst (c b).1; apply Trunc.uniq; apply Prod.mk;
    { fapply Trunc.ind;
      { intro y; transitivity; apply ap (Trunc.lift _);
        apply Trunc.recβrule; induction (c y).1; case elemπ w =>
        { transitivity; apply ap (Trunc.lift f); apply Trunc.recβrule;
          transitivity; apply Trunc.recβrule; apply ap Trunc.elem; exact w.2 };
        { apply hlevel.cumulative; apply Trunc.uniq } };
      { intro; apply hlevel.cumulative; apply Trunc.uniq } };
    { fapply Trunc.ind;
      { intro x; transitivity; apply ap (Trunc.rec _ _);
        apply Trunc.recβrule; transitivity; apply Trunc.recβrule;
        transitivity; apply ap; apply (c (f x)).2 (Trunc.elem ⟨x, idp (f x)⟩);
        apply Trunc.recβrule };
      { intro; apply hlevel.cumulative; apply Trunc.uniq } }
  end

  hott corollary induce {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B} (c : conn n f) : ∥A∥ₙ ≃ ∥B∥ₙ :=
  ⟨Trunc.lift f, Qinv.toBiinv _ (isQinv c)⟩

  hott def com {A : Type u} {B : Type v} {n : ℕ₋₂} (f : A → B)
    (P : B → n-Type) : (Π b, (P b).1) → (Π a, (P (f a)).1) :=
  λ s a, s (f a)

  hott lemma connImplQinv {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B}
    (c : conn n f) (P : B → n-Type) : qinv (com f P) :=
  begin
    fapply Sigma.mk; intros s b; apply Trunc.rec _ _ (c b).1; intro w;
    apply transport (λ b, (P b).1) w.2; apply s; exact (P b).2; apply Prod.mk;
    { intro s; apply Theorems.funext; intro a; transitivity;
      apply ap (Trunc.rec _ _); apply (c (f a)).2; apply Trunc.elem;
      exact ⟨a, idp (f a)⟩; apply Trunc.recβrule };
    { intro s; apply Theorems.funext; intro b; induction (c b).1; case elemπ w =>
      { transitivity; apply ap (Trunc.rec _ _); apply (c b).2 (Trunc.elem w);
        transitivity; apply Trunc.recβrule; apply apd s w.2 };
      { apply hlevel.cumulative; apply (P b).2 } }
  end

  hott lemma rinvImplConn {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B}
    (s : Π (P : B → n-Type), rinv (com f P)) : conn n f :=
  begin
    let P : B → n-Type := λ b, ⟨∥fib f b∥ₙ, Trunc.uniq n⟩; intro b; fapply Sigma.mk;
    apply (s P).1 (λ a, Trunc.elem ⟨a, idp (f a)⟩); fapply Trunc.ind;
    { intro ⟨a, w⟩; induction w; apply happly ((s P).2 (λ a, Trunc.elem ⟨a, idp (f a)⟩)) a };
    { intro; apply hlevel.cumulative; apply Trunc.uniq }
  end

  hott lemma rinvComProp {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B} :
    prop (Π (P : B → n-Type), rinv (com f P)) :=
  begin
    apply lemProp; intro s; apply piProp; intro P; apply contrImplProp;
    apply Equiv.rinvContr; apply connImplQinv; apply rinvImplConn; exact s
  end

  -- HoTT Book Lemma 7.5.7
  hott corollary induct {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B} :
    (conn n f) ≃ (Π (P : B → n-Type), rinv (com f P)) :=
  begin
    apply propEquivLemma; apply Connectedness.isProp; apply rinvComProp; intro c P;
    exact (Qinv.toBiinv _ (connImplQinv c P)).2; apply rinvImplConn
  end
end Connectedness

end Theorems
end GroundZero
