import GroundZero.HITs.Merely

open GroundZero.Types GroundZero.HITs
open GroundZero.Types.Id (ap)
open GroundZero.Structures

namespace GroundZero.Theorems.Functions
universe u v

hott definition injective {A : Type u} {B : Type v} (f : A → B) :=
Π x y, f x = f y → x = y

hott definition surjective {A : Type u} {B : Type v} (f : A → B) :=
Π b, ∥Σ a, f a = b∥

hott definition Surjection (A : Type u) (B : Type v) :=
Σ (f : A → B), surjective f
infixr:70 " ↠ " => Surjection

instance (A : Type u) (B : Type v) : CoeFun (A ↠ B) (λ _, A → B) := ⟨Sigma.fst⟩

hott definition fibInh {A : Type u} {B : Type v} (f : A → B) :=
λ b, ∥fib f b∥

hott definition Ran {A : Type u} {B : Type v} (f : A → B) :=
total (fibInh f)

hott definition cut {A : Type u} {B : Type v} (f : A → B) : A → Ran f :=
λ x, ⟨f x, |⟨x, idp (f x)⟩|⟩

hott lemma cutIsSurj {A : Type u} {B : Type v} (f : A → B) : surjective (cut f) :=
begin
  intro ⟨x, (H : ∥_∥)⟩; induction H;
  { case elemπ G =>
    apply Merely.elem; existsi G.1; fapply Sigma.prod;
    exact G.2; apply Merely.uniq };
  apply Merely.uniq
end

hott definition Ran.subset {A : Type u} {B : Type v} (f : A → B) : Ran f → B :=
Sigma.fst

hott definition Ran.incl {A : Type u} {B : Type v} {f : A → B} (H : surjective f) : B → Ran f :=
λ x, ⟨x, H x⟩

hott lemma surjImplRanEqv {A : Type u} {B : Type v} (f : A → B) (H : surjective f) : Ran f ≃ B :=
begin
  existsi Sigma.fst; fapply Prod.mk <;> existsi Ran.incl H;
  { intro ⟨_, _⟩; fapply Sigma.prod; reflexivity; apply Merely.uniq };
  { intro; reflexivity }
end

hott definition ranConst {A : Type u} (a : A) {B : Type v} (b : B) : Ran (Function.const A b) :=
⟨b, |⟨a, idp b⟩|⟩

hott lemma ranConstEqv {A : Type u} (a : A) {B : Type v}
  (H : hset B) (b : B) : Ran (Function.const A b) ≃ 𝟏 :=
begin
  existsi (λ _, ★); fapply Prod.mk <;> existsi (λ _, ranConst a b);
  { intro ⟨b', (G : ∥_∥)⟩; fapply Sigma.prod; change b = b';
    induction G; { case elemπ w => exact w.2 };
    apply H; apply Merely.uniq };
  { intro ★; reflexivity }
end

hott definition isEmbedding {A : Type u} {B : Type v} (f : A → B) :=
Π x y, @Equiv.biinv (x = y) (f x = f y) (ap f)

hott definition Embedding (A : Type u) (B : Type v) :=
Σ (f : A → B), isEmbedding f

infix:55 " ↪ " => Embedding

section
  variable {A : Type u} {B : Type v} (f : A ↪ B)

  hott abbreviation Embedding.ap : A → B := f.1

  hott abbreviation Embedding.eqv (x y : A) : (x = y) ≃ (f.ap x = f.ap y) :=
  ⟨Id.ap f.ap, f.2 x y⟩
end

hott theorem ntypeOverEmbedding {A : Type u} {B : Type v} (f : A ↪ B) (n : ℕ₋₂) :
  is-(hlevel.succ n)-type B → is-(hlevel.succ n)-type A :=
begin
  intros H x y; apply ntypeRespectsEquiv; apply Equiv.symm;
  existsi ap f.1; apply f.2; apply H
end

hott definition eqvMapForward {A : Type u} {B : Type v} (e : A ≃ B)
  (x y : A) (p : e x = e y) : x = y :=
(e.leftForward x)⁻¹ ⬝ (@ap B A _ _ e.left p) ⬝ (e.leftForward y)

hott lemma sigmaPropEq {A : Type u} {B : A → Type v}
  (H : Π x, prop (B x)) {x y : Sigma B} (p : x.1 = y.1) : x = y :=
begin fapply Sigma.prod; exact p; apply H end

hott lemma propSigmaEquiv {A : Type u} {B : A → Type v} (H : Π x, prop (B x))
  (x y : Σ x, B x) : (x = y) ≃ (x.1 = y.1) :=
begin
  apply Equiv.trans; apply Sigma.sigmaPath;
  apply Equiv.trans; apply Sigma.respectsEquiv;
  { intro; apply contrEquivUnit.{_, 1}; fapply Sigma.mk;
    apply H; intro; apply propIsSet; apply H };
  apply Equiv.trans; apply Sigma.const; apply unitProdEquiv
end

hott definition propSigmaEmbedding {A : Type u} {B : A → Type v}
  (H : Π x, prop (B x)) : (Σ x, B x) ↪ A :=
begin
  existsi Sigma.fst; intro x y;
  apply Equiv.transport Equiv.biinv _ (propSigmaEquiv H x y).2;
  apply Theorems.funext; intro p; induction p; reflexivity
end

hott definition isConnected (A : Type u) :=
Σ (x : A), Π y, ∥x = y∥

end GroundZero.Theorems.Functions
