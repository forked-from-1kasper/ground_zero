import GroundZero.HITs.Merely

open GroundZero.Types GroundZero.HITs
open GroundZero.Structures

namespace GroundZero.Theorems.Functions
universe u v

hott def injective {A : Type u} {B : Type v} (f : A → B) :=
Π x y, f x = f y → x = y

hott def surjective {A : Type u} {B : Type v} (f : A → B) :=
Π b, ∥Σ a, f a = b∥

hott def Surjection (A : Type u) (B : Type v) :=
Σ (f : A → B), surjective f
infixr:70 " ↠ " => Surjection

instance (A : Type u) (B : Type v) : CoeFun (A ↠ B) (λ _, A → B) := ⟨Sigma.fst⟩

hott def fibInh {A : Type u} {B : Type v} (f : A → B) :=
λ b, ∥fib f b∥

hott def Ran {A : Type u} {B : Type v} (f : A → B) :=
total (fibInh f)

hott def cut {A : Type u} {B : Type v} (f : A → B) : A → Ran f :=
λ x, ⟨f x, Merely.elem ⟨x, Id.refl⟩⟩

hott def cutIsSurj {A : Type u} {B : Type v} (f : A → B) : surjective (cut f) :=
begin
  intro ⟨x, (H : ∥_∥)⟩; induction H;
  case elemπ G => {
    apply Merely.elem; existsi G.1;
    fapply Sigma.prod; exact G.2;
    apply Merely.uniq
  };
  apply Merely.uniq
end

hott def Ran.subset {A : Type u} {B : Type v} (f : A → B) : Ran f → B :=
Sigma.fst

hott def Ran.incl {A : Type u} {B : Type v} {f : A → B} (H : surjective f) : B → Ran f :=
λ x, ⟨x, H x⟩

hott def surjImplRanEqv {A : Type u} {B : Type v} (f : A → B) (H : surjective f) : Ran f ≃ B :=
begin
  existsi Sigma.fst; fapply Prod.mk <;> existsi Ran.incl H;
  { intro ⟨_, _⟩; fapply Sigma.prod; reflexivity; apply Merely.uniq };
  { intro; reflexivity }
end

hott def ranConst {A : Type u} (a : A) {B : Type v} (b : B) :
  Ran (Function.const A b) :=
⟨b, Merely.elem ⟨a, Id.refl⟩⟩

hott def ranConstEqv {A : Type u} (a : A) {B : Type v}
  (H : hset B) (b : B) : Ran (Function.const A b) ≃ 𝟏 :=
begin
  existsi (λ _, ★); fapply Prod.mk <;> existsi (λ _, ranConst a b);
  { intro ⟨b', (G : ∥_∥)⟩; fapply Sigma.prod; change b = b';
    induction G; case elemπ w => { exact w.2 }; apply H;
    apply Merely.uniq };
  { intro ★; reflexivity }
end

hott def isEmbedding {A : Type u} {B : Type v} (f : A → B) :=
Π x y, @Equiv.biinv (x = y) (f x = f y) (Id.map f)

hott def Embedding (A : Type u) (B : Type v) :=
Σ (f : A → B), isEmbedding f

infix:55 " ↪ " => Embedding

section
  variable {A : Type u} {B : Type v} (f : A ↪ B)

  def Embedding.ap : A → B := f.1
  def Embedding.eqv (x y : A) : (x = y) ≃ (f.ap x = f.ap y) :=
  ⟨Id.map f.ap, f.2 x y⟩
end

hott def ntypeOverEmbedding {A : Type u} {B : Type v} (f : A ↪ B) (n : ℕ₋₂) :
  is-(hlevel.succ n)-type B → is-(hlevel.succ n)-type A :=
begin
  intros H x y; apply ntypeRespectsEquiv; apply Equiv.symm;
  existsi Id.map f.1; apply f.2; apply H
end

hott def eqvMapForward {A : Type u} {B : Type v} (e : A ≃ B)
  (x y : A) (p : e x = e y) : x = y :=
(e.leftForward x)⁻¹ ⬝ (@Id.map B A _ _ e.left p) ⬝ (e.leftForward y)

hott def sigmaPropEq {A : Type u} {B : A → Type v}
  (H : Π x, prop (B x)) {x y : Sigma B} (p : x.1 = y.1) : x = y :=
begin fapply Sigma.prod; exact p; apply H end

hott def propSigmaEquiv {A : Type u} {B : A → Type v} (H : Π x, prop (B x))
  (x y : Σ x, B x) : (x = y) ≃ (x.1 = y.1) :=
begin
  apply Equiv.trans; apply Sigma.sigmaPath;
  apply Equiv.trans; apply Sigma.respectsEquiv;
  { intro; apply contrEquivUnit.{_, 1}; fapply Sigma.mk;
    apply H; intro; apply propIsSet; apply H };
  apply Equiv.trans; apply Sigma.const; apply unitProdEquiv
end

hott def propSigmaEmbedding {A : Type u} {B : A → Type v}
  (H : Π x, prop (B x)) : (Σ x, B x) ↪ A :=
begin
  existsi Sigma.fst; intro x y;
  apply Equiv.transport Equiv.biinv _ (propSigmaEquiv H x y).2;
  apply Theorems.funext; intro p; induction p; reflexivity
end

hott def isConnected (A : Type u) :=
Σ (x : A), Π y, ∥x = y∥

end GroundZero.Theorems.Functions