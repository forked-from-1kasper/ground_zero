import GroundZero.HITs.Merely

open GroundZero.Types GroundZero.HITs
open GroundZero.Structures

namespace GroundZero.Theorems.Functions
universe u v

hott def injective {α : Type u} {β : Type v} (f : α → β) :=
Π x y, f x = f y → x = y

hott def fibInh {α : Type u} {β : Type v} (f : α → β) :=
λ b, ∥fib f b∥

hott def surj {α : Type u} {β : Type v} (f : α → β) :=
fiberwise (fibInh f)

hott def Ran {α : Type u} {β : Type v} (f : α → β) :=
total (fibInh f)

hott def cut {α : Type u} {β : Type v} (f : α → β) : α → Ran f :=
λ x, ⟨f x, Merely.elem ⟨x, Id.refl⟩⟩

hott def cutIsSurj {α : Type u} {β : Type v} (f : α → β) : surj (cut f) :=
begin
  intro ⟨x, (H : ∥_∥)⟩; induction H;
  case elemπ G => {
    apply Merely.elem; existsi G.1;
    fapply Sigma.prod; exact G.2;
    apply Merely.uniq
  };
  apply Merely.uniq
end

hott def Ran.subset {α : Type u} {β : Type v} (f : α → β) : Ran f → β :=
Sigma.fst

hott def Ran.incl {α : Type u} {β : Type v} {f : α → β} (H : surj f) : β → Ran f :=
λ x, ⟨x, H x⟩

hott def surjImplRanEqv {α : Type u} {β : Type v} (f : α → β) (H : surj f) : Ran f ≃ β :=
begin
  existsi Sigma.fst; fapply Prod.mk <;> existsi Ran.incl H;
  { intro ⟨_, _⟩; fapply Sigma.prod; reflexivity; apply Merely.uniq };
  { intro; reflexivity }
end

hott def ranConst {α : Type u} (a : α) {β : Type v} (b : β) :
  Ran (Function.const α b) :=
⟨b, Merely.elem ⟨a, Id.refl⟩⟩

hott def ranConstEqv {α : Type u} (a : α) {β : Type v}
  (H : hset β) (b : β) : Ran (Function.const α b) ≃ 𝟏 :=
begin
  existsi (λ _, ★); fapply Prod.mk <;> existsi (λ _, ranConst a b);
  { intro ⟨b', (G : ∥_∥)⟩; fapply Sigma.prod; change b = b';
    induction G; case elemπ w => { exact w.2 }; apply H;
    apply Merely.uniq };
  { intro ★; reflexivity }
end

hott def embedding (α : Type u) (β : Type v) :=
Σ (f : α → β), Π x y, @Equiv.biinv (x = y) (f x = f y) (Id.map f)

infix:55 " ↪ " => embedding

section
  variable {α : Type u} {β : Type v} (f : α ↪ β)

  def embedding.ap : α → β := f.1
  def embedding.eqv (x y : α) : (x = y) ≃ (f.ap x = f.ap y) :=
  ⟨Id.map f.ap, f.2 x y⟩
end

hott def ntypeOverEmbedding {α : Type u} {β : Type v} (f : α ↪ β) (n : ℕ₋₂) :
  is-(hlevel.succ n)-type β → is-(hlevel.succ n)-type α :=
begin
  intros H x y; apply ntypeRespectsEquiv; apply Equiv.symm;
  existsi Id.map f.1; apply f.2; apply H
end

hott def eqvMapForward {α : Type u} {β : Type v} (e : α ≃ β)
  (x y : α) (p : e x = e y) : x = y :=
(e.leftForward x)⁻¹ ⬝ (@Id.map β α _ _ e.left p) ⬝ (e.leftForward y)

hott def sigmaPropEq {α : Type u} {β : α → Type v}
  (H : Π x, prop (β x)) {x y : Sigma β} (p : x.1 = y.1) : x = y :=
begin fapply Sigma.prod; exact p; apply H end

hott def propSigmaEquiv {α : Type u} {β : α → Type v} (H : Π x, prop (β x))
  (x y : Σ x, β x) : (x = y) ≃ (x.1 = y.1) :=
begin
  apply Equiv.trans; apply Sigma.sigmaPath;
  apply Equiv.trans; apply Sigma.respectsEquiv;
  { intro; apply contrEquivUnit; fapply Sigma.mk;
    apply H; intro; apply propIsSet; apply H };
  apply Equiv.trans; apply Sigma.const; apply unitProdEquiv
end

hott def propSigmaEmbedding {α : Type u} {β : α → Type v}
  (H : Π x, prop (β x)) : (Σ x, β x) ↪ α :=
begin
  existsi Sigma.fst; intro x y;
  apply Equiv.transport Equiv.biinv _ (propSigmaEquiv H x y).2;
  apply Theorems.funext; intro p; induction p; reflexivity
end

hott def isConnected (α : Type u) :=
Σ (x : α), Π y, ∥x = y∥

end GroundZero.Theorems.Functions