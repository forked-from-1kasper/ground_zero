import ground_zero.HITs.truncation
import ground_zero.types.sigma
open ground_zero.types ground_zero.HITs

namespace ground_zero.theorems.functions
universes u v

hott theory

@[hott] def injective {α : Type u} {β : Type v} (f : α → β) :=
Π x y, f x = f y → x = y

@[hott] def fib_inh {α : Type u} {β : Type v} (f : α → β) :=
λ b, ∥fib f b∥

@[hott] def surj {α : Type u} {β : Type v} (f : α → β) :=
fiberwise (fib_inh f)

@[hott] def ran {α : Type u} {β : Type v} (f : α → β) :=
total (fib_inh f)

@[hott] def cut {α : Type u} {β : Type v} (f : α → β) : α → ran f :=
λ x, ⟨f x, truncation.elem ⟨x, eq.rfl⟩⟩

@[hott] def cut_is_surj {α : Type u} {β : Type v}
  (f : α → β) : surj (cut f) := begin
  intro x, induction x with x h,
  fapply truncation.ind _ _ h,
  { intro g, induction g with y p,
    apply truncation.elem, existsi y,
    fapply sigma.prod, exact p,
    apply truncation.uniq },
  { intro, apply truncation.uniq }
end

@[hott] def ran.subset {α : Type u} {β : Type v}
  (f : α → β) : ran f → β :=
sigma.fst

@[hott] def ran.incl {α : Type u} {β : Type v}
  {f : α → β} (h : surj f) : β → ran f :=
λ x, ⟨x, h x⟩

@[hott] def surj_impl_ran_eqv {α : Type u} {β : Type v}
  (f : α → β) (h : surj f) : ran f ≃ β := begin
  existsi sigma.fst, split; existsi ran.incl h,
  { intro x, induction x with x g,
    fapply sigma.prod, refl,
    apply truncation.uniq },
  { intro x, refl }
end

@[hott] def ran_const {α : Type u} (a : α) {β : Type v} (b : β) :
  ran (function.const α b) :=
⟨b, truncation.elem ⟨a, eq.rfl⟩⟩

@[hott] def ran_const_eqv {α : Type u} (a : α) {β : Type v}
  (h : ground_zero.structures.hset β) (b : β) :
  ran (function.const α b) ≃ 𝟏 := begin
  existsi (λ _, ★), split; existsi (λ _, ran_const a b),
  { intro x, induction x with b' inh,
    fapply sigma.prod, change b = b',
    fapply truncation.ind _ _ inh,
    { intro F, induction F with c p, exact p },
    { intro F, exact h },
    { apply truncation.uniq } },
  { intro x, induction x, refl }
end

@[hott] def embedding {α : Type u} {β : Type v} (f : α → β) :=
Π (x y : α), @equiv.biinv (x = y) (f x = f y) (eq.map f)

@[hott] def is_connected (α : Type u) :=
Σ (x : α), Π y, ∥x = y∥

end ground_zero.theorems.functions