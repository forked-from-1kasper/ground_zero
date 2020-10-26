import ground_zero.HITs.merely
open ground_zero.structures (hlevel.succ prop)
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
λ x, ⟨f x, merely.elem ⟨x, Id.refl⟩⟩

@[hott] def cut_is_surj {α : Type u} {β : Type v}
  (f : α → β) : surj (cut f) :=
begin
  intro x, induction x with x h,
  fapply merely.ind _ _ h,
  { intro g, induction g with y p,
    apply merely.elem, existsi y,
    fapply sigma.prod, exact p,
    apply merely.uniq },
  { intro, apply merely.uniq }
end

@[hott] def ran.subset {α : Type u} {β : Type v}
  (f : α → β) : ran f → β :=
sigma.fst

@[hott] def ran.incl {α : Type u} {β : Type v}
  {f : α → β} (h : surj f) : β → ran f :=
λ x, ⟨x, h x⟩

@[hott] def surj_impl_ran_eqv {α : Type u} {β : Type v}
  (f : α → β) (h : surj f) : ran f ≃ β :=
begin
  existsi sigma.fst, split; existsi ran.incl h,
  { intro x, induction x with x g,
    fapply sigma.prod, refl,
    apply merely.uniq },
  { intro x, refl }
end

@[hott] def ran_const {α : Type u} (a : α) {β : Type v} (b : β) :
  ran (function.const α b) :=
⟨b, merely.elem ⟨a, Id.refl⟩⟩

@[hott] def ran_const_eqv {α : Type u} (a : α) {β : Type v}
  (h : ground_zero.structures.hset β) (b : β) :
  ran (function.const α b) ≃ 𝟏 :=
begin
  existsi (λ _, ★), split; existsi (λ _, ran_const a b),
  { intro x, induction x with b' inh,
    fapply sigma.prod, change b = b',
    fapply merely.ind _ _ inh,
    { intro F, induction F with c p, exact p },
    { intro F, exact h },
    { apply merely.uniq } },
  { intro x, induction x, refl }
end

@[hott] def embedding (α : Type u) (β : Type v) :=
Σ (f : α → β), Π x y, @equiv.biinv (x = y) (f x = f y) (Id.map f)

infix ` ↪ `:50 := embedding

section
  variables {α : Type u} {β : Type v} (f : α ↪ β)

  def embedding.ap : α → β := f.fst
  def embedding.eqv (x y : α) : (x = y) ≃ (f.ap x = f.ap y) :=
  ⟨Id.map f.ap, f.snd x y⟩
end

@[hott] def ntype_over_embedding {α : Type u} {β : Type v}
  (f : α ↪ β) (n : ℕ₋₂) : is-(hlevel.succ n)-type β → is-(hlevel.succ n)-type α :=
begin
  intros H x y, apply ground_zero.structures.ntype_respects_equiv,
  { symmetry, apply f.eqv }, apply H
end

@[hott] def eqv_map_forward {α : Type u} {β : Type v} (e : α ≃ β)
  (x y : α) (p : e.forward x = e.forward y) : x = y :=
(e.left_forward x)⁻¹ ⬝ (@Id.map β α _ _ e.left p) ⬝ (e.left_forward y)

@[hott] def sigma_prop_eq {α : Type u} {β : α → Type v}
  (H : Π x, prop (β x)) {x y : sigma β} (p : x.fst = y.fst) : x = y :=
begin fapply ground_zero.types.sigma.prod, exact p, apply H end

@[hott] def prop_sigma_embedding {α : Type u} {β : α → Type v}
  (H : Π x, prop (β x)) : (Σ x, β x) ↪ α :=
begin
  existsi sigma.fst, intros x y, split; existsi sigma_prop_eq H,
  { intro p, induction x, induction y, induction p,
    change ground_zero.types.sigma.prod _ _ = _,
    transitivity, apply Id.map, change _ = idp _,
    apply ground_zero.structures.prop_is_set,
    apply H, reflexivity },
  { intro p, induction x with x X, induction y with y Y,
    change x = y at p, induction p,
    have q := H x X Y, induction q,
    change Id.map sigma.fst (ground_zero.types.sigma.prod _ _) = _,
    transitivity, apply Id.map (Id.map sigma.fst),
    apply Id.map, change _ = idp _,
    apply ground_zero.structures.prop_is_set,
    apply H, reflexivity }
end

@[hott] def is_connected (α : Type u) :=
Σ (x : α), Π y, ∥x = y∥

end ground_zero.theorems.functions