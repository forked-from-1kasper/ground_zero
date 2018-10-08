namespace ground_zero

inductive {u} const (α : Sort u) : Sort u
| f : α → const

inductive {u} generalized.rel {α : Sort u} : (const α) → (const α) → Prop
| mk : Π (a b : α), generalized.rel (const.f a) (const.f b)

def {u} generalized (α : Sort u) := @quot (const α) generalized.rel
notation `{` α `}` := generalized α

def {u} generalized.f {α : Sort u} (a : α) : {α} :=
quot.mk generalized.rel (const.f a)

def {u} generalized.e {α : Sort u} (a b : α) : generalized.f a = generalized.f b :=
quot.sound (generalized.rel.mk a b)

@[recursor] def {u} generalized.ind {α : Sort u} {π : {α} → Prop}
    (f : Π (a : α), π (generalized.f a)) : Π (x : generalized α), π x :=
  @quot.ind (const α) generalized.rel π (λ (x : const α), const.rec f x)

-- current definition is incorrect
def {u} uniq {α : Type u} (a b : {α}) : a = b := begin
  induction a, induction b,
  induction a, induction b,
  apply (@quot.sound (const α) generalized.rel (const.f a) (const.f b) (generalized.rel.mk a b)),
  repeat { trivial }
end

def {u} generalized.repeat {α : Sort u} : ℕ → Sort u
| 0 := α
| (n+1) := {generalized.repeat n}

def circle := generalized unit
notation `S¹` := circle
namespace circle
  def base : S¹ := generalized.f unit.star
  def loop : base = base := generalized.e unit.star unit.star

  def {u} rec {β : Sort u} (b : β) (s : β = β) : Π (x : S¹), β :=
  @quot.lift (const unit) generalized.rel β (λ _, b) (begin intros, simp end)
end circle

end ground_zero