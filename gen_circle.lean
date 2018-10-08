namespace ground_zero

inductive {u} const (α : Sort u) : Sort u
| f : α → const
def {u} generalized (α : Sort u) := @quot (const α) (λ _ _, true)
notation `{` α `}` := generalized α

def {u} generalized.f {α : Sort u} (a : α) : {α} :=
quot.mk (λ _ _, true) (const.f a)
def {u} generalized.e {α : Sort u} (a b : α) : generalized.f a = generalized.f b :=
quot.sound true.intro

@[recursor] def {u} generalized.ind {α : Sort u} {π : {α} → Prop}
    (f : Π (a : α), π (generalized.f a)) : Π (x : generalized α), π x :=
  @quot.ind (const α) (λ _ _, true) π (λ (x : const α), const.rec f x)

def {u} generalized.repeat {α : Sort u} : ℕ → Sort u
| 0 := α
| (n+1) := {generalized.repeat n}

def S1 := generalized unit
notation `S¹` := S1
namespace S1
  def base : S¹ := generalized.f unit.star
  def loop : base = base := generalized.e unit.star unit.star

  def {u} rec {β : Sort u} (b : β) (s : β = β) : Π (x : S¹), β :=
  @quot.lift (const unit) (λ _ _, true) β (λ _, b) (begin intros, simp end)
end S1

end ground_zero