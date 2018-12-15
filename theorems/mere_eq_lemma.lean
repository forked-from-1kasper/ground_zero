import ground_zero.HITs.trunc

namespace ground_zero.mere_eq_lemma
universe u

def to_mere_eq {α β : Sort u} (h : α = β) : ∥α = β :> Sort u∥ :=
begin induction h, apply ground_zero.HITs.trunc.elem, reflexivity end

def from_mere_eq {α β : Sort u} : ∥α = β :> Sort u∥ → α = β :=
ground_zero.HITs.trunc.rec (begin intro x, induction x, reflexivity end)

lemma mere_eq {α β : Sort u} : (α = β) ≃ ∥α = β :> Sort u∥ := begin
  existsi to_mere_eq, split; existsi from_mere_eq,
  { trivial },
  { intro h, simp, apply ground_zero.HITs.trunc.uniq }
end

end ground_zero.mere_eq_lemma