import ground_zero.algebra.group.basic
open ground_zero.structures
open ground_zero

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group
  variables {G : pregroup} [group G]
  local infix ` * `  := G.φ
  local notation `e` := G.e
  local postfix ⁻¹   := G.ι

  def P.carrier (G : pregroup) := ℕ → G.carrier

  @[hott] def P.hset (G : pregroup) : hset (P.carrier G) :=
  begin apply pi_hset, intros x a b, apply G.hset end

  section
    variables {H : pregroup}

    def P.mul : P.carrier H → P.carrier H → P.carrier H :=
    λ f g n, H.φ (f n) (g n)

    def P.one : P.carrier H := λ _, H.e
    def P.inv : P.carrier H → P.carrier H :=
    λ f n, H.ι (f n)
  end

  @[hott] def P (G : pregroup) : pregroup :=
  @pregroup.intro (P.carrier G) (λ _ _, P.hset G) P.mul P.inv P.one

  @[hott] instance P.semigroup : semigroup (P G).magma :=
  ⟨begin intros a b c, apply theorems.funext, intro n, apply G.mul_assoc end⟩

  @[hott] instance P.monoid : monoid (P G).premonoid :=
  begin
    split, exact P.semigroup,
    repeat { intro f, fapply theorems.funext, intro n },
    apply G.one_mul, apply G.mul_one
  end

  @[hott] instance P.group : group (P G) :=
  ⟨P.monoid, begin intro f, fapply theorems.funext, intro n, apply G.mul_left_inv end⟩

  @[hott] instance P.abelian (G : pregroup) [abelian G] : abelian (P G) :=
  ⟨begin intros f g, fapply theorems.funext, intro n, fapply abelian.mul_comm end⟩

  @[hott] def P.unit_sqr (H : Π x, x * x = e) (x : P.carrier G) :
    P.mul x x = P.one :=
  begin fapply theorems.funext, intro n, apply H end

  def P₂ := P Z₂
  @[hott] def P₂.periodic (x : P₂.carrier) : P.mul x x = P.one :=
  begin apply P.unit_sqr, intro b, induction b; trivial end
end group

end ground_zero.algebra