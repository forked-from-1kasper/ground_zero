import ground_zero.types.ens
open ground_zero.types ground_zero.structures

hott theory

/-
  Magma, semigroup, monoid, group, abelian group.
  * HoTT 6.11
-/

namespace ground_zero.algebra
  universe u

  def zeroeqv {α : Type u} (H : hset α) : 0-Type :=
  ⟨α, zero_eqv_set.left (λ _ _, H)⟩

  structure magma :=
  (α : 0-Type) (φ : α.fst → α.fst → α.fst)

  def magma.zero : magma → (0-Type) := magma.α

  structure semigroup extends magma :=
  (mul_assoc : Π a b c, φ (φ a b) c = φ a (φ b c))

  structure monoid extends semigroup :=
  (e : α.fst) (one_mul : Π a, φ e a = a) (mul_one : Π a, φ a e = a)

  def monoid.carrier (M : monoid) := M.α.fst

  def monoid.set (M : monoid) : hset M.carrier :=
  λ _ _, zero_eqv_set.forward M.α.snd

  structure group extends monoid :=
  (inv : α.fst → α.fst) (mul_left_inv : Π a, φ (inv a) a = e)

  def group.to_magma : group → magma :=
  semigroup.to_magma ∘ monoid.to_semigroup ∘ group.to_monoid

  def group.carrier (G : group) := G.α.fst

  def group.set (G : group) : hset G.carrier :=
  λ _ _, zero_eqv_set.forward G.α.snd

  def group.subset (G : group) := ens G.carrier
  def group.univ (G : group) : G.subset := ens.univ G.carrier

  def group.zero : group → (0-Type) :=
  magma.zero ∘ group.to_magma

  class abelian (G : group) :=
  (mul_comm : Π a b, G.φ a b = G.φ b a)
end ground_zero.algebra