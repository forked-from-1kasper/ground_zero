import GroundZero.Theorems.Prop
open GroundZero.Theorems
open GroundZero.Structures

namespace GroundZero.Types
universe u v

structure Precategory (α : Type u) :=
(hom                 : α → α → Type v)
(set                 : Π (x y : α), hset (hom x y))
(id {a : α}          : hom a a)
(comp {a b c : α}    : hom b c → hom a b → hom a c)
(idLeft {a b : α}    : Π (f : hom a b), f = comp id f)
(idRight {a b : α}   : Π (f : hom a b), f = comp f id)
(assoc {a b c d : α} : Π (f : hom a b) (g : hom b c) (h : hom c d), comp h (comp g f) = comp (comp h g) f)

section
  variable (α : Type u) (𝒞 : Precategory α)

  instance : Reflexive  𝒞.hom := ⟨λ _, 𝒞.id⟩
  instance : Transitive 𝒞.hom := ⟨λ _ _ _ p q, 𝒞.comp q p⟩
end

namespace Precategory
  def compose {α : Type u} {𝒞 : Precategory α} {a b c : α}
    (g : hom 𝒞 b c) (f : hom 𝒞 a b) : hom 𝒞 a c := 𝒞.comp g f

  local infix:60 " ∘ " => compose

  def hasInv {α : Type u} (𝒞 : Precategory α) {a b : α} (f : hom 𝒞 a b) :=
  Σ (g : hom 𝒞 b a), (f ∘ g = id 𝒞) × (g ∘ f = id 𝒞)

  def iso {α : Type u} (𝒞 : Precategory α) (a b : α) :=
  Σ (f : hom 𝒞 a b), hasInv 𝒞 f

  hott def idiso {α : Type u} (𝒞 : Precategory α) {a : α} : iso 𝒞 a a :=
  let p : id 𝒞 = id 𝒞 ∘ id 𝒞 := idLeft 𝒞 (@id α 𝒞 a);
  ⟨id 𝒞, ⟨id 𝒞, (p⁻¹, p⁻¹)⟩⟩

  instance : Reflexive (iso 𝒞) := ⟨@idiso _ 𝒞⟩

  hott def idtoiso {α : Type u} (𝒞 : Precategory α)
    {a b : α} (p : a = b) : iso 𝒞 a b :=
  begin induction p; reflexivity end

  hott def invProp {α : Type u} (𝒞 : Precategory α) {a b : α}
    (f : hom 𝒞 a b) : prop (hasInv 𝒞 f) :=
  begin
    intro ⟨g', (H₁, H₂)⟩ ⟨g, (G₁, G₂)⟩;
    fapply Sigma.prod; apply calc
        g' = id 𝒞 ∘ g'    : idLeft _ _
       ... = (g ∘ f) ∘ g' : Id.map (compose · g') G₂⁻¹
       ... = g ∘ (f ∘ g') : (assoc _ _ _ _)⁻¹
       ... = g ∘ id 𝒞     : Id.map (compose g) H₁
       ... = g            : (idRight _ _)⁻¹;
    apply productProp <;> apply set
  end

  def op {α : Type u} (𝒞 : Precategory α) : Precategory α :=
  { hom      := λ a b, hom 𝒞 b a,
    set      := λ a b, set 𝒞 b a,
    id       := 𝒞.id,
    comp     := λ p q, 𝒞.comp q p,
    idLeft   := λ p, 𝒞.idRight p,
    idRight  := λ p, 𝒞.idLeft p,
    assoc    := λ f g h, (𝒞.assoc h g f)⁻¹ }

  def Path (α : Type u) (H : groupoid α) : Precategory α :=
  { hom      := @Id α,
    set      := H,
    id       := idp _,
    comp     := λ p q, q ⬝ p,
    idRight  := λ p, (Id.reflLeft p)⁻¹,
    idLeft   := λ p, (Id.reflRight p)⁻¹,
    assoc    := λ f g h, (Id.assoc f g h)⁻¹ }
end Precategory

end GroundZero.Types