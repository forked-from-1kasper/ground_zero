# Ground Zero

[![Build Status](https://travis-ci.org/groupoid/lean.svg?branch=master)](https://travis-ci.org/groupoid/lean)

## HITs

[All of the HITs in the library](https://github.com/groupoid/lean/tree/master/ground_zero/HITs) constructed using [quotients](https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#quotients). Quotients in Lean have good computational properties (`quot.ind` computes), so we can define HITs with them without any other changes in Lean’s kernel.

There are many basic—not defined in terms of another Higher Inductive Type—HITs: truncations, pushout, homotopical reals.

Other HITs:

* Interval `I` is defined as a generalized circle of bool `{𝟐}` (also it can be a propositionally truncated bool, but with generalized circle we can get a simpler terms).
* Suspension `∑α` is defined as the pushout of the span `𝟏 ← α → 𝟏`.
* Circle `S¹` is the suspension of the bool `𝟐`.
* Sphere `S²` is the suspension of the circle `S¹`.

## Cubical Type Theory ([cubical/](https://github.com/groupoid/lean/blob/master/ground_zero/cubical/path.lean) directory)

In the topology functions from the interval to some type is a paths in this type. In HoTT book path type is defined as a classical inductive type with one constructor:

```lean
inductive eq {α : Sort u} (a : α) : α → Sort u
| refl : eq a
```

But if we define paths as `I → α`, then we can use a nice syntax for paths as in [cubicaltt](https://github.com/mortberg/cubicaltt) or [Arend](https://github.com/JetBrains/arend):

```lean
@[refl] def refl {α : Sort u} (a : α) : a ⇝ a := <i> a

@[symm] def symm {α : Sort u} {a b : α} (p : a ⇝ b) : b ⇝ a :=
<i> p # −i

def funext {α : Sort u} {β : α → Sort v} {f g : Π (x : α), β x}
  (p : Π (x : α), f x ⇝ g x) : f ⇝ g :=
<i> λ x, (p x) # i
```

The same in cubicaltt:

```cubicaltt
refl (A : U) (a : A) : Path A a a = <i> a

symm (A : U) (a b : A) (p : Path A a b) : Path A b a =
  <i> p @ -i

funExt (A : U) (B : A -> U) (f g : (x : A) -> B x)
       (p : (x : A) -> Path (B x) (f x) (g x)) :
       Path ((y : A) -> B y) f g = <i> \(a : A) -> (p a) @ i
```

We can also define `coe` as in [yacctt](https://github.com/mortberg/yacctt):

```lean
def coe.forward (π : I → Sort u) (i : I) (x : π i₀) : π i :=
interval.ind x (equiv.subst seg x) (equiv.path_over_subst eq.rfl) i

def coe (i k : I) (π : I → Sort u) : π i → π k :=
coe.forward (λ i, π i → π k) i (coe.forward π k)
```

And use it:

```lean
def trans {α β : Sort u} (p : α ⇝ β) : α → β :=
coe 0 1 (λ i, p # i)

def trans_neg {α β : Sort u} (p : α ⇝ β) : β → α :=
coe 1 0 (λ i, p # i)

def transK {α β : Sort u} (p : α ⇝ β) (x : α) :
  x ⇝ trans_neg p (trans p x) :=
<i> coe i 0 (λ i, p # i) (coe 0 i (λ i, p # i) x)
```

In yacctt:

```yacctt
trans (A B : U) (p : Path U A B) (a : A) : B = coe 0->1 p a
transNeg (A B : U) (p : Path U A B) (b : B) : A = coe 1->0 p b

transK (A B : U) (p : Path U A B) (a : A) :
  Path A a (transNeg A B p (trans A B p a)) =
  <i> coe i->0 p (coe 0->i p a)
```

We can freely transform cubical paths to classical and back:

```lean
def from_equality {α : Sort u} {a b : α} (p : a = b :> α) : Path a b :=
Path.lam (interval.rec a b p)

def to_equality {α : Sort u} {a b : α} (p : Path a b) : a = b :> α :=
begin cases p with f, apply eq.map, exact interval.seg end
```

## Dependency map

![dependency map](dependency_map.svg "dependency map")
