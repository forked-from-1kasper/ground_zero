# Ground Zero

This is an attempt to develop Homotopy Type Theory in [Lean 4](https://github.com/leanprover/lean4/).

As in [gebner/hott3](https://github.com/gebner/hott3), no modifications to the Lean kernel are made, because library uses [large eliminator checker](https://github.com/forked-from-1kasper/ground_zero/blob/master/GroundZero/Meta/HottTheory.lean) ported [from Lean 3](https://github.com/gebner/hott3/blob/master/src/hott/init/meta/support.lean). So stuff like this will print an error:

```lean
hott theorem Id.UIP {α : Type u} {a b : α} (p q : a = b) : p = q :=
begin cases p; cases q; apply Id.refl end
```

## HITs

[Most HITs in the library](https://github.com/forked-from-1kasper/lean/tree/master/ground_zero/HITs) constructed using [quotients](https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#quotients). Quotients in Lean have good computational properties (`Quot.ind` computes), so we can define HITs with them without any other changes in Lean’s kernel.

There are:

* [Interval](https://github.com/forked-from-1kasper/ground_zero/blob/master/GroundZero/HITs/Interval.lean) ![I](pictures/interval.svg).
* [Pushout](https://github.com/forked-from-1kasper/ground_zero/blob/master/GroundZero/HITs/Pushout.lean) ![pushout](pictures/pushout.svg).
* [Homotopical reals](https://github.com/forked-from-1kasper/ground_zero/blob/master/GroundZero/HITs/Reals.lean) ![R](pictures/reals.svg).
* (Sequential) [colimit](https://github.com/forked-from-1kasper/ground_zero/blob/master/GroundZero/HITs/Colimit.lean).
* [Generalized circle](https://github.com/forked-from-1kasper/ground_zero/blob/master/GroundZero/HITs/Generalized.lean) ![{α}](pictures/gen-circle.svg).
* [Propositional truncation](https://github.com/forked-from-1kasper/ground_zero/blob/master/GroundZero/HITs/Merely.lean) as a colimit of a following sequence:
  ![α → {α} → {{α}} → ...](pictures/prop-truncation-seq-colimit.svg)
* [Suspension](https://github.com/forked-from-1kasper/ground_zero/blob/master/GroundZero/HITs/Suspension.lean) ![∑α](pictures/susp.svg) is defined as the pushout of the span ![𝟏 ← α → 𝟏](pictures/susp-span.svg).
* [Circle](https://github.com/forked-from-1kasper/ground_zero/blob/master/GroundZero/HITs/Circle.lean) ![S¹](pictures/s1.svg) is the suspension of the bool ![𝟐](pictures/bool.svg).
* Sphere ![S²](pictures/s2.svg) is the suspension of the circle ![S¹](pictures/s1.svg).
* [Join](https://github.com/forked-from-1kasper/ground_zero/blob/master/GroundZero/HITs/Join.lean) ![join α β](pictures/join.svg).

There are also HITs that cannot be constructed this way. These HITs are defined using standard trick with [private structures](https://github.com/forked-from-1kasper/ground_zero/blob/master/GroundZero/HITs/Trunc.lean).

## Dependency map

![dependency map](pictures/dependency-map.svg "dependency map")
