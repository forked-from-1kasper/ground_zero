import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Command

open Lean

section
  variable {α : Sort u} (ρ : α → α → Sort v)

  class Reflexive :=
  (intro (a : α) : ρ a a)

  class Symmetric :=
  (intro (a b : α) : ρ a b → ρ b a)

  class Transitive :=
  (intro (a b c : α) : ρ a b → ρ b c → ρ a c)
end

-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Lean/Expr/Basic.lean#L100-L109
def Lean.Expr.constName (e : Expr) : Name :=
e.constName?.getD Name.anonymous

def Lean.Expr.getAppFnArgs (e : Expr) : Name × Array Expr :=
withApp e λ e a => (e.constName, a)

namespace GroundZero.Meta.Tactic

-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Ring.lean#L411-L419
def applyOnBinRel (name : Name) (ctor : Name) : Elab.Tactic.TacticM Unit := do
  let mvars ← Elab.Tactic.liftMetaMAtMain (λ mvar => do
    let ε ← Meta.instantiateMVars (← Meta.getMVarDecl mvar).type
    ε.withApp λ e es => do
      unless (es.size > 1) do Meta.throwTacticEx name mvar "expected binary relation"

      let e₂ := es.back; let es := es.pop;
      let e₁ := es.back; let es := es.pop;

      let ty  ← Meta.inferType e₁
      let ty' ← Meta.inferType e₂

      unless (← Meta.isDefEq ty ty') do Meta.throwTacticEx name mvar s!"{ty} ≠ {ty'}"

      let u ← Meta.getLevel ty
      let v ← Meta.getLevel ε

      mkApp2 (mkConst ctor [u, v]) ty (mkAppN e es)
      |> Meta.apply mvar)
  Elab.Tactic.replaceMainGoal mvars

section
  elab "reflexivity"  : tactic => applyOnBinRel `reflexivity  `Reflexive.intro
  elab "symmetry"     : tactic => applyOnBinRel `symmetry     `Symmetric.intro
  elab "transitivity" : tactic => applyOnBinRel `transitivity `Transitive.intro
end

-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Basic.lean
-- Author: Mario Carneiro
syntax "iterate" (ppSpace num)? ppSpace tacticSeq : tactic
macro_rules
  | `(tactic|iterate $seq:tacticSeq) =>
    `(tactic|try ($seq:tacticSeq); iterate $seq:tacticSeq)
  | `(tactic|iterate $n $seq:tacticSeq) =>
    match n.toNat with
    |   0   => `(tactic| skip)
    | n + 1 => `(tactic|($seq:tacticSeq); iterate $(quote n) $seq:tacticSeq)

elab "fapply " e:term : tactic =>
  Elab.Tactic.evalApplyLikeTactic (Meta.apply (cfg := {newGoals := Meta.ApplyNewGoals.all})) e

macro_rules | `(tactic| change $e:term) => `(tactic| show $e)

-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/LeftRight.lean
-- Author: Siddhartha Gadgil
def getCtors (name : Name) (mvar : MVarId) : MetaM (List Name × List Level) := do
    Meta.checkNotAssigned mvar name
    let target ← Meta.getMVarType' mvar
    matchConstInduct target.getAppFn
      (λ _ => Meta.throwTacticEx `constructor mvar "target is not an inductive datatype")
      (λ ival us => return (ival.ctors, us))

def leftRightMeta (pickLeft : Bool) (mvar : MVarId) : MetaM (List MVarId) := do
  Meta.withMVarContext mvar do
    let name := if pickLeft then `left else `right
    let (ctors, us) ← getCtors name mvar
    unless ctors.length == 2 do
      Meta.throwTacticEx `constructor mvar
        s!"{name} target applies for inductive types with exactly two constructors"
    let ctor := ctors.get! (if pickLeft then 0 else 1)
    Meta.apply mvar (mkConst ctor us)

elab "left"  : tactic => Elab.Tactic.liftMetaTactic (leftRightMeta true)
elab "right" : tactic => Elab.Tactic.liftMetaTactic (leftRightMeta false)

def getExistsiCtor (mvar : MVarId) : MetaM Name := do
  Meta.withMVarContext mvar do
    let (ctors, us) ← getCtors `existsi mvar
    unless ctors.length == 1 do
      Meta.throwTacticEx `constructor mvar
        "existsi target applies for inductive types with exactly one constructor"
    return (ctors.get! 0)

elab "existsi" e:term : tactic => do
  let ctor ← Elab.Tactic.liftMetaMAtMain getExistsiCtor
  let ε := Syntax.mkApp (mkIdent ctor) #[e]
  Elab.Tactic.evalTactic (← `(tactic| apply $ε))

end GroundZero.Meta.Tactic