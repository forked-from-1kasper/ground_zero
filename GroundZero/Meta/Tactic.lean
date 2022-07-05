import Lean.PrettyPrinter.Delaborator.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Meta.Tactic.Replace
import Lean.Elab.Command

open Lean

section
  variable {A : Sort u} (ρ : A → A → Sort v)

  class Reflexive :=
  (intro (a : A) : ρ a a)

  class Symmetric :=
  (intro (a b : A) : ρ a b → ρ b a)

  class Transitive :=
  (intro (a b c : A) : ρ a b → ρ b c → ρ a c)
end

section
  variable {A : Sort u} {B : Sort v} {C : Sort w}

  variable (ρ : A → B → Sort u')
  variable (η : B → C → Sort v')
  variable (μ : outParam (A → C → Sort w'))

  class Rewrite :=
  (intro (a : A) (b : B) (c : C) : ρ a b → η b c → μ a c)
end

-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Lean/Expr/Basic.lean#L100-L109
def Lean.Expr.constName (e : Expr) : Name :=
e.constName?.getD Name.anonymous

def Lean.Expr.getAppFnArgs (e : Expr) : Name × Array Expr :=
withApp e λ e a => (e.constName, a)

namespace GroundZero.Meta.Tactic

-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Ring.lean#L411-L419
def applyOnBinRel (name : Name) (rel : Name) : Elab.Tactic.TacticM Unit := do
  let mvars ← Elab.Tactic.liftMetaMAtMain (λ mvar => do
    let ε ← instantiateMVars (← Meta.getMVarDecl mvar).type
    ε.consumeMData.withApp λ e es => do
      unless (es.size > 1) do Meta.throwTacticEx name mvar s!"expected binary relation, got “{e} {es}”"

      let e₃ := es.back; let es := es.pop;
      let e₂ := es.back; let es := es.pop;

      let ty  ← Meta.inferType e₂
      let ty' ← Meta.inferType e₃

      unless (← Meta.isDefEq ty ty') do Meta.throwTacticEx name mvar s!"{ty} ≠ {ty'}"

      let u ← Meta.getLevel ty
      let v ← Meta.getLevel ε

      let ι ← Meta.synthInstance (mkApp2 (Lean.mkConst rel [u, v]) ty (mkAppN e es))
      let φ := (← Meta.reduceProj? (mkProj rel 0 ι)).getD ι

      Meta.apply mvar φ)
  Elab.Tactic.replaceMainGoal mvars

section
  elab "reflexivity"  : tactic => applyOnBinRel `reflexivity  `Reflexive
  elab "symmetry"     : tactic => applyOnBinRel `symmetry     `Symmetric
  elab "transitivity" : tactic => applyOnBinRel `transitivity `Transitive
end

-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Basic.lean
-- Author: Mario Carneiro
syntax "iterate" (ppSpace num)? ppSpace tacticSeq : tactic
macro_rules
  | `(tactic|iterate $seq:tacticSeq) =>
    `(tactic|try ($seq:tacticSeq); iterate $seq:tacticSeq)
  | `(tactic|iterate $n $seq:tacticSeq) =>
    match n.raw.toNat with
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

elab "whnf" : tactic => do
  let mvarId ← Elab.Tactic.getMainGoal
  let target ← Elab.Tactic.getMainTarget
  let targetNew ← Meta.whnf target
  Elab.Tactic.replaceMainGoal [← Meta.replaceTargetDefEq mvarId targetNew]

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

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/How.20to.20use.20hand.20written.20parsers/near/245760023
-- Author: Mario Carneiro
def calcLHS : Parser.Parser :=
{ fn := λ c s =>
    let s := Parser.symbolFn "..." c s
    if s.hasError then s else
    let tables := (Parser.getCategory (Parser.parserExtension.getState c.env).categories `term).get!.tables
    Parser.trailingLoop tables c s
  info := ("..." >> Parser.termParser).info }

open PrettyPrinter Elab.Term

@[combinatorFormatter GroundZero.Meta.Tactic.calcLHS] def calcLHS.formatter : Formatter := pure ()
@[combinatorParenthesizer GroundZero.Meta.Tactic.calcLHS] def calcLHS.parenthesizer : Parenthesizer := pure ()

def extRelation (e : Expr) : TermElabM (Expr × Expr) :=
  e.withApp λ e es => do
    unless (es.size > 1) do throwError "expected binary relation"
    return (es.back, mkAppN e es.pop.pop)

def getEqn (e : Syntax) : TermElabM (Syntax × Syntax) := do
  unless (e.getArgs.size > 2) do throwError "expected binary relation"
  return (e.getArgs.get! 0, e.getArgs.get! 2)

elab "calc " ε:term " : " τ:term σ:(calcLHS " : " term)* : term => do
  let σ ← Array.mapM getEqn σ

  let ε ← Elab.Term.elabTerm ε none
  let ε ← instantiateMVars ε

  let e₁ := ε.withApp (λ _ es => es.pop.back)
  let ty₁ ← Meta.inferType e₁
  let u₁  ← Meta.getLevel ty₁

  let mut (e₂, ρ₁) ← extRelation ε
  let mut η ← Elab.Term.elabTermEnsuringType τ ε

  let mut ty₂ ← Meta.inferType e₂
  let mut u₂  ← Meta.getLevel ty₂

  let mut v₁ ← Meta.getLevel ε

  for (e, τ) in σ do
    let ε ← Elab.Term.elabTerm (e.setArg 0 (← PrettyPrinter.delab e₂)) none
    let ε ← instantiateMVars ε

    let τ ← Elab.Term.elabTermEnsuringType τ ε
    let mut v₂ ← Meta.getLevel ε

    let (e₃, ρ₂) ← extRelation ε

    let ty₃ ← Meta.inferType e₃
    let u₃  ← Meta.getLevel ty₃

    let v₃ ← Meta.mkFreshLevelMVar
    let ρ₃ ← Meta.mkFreshExprMVar none

    let ι ← Meta.synthInstance (mkApp6 (Lean.mkConst `Rewrite [u₁, u₂, u₃, v₁, v₂, v₃]) ty₁ ty₂ ty₃ ρ₁ ρ₂ ρ₃)
    let φ := (← Meta.reduceProj? (mkProj `Rewrite 0 ι)).getD ι

    η := mkAppN φ #[e₁, e₂, e₃, η, τ]
    (ty₂, u₂, e₂, v₁, ρ₁) := (ty₃, u₃, e₃, v₃, ρ₃)

  return η

end GroundZero.Meta.Tactic