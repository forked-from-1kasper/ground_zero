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
def applyOnBinRel (n : Lean.Name) : Elab.Tactic.TacticM Unit := do
  let mvars ← Elab.Tactic.liftMetaMAtMain (λ mvar => do
    let ε ← Meta.instantiateMVars (← Meta.getMVarDecl mvar).type
    ε.withApp λ e es => do
      if ¬(es.size > 1) then throwError "expected binary relation"

      let e₂ := es.back; let es := es.pop;
      let e₁ := es.back; let es := es.pop;

      let ty  ← Meta.inferType e₁
      let ty' ← Meta.inferType e₂

      if ¬(← Meta.isDefEq ty ty') then throwError "{ty} ≠ {ty'}"

      let u ← Meta.getLevel ty
      let v ← Meta.getLevel ε

      mkApp2 (mkConst n [u, v]) ty (mkAppN e es)
      |> Meta.apply mvar)
  Lean.Elab.Tactic.replaceMainGoal mvars

section
  elab "reflexivity"  : tactic => applyOnBinRel `Reflexive.intro
  elab "symmetry"     : tactic => applyOnBinRel `Symmetric.intro
  elab "transitivity" : tactic => applyOnBinRel `Transitive.intro
end

end GroundZero.Meta.Tactic