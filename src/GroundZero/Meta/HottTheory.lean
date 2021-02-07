import Lean.Util.FoldConsts
import Lean.Elab.Command
import Lean.Environment
import Lean.Parser
import Lean.Meta
import Lean.Elab
import Std.Data

open Lean.Parser.Command
open Lean Std

/-
  Original implementation:
  https://github.com/gebner/hott3/blob/master/src/hott/init/meta/support.lean
-/

namespace GroundZero.Meta.HottTheory

partial def instArgsAux : LocalContext → Expr → MetaM (LocalContext × Expr)
| lctx, e => do
  let τ ← Meta.inferType e >>= Meta.whnf;
  if τ.isForall then do
    let varId ← mkFreshId
    let lctx' := lctx.mkLocalDecl varId τ.bindingName! τ.bindingDomain! τ.bindingInfo!

    withReader (fun ctx => { ctx with lctx := lctx' }) do
      mkFVar varId
      |> mkApp e
      |> instArgsAux lctx'
  else pure (lctx, e)

def instArgs (e : Expr) : MetaM (LocalContext × Expr) := do
  let ctx ← read; instArgsAux ctx.lctx e

def isProp : LocalContext → Expr → MetaM Bool :=
λ lctx e =>
  withReader (fun ctx => { ctx with lctx := lctx })
    (Expr.isProp <$> Meta.inferType e)

def isProof : LocalContext → Expr → MetaM Bool :=
λ lctx e => Meta.inferType e >>= isProp lctx

def mkNumMetaUnivs : Nat → MetaM (List Level)
| 0     => pure []
| n + 1 => do
  let id ← mkFreshId;
  let xs ← mkNumMetaUnivs n;
  return (mkLevelMVar id :: xs)

def const (c : Name) : MetaM Expr := do
  let env ← getEnv;
  match env.constants.find? c with
  | some info => do
    let num := info.lparams.length;
    let levels ← mkNumMetaUnivs num;
    return mkConst c levels
  | none => throwError! "unknown identifier “{c}”"

def uncurry {α : Type u} {β : Type v} {γ : Type w} : (α → β → γ) → (α × β → γ) :=
λ f (a, b) => f a b

def hasLargeElim (type : Name) : MetaM Bool := do
  let typeFormerIsProp ← const type >>= instArgs >>= uncurry isProp;
  let elimIsProp ← const (type ++ `rec) >>= instArgs >>= uncurry isProof;
  pure (typeFormerIsProp ∧ ¬elimIsProp)

def renderChain : List Name → String :=
String.intercalate " <- " ∘ List.map toString

def checkLargeElim (chain : List Name) (name : Name) : MetaM Unit := do
  let largeElim? ← hasLargeElim name;
  if largeElim? then throwError! "uses large eliminator: {renderChain chain}"

partial def checkDeclAux (chain : List Name) (name : Name) : MetaM Unit := do
  let env ← getEnv
  match env.find? name with
  | some (ConstantInfo.recInfo v) =>
    List.forM (checkLargeElim chain) v.all
  | some info =>
    match info.value? with
    | some expr => Array.forM (λ n => checkDeclAux (n :: chain) n)
                              expr.getUsedConstants
    | none => pure ()
  | none => throwError! "unknown identifier “{name}”"

def checkDecl : Name → MetaM Unit :=
checkDeclAux []

@[commandParser] def hott :=
parser! declModifiers false >> "hott " >> («def» <|> «theorem»)

@[commandElab «hott»] def elabHoTT : Elab.Command.CommandElab :=
λ stx => match stx.getArgs with
| #[mods, _, cmd] => do
  let declId   := cmd[1]
  let declName := declId[0].getId

  mkNode `Lean.Parser.Command.declaration #[mods, cmd]
  |> Elab.Command.elabDeclaration

  let ns ← getCurrNamespace
  checkDecl (ns ++ declName)
  |> Elab.Command.liftTermElabM (some declName)
| _ => throwError "unknown declaration"

end GroundZero.Meta.HottTheory

inductive Id' {α : Type u} : α → α → Type u
| refl (a : α) : Id' a a

-- throws an error
--hott def K {α : Type u} {a b : α} (p q : Id' a b) : Id' p q :=
--by { cases p; cases q; apply Id'.refl }

-- checks
hott def τ := 42