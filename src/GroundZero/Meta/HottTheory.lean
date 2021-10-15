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
    let varId ← mkFreshFVarId
    let lctx' := lctx.mkLocalDecl varId τ.bindingName! τ.bindingDomain! τ.bindingInfo!

    withReader (λ ctx => { ctx with lctx := lctx' }) do
      mkFVar varId
      |> mkApp e
      |> instArgsAux lctx'
  else return (lctx, e)

def instArgs (e : Expr) : MetaM (LocalContext × Expr) := do
  let ctx ← read; instArgsAux ctx.lctx e

def isProp : LocalContext → Expr → MetaM Bool :=
λ lctx e =>
  withReader (λ ctx => { ctx with lctx := lctx })
    (Expr.isProp <$> Meta.inferType e)

def isProof : LocalContext → Expr → MetaM Bool :=
λ lctx e => Meta.inferType e >>= isProp lctx

def mkNumMetaUnivs : Nat → MetaM (List Level)
|   0   => return []
| n + 1 => do
  let id ← mkFreshMVarId;
  let xs ← mkNumMetaUnivs n;
  return (mkLevelMVar id :: xs)

def const (c : Name) : MetaM Expr := do
  let env ← getEnv;
  match env.constants.find? c with
  | some info => do
    let num := info.levelParams.length;
    let levels ← mkNumMetaUnivs num;
    return mkConst c levels
  | none => throwError "unknown identifier “{c}”"

def uncurry {α : Type u} {β : Type v} {γ : Type w} : (α → β → γ) → (α × β → γ) :=
λ f (a, b) => f a b

def hasLargeElim (type : Name) : MetaM Bool := do
  let typeFormerIsProp ← const type >>= instArgs >>= uncurry isProp;
  let elimIsProp ← const (type ++ `rec) >>= instArgs >>= uncurry isProof;
  return (typeFormerIsProp ∧ ¬elimIsProp)

def renderChain : List Name → String :=
String.intercalate " <- " ∘ List.map toString

def checkLargeElim (chain : List Name) (name : Name) : MetaM Unit := do
  let largeElim? ← hasLargeElim name;
  if largeElim? then throwError "uses large eliminator: {renderChain chain}"

initialize hottDecls : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    name          := `hottDecls
    addEntryFn    := NameSet.insert
    addImportedFn := fun es => mkStateFromImportedEntries NameSet.insert {} es
  }

initialize nothott : TagAttribute ← registerTagAttribute `nothott "Marks a defintion as unsafe for HoTT"
initialize hottAxiom : TagAttribute ← registerTagAttribute `hottAxiom "Unsafely marks a definition as safe for HoTT"

def checked? (decl : Name) : MetaM Bool := do
  let env ← getEnv
  let checked ← (← hottDecls.getState env).contains decl
  let isSafe ← hottAxiom.hasTag env decl

  pure (checked ∨ isSafe)

def checkNotNotHoTT (env : Environment) (decl : Name) : MetaM Unit := do
  if nothott.hasTag env decl then
    throwError "marked as [nothott]: {decl}"
  else return ()

partial def checkDeclAux (chain : List Name) (name : Name) : MetaM Unit := do
  let env ← getEnv

  if ¬(← checked? name) then
    checkNotNotHoTT env name
    match env.find? name with
    | some (ConstantInfo.recInfo v) =>
      List.forM v.all (checkLargeElim chain)
    | some info =>
      match info.value? with
      | some expr => Array.forM (λ n => checkDeclAux (n :: chain) n)
                                expr.getUsedConstants
      | none => return ()
    | none => throwError "unknown identifier “{name}”"
  else return ()

def checkDecl : Name → MetaM Unit :=
checkDeclAux []

@[commandParser] def hott :=
leading_parser declModifiers false >> "hott " >> («def» <|> «theorem»)

@[commandElab «hott»] def elabHoTT : Elab.Command.CommandElab :=
λ stx => match stx.getArgs with
| #[mods, _, cmd] => do
  let declId   := cmd[1]
  let declName := declId[0].getId

  let ns ← getCurrNamespace
  let name := ns ++ declName

  mkNode `Lean.Parser.Command.declaration #[mods, cmd]
  |> Elab.Command.elabDeclaration

  checkDecl name
  |> Elab.Command.liftTermElabM name

  modifyEnv λ env => hottDecls.addEntry env name
| _ => throwError "unknown declaration"

end GroundZero.Meta.HottTheory