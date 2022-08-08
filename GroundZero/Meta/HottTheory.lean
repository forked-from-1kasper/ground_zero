import Lean.Elab

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
  let id ← mkFreshLMVarId;
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

def uncurry {A : Type u} {B : Type v} {C : Type w} : (A → B → C) → (A × B → C) :=
λ f (a, b) => f a b

def hasLargeElim (type : Name) : MetaM Bool := do
  let typeFormerIsProp ← const type >>= instArgs >>= uncurry isProp;
  let elimIsProp ← const (type ++ `rec) >>= instArgs >>= uncurry isProof;
  return (typeFormerIsProp ∧ ¬elimIsProp)

def renderChain : List Name → String :=
String.intercalate " <- " ∘ List.map toString

def checkLargeElim (tag : Syntax) (chain : List Name) (name : Name) : MetaM Unit := do
  let largeElim? ← hasLargeElim name;
  if largeElim? then throwErrorAt tag "uses large eliminator: {renderChain chain}"

initialize hottDecls : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    name          := `hottDecls
    addEntryFn    := NameSet.insert
    addImportedFn := fun es => mkStateFromImportedEntries NameSet.insert {} es
  }

initialize nothott : TagAttribute ← registerTagAttribute `nothott "Marks a defintion as unsafe for HoTT"
initialize hottAxiom : TagAttribute ← registerTagAttribute `hottAxiom "Unsafely marks a definition as safe for HoTT"

def unsafeDecls :=
[`Quot.lift, `Quot.ind, `Quot.rec, `Classical.choice]

def checked? (decl : Name) : MetaM Bool := do
  let env ← getEnv
  let checked := (hottDecls.getState env).contains decl
  let isSafe := hottAxiom.hasTag env decl

  pure (checked ∨ isSafe)

def checkNotNotHoTT (tag : Syntax) (env : Environment) (decl : Name) : MetaM Unit := do
  if nothott.hasTag env decl ∨ unsafeDecls.contains decl then
    throwErrorAt tag "marked as [nothott]: {decl}"
  else return ()

partial def checkDeclAux (chain : List Name) (tag : Syntax) (name : Name) : MetaM Unit := do
  let env ← getEnv

  if ¬(← checked? name) then
    checkNotNotHoTT tag env name
    match env.find? name with
    | some (ConstantInfo.recInfo v) =>
      List.forM v.all (checkLargeElim tag chain)
    | some info =>
      match info.value? with
      | some expr => Array.forM (λ n => checkDeclAux (n :: chain) tag n)
                                expr.getUsedConstants
      | none => return ()
    | none => throwError "unknown identifier “{name}”"
  else return ()

def checkDecl := checkDeclAux []

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

  if (← getEnv).contains name then do {
    Elab.Command.liftTermElabM (checkDecl declId name);
    modifyEnv (λ env => hottDecls.addEntry env name)
  }
| _ => throwError "invalid declaration"

end GroundZero.Meta.HottTheory