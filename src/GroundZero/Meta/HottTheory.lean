import Lean.Util.FoldConsts
import Lean.Elab.Command
import Lean.Parser
import Lean.Meta
import Lean.Elab
import Std.Data

open Lean.Parser.Command
open Lean Std

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

def checkLargeElim (chain : List Name) (name : Name) : MetaM Unit := do
  let largeElim? ← hasLargeElim name;
  if largeElim? then
    let decls :=
      List.map toString chain
      |> String.intercalate " <- "
    throwError! "uses large eliminator: {decls}"

partial def checkDeclAux (chain : List Name) (name : Name) : MetaM Unit := do
  let env ← getEnv;
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

@[commandParser] def hott := parser! declModifiers false >> "hott " >> «def»
@[commandElab «hott»] def elabHoTT : Elab.Command.CommandElab :=
λ stx => do
  let mods := stx[0]
  let cmd  := stx[2]
  let ⟨shortDeclName, declName, levelNames⟩ ←
    Elab.Command.liftTermElabM none (do
      let modifiers ← Elab.elabModifiers mods
      Elab.expandDeclId (← getCurrNamespace) (← Elab.Term.getLevelNames)
                        (cmd.getArg 1) modifiers)

  Elab.Command.elabDeclaration
    (mkNode `Lean.Parser.Command.def #[mods, cmd])
  Elab.Command.liftTermElabM (some declName) (checkDecl declName)

end GroundZero.Meta.HottTheory

-- check
hott def τ := 42

inductive Id' {α : Type u} : α → α → Type u
| refl (a : α) : Id' a a

-- throws an error
--hott def K {α : Type u} {a b : α} (p q : Id' a b) : Id' p q :=
--by { cases p; cases q; apply Id'.refl }