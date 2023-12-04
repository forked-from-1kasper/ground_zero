import Lean.Elab

open Lean.Parser.Command
open Lean Std

universe u v w

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

initialize nothott   : TagAttribute ← registerTagAttribute `nothott "Marks a defintion as unsafe for HoTT"
initialize hottAxiom : TagAttribute ← registerTagAttribute `hottAxiom "(Potentially) unsafely marks a definition as safe for HoTT"

def unsafeDecls :=
[`Lean.ofReduceBool, `Lean.ofReduceNat, `Quot.lift, `Quot.ind, `Quot.rec, `Classical.choice]

def checked? (decl : Name) : MetaM Bool := do
  let env         ← getEnv
  let checked    := (hottDecls.getState env).contains decl
  let markedSafe := hottAxiom.hasTag env decl

  pure (checked ∨ markedSafe)

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
    | some (ConstantInfo.opaqueInfo v) =>
      throwErrorAt tag "uses unsafe opaque: {renderChain chain}"
    | some info =>
      match info.value? with
      | some expr => Array.forM (λ n => checkDeclAux (n :: chain) tag n)
                                expr.getUsedConstants
      | none => return ()
    | none => throwError "unknown identifier “{name}”"
  else return ()

def checkDecl := checkDeclAux []

def declTok : Parser.Parser :=
    "def "         <|> "definition " <|> "theorem "   <|> "lemma "
<|> "proposition " <|> "corollary "  <|> "principle " <|> "claim "
<|> "statement "   <|> "paradox "    <|> "remark "    <|> "exercise "

def declDef := leading_parser
  Parser.ppIndent optDeclSig >> declVal >> optDefDeriving >> terminationSuffix

def decl        := leading_parser declTok >> declId >> declDef
def declExample := leading_parser ("example " <|> "counterexample ") >> declDef

@[command_parser] def hott :=
leading_parser declModifiers false >> "hott " >> (decl <|> declExample)

open Elab.Command

def defAndCheck (tag declMods declId declDef : Syntax) : CommandElabM Unit := do {
  let ns ← getCurrNamespace;
  let declName := ns ++ declId[0].getId;

  declDef.setKind `Lean.Parser.Command.«def»
  |> (Syntax.setArgs · (Array.append #[mkAtom "def ", declId] declDef.getArgs))
  |> (mkNode `Lean.Parser.Command.declaration #[declMods, ·])
  |> elabDeclaration;

  if (← getEnv).contains declName then do {
    liftTermElabM (checkDecl tag declName);
    modifyEnv (λ env => hottDecls.addEntry env declName)
  }
}

@[command_elab «hott»] def elabHoTT : CommandElab :=
λ stx => do {
  let #[mods, _, cmd] := stx.getArgs | throwError "invalid declaration";

  match cmd.getArgs with
  | #[_, declId, declDef] => defAndCheck declId mods declId declDef
  | #[tok, declDef]       => do {
    withoutModifyingEnv do {
      #[mkIdentFrom tok `_example, mkNullNode]
      |> mkNode ``Parser.Command.declId
      |> (defAndCheck tok mods · declDef)
    }
  }
  | _ => throwError "invalid definition"
}

end GroundZero.Meta.HottTheory
