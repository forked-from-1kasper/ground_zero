import Lean.Elab

open Lean.Parser
open Lean.Parser.Command
open Lean Lean.Elab Lean.Elab.Command

universe u v w

macro "run_cmd " σs:doSeq : command => `(#eval show CommandElabM Unit from do $σs)

/-
  Original implementation:
  https://github.com/gebner/hott3/blob/master/src/hott/init/meta/support.lean
-/

namespace GroundZero.Meta.HottTheory

def typeOf (c : Name) : MetaM Expr := do {
  let some info := (← getEnv).constants.find? c
    | throwError "unknown identifier “{c}”";
  return info.type
}

def isProof (e : Expr) : MetaM Bool :=
Expr.isProp <$> Meta.inferType e

def hasLargeElim (type : Name) : MetaM Bool := do {
  let typeFormerIsProp ← Meta.forallTelescopeReducing (← typeOf type) (λ xs e => return Expr.isProp e);
  let elimIsProp ← Meta.forallTelescopeReducing (← typeOf (type ++ `rec)) (λ xs e => isProof e);
  return (typeFormerIsProp ∧ ¬elimIsProp)
}

section
  @[inline] def guardb {f : Type → Type u} [Alternative f] (b : Bool) : f Unit :=
  if b then pure () else failure

  run_cmd { let ns := [``Eq, ``HEq, ``False]; liftTermElabM <|
            ns.forM (λ n => hasLargeElim n >>= guardb) }
end

def renderChain : List Name → String :=
String.intercalate " <- " ∘ List.map toString

def checkLargeElim (tag : Syntax) (chain : List Name) (name : Name) : MetaM Unit :=
do if (← hasLargeElim name) then throwErrorAt tag "uses large eliminator: {renderChain chain}"

initialize hottDecls : SimplePersistentEnvExtension Name NameSet ←
registerSimplePersistentEnvExtension {
  name          := `hottDecls
  addEntryFn    := NameSet.insert
  addImportedFn := mkStateFromImportedEntries NameSet.insert {}
}

initialize nothott   : TagAttribute ← registerTagAttribute `nothott "Marks a defintion as unsafe for HoTT"
initialize hottAxiom : TagAttribute ← registerTagAttribute `hottAxiom "(Potentially) unsafely marks a definition as safe for HoTT"

def unsafeDecls :=
[`Lean.ofReduceBool, `Lean.ofReduceNat, `Quot.lift, `Quot.ind, `Quot.rec, `Classical.choice]

def checked? (decl : Name) : MetaM Bool := do {
  let env         ← getEnv;
  let checked    := (hottDecls.getState env).contains decl;
  let markedSafe := hottAxiom.hasTag env decl;

  pure (checked ∨ markedSafe)
}

def checkNotNotHoTT (tag : Syntax) (env : Environment) (decl : Name) : MetaM Unit :=
do if nothott.hasTag env decl ∨ unsafeDecls.contains decl then
  throwErrorAt tag "marked as [nothott]: {decl}"

partial def checkDeclAux (chain : List Name) (tag : Syntax) (name : Name) : MetaM Unit := do {
  let env ← getEnv;

  if ¬(← checked? name) then {
    checkNotNotHoTT tag env name;
    match env.find? name with
    | some (ConstantInfo.recInfo v) =>
      List.forM v.all (checkLargeElim tag chain)
    | some (ConstantInfo.opaqueInfo v) =>
      throwErrorAt tag "uses unsafe opaque: {renderChain chain}"
    | some info =>
      match info.value? with
      | none      => return ()
      | some expr => Array.forM (λ n => checkDeclAux (n :: chain) tag n)
                                expr.getUsedConstants
    | none => throwError "unknown identifier “{name}”"
  } else return ()
}

def checkDecl (tag : Syntax) (name : Name) := checkDeclAux [name] tag name

def defTok := leading_parser
    "def "         <|> "definition " <|> "theorem "   <|> "lemma "
<|> "proposition " <|> "corollary "  <|> "principle " <|> "claim "
<|> "statement "   <|> "paradox "    <|> "remark "    <|> "exercise "

/--
  `reducible` and `inline` attributes are automatically added to abbreviations.
-/
def abbrevTok := leading_parser "abbrev " <|> "abbreviation "

def exampleTok := leading_parser "example " <|> "counterexample "

def declDef     := leading_parser Parser.ppIndent optDeclSig >> declVal >> optDefDeriving >> terminationSuffix
def decl        := leading_parser (defTok <|> abbrevTok) >> declId >> declDef
def declExample := leading_parser exampleTok >> declDef
def declCheck   := leading_parser "check " >> Parser.many1 Parser.ident

/--
  Adds declaration and throws an error whenever it uses singleton elimination and/or
  any other principle (i.e. global choice) inconsistent with HoTT.
-/
def hottPrefix := leading_parser "hott "

@[command_parser] def hott :=
leading_parser declModifiers false >> hottPrefix >> (decl <|> declExample <|> declCheck)

def checkAndMark (tag : Syntax) (name : Name) : CommandElabM Unit := do {
  liftTermElabM (checkDecl tag name);
  modifyEnv (λ env => hottDecls.addEntry env name)
}

def defAndCheck (tag declMods declId declDef : Syntax) : CommandElabM Name := do {
  let ns ← getCurrNamespace;
  let declName := ns ++ declId[0].getId;

  declDef.setKind `Lean.Parser.Command.«def»
  |> (Syntax.setArgs · (Array.append #[mkAtom "def ", declId] declDef.getArgs))
  |> (mkNode `Lean.Parser.Command.declaration #[declMods, ·])
  |> elabDeclaration;

  if (← getEnv).contains declName then checkAndMark tag declName

  return declName
}

def abbrevAttrs : Array Attribute :=
#[{name := `inline}, {name := `reducible}]

@[command_elab «hott»] def elabHoTT : CommandElab :=
λ stx => do {
  let #[mods, _, cmd] := stx.getArgs | throwError "incomplete declaration";

  if cmd.isOfKind ``decl then do {
    let #[tok, declId, declDef] := cmd.getArgs | throwError "invalid declaration";
    let declName ← defAndCheck declId mods declId declDef;
    if tok.isOfKind ``abbrevTok then liftTermElabM (Term.applyAttributes declName abbrevAttrs)
  }

  if cmd.isOfKind ``declExample then withoutModifyingEnv do {
    let #[tok, declDef] := cmd.getArgs | throwError "invalid example";
    let declId := mkNode ``declId #[mkIdentFrom tok `_example, mkNullNode];
    discard (defAndCheck tok mods declId declDef)
  }

  if cmd.isOfKind ``declCheck then do {
    let #[_, decls] := cmd.getArgs | throwError "invalid “check” statement";
    decls.getArgs.forM (λ stx => resolveGlobalConstNoOverload stx >>= checkAndMark stx)
  }
}

end GroundZero.Meta.HottTheory
