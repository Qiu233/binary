import Lean
import Binary.Basic

namespace Binary

open Lean
open Elab
open Deriving
open Meta hiding Context
open Term hiding Context
open Command hiding Context


/--
`bin_enum width assignment` tells how the attributed inductive type's constructors should be identified in bytes representation.
-/
syntax (name := Parser.Attr.bin_enum) "bin_enum " num ("[" num,* "]")? : attr

structure BinEnumInfo where
  width : Nat
  encoder : Term
  decoder : Term
  assignment? : Option (Array Nat)
deriving Inhabited, Repr

private def generateInfo (declName : Name) (widthStx : TSyntax `num) (assignmentStx : Option (Syntax.TSepArray `num ",")) : CoreM BinEnumInfo := do
  let width := widthStx.getNat
  if !(width matches 1 | 2 | 4 | 8) then
    throwErrorAt widthStx "only 1, 2, 4, 8 are allowed"
  let encoder : Term ← match width with
    | 1 => `($(mkIdent `Encode.encode) ($(mkIdent `α) := $(mkIdent `UInt8)))
    | 2 => `($(mkIdent `Encode.encode) ($(mkIdent `α) := $(mkIdent `UInt16)))
    | 4 => `($(mkIdent `Encode.encode) ($(mkIdent `α) := $(mkIdent `UInt32)))
    | 8 => `($(mkIdent `Encode.encode) ($(mkIdent `α) := $(mkIdent `UInt64)))
    | _ => unreachable!
  let decoder : Term ← match width with
    | 1 => `($(mkIdent `Decode.decode) ($(mkIdent `α) := $(mkIdent `UInt8)))
    | 2 => `($(mkIdent `Decode.decode) ($(mkIdent `α) := $(mkIdent `UInt16)))
    | 4 => `($(mkIdent `Decode.decode) ($(mkIdent `α) := $(mkIdent `UInt32)))
    | 8 => `($(mkIdent `Decode.decode) ($(mkIdent `α) := $(mkIdent `UInt64)))
    | _ => unreachable!
  let info ← getConstInfo declName
  let .inductInfo info := info | throwError m!"the type {declName} is not an inductive type"
  let numCtors := info.numCtors
  if numCtors ≤ 1 then
    throwError "redundant attribute on inductive type with no more than one constructor"
  let assignment? ← assignmentStx.mapM fun (x : Syntax.TSepArray `num ",") => do
    let elems := x.getElems
    if elems.size != numCtors then
      throwErrorAt (mkNullNode x) m!"number of assignment mismatched, expected {numCtors}, got {elems.size}"
    else
      let max := 2 ^ (width * 8) - 1
      let s ← elems.mapM fun (x : TSyntax `num) => do
        let v := x.getNat
        if v > max then
          throwErrorAt x "assignment {v} exceeds the maximum {max}"
        pure v
      if s.toList.eraseDups.length != s.size then
        throwErrorAt (mkNullNode x) "assignment must be injective"
      pure s
  let i : BinEnumInfo := { width := width, encoder := encoder, decoder := decoder, assignment? := assignment? }
  return i

initialize binEnumAttr : ParametricAttribute (BinEnumInfo) ←
  registerParametricAttribute {
    name := `bin_enum
    descr := "tell how to derive Encode/Decode instance for constructors, with the endianness respecting the inferred Encode/Decode instance of the representing unsigned integral type"
    getParam := fun declName stx => do
      let `(attr| bin_enum $widthStx:num $[[$assignmentStx,*]]?) := stx | throwUnsupportedSyntax
      let info ← generateInfo declName widthStx assignmentStx
      return info
  }

---

def mkEncodeHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader ``Encode 1 indVal

def aggregateStructFields (header : Header) (indName : Name) : TermElabM Term := do
  let fields := getStructureFieldsFlattened (← getEnv) indName (includeSubobjectFields := false)
  let fields ← fields.mapM fun field => do
    let target := mkIdent header.targetNames[0]!
    `(Encode.encode ($target).$(mkIdent field))
  `(ByteArray.join <| #[$fields,*])

open Parser.Term in
def mkEncodeBodyForInduct (ctx : Context) (header : Header) (indName : Name) (beInfo : BinEnumInfo) : TermElabM Term := do
  let indVal ← getConstInfoInduct indName
  let encodeFuncId := mkIdent ctx.auxFunNames[0]!
  let mkEncode (id : Ident) (type : Expr) : TermElabM Term := do
        if type.isAppOf indVal.name then `($encodeFuncId:ident $id:ident)
        else ``(Encode.encode $id:ident)
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts indVal beInfo.assignment? fun ctor args repr => do
    let tag ← `($beInfo.encoder $(quote repr))
    let ts ← args.mapM fun (id, type) => mkEncode id type
    `(ByteArray.join <| #[$tag, $ts,*])
  `(match $[$discrs],* with $alts:matchAlt*)
where
  mkAlts
    (indVal : InductiveVal) (assignment? : Option (Array Nat))
    (rhs : ConstructorVal → Array (Ident × Expr) → Nat → TermElabM Term) : TermElabM (Array (TSyntax ``matchAlt)) := do
      let mut alts := #[]
      let mut idx := 0
      let assignment := assignment?.getD (dflt := Array.range indVal.numCtors) -- the default
      for ctorName in indVal.ctors do
        let ctorInfo ← getConstInfoCtor ctorName
        let alt ← forallTelescopeReducing ctorInfo.type fun xs _ => do
          let mut patterns := #[]
          -- add `_` pattern for indices
          for _ in [:indVal.numIndices] do
            patterns := patterns.push (← `(_))
          let mut ctorArgs := #[]
          -- add `_` for inductive parameters, they are inaccessible
          for _ in [:indVal.numParams] do
            ctorArgs := ctorArgs.push (← `(_))
          -- bound constructor arguments and their types
          let mut binders := #[]
          let mut userNames := #[]
          for i in [:ctorInfo.numFields] do
            let x := xs[indVal.numParams + i]!
            let localDecl ← x.fvarId!.getDecl
            if !localDecl.userName.hasMacroScopes then
              userNames := userNames.push localDecl.userName
            let a := mkIdent (← mkFreshUserName `a)
            binders := binders.push (a, localDecl.type)
            ctorArgs := ctorArgs.push a
          patterns := patterns.push (← `(@$(mkIdent ctorInfo.name):ident $ctorArgs:term*))
          let rhs ← rhs ctorInfo binders assignment[idx]!
          `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
        alts := alts.push alt
        idx := idx + 1
      return alts

def mkEncodeBody (ctx : Context) (header : Header) (e : Expr): TermElabM Term := do
  let indName := e.getAppFn.constName!
  if isStructure (← getEnv) indName then
    aggregateStructFields header indName
  else
    let env ← getEnv
    let beInfo? := binEnumAttr.getParam? env indName
    match beInfo? with
    | none => throwError "inductive type {indName} must be attributed with `bin_enum` to automatically derive Encode"
    | some beInfo => mkEncodeBodyForInduct ctx header indName beInfo

def mkEncodeAuxFunction (ctx : Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let header     ←  mkEncodeHeader ctx.typeInfos[i]!
  let binders    := header.binders
  Term.elabBinders binders fun _ => do
  let type       ← Term.elabTerm header.targetType none
  let mut body   ← mkEncodeBody ctx header type
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx ``Encode header.argNames
    body ← mkLet letDecls body
    `(private partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : ByteArray := $body:term)
  else
    `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : ByteArray := $body:term)

def mkEncodeMutualBlock (ctx : Context) : TermElabM Command := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkEncodeAuxFunction ctx i)
  `(mutual
     $auxDefs:command*
    end)

private def mkEncodeInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext "encode" declName
  let cmds := #[← mkEncodeMutualBlock ctx] ++ (← mkInstanceCmds ctx ``Encode #[declName])
  trace[Binary.Deriving.encode] "\n{cmds}"
  return cmds

def mkEncodeInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    for declName in declNames do
      let cmds ← liftTermElabM <| mkEncodeInstance declName
      cmds.forM elabCommand
    return true
  else
    return false

----

def mkDecodeHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader ``Decode 0 indVal

def decodeStructFields (indName : Name) : TermElabM Term := do
  let fields := getStructureFieldsFlattened (← getEnv) indName (includeSubobjectFields := false)
  let fields ← fields.mapM fun field => do
    let var := mkIdent field
    let init ← `(Parser.Term.doSeqItem| let $var:ident ← Decode.decode)
    let field ← `(Parser.Term.structInstField| $(mkIdent field):ident := $var)
    pure (init, field)
  let (inits, fields) := fields.unzip
  let inst ← `(Parser.Term.structInst| {$fields,*})
  let construct ← `(Parser.Term.doSeqItem| return $inst:structInst)
  let program ← `(do $inits* $construct)
  return program

open Parser.Term in
def mkDecodeBodyForInduct (ctx : Context) (indName : Name) (beInfo : BinEnumInfo) : TermElabM Term := do
  let indVal ← getConstInfoInduct indName
  let alts ← mkAlts indVal
  let auxTerm ← alts.foldrM (fun xs x => `(Alternative.orElse $xs (fun _ => $x))) (← `(Getter.error ("unrecognized tag value encountered when trying to decode a constructor of type " ++ $(quote (indName.toString)))))
  `($auxTerm)
where
  mkAlts (indVal : InductiveVal) : TermElabM (Array Term) := do
  let assignment := beInfo.assignment?.getD (dflt := Array.range indVal.numCtors) -- the default
  let mut alts := #[]
  let mut ctorIdx := 0
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let alt ← do forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut binders   := #[]
        let mut userNames := #[]
        for i in [:ctorInfo.numFields] do
          let x := xs[indVal.numParams + i]!
          let localDecl ← x.fvarId!.getDecl
          if !localDecl.userName.hasMacroScopes then
            userNames := userNames.push localDecl.userName
          let a := mkIdent (← mkFreshUserName `a)
          binders := binders.push (a, localDecl.type)
        let decodeFuncId := mkIdent ctx.auxFunNames[0]!
        let mkDecode (type : Expr) : TermElabM (TSyntax ``doExpr) :=
          if type.isAppOf indVal.name then `(Lean.Parser.Term.doExpr| $decodeFuncId:ident)
          else `(Lean.Parser.Term.doExpr| Decode.decode)
        let identNames := binders.map Prod.fst
        let decodes ← binders.mapM fun (_, type) => mkDecode type
        let repr := assignment[ctorIdx]!
        let stx ←
          `(do
              if (← $(beInfo.decoder)) != $(quote repr) then
                Getter.error ""
              else
                $[let $identNames:ident ← $decodes:doExpr]*
                return $(mkIdent ctorName):ident $identNames*)
        pure (stx, ctorInfo.numFields)
    alts := alts.push alt
    ctorIdx := ctorIdx + 1
  return alts.unzip.fst

def mkDecodeBody (ctx : Context) (e : Expr) : TermElabM Term := do
  let indName := e.getAppFn.constName!
  if isStructure (← getEnv) indName then
    decodeStructFields indName
  else
    let env ← getEnv
    let beInfo? := binEnumAttr.getParam? env indName
    match beInfo? with
    | none => throwError "inductive type {indName} must be attributed with `bin_enum` to automatically derive Decode"
    | some beInfo => mkDecodeBodyForInduct ctx indName beInfo

def mkDecodeAuxFunction (ctx : Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let header     ←  mkDecodeHeader ctx.typeInfos[i]!
  let binders    := header.binders
  Term.elabBinders binders fun _ => do
  let type       ← Term.elabTerm header.targetType none
  let mut body   ← mkDecodeBody ctx type
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx ``Decode header.argNames
    body ← mkLet letDecls body
    `(private partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Getter $(header.targetType) := $body:term)
  else
    `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Getter $(header.targetType) := $body:term)

def mkDecodeMutualBlock (ctx : Context) : TermElabM Command := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkDecodeAuxFunction ctx i)
  `(mutual
     $auxDefs:command*
    end)

private def mkDecodeInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext "decode" declName
  let cmds := #[← mkDecodeMutualBlock ctx] ++ (← mkInstanceCmds ctx ``Decode #[declName])
  trace[Binary.Deriving.decode] "\n{cmds}"
  return cmds

def mkDecodeInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    for declName in declNames do
      let cmds ← liftTermElabM <| mkDecodeInstance declName
      cmds.forM elabCommand
    return true
  else
    return false

initialize
  registerDerivingHandler ``Encode mkEncodeInstanceHandler
  registerDerivingHandler ``Decode mkDecodeInstanceHandler

  registerTraceClass `Binary.Deriving.encode
  registerTraceClass `Binary.Deriving.decode
