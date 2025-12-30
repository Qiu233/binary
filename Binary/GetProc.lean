module

public import Lean
import Binary.Basic
import Binary.Get
public import Binary.Hex

public meta section

namespace Binary

open Lean Meta Elab Parser Term

declare_syntax_cat get_proc (behavior := symbol)

syntax get_proc_ascription_types :=
  &"UInt8" <|>
  &"UInt16" <|>
  &"UInt32" <|>
  &"UInt64" <|>
  &"Int8" <|>
  &"Int16" <|>
  &"Int32" <|>
  &"Int64" <|>
  &"Float32" <|>
  &"Float"

syntax get_proc_ascription_bytes := &"bytes" term
syntax get_proc_ascription := " : " (get_proc_ascription_bytes <|> (get_proc_ascription_types (" < " <|> " > ")?) <|> term)

syntax Parser.ident get_proc_ascription : get_proc
syntax Parser.ident " ← " term : get_proc
syntax &"hex " Hex.hexStr : get_proc
syntax &"yield " term : get_proc
syntax num get_proc_ascription : get_proc

syntax (name := getProcStx) "get!" "{" get_proc,*,? "}" : term

private def getAscriptionNumeralType (le? : Option Bool) : TSyntax ``get_proc_ascription_types → TermElabM (TSyntax `term) := fun stx => do
  match stx with
  | `(get_proc_ascription_types| UInt8) => ``(getThe UInt8)
  | `(get_proc_ascription_types| Int8) => ``(getThe Int8)
  | `(get_proc_ascription_types| $x) =>
    let ty := x.raw[0][0].getAtomVal
    let t := mkIdentFrom x (Name.mkStr1 ty)
    let l := mkIdentFrom x (Name.str `Binary.Primitive.LE s!"instDecode{ty}")
    let b := mkIdentFrom x (Name.str `Binary.Primitive.BE s!"instDecode{ty}")
    match le? with
    | .none => ``(getThe $t)
    | .some true => ``(@get _ $l)
    | .some false => ``(@get _ $b)

private def getAscription : TSyntax ``get_proc_ascription → TermElabM (TSyntax `term) := fun stx => do
  match stx with
  | `(get_proc_ascription| : $bs:get_proc_ascription_bytes) =>
    match bs with
    | `(get_proc_ascription_bytes| bytes $len) =>
      ``(get_bytes $len)
    | _ => throwUnsupportedSyntax
  | `(get_proc_ascription| : $type:get_proc_ascription_types $[$tk?]?) =>
    let le? := tk?.map fun x => x.raw.getAtomVal.trim == " < "
    getAscriptionNumeralType le? type
  | `(get_proc_ascription| : $type:term) =>
    let type' ← elabType type
    let instType := Expr.app (Expr.const ``Decode []) type'
    let .some _ ← synthInstance? instType | throwErrorAt type "failed to synthesize instance {instType}"
    ``(getThe $type)
  | _ => throwUnsupportedSyntax

private def getFileLoc (pos : String.Pos.Raw) : MetaM String := do
  let map ← getFileMap
  let pos := map.toPosition pos
  let fileName ← getFileName
  return s!"{fileName}:{pos.line}:{pos.column}: "

@[term_elab getProcStx]
public def elabGetProcStx : TermElab := fun stx type? => do
  let `(getProcStx| get! { $body,* }) := stx | throwUnsupportedSyntax
  let es := body.getElems
  let mut ns := #[]
  let mut ts := #[]
  for e in es, i in List.range es.size do
    match e with
    | `(get_proc| $x:ident $ascr) =>
      let a ← getAscription ascr
      let s ← `(doSeqItem| let $x ← $a:term)
      ns := ns.push x
      ts := ts.push s
    | `(get_proc| $x:ident ← $action) =>
      let s ← `(doSeqItem| let $x ← $action:term)
      ns := ns.push x
      ts := ts.push s
    | `(get_proc| hex $hex:hexStr) =>
      let vs ← Hex.elabHexStr hex.raw[0][0].getAtomVal
      if vs.isEmpty then
        continue
      let pos? ← liftM <| hex.raw.getPos?.mapM getFileLoc
      let posStr := quote <| pos?.getD ""
      let f := fun (v : UInt8) => `(doSeqItem| let $(quote v.toNat):num ← getThe UInt8 | throw (DecodeError.userError s!"{$posStr:str}hex literal assertion failed"))
      let rs ← vs.mapM f
      ts := ts.append rs
    | `(get_proc| $n:num $ascr) =>
      let a ← getAscription ascr
      let pos? ← liftM <| n.raw.getPos?.mapM getFileLoc
      let posStr := quote <| pos?.getD ""
      let s ← `(doSeqItem| let $n:num ← $a:term | throw (DecodeError.userError s!"{$posStr:str}numeral literal assertion failed"))
      ts := ts.push s
    | `(get_proc| yield $r) =>
      if i != es.size - 1 then
        throwErrorAt e "yield must be the last element"
      let s ← `(doSeqItem| return $r)
      ts := ts.push s
    | _ => throwUnsupportedSyntax
  let s ← `(do
    $ts*
    )
  withMacroExpansion stx s do
    elabTerm s type?

end Binary

end
