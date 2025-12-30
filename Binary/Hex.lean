module

public meta import Lean

meta section

namespace Hex

open Lean Elab Parser Term

@[inline]
private def isHexChar : Char → Bool := fun c => c.isDigit || ('A' ≤ c && c ≤ 'F') || ('a' ≤ c && c ≤ 'f') || c.isWhitespace

abbrev hexStrLitKind : SyntaxNodeKind := `hexStrLitKind
abbrev hexStrKind : SyntaxNodeKind := `hexStrKind

partial def hexStrFn : ParserFn := fun c s =>
  let stackSize := s.stackSize
  let rec parse (startPos : String.Pos.Raw) (c : ParserContext) (s : ParserState) : ParserState :=
    let i := s.pos
    if c.atEnd i then
      let s := s.mkError "unterminated string literal"
      s.mkNode hexStrKind stackSize
    else
      let curr := c.get i
      let s    := s.setPos (c.next i)
      if curr == '\"' then
        let s := mkNodeToken hexStrLitKind startPos true c s
        s.mkNode hexStrKind stackSize
      else if curr == '\\' then
        s.mkUnexpectedError "unexpected '\\', escape is not allowed here"
      else if isHexChar curr then
        parse startPos c s
      else
        s.mkError "hex character"
  let startPos := s.pos
  if c.atEnd startPos then
    s.mkEOIError
  else
    let curr  := c.get s.pos;
    if curr != '\"' then
      s.mkError "hex string"
    else
      let s := s.next c startPos
      parse startPos c s

@[inline] public def hexStrNoAntiquot : Parser := {
  fn   := hexStrFn,
  info := mkAtomicInfo "hexStr"
}

public def hexStr : Parser :=
  withAntiquot (mkAntiquot "hexStr" hexStrKind) $ hexStrNoAntiquot

open PrettyPrinter Formatter Syntax.MonadTraverser in
@[combinator_formatter hexStr]
public def hexStr.formatter (p : Formatter) : Formatter := do
  visitArgs $ (← getCur).getArgs.reverse.forM fun chunk =>
    match chunk.isLit? hexStrLitKind with
    | some str => push str *> goLeft
    | none     => p

open PrettyPrinter Parenthesizer Syntax.MonadTraverser in
@[combinator_parenthesizer hexStr]
public def hexStr.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  visitArgs $ (← getCur).getArgs.reverse.forM fun chunk =>
    if chunk.isOfKind hexStrLitKind then
      goLeft
    else
      p

def convert_hex (pairs : List (Char × Char)) : Array UInt8 := Id.run do
  let mut r : Array UInt8 := Array.emptyWithCapacity pairs.length
  for (a, b) in pairs do
    let v := getC a * 16 + getC b
    r := r.push v
  return r
where getC (c : Char) : UInt8 :=
  if c.isDigit then (c.val - '0'.val).toUInt8
  else if ('A' ≤ c && c ≤ 'F') then (c.val - 'A'.val + 10).toUInt8
  else if ('a' ≤ c && c ≤ 'f') then (c.val - 'a'.val + 10).toUInt8
  else unreachable!

syntax (name := hexStrStx) "hex!" hexStr : term

@[term_elab hexStrStx]
public meta def elabHexStrStx : TermElab := fun hex _ => do
  let str := hex[1][0][0]
  let str := str.getAtomVal.trim
  assert! str.front == '\"'
  assert! str.back == '\"'
  let content := str.toList.extract 1 (str.length - 1)
  let content := content.filter fun x => !x.isWhitespace
  if content.length % 2 != 0 then
    throwError "hex characters must be of even length, consider adding padding zeros"
  let paired := List.range (content.length / 2) |>.map fun i => (content[i * 2]!, content[i * 2 + 1]!)
  let data := convert_hex paired
  let ts ← data.mapM fun x => `($(quote x.toNat):num)
  let arr ← `(ByteArray.mk #[ $ts,* ])
  withMacroExpansion hex arr do
    elabTerm arr (Expr.const ``ByteArray [])
