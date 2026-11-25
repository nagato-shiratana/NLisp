namespace NLisp.Lexical

def whitespace (c : Char) : Bool :=
  let n := c.toNat
  (0x9 ≤ n && n ≤ 0xd) || n == 0x20 || n == 0x85 || n == 0xa0 || n == 0x1680 ||
  (0x2000 ≤ n && n ≤ 0x200a) || n == 0x2028 || n == 0x2029 || n == 0x202f ||
  n == 0x205f || n == 0x3000

def lineEnding (c : Char) : Bool :=
  c == '\r' || c == '\n' || c.toNat == 0x85 || c.toNat == 0x2028 || c.toNat == 0x2029

def delimiter (c : Char) : Bool :=
  c == '(' || c == ')' || c == ';' || c == '"' || whitespace c

def digits (characters : List Char) : Bool :=
  !characters.isEmpty && characters.all (fun c => '0' ≤ c && c ≤ '9')

def asciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def unsignedCharacters (characters : List Char) : List Char :=
  match characters with
  | '-' :: tail => tail
  | other => other

def integerLiteral (characters : List Char) : Bool :=
  match unsignedCharacters characters with
  | ['0'] => true
  | first :: tail => ('1' ≤ first && first ≤ '9') && tail.all asciiDigit
  | [] => false

def exponentLiteral (characters : List Char) : Bool :=
  match characters with
  | [] => true
  | 'e' :: tail | 'E' :: tail =>
      match tail with
      | '+' :: rest | '-' :: rest => digits rest
      | rest => digits rest
  | _ => false

def floatLiteral (characters : List Char) : Bool :=
  let unsigned := unsignedCharacters characters
  match unsigned with
  | first :: _ =>
      if !asciiDigit first then false else
      match unsigned.dropWhile asciiDigit with
      | '.' :: fraction =>
          match fraction with
          | digit :: _ => asciiDigit digit && exponentLiteral (fraction.dropWhile asciiDigit)
          | [] => false
      | _ => false
  | [] => false

private def signedDecimal (text : String) : Option Int := do
  let characters := text.toList
  let (negative, digits) := match characters with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | rest => (false, rest)
  if !digits.all asciiDigit || digits.isEmpty then none else
  let magnitude ← String.mk digits |>.toNat?
  pure (if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude)

/-- Parse the finite decimal syntax accepted for Float atoms. The significand
is accumulated as an integer and its decimal scale is converted once. -/
def parseFloatLiteral (text : String) : Option Float := do
  let (negative, unsigned) := if text.startsWith "-" then
    (true, String.mk (text.toList.drop 1)) else (false, text)
  let lowerParts := unsigned.splitOn "e"
  let (mantissa, exponentText) := if lowerParts.length == 1 then
      let upperParts := unsigned.splitOn "E"
      if upperParts.length == 1 then (unsigned, none) else
        match upperParts with | [m, e] => (m, some e) | _ => ("", some "")
    else match lowerParts with | [m, e] => (m, some e) | _ => ("", some "")
  let [whole, fractional] := mantissa.splitOn "." | none
  if whole.isEmpty || fractional.isEmpty ||
      !(whole.toList ++ fractional.toList).all asciiDigit then none else
  let significand ← String.mk (whole.toList ++ fractional.toList) |>.toNat?
  let explicitExponent ← match exponentText with
    | none => pure 0
    | some exponent => signedDecimal exponent
  let scale := explicitExponent - Int.ofNat fractional.length
  let significantDigits := (whole.toList ++ fractional.toList).dropWhile (· == '0')
  let signedZero := if negative then Float.neg (Float.ofScientific 0 false 0)
    else Float.ofScientific 0 false 0
  let signedInfinity := if negative then
      Float.neg (Float.ofScientific 1 false 0 / Float.ofScientific 0 false 0)
    else Float.ofScientific 1 false 0 / Float.ofScientific 0 false 0
  if significantDigits.isEmpty then pure signedZero else
  let decimalOrder := Int.ofNat (significantDigits.length - 1) + scale
  if decimalOrder > 400 then pure signedInfinity else
  if decimalOrder < -400 then pure signedZero else
  let value := Float.ofScientific significand (scale < 0) scale.natAbs
  pure (if negative then -value else value)

/-- Complete Float atom reader: successful conversion always carries the
same ASCII decimal grammar used by the source reader. -/
def readFloatLiteral (text : String) : Option Float :=
  if floatLiteral text.toList then parseFloatLiteral text else none

private def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def readHexScalar (digits : List Char) : Option Char := do
  if digits.isEmpty || digits.length > 6 then none else
  let value ← digits.foldlM (fun acc c => do pure (acc * 16 + (← hexDigit c))) 0
  if value > 0x10ffff || (0xd800 ≤ value && value ≤ 0xdfff) then none
  else some (Char.ofNat value)

private def readUnicodeEscape : List Char → Option (Char × List Char)
  | 'u' :: '{' :: rest => do
      let digits := rest.takeWhile (· != '}')
      let '}' :: tail := rest.drop digits.length | none
      let scalar ← readHexScalar digits
      pure (scalar, tail)
  | _ => none

private def decodeStringBody : Nat → List Char → Option (List Char)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, '\\' :: 'n' :: tail => (('\n' :: ·) <$> decodeStringBody fuel tail)
  | fuel + 1, '\\' :: 'r' :: tail => (('\r' :: ·) <$> decodeStringBody fuel tail)
  | fuel + 1, '\\' :: 't' :: tail => (('\t' :: ·) <$> decodeStringBody fuel tail)
  | fuel + 1, '\\' :: '"' :: tail => (( '"' :: ·) <$> decodeStringBody fuel tail)
  | fuel + 1, '\\' :: '\\' :: tail => (('\\' :: ·) <$> decodeStringBody fuel tail)
  | fuel + 1, '\\' :: rest => do
      let (scalar, tail) ← readUnicodeEscape rest
      pure (scalar :: (← decodeStringBody fuel tail))
  | _ + 1, '"' :: _ => none
  | fuel + 1, c :: tail => (c :: ·) <$> decodeStringBody fuel tail

/-- Decode the quoted atom spelling used by the C reader. Unicode escapes
are scalar checked, and the resulting Lean String can contain U+0000. -/
def readStringLiteral (text : String) : Option String := do
  let '"' :: rest := text.toList | none
  let body := rest.take (rest.length - 1)
  if rest.getLast? != some '"' then none else
  let decoded ← decodeStringBody text.toList.length body
  pure (String.mk decoded)

/-- Decode C's character literal spelling, including named whitespace and
braced Unicode scalar escapes. -/
def readCharacterLiteral (text : String) : Option Char := do
  let '#' :: '\\' :: body := text.toList | none
  if body == ['n','e','w','l','i','n','e'] then pure '\n' else
  if body == ['s','p','a','c','e'] then pure ' ' else
  if body == ['t','a','b'] then pure '\t' else
  match body with
  | 'u' :: '{' :: _ => do
      let (scalar, tail) ← readUnicodeEscape body
      if tail.isEmpty then pure scalar else none
  | [scalar] => pure scalar
  | _ => none

theorem readFloatLiteral_lexical {text : String} {value : Float}
    (read : readFloatLiteral text = some value) :
    floatLiteral text.toList = true := by
  unfold readFloatLiteral at read
  split at read
  · assumption
  · simp at read

def literal (name : String) : Bool :=
  name == "true" || name == "false" || name == "unit" ||
  name.startsWith "\"" || name.startsWith "#\\" ||
  integerLiteral name.toList || floatLiteral name.toList


def reserved : List String :=
  ["true", "false", "unit", "define", "defun", "defrec", "lambda", "if", "let", "begin",
   "forall", "type-app", "match", "define-macro", "syntax-rules/typed",
   "Boolean", "Integer", "Float", "String", "Character", "Unit", "List", "Option", "Function", "Syntax",
   "Nil", "Cons", "None", "Some"]

def identifier (name : String) : Bool :=
  !name.isEmpty && !reserved.contains name && !literal name && !name.toList.any delimiter

def distinctNames : List String → Bool
  | [] => true
  | head :: tail => !tail.contains head && distinctNames tail

end NLisp.Lexical
