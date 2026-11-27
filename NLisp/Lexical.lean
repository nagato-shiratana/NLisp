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

private def cFloatSignDigits : List Char → List Char
  | '+' :: tail | '-' :: tail => tail
  | tail => tail

private theorem cFloatSignDigits_eq_exponentDigits (tail : List Char) :
    digits (cFloatSignDigits tail) =
      (match tail with
      | '+' :: rest | '-' :: rest => digits rest
      | rest => digits rest) := by
  cases tail with
  | nil => rfl
  | cons head rest =>
      by_cases plus : head = '+'
      · subst head
        rfl
      · by_cases minus : head = '-'
        · subst head
          rfl
        · simp [cFloatSignDigits, plus, minus]

/- A direct functional model of C's `float_atom` cursor walk: scan the
integer digits, require a decimal point and fractional digit, optionally scan
an exponent marker/sign/digits, then require end of token. -/
def cFloatExponentSyntax (characters : List Char) : Bool :=
  match characters with
  | [] => true
  | 'e' :: tail | 'E' :: tail =>
      digits (cFloatSignDigits tail)
  | _ => false

def cFloatAtomSyntax (characters : List Char) : Bool :=
  let unsigned := unsignedCharacters characters
  match unsigned with
  | first :: _ =>
      if !asciiDigit first then false else
      match unsigned.dropWhile asciiDigit with
      | '.' :: fraction =>
          match fraction with
          | digit :: _ =>
              asciiDigit digit && cFloatExponentSyntax (fraction.dropWhile asciiDigit)
          | [] => false
      | _ => false
  | [] => false

theorem cFloatExponentSyntax_eq_exponentLiteral (characters : List Char) :
    cFloatExponentSyntax characters = exponentLiteral characters := by
  cases characters with
  | nil => rfl
  | cons head tail =>
      by_cases lowerE : head = 'e'
      · subst head
        simp only [cFloatExponentSyntax, exponentLiteral]
        exact cFloatSignDigits_eq_exponentDigits tail
      · by_cases upperE : head = 'E'
        · subst head
          simp only [cFloatExponentSyntax, exponentLiteral]
          exact cFloatSignDigits_eq_exponentDigits tail
        · simp [cFloatExponentSyntax, exponentLiteral, lowerE, upperE]

theorem cFloatAtomSyntax_eq_floatLiteral (characters : List Char) :
    cFloatAtomSyntax characters = floatLiteral characters := by
  unfold cFloatAtomSyntax floatLiteral
  simp only []
  split <;> simp_all [cFloatExponentSyntax_eq_exponentLiteral]

private def signedDecimal (text : String) : Option Int := do
  let characters := text.toList
  let (negative, digits) := match characters with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | rest => (false, rest)
  if !digits.all asciiDigit || digits.isEmpty then none else
  let magnitude ← String.mk digits |>.toNat?
  pure (if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude)

/-- Convert the unsigned decimal magnitude for a Float atom. Sign application
is kept outside this routine so every rounding/overflow/underflow branch has
one unsigned binary64 result to which the source sign is applied afterward. -/
private def parseUnsignedFloatMagnitude (unsigned : String) : Option Float := do
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
  let zero := Float.ofScientific 0 false 0
  let infinity := Float.ofScientific 1 false 0 / Float.ofScientific 0 false 0
  if significantDigits.isEmpty then pure zero else
  let decimalOrder := Int.ofNat (significantDigits.length - 1) + scale
  if decimalOrder > 400 then pure infinity else
  if decimalOrder < -400 then pure zero else
  let value := Float.ofScientific significand (scale < 0) scale.natAbs
  pure value

/-- Parse a decimal Float atom by converting its unsigned exact significand
and decimal scale, then applying the lexical sign once to the rounded result.
This mirrors C's final sign-bit application for finite values, infinities, and
signed zeros. -/
def parseFloatLiteral (text : String) : Option Float := do
  let magnitude ← match text.toList with
    | '-' :: rest => (parseUnsignedFloatMagnitude (String.mk rest)).map Float.neg
    | _ => parseUnsignedFloatMagnitude text
  pure magnitude

/-- A leading minus applies after the unsigned magnitude conversion. This
shows sign handling is independent of decimal rounding and also covers the
parser's overflow-to-infinity and underflow-to-zero branches. -/
theorem parseFloatLiteral_negative_sign_after_rounding (characters : List Char) :
    parseFloatLiteral (String.mk ('-' :: characters)) =
      (parseUnsignedFloatMagnitude (String.mk characters)).map Float.neg := by
  simp [parseFloatLiteral, String.toList]

/-- Complete Float atom reader: successful conversion always carries the
same ASCII decimal grammar used by the source reader. -/
def readFloatLiteral (text : String) : Option Float :=
  if floatLiteral text.toList then parseFloatLiteral text else none

/-- Representative overflow inputs reach the non-finite binary64 branch for
both source signs. -/
theorem readFloatLiteral_positive_overflow_is_infinite :
    (readFloatLiteral "1.0e401").map Float.isInf = some true := by native_decide

theorem readFloatLiteral_negative_overflow_is_infinite :
    (readFloatLiteral "-1.0e401").map Float.isInf = some true := by native_decide

/-- Inputs below the parser's decimal-order cutoff produce finite zero
magnitude for both signs; the general sign-application theorem above covers
the signed result path. -/
theorem readFloatLiteral_positive_underflow_converts_to_zero :
    (readFloatLiteral "1.0e-401").map Float.toUInt64 = some 0 := by native_decide

theorem readFloatLiteral_negative_underflow_converts_to_zero :
    (readFloatLiteral "-1.0e-401").map Float.toUInt64 = some 0 := by native_decide

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

def hexDigitsValue (digits : List Char) : Option Nat :=
  digits.foldlM (fun acc c => do pure (acc * 16 + (← hexDigit c))) 0

/-- Decode a nonempty, at most six digit hexadecimal Unicode scalar escape. -/
def readHexScalar (digits : List Char) : Option Char := do
  if digits.isEmpty || digits.length > 6 then none else
  let value ← hexDigitsValue digits
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

/-- The Lean string reader implements C's complete literal escape table:
newline, carriage return, tab, quote, backslash, and braced Unicode scalar.
Unknown escapes, malformed Unicode escapes, and an unescaped quote in the
payload are rejected. -/
theorem readStringLiteral_escape_table :
    readStringLiteral (String.mk ['"', '\\', 'n', '\\', 'r', '\\', 't',
      '\\', '"', '\\', '\\', '"']) =
        some (String.mk ['\n', '\r', '\t', '"', '\\']) ∧
    readStringLiteral (String.mk ['"', '\\', 'u', '{', '0', '}', '"']) =
        some (String.mk [Char.ofNat 0]) ∧
    readStringLiteral (String.mk ['"', '\\', 'q', '"']) = none ∧
    readStringLiteral (String.mk ['"', '\\', 'u', '{', 'D', '8', '0', '0', '}', '"']) = none ∧
    readStringLiteral (String.mk ['"', 'a', '"', 'b', '"']) = none := by
  decide

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

/-- Lean's reader accepts the ordinary source spelling for every Unicode
scalar as exactly that character. The C byte-decoder half is
`cCharacterPayload_encodeUtf8String_singleton`. -/
theorem readCharacterLiteral_single_scalar (character : Char) :
    readCharacterLiteral (String.mk ['#', '\\', character]) = some character := by
  have spelling : (String.mk ['#', '\\', character]).toList = ['#', '\\', character] := rfl
  simp [readCharacterLiteral, readUnicodeEscape, spelling]

private def utf8Continuation (byte : UInt8) : Bool :=
  0x80 ≤ byte.toNat && byte.toNat ≤ 0xbf

private def utf8Scalar (value : Nat) : Bool :=
  value ≤ 0x10ffff && !(0xd800 ≤ value && value ≤ 0xdfff)

/-- The scalar-to-byte operation used by C `utf8_put`, expressed over Nat
arithmetic before narrowing each result to one byte. -/
def utf8PutCodepoint (value : Nat) : List UInt8 :=
  if value < 0x80 then
    [UInt8.ofNat value]
  else if value < 0x800 then
    [UInt8.ofNat (0xc0 + value / 64), UInt8.ofNat (0x80 + value % 64)]
  else if value < 0x10000 then
    [UInt8.ofNat (0xe0 + value / 4096),
      UInt8.ofNat (0x80 + (value / 64) % 64), UInt8.ofNat (0x80 + value % 64)]

  else
    [UInt8.ofNat (0xf0 + value / 262144),
      UInt8.ofNat (0x80 + (value / 4096) % 64),
      UInt8.ofNat (0x80 + (value / 64) % 64), UInt8.ofNat (0x80 + value % 64)]

/-- On the ASCII branch, the custom arithmetic encoder emits the same byte as
Lean's character encoder. -/
theorem utf8PutCodepoint_ascii_eq_lean (value : Nat) (ascii : value < 0x80) :
    utf8PutCodepoint value = String.utf8EncodeChar (Char.ofNat value) := by
  have valid : value.isValidChar := by
    simp [Nat.isValidChar]
    omega
  have characterValue : (Char.ofNat value).val.toNat = value := by
    simp [Char.ofNat, valid, Char.ofNatAux, UInt32.toNat, Fin.ofNat, ascii]
  have charValue : (Char.ofNat value).val = UInt32.ofNat value := by
    apply congrArg UInt32.mk
    apply Fin.ext
    change (Char.ofNat value).val.toNat = (UInt32.ofNat value).toNat
    rw [characterValue]
    simp [UInt32.ofNat, UInt32.toNat, Fin.ofNat, ascii]
    omega
  have asciiValue : (Char.ofNat value).val ≤ 127 := by
    rw [charValue]
    change (UInt32.ofNat value).toNat ≤ 127
    simp [UInt32.ofNat, UInt32.toNat, Fin.ofNat, ascii]
    omega
  have coreAscii : UInt32.ofNat value ≤ 127 := by
    rw [← charValue]
    exact asciiValue
  have byteValue : (UInt32.ofNat value).toUInt8 = UInt8.ofNat value := by
    apply congrArg UInt8.mk
    apply Fin.ext
    simp [UInt32.toUInt8, UInt32.ofNat, UInt32.toNat,
      UInt8.ofNat, UInt8.toNat, Fin.ofNat]
    omega
  simp only [utf8PutCodepoint, if_pos ascii]
  unfold String.utf8EncodeChar
  rw [charValue]
  simp only [if_pos coreAscii]
  change [UInt8.ofNat value] = [(UInt32.ofNat value).toUInt8]
  exact congrArg (fun byte : UInt8 => [byte]) byteValue.symm

/-- Encode a sequence of Unicode scalar values by concatenating their UTF-8
byte encodings. -/
def encodeUtf8Codepoints : List Nat → List UInt8
  | [] => []
  | value :: rest => utf8PutCodepoint value ++ encodeUtf8Codepoints rest

private theorem encodeUtf8Codepoints_append (left right : List Nat) :
    encodeUtf8Codepoints (left ++ right) =
      encodeUtf8Codepoints left ++ encodeUtf8Codepoints right := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      change utf8PutCodepoint head ++ encodeUtf8Codepoints (tail ++ right) =
        (utf8PutCodepoint head ++ encodeUtf8Codepoints tail) ++
          encodeUtf8Codepoints right
      rw [ih]
      simp [List.append_assoc]

/-- Convert a scalar sequence to a Lean string. -/
def stringOfCodepoints : List Nat → String
  | [] => ""
  | value :: rest => String.singleton (Char.ofNat value) ++ stringOfCodepoints rest

/-- The byte count selected by `utf8PutCodepoint` agrees with the UTF-8
thresholds, for every natural input (including values outside scalar range). -/
theorem utf8PutCodepoint_length (value : Nat) :
    (utf8PutCodepoint value).length =
      if value < 0x80 then 1 else if value < 0x800 then 2
      else if value < 0x10000 then 3 else 4 := by
  by_cases ascii : value < 0x80
  · simp [utf8PutCodepoint, ascii]
  · by_cases twoByte : value < 0x800
    · simp [utf8PutCodepoint, ascii, twoByte]
    · by_cases threeByte : value < 0x10000
      · simp [utf8PutCodepoint, ascii, twoByte, threeByte]
      · simp [utf8PutCodepoint, ascii, twoByte, threeByte]

private theorem uint8_toNat_ofNat_of_lt (value : Nat) (bound : value < 256) :
    (UInt8.ofNat value).toNat = value := by
  simp [UInt8.toNat, UInt8.ofNat, Fin.ofNat, Nat.mod_eq_of_lt bound]

private def utf8Pair (first second : UInt8) : Nat :=
  (first.toNat % 32) * 64 + (second.toNat % 64)

/-- The payload bits emitted for a two-byte scalar reconstruct its source
codepoint after the lead and continuation prefix bits are removed. -/
theorem utf8Pair_utf8PutCodepoint_twoByte (value : Nat)
    (lower : 0x80 ≤ value) (upper : value < 0x800) :
    utf8Pair (UInt8.ofNat (0xc0 + value / 64))
      (UInt8.ofNat (0x80 + value % 64)) = value := by
  have leadBound : 0xc0 + value / 64 < 256 := by omega
  have tailBound : 0x80 + value % 64 < 256 := by omega
  have quotientBound : value / 64 < 32 := by omega
  have remainderBound : value % 64 < 64 := Nat.mod_lt _ (by omega)
  have leadPayload : (0xc0 + value / 64) % 32 = value / 64 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt quotientBound]
  have tailPayload : (0x80 + value % 64) % 64 = value % 64 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt remainderBound]
  unfold utf8Pair
  rw [uint8_toNat_ofNat_of_lt _ leadBound,
    uint8_toNat_ofNat_of_lt _ tailBound, leadPayload, tailPayload]
  simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div value 64

private def utf8Triple (first second third : UInt8) : Nat :=
  (first.toNat % 16) * 4096 + (second.toNat % 64) * 64 + third.toNat % 64

/-- The three payload groups emitted for a three-byte scalar reconstruct the
source codepoint after removing the lead and continuation prefixes. -/
theorem utf8Triple_utf8PutCodepoint_threeByte (value : Nat)
    (lower : 0x800 ≤ value) (upper : value < 0x10000) :
    utf8Triple (UInt8.ofNat (0xe0 + value / 4096))
      (UInt8.ofNat (0x80 + (value / 64) % 64))
      (UInt8.ofNat (0x80 + value % 64)) = value := by
  have leadBound : 0xe0 + value / 4096 < 256 := by omega
  have middleBound : 0x80 + (value / 64) % 64 < 256 := by omega
  have tailBound : 0x80 + value % 64 < 256 := by omega
  have quotientBound : value / 4096 < 16 := by omega
  have middleRemainderBound : (value / 64) % 64 < 64 := Nat.mod_lt _ (by omega)
  have tailRemainderBound : value % 64 < 64 := Nat.mod_lt _ (by omega)
  have leadPayload : (0xe0 + value / 4096) % 16 = value / 4096 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt quotientBound]
  have middlePayload : (0x80 + (value / 64) % 64) % 64 =
      (value / 64) % 64 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt middleRemainderBound]
  have tailPayload : (0x80 + value % 64) % 64 = value % 64 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt tailRemainderBound]
  unfold utf8Triple
  rw [uint8_toNat_ofNat_of_lt _ leadBound,
    uint8_toNat_ofNat_of_lt _ middleBound,
    uint8_toNat_ofNat_of_lt _ tailBound,
    leadPayload, middlePayload, tailPayload]
  have quotientDivision := Nat.div_div_eq_div_mul value 64 64
  omega

private def utf8Quad (first second third fourth : UInt8) : Nat :=
  (first.toNat % 8) * 262144 + (second.toNat % 64) * 4096 +
    (third.toNat % 64) * 64 + fourth.toNat % 64

/-- The four payload groups emitted for a four-byte scalar reconstruct the
source codepoint after removing the lead and continuation prefixes. -/
theorem utf8Quad_utf8PutCodepoint_fourByte (value : Nat)
    (lower : 0x10000 ≤ value) (upper : value < 0x110000) :
    utf8Quad (UInt8.ofNat (0xf0 + value / 262144))
      (UInt8.ofNat (0x80 + (value / 4096) % 64))
      (UInt8.ofNat (0x80 + (value / 64) % 64))
      (UInt8.ofNat (0x80 + value % 64)) = value := by
  have leadBound : 0xf0 + value / 262144 < 256 := by omega
  have secondBound : 0x80 + (value / 4096) % 64 < 256 := by omega
  have thirdBound : 0x80 + (value / 64) % 64 < 256 := by omega
  have fourthBound : 0x80 + value % 64 < 256 := by omega
  have quotientBound : value / 262144 < 8 := by omega
  have secondRemainderBound : (value / 4096) % 64 < 64 := Nat.mod_lt _ (by omega)
  have thirdRemainderBound : (value / 64) % 64 < 64 := Nat.mod_lt _ (by omega)
  have fourthRemainderBound : value % 64 < 64 := Nat.mod_lt _ (by omega)
  have leadPayload : (0xf0 + value / 262144) % 8 = value / 262144 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt quotientBound]
  have secondPayload : (0x80 + (value / 4096) % 64) % 64 =
      (value / 4096) % 64 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt secondRemainderBound]
  have thirdPayload : (0x80 + (value / 64) % 64) % 64 =
      (value / 64) % 64 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt thirdRemainderBound]
  have fourthPayload : (0x80 + value % 64) % 64 = value % 64 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt fourthRemainderBound]
  unfold utf8Quad
  rw [uint8_toNat_ofNat_of_lt _ leadBound,
    uint8_toNat_ofNat_of_lt _ secondBound,
    uint8_toNat_ofNat_of_lt _ thirdBound,
    uint8_toNat_ofNat_of_lt _ fourthBound,
    leadPayload, secondPayload, thirdPayload, fourthPayload]
  omega

/-- Decode one UTF-8 scalar using the same lead-byte ranges, continuation
checks, overlong rejection, and scalar validation as C `utf8_next`. -/
def utf8Next : List UInt8 → Option (Char × List UInt8)
  | [] => none
  | first :: rest =>
      if first.toNat < 0x80 then some (Char.ofNat first.toNat, rest)
      else match rest with
      | second :: tail =>
          if 0xc2 ≤ first.toNat && first.toNat ≤ 0xdf && utf8Continuation second then
            let value := utf8Pair first second
            if value < 0x80 || !utf8Scalar value then none
            else some (Char.ofNat value, tail)
          else match tail with
          | third :: tail' =>
              if 0xe0 ≤ first.toNat && first.toNat ≤ 0xef &&
                  utf8Continuation second && utf8Continuation third then
                let value := utf8Triple first second third
                if value < 0x800 || !utf8Scalar value then none
                else some (Char.ofNat value, tail')
              else match tail' with
              | fourth :: tail'' =>
                  if 0xf0 ≤ first.toNat && first.toNat ≤ 0xf4 &&
                      utf8Continuation second && utf8Continuation third &&
                      utf8Continuation fourth then
                    let value := utf8Quad first second third fourth
                    if value < 0x10000 || !utf8Scalar value then none
                    else some (Char.ofNat value, tail'')
                  else none
              | [] => none
          | [] => none
      | [] => none

/-- The C `utf8_next` lead-byte dispatch and the Lean decoder reject exactly
the non-ASCII bytes outside the supported 2/3/4-byte lead ranges. -/
theorem utf8Next_rejects_invalid_lead (first : UInt8) (rest : List UInt8)
    (notAscii : ¬ first.toNat < 0x80)
    (notTwoByte : ¬ (0xc2 ≤ first.toNat ∧ first.toNat ≤ 0xdf))
    (notThreeByte : ¬ (0xe0 ≤ first.toNat ∧ first.toNat ≤ 0xef))
    (notFourByte : ¬ (0xf0 ≤ first.toNat ∧ first.toNat ≤ 0xf4)) :
    utf8Next (first :: rest) = none := by
  cases rest with
  | nil => simp [utf8Next, notAscii]
  | cons second tail =>
      cases tail with
      | nil => simp [utf8Next, notAscii, notTwoByte]
      | cons third tail' =>
          cases tail' with
          | nil => simp [utf8Next, notAscii, notTwoByte, notThreeByte]
          | cons fourth tail'' =>
              simp [utf8Next, notAscii, notTwoByte, notThreeByte, notFourByte]

/-- Within the accepted two-byte lead range, any non-continuation second byte
is rejected, matching the first iteration of C's continuation loop. -/
theorem utf8Next_rejects_bad_twoByte_continuation (first second : UInt8)
    (leadLower : 0xc2 ≤ first.toNat) (leadUpper : first.toNat ≤ 0xdf)
    (badContinuation : utf8Continuation second = false) (tail : List UInt8) :
    utf8Next (first :: second :: tail) = none := by
  have notAscii : ¬ first.toNat < 0x80 := by omega
  cases tail with
  | nil => simp [utf8Next, notAscii, leadLower, leadUpper, badContinuation]
  | cons third tail' =>
      cases tail' with
      | nil => simp [utf8Next, notAscii, leadLower, leadUpper, badContinuation]
      | cons fourth tail'' =>
          simp [utf8Next, notAscii, leadLower, leadUpper, badContinuation]

/-- A three-byte lead followed by a malformed second byte is rejected,
matching the first iteration of C's two-step continuation loop. -/
theorem utf8Next_rejects_bad_threeByte_second (first second : UInt8)
    (leadLower : 0xe0 ≤ first.toNat) (leadUpper : first.toNat ≤ 0xef)
    (badContinuation : utf8Continuation second = false) (tail : List UInt8) :
    utf8Next (first :: second :: tail) = none := by
  have notAscii : ¬ first.toNat < 0x80 := by omega
  have notTwoByte : ¬ (0xc2 ≤ first.toNat ∧ first.toNat ≤ 0xdf) := by omega
  have notFourByte : ¬ (0xf0 ≤ first.toNat ∧ first.toNat ≤ 0xf4) := by omega
  cases tail with
  | nil => simp [utf8Next, notAscii, notTwoByte, leadLower, leadUpper,
      notFourByte, badContinuation]
  | cons third tail' =>
      cases tail' with
      | nil => simp [utf8Next, notAscii, notTwoByte, leadLower, leadUpper,
          notFourByte, badContinuation]
      | cons fourth tail'' =>
          simp [utf8Next, notAscii, notTwoByte, leadLower, leadUpper,
            notFourByte, badContinuation]

/-- A three-byte lead with a valid second byte but malformed third byte is
rejected, matching the second iteration of C's continuation loop. -/
theorem utf8Next_rejects_bad_threeByte_third (first second third : UInt8)
    (leadLower : 0xe0 ≤ first.toNat) (leadUpper : first.toNat ≤ 0xef)
    (secondContinuation : utf8Continuation second = true)
    (badContinuation : utf8Continuation third = false) (tail : List UInt8) :
    utf8Next (first :: second :: third :: tail) = none := by
  have notAscii : ¬ first.toNat < 0x80 := by omega
  have notTwoByte : ¬ (0xc2 ≤ first.toNat ∧ first.toNat ≤ 0xdf) := by omega
  have notFourByte : ¬ (0xf0 ≤ first.toNat ∧ first.toNat ≤ 0xf4) := by omega
  cases tail with
  | nil => simp [utf8Next, notAscii, notTwoByte, leadLower, leadUpper,
      notFourByte, secondContinuation, badContinuation]
  | cons fourth tail' =>
      simp [utf8Next, notAscii, notTwoByte, leadLower, leadUpper,
        notFourByte, secondContinuation, badContinuation]

/-- A four-byte lead followed by a malformed second byte is rejected. -/
theorem utf8Next_rejects_bad_fourByte_second (first second : UInt8)
    (leadLower : 0xf0 ≤ first.toNat) (leadUpper : first.toNat ≤ 0xf4)
    (badContinuation : utf8Continuation second = false) (tail : List UInt8) :
    utf8Next (first :: second :: tail) = none := by
  have notAscii : ¬ first.toNat < 0x80 := by omega
  have notTwoByte : ¬ (0xc2 ≤ first.toNat ∧ first.toNat ≤ 0xdf) := by omega
  have notThreeByte : ¬ (0xe0 ≤ first.toNat ∧ first.toNat ≤ 0xef) := by omega
  cases tail with
  | nil => simp [utf8Next, notAscii, notTwoByte, notThreeByte,
      leadLower, leadUpper, badContinuation]
  | cons third tail' =>
      cases tail' with
      | nil => simp [utf8Next, notAscii, notTwoByte, notThreeByte,
          leadLower, leadUpper, badContinuation]
      | cons fourth tail'' =>
          simp [utf8Next, notAscii, notTwoByte, notThreeByte,
            leadLower, leadUpper, badContinuation]

/-- A four-byte lead with a malformed third byte is rejected. -/
theorem utf8Next_rejects_bad_fourByte_third (first second third : UInt8)
    (leadLower : 0xf0 ≤ first.toNat) (leadUpper : first.toNat ≤ 0xf4)
    (secondContinuation : utf8Continuation second = true)
    (badContinuation : utf8Continuation third = false) (tail : List UInt8) :
    utf8Next (first :: second :: third :: tail) = none := by
  have notAscii : ¬ first.toNat < 0x80 := by omega
  have notTwoByte : ¬ (0xc2 ≤ first.toNat ∧ first.toNat ≤ 0xdf) := by omega
  have notThreeByte : ¬ (0xe0 ≤ first.toNat ∧ first.toNat ≤ 0xef) := by omega
  cases tail with
  | nil => simp [utf8Next, notAscii, notTwoByte, notThreeByte,
      leadLower, leadUpper, secondContinuation, badContinuation]
  | cons fourth tail' =>
      simp [utf8Next, notAscii, notTwoByte, notThreeByte, leadLower,
        leadUpper, secondContinuation, badContinuation]

/-- A four-byte lead with valid second/third bytes but malformed fourth byte
is rejected at the final iteration of C's continuation loop. -/
theorem utf8Next_rejects_bad_fourByte_fourth (first second third fourth : UInt8)
    (leadLower : 0xf0 ≤ first.toNat) (leadUpper : first.toNat ≤ 0xf4)
    (secondContinuation : utf8Continuation second = true)
    (thirdContinuation : utf8Continuation third = true)
    (badContinuation : utf8Continuation fourth = false) (tail : List UInt8) :
    utf8Next (first :: second :: third :: fourth :: tail) = none := by
  have notAscii : ¬ first.toNat < 0x80 := by omega
  have notTwoByte : ¬ (0xc2 ≤ first.toNat ∧ first.toNat ≤ 0xdf) := by omega
  have notThreeByte : ¬ (0xe0 ≤ first.toNat ∧ first.toNat ≤ 0xef) := by omega
  simp [utf8Next, notAscii, notTwoByte, notThreeByte, leadLower,
    leadUpper, secondContinuation, thirdContinuation, badContinuation]

/-- The two-byte decoder branch is correct whenever its prefix, continuation,
and reconstructed scalar guards hold. -/
theorem utf8Next_twoByte_of_guards (first second : UInt8)
    (lead : 0xc2 ≤ first.toNat ∧ first.toNat ≤ 0xdf)
    (continuation : utf8Continuation second = true)
    (payloadLower : 0x80 ≤ utf8Pair first second)
    (scalar : utf8Scalar (utf8Pair first second) = true) :
    utf8Next [first, second] = some (Char.ofNat (utf8Pair first second), []) := by
  have firstNotAscii : ¬ first.toNat < 0x80 := by omega
  simp [utf8Next, firstNotAscii, lead.1, lead.2, continuation,
    payloadLower, scalar]

/-- A successful two-byte prefix leaves an arbitrary following byte suffix
untouched. -/
theorem utf8Next_twoByte_of_guards_append (first second : UInt8)
    (suffix : List UInt8)
    (lead : 0xc2 ≤ first.toNat ∧ first.toNat ≤ 0xdf)
    (continuation : utf8Continuation second = true)
    (payloadLower : 0x80 ≤ utf8Pair first second)
    (scalar : utf8Scalar (utf8Pair first second) = true) :
    utf8Next ([first, second] ++ suffix) =
      some (Char.ofNat (utf8Pair first second), suffix) := by
  have firstNotAscii : ¬ first.toNat < 0x80 := by omega
  simp [utf8Next, firstNotAscii, lead.1, lead.2, continuation,
    payloadLower, scalar]

/-- The three-byte decoder branch is correct whenever its prefix,
continuation, and reconstructed scalar guards hold. -/
theorem utf8Next_threeByte_of_guards (first second third : UInt8)
    (lead : 0xe0 ≤ first.toNat ∧ first.toNat ≤ 0xef)
    (secondContinuation : utf8Continuation second = true)
    (thirdContinuation : utf8Continuation third = true)
    (payloadLower : 0x800 ≤ utf8Triple first second third)
    (scalar : utf8Scalar (utf8Triple first second third) = true) :
    utf8Next [first, second, third] =
      some (Char.ofNat (utf8Triple first second third), []) := by
  have firstNotAscii : ¬ first.toNat < 0x80 := by omega
  have notTwoByte : ¬ (0xc2 ≤ first.toNat ∧ first.toNat ≤ 0xdf) := by omega
  simp [utf8Next, firstNotAscii, lead.1, lead.2, secondContinuation,
    thirdContinuation, payloadLower, scalar, notTwoByte]

/-- A successful three-byte prefix leaves an arbitrary following byte suffix
untouched. -/
theorem utf8Next_threeByte_of_guards_append (first second third : UInt8)
    (suffix : List UInt8)
    (lead : 0xe0 ≤ first.toNat ∧ first.toNat ≤ 0xef)
    (secondContinuation : utf8Continuation second = true)
    (thirdContinuation : utf8Continuation third = true)
    (payloadLower : 0x800 ≤ utf8Triple first second third)
    (scalar : utf8Scalar (utf8Triple first second third) = true) :
    utf8Next ([first, second, third] ++ suffix) =
      some (Char.ofNat (utf8Triple first second third), suffix) := by
  have firstNotAscii : ¬ first.toNat < 0x80 := by omega
  have notTwoByte : ¬ (0xc2 ≤ first.toNat ∧ first.toNat ≤ 0xdf) := by omega
  simp [utf8Next, firstNotAscii, lead.1, lead.2, secondContinuation,
    thirdContinuation, payloadLower, scalar, notTwoByte]

/-- The four-byte decoder branch is correct whenever its prefix,
continuation, and reconstructed scalar guards hold. -/
theorem utf8Next_fourByte_of_guards (first second third fourth : UInt8)
    (lead : 0xf0 ≤ first.toNat ∧ first.toNat ≤ 0xf4)
    (secondContinuation : utf8Continuation second = true)
    (thirdContinuation : utf8Continuation third = true)
    (fourthContinuation : utf8Continuation fourth = true)
    (payloadLower : 0x10000 ≤ utf8Quad first second third fourth)
    (scalar : utf8Scalar (utf8Quad first second third fourth) = true) :
    utf8Next [first, second, third, fourth] =
      some (Char.ofNat (utf8Quad first second third fourth), []) := by
  have firstNotAscii : ¬ first.toNat < 0x80 := by omega
  have notTwoByte : ¬ (0xc2 ≤ first.toNat ∧ first.toNat ≤ 0xdf) := by omega
  have notThreeByte : ¬ (0xe0 ≤ first.toNat ∧ first.toNat ≤ 0xef) := by omega
  simp [utf8Next, firstNotAscii, lead.1, lead.2, secondContinuation,
    thirdContinuation, fourthContinuation, payloadLower, scalar,
    notTwoByte, notThreeByte]

/-- A successful four-byte prefix leaves an arbitrary following byte suffix
untouched. -/
theorem utf8Next_fourByte_of_guards_append (first second third fourth : UInt8)
    (suffix : List UInt8)
    (lead : 0xf0 ≤ first.toNat ∧ first.toNat ≤ 0xf4)
    (secondContinuation : utf8Continuation second = true)
    (thirdContinuation : utf8Continuation third = true)
    (fourthContinuation : utf8Continuation fourth = true)
    (payloadLower : 0x10000 ≤ utf8Quad first second third fourth)
    (scalar : utf8Scalar (utf8Quad first second third fourth) = true) :
    utf8Next ([first, second, third, fourth] ++ suffix) =
      some (Char.ofNat (utf8Quad first second third fourth), suffix) := by
  have firstNotAscii : ¬ first.toNat < 0x80 := by omega
  have notTwoByte : ¬ (0xc2 ≤ first.toNat ∧ first.toNat ≤ 0xdf) := by omega
  have notThreeByte : ¬ (0xe0 ≤ first.toNat ∧ first.toNat ≤ 0xef) := by omega
  simp [utf8Next, firstNotAscii, lead.1, lead.2, secondContinuation,
    thirdContinuation, fourthContinuation, payloadLower, scalar,
    notTwoByte, notThreeByte]

/-- Compose the emitted-byte bounds and payload reconstruction with the
two-byte decoder branch to obtain the full range round trip. -/
theorem utf8Next_utf8PutCodepoint_twoByte (value : Nat)
    (lower : 0x80 ≤ value) (upper : value < 0x800)
    (suffix : List UInt8) :
    utf8Next (utf8PutCodepoint value ++ suffix) =
      some (Char.ofNat value, suffix) := by
  let first := UInt8.ofNat (0xc0 + value / 64)
  let second := UInt8.ofNat (0x80 + value % 64)
  have firstBound : 0xc0 + value / 64 < 256 := by omega
  have secondBound : 0x80 + value % 64 < 256 := by omega
  have firstValue : first.toNat = 0xc0 + value / 64 := by
    simp [first, UInt8.toNat, UInt8.ofNat, Fin.ofNat,
      Nat.mod_eq_of_lt firstBound]
  have secondValue : second.toNat = 0x80 + value % 64 := by
    simp [second, UInt8.toNat, UInt8.ofNat, Fin.ofNat,
      Nat.mod_eq_of_lt secondBound]
  have encoded : utf8PutCodepoint value = [first, second] := by
    simp [utf8PutCodepoint, Nat.not_lt.mpr lower, upper, first, second]
  have payload := utf8Pair_utf8PutCodepoint_twoByte value lower upper
  have lead : 0xc2 ≤ first.toNat ∧ first.toNat ≤ 0xdf := by
    rw [firstValue]
    constructor <;> omega
  have continuation : utf8Continuation second = true := by
    rw [utf8Continuation, secondValue]
    simp
    omega
  have payloadLower : 0x80 ≤ utf8Pair first second := by
    rw [payload]
    exact lower
  have scalar : utf8Scalar (utf8Pair first second) = true := by
    rw [payload]
    simp [utf8Scalar]
    omega
  rw [encoded]
  simpa [payload] using utf8Next_twoByte_of_guards_append first second suffix
    lead continuation payloadLower scalar

/-- Compose the emitted-byte bounds and payload reconstruction with the
three-byte decoder branch to obtain the full range round trip. -/
theorem utf8Next_utf8PutCodepoint_threeByte (value : Nat)
    (lower : 0x800 ≤ value) (upper : value < 0x10000)
    (notSurrogate : ¬ (0xd800 ≤ value ∧ value ≤ 0xdfff))
    (suffix : List UInt8) :
    utf8Next (utf8PutCodepoint value ++ suffix) =
      some (Char.ofNat value, suffix) := by
  let first := UInt8.ofNat (0xe0 + value / 4096)
  let second := UInt8.ofNat (0x80 + (value / 64) % 64)
  let third := UInt8.ofNat (0x80 + value % 64)
  have firstBound : 0xe0 + value / 4096 < 256 := by omega
  have secondBound : 0x80 + (value / 64) % 64 < 256 := by omega
  have thirdBound : 0x80 + value % 64 < 256 := by omega
  have firstValue : first.toNat = 0xe0 + value / 4096 := by
    simp [first, UInt8.toNat, UInt8.ofNat, Fin.ofNat,
      Nat.mod_eq_of_lt firstBound]
  have secondValue : second.toNat = 0x80 + (value / 64) % 64 := by
    simp [second, UInt8.toNat, UInt8.ofNat, Fin.ofNat,
      Nat.mod_eq_of_lt secondBound]
  have thirdValue : third.toNat = 0x80 + value % 64 := by
    simp [third, UInt8.toNat, UInt8.ofNat, Fin.ofNat,
      Nat.mod_eq_of_lt thirdBound]
  have encoded : utf8PutCodepoint value = [first, second, third] := by
    have notAscii : ¬ value < 0x80 := by omega
    have notTwoByte : ¬ value < 0x800 := Nat.not_lt.mpr lower
    simp [utf8PutCodepoint, notAscii, notTwoByte, upper, first, second, third]
  have payload := utf8Triple_utf8PutCodepoint_threeByte value lower upper
  have lead : 0xe0 ≤ first.toNat ∧ first.toNat ≤ 0xef := by
    rw [firstValue]
    constructor <;> omega
  have secondContinuation : utf8Continuation second = true := by
    rw [utf8Continuation, secondValue]
    simp
    omega
  have thirdContinuation : utf8Continuation third = true := by
    rw [utf8Continuation, thirdValue]
    simp
    omega
  have payloadLower : 0x800 ≤ utf8Triple first second third := by
    rw [payload]
    exact lower
  have scalar : utf8Scalar (utf8Triple first second third) = true := by
    rw [payload]
    have scalarBound : value ≤ 0x10ffff := by omega
    simp [utf8Scalar, scalarBound, notSurrogate]
    omega
  rw [encoded]
  simpa [payload] using utf8Next_threeByte_of_guards_append first second third suffix
    lead secondContinuation thirdContinuation payloadLower scalar

/-- Compose the emitted-byte bounds and payload reconstruction with the
four-byte decoder branch to obtain the Unicode scalar round trip. -/
theorem utf8Next_utf8PutCodepoint_fourByte (value : Nat)
    (lower : 0x10000 ≤ value) (upper : value ≤ 0x10ffff)
    (suffix : List UInt8) :
    utf8Next (utf8PutCodepoint value ++ suffix) =
      some (Char.ofNat value, suffix) := by
  let first := UInt8.ofNat (0xf0 + value / 262144)
  let second := UInt8.ofNat (0x80 + (value / 4096) % 64)
  let third := UInt8.ofNat (0x80 + (value / 64) % 64)
  let fourth := UInt8.ofNat (0x80 + value % 64)
  have firstBound : 0xf0 + value / 262144 < 256 := by omega
  have secondBound : 0x80 + (value / 4096) % 64 < 256 := by omega
  have thirdBound : 0x80 + (value / 64) % 64 < 256 := by omega
  have fourthBound : 0x80 + value % 64 < 256 := by omega
  have firstValue : first.toNat = 0xf0 + value / 262144 := by
    simp [first, UInt8.toNat, UInt8.ofNat, Fin.ofNat,
      Nat.mod_eq_of_lt firstBound]
  have secondValue : second.toNat = 0x80 + (value / 4096) % 64 := by
    simp [second, UInt8.toNat, UInt8.ofNat, Fin.ofNat,
      Nat.mod_eq_of_lt secondBound]
  have thirdValue : third.toNat = 0x80 + (value / 64) % 64 := by
    simp [third, UInt8.toNat, UInt8.ofNat, Fin.ofNat,
      Nat.mod_eq_of_lt thirdBound]
  have fourthValue : fourth.toNat = 0x80 + value % 64 := by
    simp [fourth, UInt8.toNat, UInt8.ofNat, Fin.ofNat,
      Nat.mod_eq_of_lt fourthBound]
  have notAscii : ¬ value < 0x80 := by omega
  have notTwoByte : ¬ value < 0x800 := by omega
  have notThreeByte : ¬ value < 0x10000 := by omega
  have encoded : utf8PutCodepoint value = [first, second, third, fourth] := by
    simp [utf8PutCodepoint, notAscii, notTwoByte, notThreeByte,
      first, second, third, fourth]
  have payload := utf8Quad_utf8PutCodepoint_fourByte value lower (by omega)
  have lead : 0xf0 ≤ first.toNat ∧ first.toNat ≤ 0xf4 := by
    rw [firstValue]
    constructor <;> omega
  have secondContinuation : utf8Continuation second = true := by
    rw [utf8Continuation, secondValue]
    simp
    omega
  have thirdContinuation : utf8Continuation third = true := by
    rw [utf8Continuation, thirdValue]
    simp
    omega
  have fourthContinuation : utf8Continuation fourth = true := by
    rw [utf8Continuation, fourthValue]
    simp
    omega
  have payloadLower : 0x10000 ≤ utf8Quad first second third fourth := by
    rw [payload]
    exact lower
  have scalar : utf8Scalar (utf8Quad first second third fourth) = true := by
    rw [payload]
    have scalarBound : value ≤ 0x10ffff := upper
    have notSurrogate : ¬ (0xd800 ≤ value ∧ value ≤ 0xdfff) := by omega
    simp [utf8Scalar, scalarBound, notSurrogate]
    omega
  rw [encoded]
  simpa [payload] using utf8Next_fourByte_of_guards_append first second third fourth suffix
    lead secondContinuation thirdContinuation fourthContinuation payloadLower scalar

/-- Decode a complete UTF-8 byte sequence. Embedded zero bytes are retained
as U+0000, matching the explicit-length string representation in C. -/
private def decodeUtf8Fuel : Nat → List UInt8 → Option String
  | 0, _ => none
  | _ + 1, [] => some ""
  | fuel + 1, byte :: bytes => do
      let (scalar, rest) ← utf8Next (byte :: bytes)
      let suffix ← decodeUtf8Fuel fuel rest
      pure (String.singleton scalar ++ suffix)

def decodeUtf8 (bytes : List UInt8) : Option String :=
  decodeUtf8Fuel (bytes.length + 1) bytes


def AsciiBytes : List UInt8 → Prop
  | [] => True
  | byte :: tail => byte.toNat < 0x80 ∧ AsciiBytes tail

def decodeAsciiBytes : List UInt8 → String
  | [] => ""
  | byte :: tail => String.singleton (Char.ofNat byte.toNat) ++ decodeAsciiBytes tail

private theorem decodeUtf8Fuel_ascii (fuel : Nat) (bytes : List UInt8)
    (ascii : AsciiBytes bytes) (fuelBound : bytes.length < fuel) :
    decodeUtf8Fuel fuel bytes = some (decodeAsciiBytes bytes) := by
  induction bytes generalizing fuel with
  | nil =>
      cases fuel with
      | zero => simp at fuelBound
      | succ fuel => rfl
  | cons byte tail ih =>
      cases fuel with
      | zero => exact (Nat.not_lt_zero _ fuelBound).elim
      | succ fuel =>
          have tailBound : tail.length < fuel := by
            have bound : Nat.succ tail.length < Nat.succ fuel := by simpa using fuelBound
            exact Nat.lt_of_succ_lt_succ bound
          simp [decodeUtf8Fuel, decodeAsciiBytes, utf8Next, ascii.1,
            ih fuel ascii.2 tailBound]

theorem decodeUtf8_ascii_bytes (bytes : List UInt8) (ascii : AsciiBytes bytes) :
    decodeUtf8 bytes = some (decodeAsciiBytes bytes) := by
  exact decodeUtf8Fuel_ascii (bytes.length + 1) bytes ascii (by simp)

theorem decodeUtf8_ascii_nul :
    decodeUtf8 [0x41, 0x00, 0x42] =
      some (String.singleton 'A' ++ String.singleton (Char.ofNat 0) ++ String.singleton 'B') := by
  rfl

theorem decodeUtf8_rejects_overlong_nul :
    decodeUtf8 [0xc0, 0x80] = none := by
  rfl

theorem decodeUtf8_rejects_surrogate :
    decodeUtf8 [0xed, 0xa0, 0x80] = none := by
  rfl

theorem decodeUtf8_rejects_truncated_sequence :
    decodeUtf8 [0xf0, 0x9f, 0x92] = none := by
  rfl

theorem utf8Next_decodes_two_byte_scalar :
    utf8Next [0xc3, 0xa9] = some (Char.ofNat 0xe9, []) := by
  rfl

theorem utf8Next_decodes_three_byte_scalar :
    utf8Next [0xe2, 0x82, 0xac] = some (Char.ofNat 0x20ac, []) := by
  rfl

theorem utf8Next_decodes_four_byte_scalar :
    utf8Next [0xf0, 0x9f, 0x98, 0x80] = some (Char.ofNat 0x1f600, []) := by
  rfl

theorem utf8Next_decodes_maximum_scalar :
    utf8Next [0xf4, 0x8f, 0xbf, 0xbf] = some (Char.ofNat 0x10ffff, []) := by
  rfl

theorem utf8Next_rejects_above_maximum_scalar :
    utf8Next [0xf4, 0x90, 0x80, 0x80] = none := by
  rfl

/-- ASCII scalars emitted by `utf8PutCodepoint` are recovered by the
single-scalar decoder, with no trailing bytes. -/
theorem utf8Next_utf8PutCodepoint_ascii (value : Nat) (ascii : value < 0x80) :
    utf8Next (utf8PutCodepoint value) = some (Char.ofNat value, []) := by
  have byteBound : value < 256 := by omega
  simp [utf8PutCodepoint, ascii, utf8Next,
    uint8_toNat_ofNat_of_lt value byteBound, Char.ofNat]

/-- ASCII scalar decoding preserves an arbitrary byte suffix. -/
theorem utf8Next_utf8PutCodepoint_ascii_append (value : Nat)
    (ascii : value < 0x80) (suffix : List UInt8) :
    utf8Next (utf8PutCodepoint value ++ suffix) =
      some (Char.ofNat value, suffix) := by
  have byteBound : value < 256 := by omega
  simp [utf8PutCodepoint, ascii, utf8Next,
    uint8_toNat_ofNat_of_lt value byteBound, Char.ofNat]

/-- Every valid Unicode scalar encoder prefix decodes to that scalar while
leaving all later bytes untouched. -/
theorem utf8Next_utf8PutCodepoint_append (value : Nat)
    (isScalar : utf8Scalar value = true) (suffix : List UInt8) :
    utf8Next (utf8PutCodepoint value ++ suffix) =
      some (Char.ofNat value, suffix) := by
  by_cases ascii : value < 0x80
  · exact utf8Next_utf8PutCodepoint_ascii_append value ascii suffix
  · by_cases twoByte : value < 0x800
    · have lower : 0x80 ≤ value := by omega
      exact utf8Next_utf8PutCodepoint_twoByte value lower twoByte suffix
    · by_cases threeByte : value < 0x10000
      · have lower : 0x800 ≤ value := by omega
        have notSurrogate : ¬ (0xd800 ≤ value ∧ value ≤ 0xdfff) := by
          intro surrogate
          have invalid : utf8Scalar value = false := by
            simp [utf8Scalar, surrogate.1, surrogate.2]
          rw [invalid] at isScalar
          contradiction
        exact utf8Next_utf8PutCodepoint_threeByte value lower threeByte
          notSurrogate suffix
      · have lower : 0x10000 ≤ value := by omega
        have upper : value ≤ 0x10ffff := by
          by_cases bound : value ≤ 0x10ffff
          · exact bound
          · have tooLarge : 0x10ffff < value := Nat.lt_of_not_ge bound
            have invalid : utf8Scalar value = false := by
              have notBound : ¬ value ≤ 0x10ffff := by omega
              have boundDecide : decide (value ≤ 0x10ffff) = false :=
                (decide_eq_false_iff_not (value ≤ 0x10ffff)).2 notBound
              simp [utf8Scalar, boundDecide]
            rw [invalid] at isScalar
            contradiction
        exact utf8Next_utf8PutCodepoint_fourByte value lower upper suffix

/-- Decoding the concatenation of valid scalar encodings returns the same
string, provided the decoder fuel exceeds the number of scalars. -/
theorem decodeUtf8Fuel_encodeUtf8Codepoints (values : List Nat) (fuel : Nat)
    (valid : ∀ value ∈ values, utf8Scalar value = true)
    (fuelBound : values.length < fuel) :
    decodeUtf8Fuel fuel (encodeUtf8Codepoints values) =
      some (stringOfCodepoints values) := by
  induction values generalizing fuel with
  | nil =>
      cases fuel with
      | zero => simp at fuelBound
      | succ fuel => simp [decodeUtf8Fuel, stringOfCodepoints,
          encodeUtf8Codepoints]
  | cons head tail ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have tailBound : tail.length < fuel := by simp at fuelBound; omega
          have validHead : utf8Scalar head = true := valid head (by simp)
          have validTail : ∀ value ∈ tail, utf8Scalar value = true := by
            intro value member
            exact valid value (by simp [member])
          have decodedHead := utf8Next_utf8PutCodepoint_append head validHead
            (encodeUtf8Codepoints tail)
          have tailDecoded := ih fuel validTail tailBound
          by_cases ascii : head < 0x80
          · simp only [encodeUtf8Codepoints, utf8PutCodepoint, if_pos ascii]
            have decodedHead' := by
              simpa [utf8PutCodepoint, ascii] using decodedHead
            simp only [decodeUtf8Fuel]
            simp [List.nil_append, decodedHead', tailDecoded, stringOfCodepoints]
          · by_cases twoByte : head < 0x800
            · simp only [encodeUtf8Codepoints, utf8PutCodepoint,
                if_neg ascii, if_pos twoByte]
              have decodedHead' := by
                simpa [utf8PutCodepoint, ascii, twoByte] using decodedHead
              simp only [decodeUtf8Fuel]
              simp [List.nil_append, decodedHead', tailDecoded, stringOfCodepoints]
            · by_cases threeByte : head < 0x10000
              · simp only [encodeUtf8Codepoints, utf8PutCodepoint,
                  if_neg ascii, if_neg twoByte, if_pos threeByte]
                have decodedHead' := by
                  simpa [utf8PutCodepoint, ascii, twoByte, threeByte] using decodedHead
                simp only [decodeUtf8Fuel]
                simp [List.nil_append, decodedHead', tailDecoded, stringOfCodepoints]
              · simp only [encodeUtf8Codepoints, utf8PutCodepoint,
                  if_neg ascii, if_neg twoByte, if_neg threeByte]
                have decodedHead' := by
                  simpa [utf8PutCodepoint, ascii, twoByte, threeByte] using decodedHead
                simp only [decodeUtf8Fuel]
                simp [List.nil_append, decodedHead', tailDecoded, stringOfCodepoints]

theorem utf8PutCodepoint_length_pos (value : Nat) :
    1 ≤ (utf8PutCodepoint value).length := by
  rw [utf8PutCodepoint_length]
  by_cases ascii : value < 0x80
  · simp [ascii]
  · by_cases twoByte : value < 0x800
    · simp [ascii, twoByte]
    · by_cases threeByte : value < 0x10000 <;> simp [ascii, twoByte, threeByte]

theorem encodeUtf8Codepoints_length_ge (values : List Nat) :
    values.length ≤ (encodeUtf8Codepoints values).length := by
  induction values with
  | nil => simp [encodeUtf8Codepoints]
  | cons head tail ih =>
      simp only [encodeUtf8Codepoints, List.length_append, List.length_cons]
      have positive := utf8PutCodepoint_length_pos head
      omega

/-- The public decoder uses enough fuel to decode every scalar in a valid
encoded scalar list, and returns the original string. -/
theorem decodeUtf8_encodeUtf8Codepoints (values : List Nat)
    (valid : ∀ value ∈ values, utf8Scalar value = true) :
    decodeUtf8 (encodeUtf8Codepoints values) = some (stringOfCodepoints values) := by
  unfold decodeUtf8
  apply decodeUtf8Fuel_encodeUtf8Codepoints
  · exact valid
  · have lengthBound := encodeUtf8Codepoints_length_ge values
    omega

/-- A Lean `Char` satisfies the same Unicode scalar predicate used by the
byte decoder. -/
theorem char_toNat_utf8Scalar (character : Char) :
    utf8Scalar character.toNat = true := by
  have valid : character.toNat < 0xd800 ∨
      0xdfff < character.toNat ∧ character.toNat < 0x110000 := by
    simpa [Char.toNat, UInt32.isValidChar, Nat.isValidChar] using character.valid
  rcases valid with belowSurrogate | ⟨aboveSurrogate, belowMaximum⟩
  · simp [utf8Scalar]
    omega
  · simp [utf8Scalar]
    omega

private theorem uint32_ofNat_toNat (value : UInt32) :
    UInt32.ofNat value.toNat = value := by
  cases value with
  | mk raw =>
      apply congrArg UInt32.mk
      apply Fin.ext
      simp [UInt32.toNat, UInt32.ofNat, Fin.ofNat, Nat.mod_eq_of_lt raw.isLt]

private theorem char_value_ext {left right : Char}
    (sameValue : left.val = right.val) : left = right := by
  cases left with
  | mk leftValue leftValid =>
      cases right with
      | mk rightValue rightValid =>
          cases sameValue
          have proofEq : leftValid = rightValid := Subsingleton.elim _ _
          cases proofEq
          rfl

/-- Converting a valid Lean character to its scalar value and back preserves
the character exactly. -/
theorem char_ofNat_toNat_identity (character : Char) :
    Char.ofNat character.toNat = character := by
  cases character with
  | mk value valid =>
      have validNat : value.toNat.isValidChar := by
        simpa [UInt32.isValidChar] using valid
      apply char_value_ext
      change (if h : value.toNat.isValidChar then
        Char.ofNatAux value.toNat h else _).val = value
      rw [dif_pos validNat]
      unfold Char.ofNatAux
      cases value with
      | mk raw =>
          apply congrArg UInt32.mk
          apply Fin.ext
          simp [Char.toNat, UInt32.toNat, UInt32.ofNat, Fin.ofNat,
            Nat.mod_eq_of_lt raw.isLt]

theorem stringOfCodepoints_charToNat (characters : List Char) :
    stringOfCodepoints (characters.map Char.toNat) = String.mk characters := by
  induction characters with
  | nil => rfl
  | cons head tail ih =>
      simp only [stringOfCodepoints, char_ofNat_toNat_identity, ih,
        String.singleton, String.push]
      change String.mk ([head] ++ tail) = String.mk (head :: tail)
      rfl

/-- Encode a Lean string by concatenating the UTF-8 encoding of each of its
characters. -/
def encodeUtf8String (text : String) : List UInt8 :=
  encodeUtf8Codepoints (text.toList.map Char.toNat)

/-- The byte reader consumes exactly one canonical UTF-8 character and leaves
the following bytes untouched. This is the local C `utf8_next` / encoder
correspondence used to reason about reader and string-buffer boundaries. -/
theorem utf8Next_encodeUtf8String_singleton_append (character : Char)
    (suffix : List UInt8) :
    utf8Next (encodeUtf8String (String.singleton character) ++ suffix) =
      some (character, suffix) := by
  have scalar : utf8Scalar character.toNat = true := char_toNat_utf8Scalar character
  have decoded := utf8Next_utf8PutCodepoint_append character.toNat scalar suffix
  simpa [encodeUtf8String, String.toList, encodeUtf8Codepoints,
    char_ofNat_toNat_identity] using decoded

/-- C's ordinary character-literal payload path: decode exactly one UTF-8
scalar and reject trailing bytes. The caller has consumed `#\\`; Unicode
escape spellings use C's separate `unicode_escape` branch. -/
def cCharacterPayload (bytes : List UInt8) : Option Char :=
  match utf8Next bytes with
  | some (character, []) => some character
  | _ => none

/-- Every Lean character is accepted by C's `utf8_next` payload path when
encoded canonically, with no bytes left after the scalar. -/
theorem cCharacterPayload_encodeUtf8String_singleton (character : Char) :
    cCharacterPayload (encodeUtf8String (String.singleton character)) =
      some character := by
  unfold cCharacterPayload
  have decoded := utf8Next_encodeUtf8String_singleton_append character []
  have decoded' : utf8Next (encodeUtf8String (String.singleton character)) =
      some (character, []) := by simpa using decoded
  rw [decoded']

/-- Named whitespace spellings and their one-scalar UTF-8 payload spellings
produce the same character as C's ordinary `utf8_next` payload path. -/
theorem readCharacterLiteral_named_matches_cCharacterPayload :
    readCharacterLiteral "#\\newline" =
        cCharacterPayload (encodeUtf8String (String.singleton '\n')) ∧
    readCharacterLiteral "#\\space" =
        cCharacterPayload (encodeUtf8String (String.singleton ' ')) ∧
    readCharacterLiteral "#\\tab" =
    cCharacterPayload (encodeUtf8String (String.singleton '\t')) := by
  decide

/-- ASCII strings use the same per-character byte sequence as Lean's native
UTF-8 encoder. -/
theorem encodeUtf8Codepoints_ascii_chars (characters : List Char)
    (ascii : ∀ character ∈ characters, character.toNat < 0x80) :
    encodeUtf8Codepoints (characters.map Char.toNat) =
      List.join (characters.map String.utf8EncodeChar) := by
  induction characters with
  | nil => rfl
  | cons character rest ih =>
      have characterAscii : character.toNat < 0x80 := ascii character (by simp)
      have restAscii : ∀ item ∈ rest, item.toNat < 0x80 := by
        intro item member
        exact ascii item (by simp [member])
      change utf8PutCodepoint character.toNat ++ encodeUtf8Codepoints (rest.map Char.toNat) =
        String.utf8EncodeChar character ++ List.join (rest.map String.utf8EncodeChar)
      rw [utf8PutCodepoint_ascii_eq_lean character.toNat characterAscii,
        char_ofNat_toNat_identity character, ih restAscii]

theorem encodeUtf8String_ascii_chars (text : String)
    (ascii : ∀ character ∈ text.toList, character.toNat < 0x80) :
    encodeUtf8String text = List.join (text.toList.map String.utf8EncodeChar) := by
  unfold encodeUtf8String
  exact encodeUtf8Codepoints_ascii_chars text.toList ascii

theorem encodeUtf8String_eq_native_utf8_of_ascii (text : String)
    (ascii : ∀ character ∈ text.toList, character.toNat < 0x80) :
    encodeUtf8String text = text.toUTF8.data.data := by
  rw [encodeUtf8String_ascii_chars text ascii]
  rfl


/-- Decoding the byte encoding of a Lean string reconstructs its scalar
sequence as a Lean string. -/
theorem decodeUtf8_encodeUtf8String (text : String) :
    decodeUtf8 (encodeUtf8String text) =
      some (stringOfCodepoints (text.toList.map Char.toNat)) := by
  unfold encodeUtf8String
  apply decodeUtf8_encodeUtf8Codepoints
  intro value member
  rcases List.mem_map.mp member with ⟨character, _member, rfl⟩
  exact char_toNat_utf8Scalar character

/-- Exact String-level round trip for the public UTF-8 codec. -/
theorem decodeUtf8_encodeUtf8String_exact (text : String) :
    decodeUtf8 (encodeUtf8String text) = some text := by
  rw [decodeUtf8_encodeUtf8String, stringOfCodepoints_charToNat]
  rfl

/-- UTF-8 byte equality is equivalent to Lean string equality because the
decoder is a left inverse of `encodeUtf8String`. This is the semantic basis
for C's length-and-`memcmp` implementation of `string=` on valid Text. -/
theorem encodeUtf8String_injective {left right : String}
    (sameBytes : encodeUtf8String left = encodeUtf8String right) :
    left = right := by
  have decoded := congrArg decodeUtf8 sameBytes
  rw [decodeUtf8_encodeUtf8String_exact, decodeUtf8_encodeUtf8String_exact] at decoded
  injection decoded

/-- Equality of valid UTF-8 byte strings is exactly equality of the decoded
Lean strings, matching C `string=`'s length-and-byte comparison. -/
theorem encodeUtf8String_eq_iff {left right : String} :
    encodeUtf8String left = encodeUtf8String right ↔ left = right := by
  constructor
  · exact encodeUtf8String_injective
  · intro same
    cases same
    rfl

/-- Concatenating Lean strings and then encoding is the same as concatenating
their canonical UTF-8 byte sequences, matching C `string-append`'s Text
buffer construction. -/
theorem encodeUtf8String_append (left right : String) :
    encodeUtf8String (left ++ right) =
      encodeUtf8String left ++ encodeUtf8String right := by
  simp only [encodeUtf8String, String.toList]
  change encodeUtf8Codepoints ((left.data ++ right.data).map Char.toNat) = _
  rw [List.map_append]
  exact encodeUtf8Codepoints_append (left.data.map Char.toNat)
    (right.data.map Char.toNat)

/-- C's `Text` representation stores an explicit byte buffer and length. -/
structure CTextModel where
  bytes : List UInt8
  deriving DecidableEq, Repr

def CTextModel.ofString (text : String) : CTextModel :=
  ⟨encodeUtf8String text⟩

def CTextModel.byteLength (text : CTextModel) : Nat := text.bytes.length

/-- Boolean form of C's length check followed by `memcmp`. -/
def CTextModel.stringEqual (left right : CTextModel) : Bool :=
  (left.byteLength == right.byteLength) && (left.bytes == right.bytes)

/-- C's `string-append` copies both length-bearing byte buffers in order. -/
def CTextModel.stringAppend (left right : CTextModel) : CTextModel :=
  ⟨left.bytes ++ right.bytes⟩

/-- Runtime Text values produced by the reader and String builtins are exactly
the canonical UTF-8 encodings of Lean strings. -/
def CTextModel.WellFormed (text : CTextModel) : Prop :=
  ∃ source, text = CTextModel.ofString source

theorem CTextModel.ofString_wellFormed (text : String) :
    CTextModel.WellFormed (CTextModel.ofString text) :=
  ⟨text, rfl⟩

theorem CTextModel.stringEqual_ofString_iff (left right : String) :
    CTextModel.stringEqual (CTextModel.ofString left) (CTextModel.ofString right) =
      decide (left = right) := by
  by_cases same : left = right
  · subst right
    simp [CTextModel.stringEqual, CTextModel.ofString, CTextModel.byteLength]
  · have bytesDifferent : encodeUtf8String left ≠ encodeUtf8String right := by
      intro bytesSame
      exact same (encodeUtf8String_injective bytesSame)
    have bytesComparison :
        (encodeUtf8String left == encodeUtf8String right) = false := by
      exact (beq_eq_false_iff_ne _ _).mpr bytesDifferent
    simp [CTextModel.stringEqual, CTextModel.ofString, CTextModel.byteLength,
      same, bytesComparison]

theorem CTextModel.stringAppend_ofString (left right : String) :
    CTextModel.stringAppend (CTextModel.ofString left) (CTextModel.ofString right) =
      CTextModel.ofString (left ++ right) := by
  apply congrArg CTextModel.mk
  exact encodeUtf8String_append left right |>.symm

/-- The canonical length-bearing C Text bytes decode to the String they
represent. This connects the runtime byte record directly to the public
UTF-8 decoder, including embedded NUL characters. -/
theorem CTextModel.decode_ofString (text : String) :
    decodeUtf8 (CTextModel.ofString text).bytes = some text := by
  exact decodeUtf8_encodeUtf8String_exact text

/-- C-style concatenation of two canonical Text buffers decodes to the
corresponding String append. -/
theorem CTextModel.decode_stringAppend_ofString (left right : String) :
    decodeUtf8
        (CTextModel.stringAppend (CTextModel.ofString left)
          (CTextModel.ofString right)).bytes = some (left ++ right) := by
  rw [CTextModel.stringAppend_ofString]
  exact CTextModel.decode_ofString (left ++ right)

/-- C's byte-copy append preserves the canonical UTF-8 Text invariant. -/
theorem CTextModel.stringAppend_preserves_wellFormed
    (left right : CTextModel) (leftValid : CTextModel.WellFormed left)
    (rightValid : CTextModel.WellFormed right) :
    CTextModel.WellFormed (CTextModel.stringAppend left right) := by
  rcases leftValid with ⟨leftString, rfl⟩
  rcases rightValid with ⟨rightString, rfl⟩
  exact ⟨leftString ++ rightString, CTextModel.stringAppend_ofString _ _⟩

/-- Every well-formed runtime Text decodes to its represented source string. -/
theorem CTextModel.decode_wellFormed
    (text : CTextModel) (wellFormed : CTextModel.WellFormed text) :
    ∃ source, decodeUtf8 text.bytes = some source := by
  rcases wellFormed with ⟨source, rfl⟩
  exact ⟨source, CTextModel.decode_ofString source⟩

/-- Comparing the result of a C-style Text append with another canonical
Text value agrees with comparing the corresponding Lean strings. -/
theorem CTextModel.stringEqual_after_append_iff
    (left right expected : String) :
    CTextModel.stringEqual
        (CTextModel.stringAppend (CTextModel.ofString left)
          (CTextModel.ofString right))
        (CTextModel.ofString expected) = decide (left ++ right = expected) := by
  rw [CTextModel.stringAppend_ofString]
  exact CTextModel.stringEqual_ofString_iff (left ++ right) expected

theorem CTextModel.stringAppend_byteLength (left right : CTextModel) :
    (CTextModel.stringAppend left right).byteLength =
      left.byteLength + right.byteLength := by
  simp [CTextModel.stringAppend, CTextModel.byteLength, List.length_append]

/-- The byte-copy concatenation performed by C's `string-append` is
associative, including for buffers that contain embedded NUL bytes. -/
theorem CTextModel.stringAppend_assoc (first second third : CTextModel) :
    CTextModel.stringAppend (CTextModel.stringAppend first second) third =
      CTextModel.stringAppend first (CTextModel.stringAppend second third) := by
  simp [CTextModel.stringAppend, List.append_assoc]

/-- The empty length-bearing buffer is both identities for C's append. -/
theorem CTextModel.stringAppend_empty (text : CTextModel) :
    CTextModel.stringAppend text ⟨[]⟩ = text ∧
      CTextModel.stringAppend ⟨[]⟩ text = text := by
  simp [CTextModel.stringAppend]

/-- Decoding the two canonical UTF-8 buffers after C-style concatenation
returns the concatenated Lean string. -/
theorem decodeUtf8_encodeUtf8String_append (left right : String) :
    decodeUtf8 (encodeUtf8String left ++ encodeUtf8String right) =
      some (left ++ right) := by
  rw [← encodeUtf8String_append, decodeUtf8_encodeUtf8String_exact]


/-- The escaped NUL is preserved as an actual character in the Lean string.
This models C's length-bearing `Text`: an escaped U+0000 is data even though
the source spelling itself contains no NUL byte. -/
theorem readStringLiteral_preserves_embedded_nul :
    readStringLiteral "\"a\\u{0}b\"" =
      some (String.mk ['a', Char.ofNat 0, 'b']) := by decide

theorem readStringLiteral_cText_preserves_embedded_nul :
    (readStringLiteral "\"a\\u{0}b\"").map CTextModel.ofString =
      some ⟨[97, 0, 98]⟩ := by decide

/-- C's length-bearing Text operations preserve an embedded U+0000 as data:
the suffix after the NUL survives concatenation and the UTF-8 decoder recovers
the complete string. -/
theorem CTextModel.embeddedNul_append_is_lengthBearing :
    let nul := Char.ofNat 0
    let left := String.mk ['a', nul]
    let right := String.mk ['b']
    (CTextModel.stringAppend (CTextModel.ofString left)
      (CTextModel.ofString right)).bytes = [97, 0, 98] ∧
    (CTextModel.stringAppend (CTextModel.ofString left)
      (CTextModel.ofString right)).byteLength = 3 ∧
    decodeUtf8 (CTextModel.stringAppend (CTextModel.ofString left)
      (CTextModel.ofString right)).bytes = some (String.mk ['a', nul, 'b']) := by
  decide

theorem CTextModel.stringEqual_embeddedNul_not_prefix :
    CTextModel.stringEqual
      (CTextModel.ofString (String.mk ['a', Char.ofNat 0, 'b']))
      (CTextModel.ofString "a") = false := by
  rw [CTextModel.stringEqual_ofString_iff]
  decide

/-- Every successful source string literal produces a canonical runtime Text
buffer.  This connects the reader's escaped-string result to the invariant
used by the C-style byte-buffer model, for arbitrary literal contents. -/
theorem readStringLiteral_cText_wellFormed {spelling : String} {value : String}
    (_read : readStringLiteral spelling = some value) :
    CTextModel.WellFormed (CTextModel.ofString value) :=
  CTextModel.ofString_wellFormed value

/-- A successfully decoded source string literal can be recovered exactly
from its length-bearing UTF-8 runtime representation. -/
theorem readStringLiteral_cText_decodes_exactly {spelling : String} {value : String}
    (_read : readStringLiteral spelling = some value) :
    decodeUtf8 (CTextModel.ofString value).bytes = some value :=
  CTextModel.decode_ofString value

theorem readStringLiteral_unicode_scalar_roundtrips :
    readStringLiteral "\"λ😀\"" = some "λ😀" := by decide

theorem readCharacterLiteral_unicode_nul :
    readCharacterLiteral "#\\u{0}" = some (Char.ofNat 0) := by decide

theorem readCharacterLiteral_rejects_surrogate_escape :
    readCharacterLiteral "#\\u{D800}" = none := by decide

/-- Boundary cases for the C `unicode_escape` contract: the maximum Unicode
scalar is accepted, while out-of-range, empty, overlong, non-hex, and
partially consumed escapes are rejected. -/
theorem readCharacterLiteral_unicode_escape_boundaries :
    readCharacterLiteral "#\\u{10FFFF}" = some (Char.ofNat 0x10ffff) ∧
    readCharacterLiteral "#\\u{110000}" = none ∧
    readCharacterLiteral "#\\u{}" = none ∧
    readCharacterLiteral "#\\u{1234567}" = none ∧
    readCharacterLiteral "#\\u{12g}" = none ∧
    readCharacterLiteral "#\\u{41}x" = none := by
  decide

theorem readFloatLiteral_lexical {text : String} {value : Float}
    (read : readFloatLiteral text = some value) :
    floatLiteral text.toList = true := by
  unfold readFloatLiteral at read
  split at read
  · assumption
  · simp at read

theorem readFloatLiteral_satisfies_cFloatAtomSyntax {text : String} {value : Float}
    (read : readFloatLiteral text = some value) :
    cFloatAtomSyntax text.toList = true := by
  rw [cFloatAtomSyntax_eq_floatLiteral]
  exact readFloatLiteral_lexical read

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
