import NLisp.CExpansion

namespace NLisp.SourceReader
open CMacroCopy

inductive Token where
  | left
  | right
  | atom : (text : String) → (identity : Nat) → identity % 3 = 1 → Token
  deriving DecidableEq

instance : Repr Token where
  reprPrec token _ :=
    match token with
    | .left => "Token.left"
    | .right => "Token.right"
    | .atom text identity _ =>
        "Token.atom " ++ repr text ++ " " ++ repr identity

def Token.sourceIdentityClass : Token → Prop
  | .left | .right => True
  | .atom _ identity _ => identity % 3 = 1

/-- Source atoms reserve the residue class `1 mod 3`; macro-generated binders
use `2 mod 3`, while the remaining class is available to internal markers. -/
def sourceAtom (text : String) (index : Nat) : Token :=
  .atom text (3 * (index + 1) + 1) (by omega)

theorem sourceAtom_identity_class (text : String) (index : Nat) :
    (sourceAtom text index).sourceIdentityClass := by
  unfold Token.sourceIdentityClass sourceAtom
  omega

theorem Token.sourceIdentityClass_holds (token : Token) : token.sourceIdentityClass := by
  cases token with
  | left => trivial
  | right => trivial
  | atom _ _ proof => exact proof

/-- Identity numbers carried by source-atom lexer tokens. Delimiters have no
identity and are omitted. -/
def sourceTokenIdentities : List Token → List Nat
  | [] => []
  | .atom _ identity _ :: tail => identity :: sourceTokenIdentities tail
  | _ :: tail => sourceTokenIdentities tail

theorem sourceTokenIdentities_have_source_class (tokens : List Token) :
    ∀ identity, identity ∈ sourceTokenIdentities tokens → identity % 3 = 1 := by
  induction tokens with
  | nil => simp [sourceTokenIdentities]
  | cons token tail ih =>
      cases token with
      | left => simpa [sourceTokenIdentities] using ih
      | right => simpa [sourceTokenIdentities] using ih
      | atom name identity identityClass =>
          intro current member
          simp only [sourceTokenIdentities, List.mem_cons] at member
          rcases member with same | later
          · cases same
            exact identityClass
          · exact ih current later

def whitespace := Lexical.whitespace

def delimiter := Lexical.delimiter

def atomCharacters : List Char → List Char × List Char
  | [] => ([], [])
  | c :: tail =>
      if delimiter c then ([], c :: tail) else
      let (chunk, remaining) := atomCharacters tail
      (c :: chunk, remaining)

def stringCharacters : List Char → Option (List Char × List Char)
  | [] => none
  | '"' :: tail => some ([], tail)
  | '\\' :: escaped :: tail => do
      let (chunk, remaining) ← stringCharacters tail
      pure ('\\' :: escaped :: chunk, remaining)
  | '\\' :: [] => none
  | c :: tail => do
      let (chunk, remaining) ← stringCharacters tail
      pure (c :: chunk, remaining)

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def scalar (value : Nat) : Bool :=
  value ≤ 0x10ffff && !(0xd800 ≤ value && value ≤ 0xdfff)

def unicodeDigits : List Char → Nat → Nat → Option (List Char)
  | [], _, _ => none
  | '}' :: tail, value, count =>
      if 0 < count && count ≤ 6 && scalar value then some tail else none
  | c :: tail, value, count => do
      if count ≥ 6 then none else
      let digit ← hexValue c
      unicodeDigits tail (value * 16 + digit) (count + 1)

def stringValid : Nat → List Char → Bool
  | 0, _ => false
  | _ + 1, [] => true
  | fuel + 1, '\\' :: escaped :: tail =>
      if escaped == 'u' then
        match tail with
        | '{' :: digits =>
            match unicodeDigits digits 0 0 with
            | some remaining => stringValid fuel remaining
            | none => false
        | _ => false
      else if escaped == 'n' || escaped == 'r' || escaped == 't' || escaped == '"' || escaped == '\\' then
        stringValid fuel tail
      else false
  | _ + 1, '\\' :: [] => false
  | fuel + 1, _ :: tail => stringValid fuel tail

def characterValid (characters : List Char) : Bool :=
  match characters with
  | [_] => true
  | 'u' :: '{' :: digits =>
      match unicodeDigits digits 0 0 with
      | some [] => true
      | _ => false
  | other => String.mk other == "newline" || String.mk other == "space" || String.mk other == "tab"

/- An explicit primitive recursion with a token accumulator keeps closed
source checks linear in space, without retaining the whole lexer call stack. -/
def lexLoop : Nat → List Char → Nat → List Token → Option (List Token) :=
  Nat.rec (fun _ _ _ => none) (fun _ previous characters index reversed =>
    match characters with
    | [] => some reversed.reverse
    | c :: tail => do
        if whitespace c then previous tail index reversed
        else if c == ';' then previous (tail.dropWhile (fun char => !Lexical.lineEnding char)) index reversed
        else if c == '(' then previous tail (index + 1) (.left :: reversed)
        else if c == ')' then previous tail (index + 1) (.right :: reversed)
        else if c == '"' then
          let (content, remaining) ← stringCharacters tail
          if !stringValid (content.length + 1) content then none else
          let text := String.mk ('"' :: (content ++ ['"']))
          previous remaining (index + 1) (sourceAtom text index :: reversed)
        else if c == '#' then
          match tail with
          | '\\' :: rest =>
              let (content, remaining) := match rest with
                | next :: afterNext =>
                    if next == '(' || next == ')' || next == ';' || next == '"' then
                      ([next], afterNext)
                    else atomCharacters rest
                | [] => ([], [])
              if !characterValid content then none else
              let text := String.mk ('#' :: '\\' :: content)
              previous remaining (index + 1) (sourceAtom text index :: reversed)
          | _ =>
              let (content, remaining) := atomCharacters (c :: tail)
              let text := String.mk content
              if text.startsWith "#%nlisp" then none else
              previous remaining (index + 1) (sourceAtom text index :: reversed)
        else
          let (content, remaining) := atomCharacters (c :: tail)
          previous remaining (index + 1) (sourceAtom (String.mk content) index :: reversed))

def lex (fuel : Nat) (characters : List Char) (index : Nat) : Option (List Token) :=
  lexLoop fuel characters index []

/-- The token type carries the source-identity invariant, so it holds for all
atoms in every successful lexer result without a separate assumption about the
lexer branch that emitted them. -/
theorem lex_success_sourceIdentityClass (fuel : Nat) (characters : List Char)
    (index : Nat) (tokens : List Token)
    (_success : lex fuel characters index = some tokens) :
    ∀ token, token ∈ tokens → token.sourceIdentityClass := by
  intro token _member
  exact Token.sourceIdentityClass_holds token

structure ParseOperations where
  expression : List Token → Option (Tree × List Token)
  children : List Token → Option (List Tree × List Token)
  forms : List Token → Option (List Tree)

def parseOperations : Nat → ParseOperations
  | 0 => ⟨fun _ => none, fun _ => none, fun _ => none⟩
  | fuel + 1 =>
      let previous := parseOperations fuel
      { expression := fun tokens =>
          match tokens with
          | .left :: tail => do
              let (items, remaining) ← previous.children tail
              pure (.list items, remaining)
          | .atom name identity _ :: tail => some (.atom ⟨name, none, identity⟩, tail)
          | _ => none
        children := fun tokens =>
          match tokens with
          | .right :: tail => some ([], tail)
          | [] => none
          | other => do
              let (head, remaining) ← previous.expression other
              let (tail, final) ← previous.children remaining
              pure (head :: tail, final)
        forms := fun tokens =>
          match tokens with
          | [] => some []
          | other => do
              let (head, remaining) ← previous.expression other
              return head :: (← previous.forms remaining) }

/-- Trees parsed from source tokens preserve the reserved source-identity
residue class on every atom. -/
inductive SourceIdentityTree : Tree → Prop where
  | atom (value : Atom) (sourceClass : value.token % 3 = 1) :
      SourceIdentityTree (.atom value)
  | list (items : List Tree)
      (children : ∀ child, child ∈ items → SourceIdentityTree child) :
      SourceIdentityTree (.list items)

theorem parseOperations_right_expression_none (fuel : Nat) (tail : List Token) :
    (parseOperations fuel).expression (.right :: tail) = none := by
  cases fuel <;> rfl

/-- Every successful expression, child-list, or top-level form parse retains
the token class carried by source atoms. This is a parser-wide invariant, not
only the direct atom parsing case. -/
theorem parseOperations_preserves_sourceIdentityClass (fuel : Nat) :
    (∀ tokens tree rest, (parseOperations fuel).expression tokens = some (tree, rest) →
      SourceIdentityTree tree) ∧
    (∀ tokens trees rest, (parseOperations fuel).children tokens = some (trees, rest) →
      ∀ tree, tree ∈ trees → SourceIdentityTree tree) ∧
    (∀ tokens trees, (parseOperations fuel).forms tokens = some trees →
      ∀ tree, tree ∈ trees → SourceIdentityTree tree) := by
  induction fuel with
  | zero =>
      simp only [parseOperations]
      refine ⟨?_, ?_, ?_⟩ <;> intro _tokens <;> simp
  | succ fuel ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro tokens tree rest parsed
        simp only [parseOperations] at parsed
        cases tokens with
        | nil => simp at parsed
        | cons token tail =>
            cases token with
            | left =>
                simp only [parseOperations] at parsed
                obtain ⟨childResult, childrenParsed, outputEq⟩ :=
                  Option.bind_eq_some.mp parsed
                rcases childResult with ⟨items, remaining⟩
                have pairEq : (Tree.list items, remaining) = (tree, rest) :=
                  Option.some.inj outputEq
                rcases Prod.mk.inj pairEq with ⟨treeEq, restEq⟩
                cases treeEq
                cases restEq
                apply SourceIdentityTree.list
                intro child member
                exact ih.2.1 tail items rest childrenParsed child member
            | right => simp at parsed
            | atom name identity identityClass =>
                simp only at parsed
                cases parsed
                exact SourceIdentityTree.atom ⟨name, none, identity⟩ identityClass
      · intro tokens trees rest parsed tree member
        simp only [parseOperations] at parsed
        cases tokens with
        | nil => simp at parsed
        | cons token tail =>
            cases token with
            | right =>
                simp only at parsed
                have pairEq := Option.some.inj parsed
                rcases Prod.mk.inj pairEq with ⟨treesEq, restEq⟩
                cases treesEq
                cases restEq
                simp at member
            | left =>
                simp only at parsed
                obtain ⟨headResult, headParsed, tailParsed⟩ :=
                  Option.bind_eq_some.mp parsed
                rcases headResult with ⟨head, remaining⟩
                obtain ⟨tailResult, tailParsed, outputEq⟩ :=
                  Option.bind_eq_some.mp tailParsed
                rcases tailResult with ⟨tailTrees, final⟩
                have pairEq : (head :: tailTrees, final) = (trees, rest) :=
                  Option.some.inj outputEq
                rcases Prod.mk.inj pairEq with ⟨treesEq, restEq⟩
                cases treesEq
                cases restEq
                simp only [List.mem_cons] at member
                rcases member with same | later
                · subst tree
                  exact ih.1 (Token.left :: tail) head remaining headParsed
                · exact ih.2.1 remaining tailTrees rest tailParsed tree later
            | atom name identity identityClass =>
                simp only at parsed
                obtain ⟨headResult, headParsed, tailParsed⟩ :=
                  Option.bind_eq_some.mp parsed
                rcases headResult with ⟨head, remaining⟩
                obtain ⟨tailResult, tailParsed, outputEq⟩ :=
                  Option.bind_eq_some.mp tailParsed
                rcases tailResult with ⟨tailTrees, final⟩
                have pairEq : (head :: tailTrees, final) = (trees, rest) :=
                  Option.some.inj outputEq
                rcases Prod.mk.inj pairEq with ⟨treesEq, restEq⟩
                cases treesEq
                cases restEq
                simp only [List.mem_cons] at member
                rcases member with same | later
                · subst tree
                  exact ih.1 (Token.atom name identity identityClass :: tail) head remaining headParsed
                · exact ih.2.1 remaining tailTrees rest tailParsed tree later
      · intro tokens trees parsed tree member
        simp only [parseOperations] at parsed
        cases tokens with
        | nil =>
            have treesEq : ([] : List Tree) = trees := Option.some.inj parsed
            cases treesEq
            simp at member
        | cons token tail =>
            cases token with
            | left =>
                simp only at parsed
                obtain ⟨headResult, headParsed, tailParsed⟩ :=
                  Option.bind_eq_some.mp parsed
                rcases headResult with ⟨head, remaining⟩
                obtain ⟨tailTrees, formsParsed, treesEq⟩ :=
                  Option.bind_eq_some.mp tailParsed
                have listEq : head :: tailTrees = trees := Option.some.inj treesEq
                cases listEq
                simp only [List.mem_cons] at member
                rcases member with same | later
                · subst tree
                  exact ih.1 (Token.left :: tail) head remaining headParsed
                · exact ih.2.2 remaining tailTrees formsParsed tree later
            | right =>
                simp only [parseOperations_right_expression_none] at parsed
                simp at parsed
            | atom name identity identityClass =>
                simp only at parsed
                obtain ⟨headResult, headParsed, tailParsed⟩ :=
                  Option.bind_eq_some.mp parsed
                rcases headResult with ⟨head, remaining⟩
                obtain ⟨tailTrees, formsParsed, treesEq⟩ :=
                  Option.bind_eq_some.mp tailParsed
                have listEq : head :: tailTrees = trees := Option.some.inj treesEq
                cases listEq
                simp only [List.mem_cons] at member
                rcases member with same | later
                · subst tree
                  exact ih.1 (Token.atom name identity identityClass :: tail) head remaining headParsed
                · exact ih.2.2 remaining tailTrees formsParsed tree later

theorem parseOperations_atom_preserves_identity (fuel : Nat) (name : String)
    (identity : Nat) (identityClass : identity % 3 = 1) (tail : List Token) :
    (parseOperations (fuel + 1)).expression (.atom name identity identityClass :: tail) =
      some (.atom ⟨name, none, identity⟩, tail) := rfl

theorem parseOperations_atom_preserves_sourceIdentityClass (fuel : Nat) (name : String)
    (identity : Nat) (identityClass : identity % 3 = 1) (tail : List Token) :
    ∃ tree, (parseOperations (fuel + 1)).expression
        (.atom name identity identityClass :: tail) = some (tree, tail) ∧
      match tree with
      | .atom atom => atom.token % 3 = 1
      | .list _ => False := by
  exact ⟨.atom ⟨name, none, identity⟩,
    parseOperations_atom_preserves_identity fuel name identity identityClass tail,
    identityClass⟩

def readWithFuel (lexFuel parseFuel : Nat) (source : String) : Option (List Tree) := do
  let characters := source.toList
  if characters.any (fun c => c.toNat == 0) then none else
  let tokens ← lex lexFuel characters 0
  (parseOperations parseFuel).forms tokens

theorem readWithFuel_success_iff (lexFuel parseFuel : Nat) (source : String)
    (trees : List Tree) :
    readWithFuel lexFuel parseFuel source = some trees ↔
      source.toList.any (fun c => c.toNat == 0) = false ∧
      ∃ tokens, lex lexFuel source.toList 0 = some tokens ∧
        (parseOperations parseFuel).forms tokens = some trees := by
  unfold readWithFuel
  by_cases hasNul : source.toList.any (fun c => c.toNat == 0) = true
  · simp [hasNul]
  · simp only [Bool.not_eq_true] at hasNul
    simp only [hasNul, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
    cases lexResult : lex lexFuel source.toList 0 with
    | none => simp [lexResult]
    | some tokens => simp [lexResult]

/-- A successful full source read preserves the reserved identity class on
every atom in the parsed form list. -/
theorem readWithFuel_success_sourceIdentityClass
    (lexFuel parseFuel : Nat) (source : String) (trees : List Tree)
    (read : readWithFuel lexFuel parseFuel source = some trees) :
    ∀ tree, tree ∈ trees → SourceIdentityTree tree := by
  obtain ⟨_noNul, tokens, _lexed, parsed⟩ :=
    (readWithFuel_success_iff lexFuel parseFuel source trees).mp read
  exact (parseOperations_preserves_sourceIdentityClass parseFuel).2.2
    tokens trees parsed

/-- Every failed bounded source read is accounted for by one of the reader's
three explicit rejection points: embedded NUL, lexical failure, or a parse
failure after successful lexing. -/
theorem readWithFuel_failure_iff (lexFuel parseFuel : Nat) (source : String) :
    readWithFuel lexFuel parseFuel source = none ↔
      source.toList.any (fun c => c.toNat == 0) = true ∨
      lex lexFuel source.toList 0 = none ∨
      ∃ tokens, lex lexFuel source.toList 0 = some tokens ∧
        (parseOperations parseFuel).forms tokens = none := by
  unfold readWithFuel
  by_cases hasNul : source.toList.any (fun c => c.toNat == 0) = true
  · simp [hasNul]
  · simp [hasNul]
    cases lexResult : lex lexFuel source.toList 0 with
    | none => simp [lexResult]
    | some tokens =>
        cases parseResult : (parseOperations parseFuel).forms tokens <;>
          simp [lexResult, parseResult]

/-- Read an explicit-length UTF-8 byte sequence through the validated byte
decoder and then the ordinary source reader. This provides the byte-oriented
entry point corresponding to the C reader's input representation. -/
def readBytesWithFuel (lexFuel parseFuel : Nat) (bytes : List UInt8) :
    Option (List Tree) := do
  let source ← Lexical.decodeUtf8 bytes
  readWithFuel lexFuel parseFuel source

/-- Explicit failure classes for the byte-oriented source reader.  The order
matches the actual pipeline: UTF-8 decoding, embedded-NUL rejection, lexing,
then parsing. -/
inductive SourceReadFailure where
  | invalidUtf8
  | embeddedNul
  | lexical
  | parse
  deriving DecidableEq, Repr

/-- Public status classes used by the C file-processing API. -/
inductive CReaderStatus where
  | ioError
  | parseError
  deriving DecidableEq, Repr

def CReaderStatus.code : CReaderStatus → Nat
  | .ioError => 3
  | .parseError => 4

def SourceReadFailure.cStatus : SourceReadFailure → CReaderStatus
  | .invalidUtf8 | .embeddedNul | .lexical | .parse => .parseError

theorem SourceReadFailure.cStatus_parseError (failure : SourceReadFailure) :
    failure.cStatus = .parseError := by
  cases failure <;> rfl

/-- Failures before bytes reach the source reader are C I/O errors; failures
inside the UTF-8/lexer/parser pipeline are parse errors. -/
inductive CFileReadFailure where
  | openFile
  | size
  | read
  | source (failure : SourceReadFailure)
  deriving DecidableEq, Repr

def CFileReadFailure.status : CFileReadFailure → CReaderStatus
  | .openFile | .size | .read => .ioError
  | .source failure => failure.cStatus

theorem CFileReadFailure.status_classification (failure : CFileReadFailure) :
    failure.status = .ioError ∨ failure.status = .parseError := by
  cases failure with
  | openFile => exact Or.inl rfl
  | size => exact Or.inl rfl
  | read => exact Or.inl rfl
  | source sourceFailure => exact Or.inr sourceFailure.cStatus_parseError

theorem CFileReadFailure.status_code (failure : CFileReadFailure) :
    failure.status.code =
      match failure with
      | .openFile | .size | .read => 3
      | .source _ => 4 := by
  cases failure with
  | openFile => rfl
  | size => rfl
  | read => rfl
  | source sourceFailure => cases sourceFailure <;> rfl

/-- Classify a failed byte read at its first rejecting stage.  This retains
more information than the public `Option` reader result and is the Lean-side
target for connecting reader diagnostics to runtime errors. -/
def readBytesFailureKind (lexFuel parseFuel : Nat) (bytes : List UInt8) :
    Option SourceReadFailure :=
  match Lexical.decodeUtf8 bytes with
  | none => some .invalidUtf8
  | some source =>
      if source.toList.any (fun c => c.toNat == 0) then some .embeddedNul
      else
        match lex lexFuel source.toList 0 with
        | none => some .lexical
        | some tokens =>
            match (parseOperations parseFuel).forms tokens with
            | none => some .parse
            | some _ => none

/-- The byte reader fails exactly when its prioritized failure classifier
returns one of the four explicit rejection reasons. -/
theorem readBytesFailureKind_some_iff (lexFuel parseFuel : Nat)
    (bytes : List UInt8) :
    (∃ kind, readBytesFailureKind lexFuel parseFuel bytes = some kind) ↔
      readBytesWithFuel lexFuel parseFuel bytes = none := by
  unfold readBytesFailureKind readBytesWithFuel
  cases decoded : Lexical.decodeUtf8 bytes with
  | none => simp [decoded]
  | some source =>
      by_cases hasNul : source.toList.any (fun c => c.toNat == 0) = true
      · have nulWitness : ∃ c, c ∈ source.toList ∧ c.toNat == 0 := by
          simpa only [List.any_eq_true] using hasNul
        simp [decoded, hasNul, readWithFuel, List.any_eq_true, nulWitness]
        intro noNul
        intro tokens _tokensLexed
        obtain ⟨c, hmem, hzero⟩ := nulWitness
        exfalso
        exact (noNul c hmem) (by simpa using hzero)
      · cases lexResult : lex lexFuel source.toList 0 with
        | none => simp [decoded, hasNul, lexResult, readWithFuel, List.any_eq_true]
        | some tokens =>
            cases parseResult : (parseOperations parseFuel).forms tokens with
            | none => simp [decoded, hasNul, lexResult, parseResult, readWithFuel,
                List.any_eq_true]
            | some trees =>
                have allNonzero : ∀ c ∈ source.toList, c.toNat ≠ 0 := by
                  intro c hmem hzero
                  apply hasNul
                  apply List.any_eq_true.mpr
                  exact ⟨c, hmem, by simp [hzero]⟩
                have allNonzeroProp : ∀ c ∈ source.toList, ¬ c.toNat = 0 := by
                  exact allNonzero
                simp [decoded, hasNul, lexResult, parseResult, readWithFuel,
                  List.any_eq_true, allNonzero, allNonzeroProp]
                exact allNonzeroProp

/-- Collapse the detailed byte-reader diagnostic partition to the public C
status returned by the file-processing API. Every reader-stage rejection is a
parse error; file opening and I/O failures are represented separately by
`CFileReadFailure`. -/
def readBytesFailureStatus (lexFuel parseFuel : Nat) (bytes : List UInt8) :
    Option CReaderStatus :=
  (readBytesFailureKind lexFuel parseFuel bytes).map SourceReadFailure.cStatus

theorem readBytesFailureStatus_parseError_iff (lexFuel parseFuel : Nat)
    (bytes : List UInt8) :
    readBytesFailureStatus lexFuel parseFuel bytes = some .parseError ↔
      readBytesWithFuel lexFuel parseFuel bytes = none := by
  cases kindResult : readBytesFailureKind lexFuel parseFuel bytes with
  | none =>
      have success := (readBytesFailureKind_some_iff lexFuel parseFuel bytes).2
      simp [readBytesFailureStatus, kindResult] at success
      simp [readBytesFailureStatus, kindResult, success]
  | some kind =>
      have failure := (readBytesFailureKind_some_iff lexFuel parseFuel bytes).1
        ⟨kind, kindResult⟩
      have status := SourceReadFailure.cStatus_parseError kind
      simp [readBytesFailureStatus, kindResult, status, failure]

/-- Invalid UTF-8 is reported as the first failure class exactly when byte
decoding rejects the input. -/
theorem readBytesFailureKind_invalidUtf8_iff (lexFuel parseFuel : Nat)
    (bytes : List UInt8) :
    readBytesFailureKind lexFuel parseFuel bytes = some .invalidUtf8 ↔
      Lexical.decodeUtf8 bytes = none := by
  cases decoded : Lexical.decodeUtf8 bytes with
  | none => simp [readBytesFailureKind, decoded]
  | some source =>
      by_cases hasNul : source.toList.any (fun c => c.toNat == 0) = true
      · simp [readBytesFailureKind, decoded, hasNul]
      · cases lexResult : lex lexFuel source.toList 0 with
        | none => simp [readBytesFailureKind, decoded, hasNul, lexResult]
        | some tokens =>
            cases parseResult : (parseOperations parseFuel).forms tokens <;>
              simp [readBytesFailureKind, decoded, hasNul, lexResult, parseResult]

/-- Embedded NUL is classified before lexing, after successful UTF-8 decoding. -/
theorem readBytesFailureKind_embeddedNul_iff (lexFuel parseFuel : Nat)
    (bytes : List UInt8) :
    readBytesFailureKind lexFuel parseFuel bytes = some .embeddedNul ↔
      ∃ source, Lexical.decodeUtf8 bytes = some source ∧
        source.toList.any (fun c => c.toNat == 0) = true := by
  unfold readBytesFailureKind
  constructor
  · intro classified
    cases decoded : Lexical.decodeUtf8 bytes with
    | none => simp [decoded] at classified
    | some source =>
        by_cases hasNul : source.toList.any (fun c => c.toNat == 0) = true
        · exact ⟨source, rfl, hasNul⟩
        · cases lexResult : lex lexFuel source.toList 0 with
          | none => simp [decoded, hasNul, lexResult] at classified
          | some tokens =>
              cases parseResult : (parseOperations parseFuel).forms tokens <;>
                simp [decoded, hasNul, lexResult, parseResult] at classified
  · rintro ⟨source, decoded, hasNul⟩
    simp [decoded, hasNul]

theorem readBytesFailureKind_lexical_iff (lexFuel parseFuel : Nat)
    (bytes : List UInt8) :
    readBytesFailureKind lexFuel parseFuel bytes = some .lexical ↔
      ∃ source, Lexical.decodeUtf8 bytes = some source ∧
        source.toList.any (fun c => c.toNat == 0) ≠ true ∧
        lex lexFuel source.toList 0 = none := by
  unfold readBytesFailureKind
  constructor
  · intro classified
    cases decoded : Lexical.decodeUtf8 bytes with
    | none => simp [decoded] at classified
    | some source =>
        by_cases hasNul : source.toList.any (fun c => c.toNat == 0) = true
        · simp [decoded, hasNul] at classified
        · cases lexResult : lex lexFuel source.toList 0 with
          | none => exact ⟨source, rfl, hasNul, lexResult⟩
          | some tokens =>
              exfalso
              cases parseResult : (parseOperations parseFuel).forms tokens <;>
                simp [decoded, hasNul, lexResult, parseResult] at classified
  · rintro ⟨source, decoded, hasNul, lexResult⟩
    simp [decoded, hasNul, lexResult]

theorem readBytesFailureKind_parse_iff (lexFuel parseFuel : Nat)
    (bytes : List UInt8) :
    readBytesFailureKind lexFuel parseFuel bytes = some .parse ↔
      ∃ source tokens, Lexical.decodeUtf8 bytes = some source ∧
        source.toList.any (fun c => c.toNat == 0) ≠ true ∧
        lex lexFuel source.toList 0 = some tokens ∧
        (parseOperations parseFuel).forms tokens = none := by
  unfold readBytesFailureKind
  constructor
  · intro classified
    cases decoded : Lexical.decodeUtf8 bytes with
    | none => simp [decoded] at classified
    | some source =>
        by_cases hasNul : source.toList.any (fun c => c.toNat == 0) = true
        · simp [decoded, hasNul] at classified
        · cases lexResult : lex lexFuel source.toList 0 with
          | none => simp [decoded, hasNul, lexResult] at classified
          | some tokens =>
              cases parseResult : (parseOperations parseFuel).forms tokens with
              | none => exact ⟨source, tokens, rfl, hasNul, lexResult, parseResult⟩
              | some trees => simp [decoded, hasNul, lexResult, parseResult] at classified
  · rintro ⟨source, tokens, decoded, hasNul, lexResult, parseResult⟩
    simp [decoded, hasNul, lexResult, parseResult]

theorem readBytesWithFuel_success_iff (lexFuel parseFuel : Nat)
    (bytes : List UInt8) (trees : List Tree) :
    readBytesWithFuel lexFuel parseFuel bytes = some trees ↔
      ∃ source, Lexical.decodeUtf8 bytes = some source ∧
        readWithFuel lexFuel parseFuel source = some trees := by
  unfold readBytesWithFuel
  cases decoded : Lexical.decodeUtf8 bytes <;> simp [decoded]

/-- Full success contract for the byte-oriented reader. It exposes the UTF-8
decode, embedded-NUL check, lexer token stream, and parser result in the same
left-to-right order as the implementation. -/
theorem readBytesWithFuel_success_pipeline (lexFuel parseFuel : Nat)
    (bytes : List UInt8) (trees : List Tree) :
    readBytesWithFuel lexFuel parseFuel bytes = some trees ↔
      ∃ source tokens,
        Lexical.decodeUtf8 bytes = some source ∧
        source.toList.any (fun c => c.toNat == 0) = false ∧
        lex lexFuel source.toList 0 = some tokens ∧
        (parseOperations parseFuel).forms tokens = some trees := by
  rw [readBytesWithFuel_success_iff]
  constructor
  · rintro ⟨source, decoded, readSuccess⟩
    obtain ⟨noNul, tokens, lexed, parsed⟩ :=
      (readWithFuel_success_iff lexFuel parseFuel source trees).mp readSuccess
    exact ⟨source, tokens, decoded, noNul, lexed, parsed⟩
  · rintro ⟨source, tokens, decoded, noNul, lexed, parsed⟩
    exact ⟨source, decoded,
      (readWithFuel_success_iff lexFuel parseFuel source trees).mpr
        ⟨noNul, tokens, lexed, parsed⟩⟩

theorem readBytesWithFuel_failure_iff (lexFuel parseFuel : Nat)
    (bytes : List UInt8) :
    readBytesWithFuel lexFuel parseFuel bytes = none ↔
      Lexical.decodeUtf8 bytes = none ∨
      ∃ source, Lexical.decodeUtf8 bytes = some source ∧
        readWithFuel lexFuel parseFuel source = none := by
  unfold readBytesWithFuel
  cases decoded : Lexical.decodeUtf8 bytes <;> simp [decoded]

def read (source : String) : Option (List Tree) := do
  let characters := source.toList
  if characters.any (fun c => c.toNat == 0) then none else
  let tokens ← lex (characters.length + 1) characters 0
  (parseOperations (4 * tokens.length + 4)).forms tokens

theorem read_failure_iff (source : String) :
    read source = none ↔
      source.toList.any (fun c => c.toNat == 0) = true ∨
      lex (source.toList.length + 1) source.toList 0 = none ∨
      ∃ tokens,
        lex (source.toList.length + 1) source.toList 0 = some tokens ∧
        (parseOperations (4 * tokens.length + 4)).forms tokens = none := by
  unfold read
  by_cases hasNul : source.toList.any (fun c => c.toNat == 0) = true
  · simp [hasNul]
  · simp [hasNul]
    cases lexResult : lex (source.toList.length + 1) source.toList 0 with
    | none => simp [lexResult]
    | some tokens =>
        cases parseResult : (parseOperations (4 * tokens.length + 4)).forms tokens <;>
          simp [lexResult, parseResult]

def flattenEntry : Tree → Option Tree
  | .list (.atom name :: tail) =>
      if tail.length = 2 ∨ tail.length = 3 then
        some (.list (.atom ⟨"defun", none, 0⟩ :: .atom name :: tail))
      else none
  | _ => none

def flattenForm (tree : Tree) : Option (List Tree) :=
  match tree with
  | .list (head :: tail) =>
      if named head "defrec" then
        match tail with
        | [.list entries@(_ :: _)] => entries.mapM flattenEntry
        | _ => none
      else some [tree]
  | _ => some [tree]

def normalize (forms : List Tree) : Option (List Tree) := do
  pure (← forms.mapM flattenForm).join

end NLisp.SourceReader
