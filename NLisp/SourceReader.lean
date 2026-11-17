import NLisp.CExpansion

namespace NLisp.SourceReader
open CMacroCopy

inductive Token where
  | left
  | right
  | atom : String → Nat → Token
  deriving DecidableEq, Repr

def whitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n' || c.toNat == 11 || c.toNat == 12

def delimiter (c : Char) : Bool :=
  c == '(' || c == ')' || c == ';' || c == '"' || whitespace c

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
        else if c == ';' then previous (tail.dropWhile (fun char => char != '\r' && char != '\n')) index reversed
        else if c == '(' then previous tail (index + 1) (.left :: reversed)
        else if c == ')' then previous tail (index + 1) (.right :: reversed)
        else if c == '"' then
          let (content, remaining) ← stringCharacters tail
          if !stringValid (content.length + 1) content then none else
          let text := String.mk ('"' :: (content ++ ['"']))
          previous remaining (index + 1) (.atom text (3 * (index + 1) + 1) :: reversed)
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
              previous remaining (index + 1) (.atom text (3 * (index + 1) + 1) :: reversed)
          | _ =>
              let (content, remaining) := atomCharacters (c :: tail)
              let text := String.mk content
              if text.startsWith "#%nlisp" then none else
              previous remaining (index + 1) (.atom text (3 * (index + 1) + 1) :: reversed)
        else
          let (content, remaining) := atomCharacters (c :: tail)
          previous remaining (index + 1) (.atom (String.mk content) (3 * (index + 1) + 1) :: reversed))

def lex (fuel : Nat) (characters : List Char) (index : Nat) : Option (List Token) :=
  lexLoop fuel characters index []

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
          | .atom name identity :: tail => some (.atom ⟨name, none, identity⟩, tail)
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

def readWithFuel (lexFuel parseFuel : Nat) (source : String) : Option (List Tree) := do
  let characters := source.toList
  if characters.any (fun c => c.toNat == 0) then none else
  let tokens ← lex lexFuel characters 0
  (parseOperations parseFuel).forms tokens

def read (source : String) : Option (List Tree) := do
  let characters := source.toList
  if characters.any (fun c => c.toNat == 0) then none else
  let tokens ← lex (characters.length + 1) characters 0
  (parseOperations (4 * tokens.length + 4)).forms tokens

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
