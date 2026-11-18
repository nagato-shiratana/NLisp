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
  !characters.isEmpty && characters.all Char.isDigit

def unsignedCharacters (characters : List Char) : List Char :=
  match characters with
  | '-' :: tail => tail
  | other => other

def integerLiteral (characters : List Char) : Bool :=
  match unsignedCharacters characters with
  | ['0'] => true
  | first :: tail => ('1' ≤ first && first ≤ '9') && tail.all Char.isDigit
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
      if !first.isDigit then false else
      match unsigned.dropWhile Char.isDigit with
      | '.' :: fraction =>
          match fraction with
          | digit :: _ => digit.isDigit && exponentLiteral (fraction.dropWhile Char.isDigit)
          | [] => false
      | _ => false
  | [] => false

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
