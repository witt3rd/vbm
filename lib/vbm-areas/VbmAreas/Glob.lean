/-! # The glob language (S2)

A pattern is a `String`; the working form is its `toList`. `*` matches any run of characters (including `/` and the empty run), `?` exactly one character, everything else is literal; case-sensitive; the whole path must match. Malformed patterns and working directories are refused with a typed `Glob.Reason`. -/
namespace VbmAreas

/-- A path or a pattern in working form. -/
abbrev Chars := List Char

/-- Why a pattern or a working directory is refused (closed). `wildcard` is raised for a working directory only. -/
inductive Glob.Reason where
  | empty | forbiddenChar | leadingSlash | leadingDotSlash | trailingSlash | doubleSlash | dotDotSegment | wildcard
  deriving DecidableEq, Repr

/-- The characters no pattern may contain: `[ ] \ { }`. -/
def Glob.forbiddenChar (c : Char) : Bool := c == '[' || c == ']' || c == '\\' || c == '{' || c == '}'

/-- The two wildcard characters. -/
def Glob.isWild (c : Char) : Bool := c == '*' || c == '?'

/-- Split on `/`; never empty (`""` is one empty segment). -/
def Glob.segments : Chars → List Chars
  | [] => [[]]
  | c :: cs =>
    match Glob.segments cs with
    | s :: rest => if c = '/' then [] :: s :: rest else (c :: s) :: rest
    | [] => [[c]]

/-- The text contains `//`. -/
def Glob.hasDoubleSlash : Chars → Bool
  | '/' :: '/' :: _ => true
  | _ :: cs => Glob.hasDoubleSlash cs
  | [] => false

/-- The first refusal of a pattern, in the order of the contract; `none` = accepted. -/
def Glob.refusalChars (g : Chars) : Option Glob.Reason :=
  if g.isEmpty then some .empty
  else if g.any Glob.forbiddenChar then some .forbiddenChar
  else if g.head? = some '/' then some .leadingSlash
  else if ['.', '/'].isPrefixOf g then some .leadingDotSlash
  else if g.getLast? = some '/' then some .trailingSlash
  else if Glob.hasDoubleSlash g then some .doubleSlash
  else if (Glob.segments g).any (· == ['.', '.']) then some .dotDotSegment
  else none

/-- The refusal of a glob pattern. -/
def Glob.refusal (g : String) : Option Glob.Reason := Glob.refusalChars g.toList

/-- A glob pattern is valid exactly when it is not refused. -/
def Glob.valid (g : String) : Bool := decide (Glob.refusal g = none)

/-- The refusal of a working directory: the pattern rules, and no `*` or `?`. -/
def Glob.cwdRefusal (c : String) : Option Glob.Reason :=
  match Glob.refusal c with
  | some r => some r
  | none => if c.toList.any Glob.isWild then some .wildcard else none

/-- A working directory is valid exactly when it is not refused. -/
def Glob.validCwd (c : String) : Bool := decide (Glob.cwdRefusal c = none)

/-- Some suffix of the text (the text itself, then shorter, down to the empty one) satisfies `f`. -/
def Glob.anySuffix (f : Chars → Bool) : Chars → Bool
  | [] => f []
  | s@(_ :: t) => f s || Glob.anySuffix f t

/-- The matcher over characters: structural on the pattern, the star case runs over the suffixes of the path. -/
def Glob.matchChars : Chars → Chars → Bool
  | [], s => s.isEmpty
  | '*' :: ps, s => Glob.anySuffix (fun t => Glob.matchChars ps t) s
  | '?' :: ps, _ :: s => Glob.matchChars ps s
  | '?' :: _, [] => false
  | c :: ps, d :: s => c == d && Glob.matchChars ps s
  | _ :: _, [] => false

/-- `Glob.matches pat path`: the whole path matches the pattern. -/
def Glob.matches (pat path : String) : Bool := Glob.matchChars pat.toList path.toList

/-- The segments before the first one containing `*` or `?`; the last segment (the file part) never counts. -/
def Glob.dirSegs : List Chars → List Chars
  | [] => []
  | [_] => []
  | s :: rest => if s.any Glob.isWild then [] else s :: Glob.dirSegs rest

/-- Join segments with `/`. -/
def Glob.join : List Chars → Chars
  | [] => []
  | [s] => s
  | s :: rest => s ++ '/' :: Glob.join rest

/-- The directory a glob starts in, `""` for the root. -/
def Glob.startDir (g : String) : String := String.ofList (Glob.join (Glob.dirSegs (Glob.segments g.toList)))

/-- `xs` is a proper prefix of `ys`. -/
def Glob.properPrefix : List Chars → List Chars → Bool
  | [], _ :: _ => true
  | x :: xs, y :: ys => x == y && Glob.properPrefix xs ys
  | _, _ => false

/-- A path lies strictly under a directory, by whole segments; every non-empty path lies under the root `""`. -/
def Glob.under (dir path : String) : Bool :=
  Glob.properPrefix (if dir.isEmpty then [] else Glob.segments dir.toList) (Glob.segments path.toList)

end VbmAreas
