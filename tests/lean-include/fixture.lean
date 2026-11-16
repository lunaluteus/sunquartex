/-!
## Lean source inclusion

Documentation should become prose while declarations stay in code blocks.
-/

namespace LeanIncludeFixture

def ordinary : String := "/- not documentation -/"
def escaped : String := "\"/- still a string -/\""
def raw : String := r#"A "quote" followed by /- raw text -/"#
def moreHashes : String := r##"A "# followed by /- raw text -/"##
def rawBackslash : String := r"ends in a backslash\"
def interpolated : String := s!"value {"/-"} and /- literal text -/"
def interpolatedNested : String := s!"value {s!"inner {"/-"}"} and /- literal text -/"
def quote : Char := '"'
def «/- quoted identifier -/» : Nat := 7

-- A line comment containing /- must stay in the code block.
def afterLineComment : Nat := 11

/-
Outer documentation before the nested comment.
/- A nested comment. -/
Outer documentation after the nested comment.
-/
def afterNested : Nat := 13

/-No leading whitespace is required.-/
def afterNoSpace : Nat := 17

/-!-/
/-- An empty block comment follows this declaration. -/
def beforeEmpty : Nat := 19
/- -/
def afterEmpty : Nat := 23

def openerOnly : String := "/-"
def finalDeclaration : Nat := 29

end LeanIncludeFixture
