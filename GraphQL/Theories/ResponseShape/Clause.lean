import GraphQL.Theories.ResponseShape.Syntax

/-! Executable Boolean-clause operations for response shapes. -/

namespace GraphQL

namespace ResponseShape

/-- Checks that names occur in strict ascending order. -/
def namesStrictlyIncreasing : List Name -> Bool
  | [] => true
  | [_name] => true
  | left :: right :: rest =>
      decide (left < right) && namesStrictlyIncreasing (right :: rest)

namespace Clause

/-- Inserts a literal into variable-name order. -/
def insertLiteralSorted (literal : BoolLiteral) : List BoolLiteral -> List BoolLiteral
  | [] => [literal]
  | candidate :: rest =>
      if literal.1 <= candidate.1 then
        literal :: candidate :: rest
      else
        candidate :: insertLiteralSorted literal rest

/-- Canonical variable-name ordering for a conjunction's literals. -/
def sortLiterals : List BoolLiteral -> List BoolLiteral
  | [] => []
  | literal :: rest => insertLiteralSorted literal (sortLiterals rest)

/-- Canonicalizes a clause without repairing duplicate or unsupported variables. -/
def canonical (clause : Clause) : Clause :=
  { literals := sortLiterals clause.literals }

/--
Checks the raw-clause invariant: strict variable-name order and membership in the
declared Boolean support. Strict order also excludes duplicate and contradictory
literals. The empty clause is valid.
-/
def validBool (support : List NormalForm.BoolVar) (clause : Clause) : Bool :=
  namesStrictlyIncreasing (clause.literals.map Prod.fst)
  && clause.literals.all (fun literal => support.contains literal.1)

/-- A canonical, noncontradictory conjunction over a declared Boolean support. -/
def Valid (support : List NormalForm.BoolVar) (clause : Clause) : Prop :=
  clause.validBool support = true

instance instDecidableValid (support : List NormalForm.BoolVar) (clause : Clause)
    : Decidable (clause.Valid support) := by
  unfold Valid
  infer_instance

/-- Checks whether every literal in a clause agrees with an assignment. -/
def holdsInBool (assignment : NormalForm.BoolCase) (clause : Clause) : Bool :=
  clause.literals.all
    (fun literal => assignment.lookup? literal.1 == some literal.2)

/-- A clause is active when all of its literals agree with the assignment. -/
def HoldsIn (assignment : NormalForm.BoolCase) (clause : Clause) : Prop :=
  ∀ literal ∈ clause.literals,
    assignment.lookup? literal.1 = some literal.2

instance instDecidableHoldsIn (assignment : NormalForm.BoolCase) (clause : Clause)
    : Decidable (clause.HoldsIn assignment) := by
  unfold HoldsIn
  infer_instance

/-- Checks that a valid clause assigns every support variable exactly once. -/
def completeMintermBool
    (support : List NormalForm.BoolVar) (clause : Clause) : Bool :=
  decide support.Nodup
  && clause.validBool support
  && support.all
      (fun varName =>
        clause.literals.any (fun literal => literal.1 == varName))

/-- A canonical complete assignment of one Boolean value to every support variable. -/
def CompleteMinterm
    (support : List NormalForm.BoolVar) (clause : Clause) : Prop :=
  clause.completeMintermBool support = true

instance instDecidableCompleteMinterm
    (support : List NormalForm.BoolVar) (clause : Clause)
    : Decidable (clause.CompleteMinterm support) := by
  unfold CompleteMinterm
  infer_instance

end Clause

end ResponseShape

end GraphQL
