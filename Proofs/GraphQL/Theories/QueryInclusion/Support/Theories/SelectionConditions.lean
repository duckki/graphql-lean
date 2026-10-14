import GraphQL.Theories.QueryInclusion

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.SelectionConditions

open GraphQL.Execution

inductive BooleanLiteral where
  | positive (variableName : Name)
  | negative (variableName : Name)
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

end GraphQL.SelectionConditions

namespace GraphQL.SelectionConditions.BooleanLiteral

open GraphQL.Execution

def variableName : BooleanLiteral -> Name
  | .positive variableName => variableName
  | .negative variableName => variableName

end GraphQL.SelectionConditions.BooleanLiteral

namespace GraphQL.SelectionConditions

open GraphQL.Execution

inductive BranchCondition where
  | typeCondition (typeName : Name)
  | booleanLiteral (literal : BooleanLiteral)
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

end GraphQL.SelectionConditions

namespace GraphQL.SelectionConditions.BranchCondition

open GraphQL.Execution

def parentType (condition : BranchCondition) (currentParentType : Name) : Name :=
  match condition with
  | .typeCondition typeName => typeName
  | .booleanLiteral _literal => currentParentType

end GraphQL.SelectionConditions.BranchCondition
