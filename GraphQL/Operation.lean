import GraphQL.Schema

/-! GraphQL operation representation
Spec reference: GraphQL September 2025.
- 2.3-2.4 Documents and Operations: this file models a single query-like operation, not
  a full executable document with multiple operations or operation kinds.
- 2.5-2.9 Selection Sets, Fields, Arguments, Aliases, and inline fragments: selection
  syntax is represented structurally, with aliases encoded as `responseName`.
- 2.10-2.13 Values, Variables, Type References, and Directives: variables and only the
  built-in executable directives `@skip` and `@include` are modeled.
- Layering note: this core operation syntax is fragment-free. Named fragment definitions
  and fragment spreads live in `GraphQL.NamedFragment` and can be translated to this core
  surface after inlining.
-/

namespace GraphQL

-- Spec 2.7 `Argument`: faithful shape for a name/value pair; directive arguments are only
-- modeled for built-ins elsewhere.
structure Argument where
  name : Name
  value : InputValue
deriving Repr

namespace Argument

-- Spec 5.3.2 field argument comparison: arguments are a set by name; source order is not
-- semantically relevant.
def equivalent (left right : Argument) : Prop :=
  left.name = right.name ∧ left.value.equivalent right.value

-- Spec 5.3.2 field argument comparison lifted to argument lists as unordered sets by
-- argument name.
def argumentsEquivalent (left right : List Argument) : Prop :=
  (∀ argument,
    argument ∈ left -> ∃ argument', argument' ∈ right ∧ argument.equivalent argument')
  ∧ (∀ argument,
      argument ∈ right -> ∃ argument', argument' ∈ left ∧ argument'.equivalent argument)

-- First value supplied for an argument name. Validation rejects duplicate names, so
-- executable operations have at most one matching entry.
def lookupValue? : List Argument -> Name -> Option InputValue
  | [], _name => none
  | argument :: rest, name =>
      if argument.name = name then some argument.value else lookupValue? rest name

end Argument

-- Spec 2.11 `VariableDefinition`: partial; name, type, and default are represented, but
-- descriptions and directives are omitted.
structure VariableDefinition where
  name : Name
  typeRef : TypeRef
  defaultValue : Option ConstInputValue := none
deriving Repr

-- Position-wise equivalence of the operation-variable names and defaults that affect
-- execution. Types are intentionally omitted because supplied values are assumed
-- already coerced and type-conformant at the modeled execution boundary.
def variableDefinitionsEquivalent
    : List VariableDefinition -> List VariableDefinition -> Prop
  | [], [] => True
  | left :: leftRest, right :: rightRest =>
      left.name = right.name
      ∧ match left.defaultValue, right.defaultValue with
        | none, none =>
            variableDefinitionsEquivalent leftRest rightRest
        | some leftDefault, some rightDefault =>
            InputValue.equivalent leftDefault.toInputValue rightDefault.toInputValue
            ∧ variableDefinitionsEquivalent leftRest rightRest
        | _, _ => False
  | _, _ => False

-- Spec 3.13.1 `@skip` and 3.13.2 `@include`: partial; only these two built-in executable
-- directives are represented, not arbitrary/custom directives or directive locations.
inductive DirectiveApplication where
  | skip (ifArgument : InputValue)
  | include (ifArgument : InputValue)
deriving Repr

-- Spec 2.5 `SelectionSet`, 2.6 `Field`, 2.8 `Alias`, and 2.9.2 `InlineFragment`:
-- partial; source grammar, named fragment spreads, and custom directives are omitted,
-- aliases are precomputed into response names.
inductive Selection where
  | field
    (responseName : Name)
    (fieldName : Name)
    (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection)
  | inlineFragment
    (typeCondition : Option Name)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection)
deriving Repr

-- Spec 2.4 `OperationType`: scoped to query operations for now.
inductive OperationType where
  | query
deriving Repr, DecidableEq

namespace OperationType

-- Spec 3.3.1 root operation type lookup, restricted to `query`.
def rootType (operationType : OperationType) (schema : Schema) : Name :=
  match operationType with
  | .query => schema.queryType

end OperationType

-- Spec 2.4 `OperationDefinition`: partial; document-level operation selection and
-- mutation/subscription operation kinds are omitted.
structure Operation where
  name : Option Name := none
  operationType : OperationType := .query
  variableDefinitions : List VariableDefinition := []
  selectionSet : List Selection
deriving Repr

namespace Operation

-- Spec 3.3.1 root operation type lookup for the operation's kind.
def rootType (operation : Operation) (schema : Schema) : Name :=
  operation.operationType.rootType schema

end Operation

mutual
  -- Non-spec structural metric used by recursive operation transformations.
  def Selection.size : Selection -> Nat
    | .field _ _ _ _ selectionSet => 1 + SelectionSet.size selectionSet
    | .inlineFragment _ _ selectionSet => 1 + SelectionSet.size selectionSet

  def SelectionSet.size : List Selection -> Nat
    | [] => 0
    | selection :: rest => selection.size + SelectionSet.size rest
end

-- Non-spec structural metric over operation selections.
def Operation.size (operation : Operation) : Nat :=
  SelectionSet.size operation.selectionSet

namespace Selection

-- Spec 2.8 `Alias` / response name: faithful for fields; non-field selections have no
-- response name.
def responseName? : Selection -> Option Name
  | .field responseName _fieldName _arguments _directives _selectionSet =>
      some responseName
  | _ => none

-- Spec 6.3.2 `CollectSubfields`: partial helper exposing a selection's nested selection
-- set.
def subselections : Selection -> List Selection
  | .field _responseName _fieldName _arguments _directives selectionSet => selectionSet
  | .inlineFragment _typeCondition _directives selectionSet => selectionSet

-- Spec 6.3.2 `CollectFields` helper: recognizes field selections.
def isField : Selection -> Prop
  | .field .. => True
  | _ => False

-- Spec 6.3.2 `CollectFields` helper: recognizes inline-fragment selections.
def isInlineFragment : Selection -> Prop
  | .inlineFragment .. => True
  | _ => False

end Selection

namespace SelectionSet

-- Spec 6.3.2 field collection groups by response name: partial helper that only filters
-- direct fields and does not traverse inline fragments.
def fieldsWithResponseName (responseName : Name) (selectionSet : List Selection)
    : List Selection :=
  selectionSet.filter
    (fun selection =>
      match selection.responseName? with
      | some name => name == responseName
      | none => false)

-- Spec 6.3.2 field collection helper: removes direct fields with one response name.
def withoutFieldSelectionsWithResponseName (responseName : Name)
    (selectionSet : List Selection)
    : List Selection :=
  selectionSet.filter
    (fun selection =>
      match selection.responseName? with
      | some name => !(name == responseName)
      | none => true)

-- Spec 6.3.2 `CollectSubfields` analogue: concatenates nested selection sets.
def mergeSelectionSets (selections : List Selection) : List Selection :=
  selections.foldl (fun merged selection => merged ++ selection.subselections) []

end SelectionSet

end GraphQL
