import GraphQL.Operation

/-! Separate operation syntax for incremental-delivery draft PR #1110 at 045e193.

DirectiveApplication, Selection, and Operation belong to GraphQL.IncrementalDelivery.
The main GraphQL syntax remains unchanged. Schema/input values, field arguments,
variable definitions, and the query operation kind are shared with the main model.
Named fragments and incremental-directive validation remain outside this module.
-/

namespace GraphQL
namespace IncrementalDelivery

/-- Spec 3.13 and incremental-delivery draft PR #1110. Defaults are represented in
constructor arguments; raw values remain permissive, with locations and argument validity
left to validation. Incremental validation and named-fragment delivery are not modeled in
this module yet.
-/
inductive DirectiveApplication where
  | skip (ifArgument : InputValue)
  | include (ifArgument : InputValue)
  | defer (ifArgument : InputValue := .boolean true) (label : Option InputValue := none)
  | stream (ifArgument : InputValue := .boolean true) (label : Option InputValue := none)
    (initialCount : InputValue := .int 0)
deriving Repr

/-- Spec 2.5 `SelectionSet`, 2.6 `Field`, 2.8 `Alias`, and 2.9.2 `InlineFragment`:
partial; source grammar, named fragment spreads, and custom directives are omitted,
aliases are precomputed into response names.
-/
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

/-- Spec 2.4 `OperationDefinition`: partial; document-level operation selection and
mutation/subscription operation kinds are omitted.
-/
structure Operation where
  name : Option Name := none
  operationType : OperationType := .query
  variableDefinitions : List VariableDefinition := []
  selectionSet : List Selection
deriving Repr

namespace Operation

/-- Spec 3.3.1 root operation type lookup for the operation's kind. -/
def rootType (operation : Operation) (schema : Schema) : Name :=
  operation.operationType.rootType schema

end Operation

mutual
  /-- Non-spec structural metric used by recursive operation transformations. -/
  def Selection.size : Selection -> Nat
    | .field _ _ _ _ selectionSet => 1 + SelectionSet.size selectionSet
    | .inlineFragment _ _ selectionSet => 1 + SelectionSet.size selectionSet

  def SelectionSet.size : List Selection -> Nat
    | [] => 0
    | selection :: rest => selection.size + SelectionSet.size rest
end

/-- Non-spec structural metric over operation selections. -/
def Operation.size (operation : Operation) : Nat :=
  SelectionSet.size operation.selectionSet

namespace Selection

/-- Spec 2.8 `Alias` / response name: faithful for fields; non-field selections have no
response name.
-/
def responseName? : Selection -> Option Name
  | .field responseName _fieldName _arguments _directives _selectionSet =>
      some responseName
  | _ => none

/-- Spec 6.3.2 `CollectSubfields`: partial helper exposing a selection's nested selection
set.
-/
def subselections : Selection -> List Selection
  | .field _responseName _fieldName _arguments _directives selectionSet => selectionSet
  | .inlineFragment _typeCondition _directives selectionSet => selectionSet

/-- Spec 6.3.2 `CollectFields` helper: recognizes field selections. -/
def isField : Selection -> Prop
  | .field .. => True
  | _ => False

/-- Spec 6.3.2 `CollectFields` helper: recognizes inline-fragment selections. -/
def isInlineFragment : Selection -> Prop
  | .inlineFragment .. => True
  | _ => False

end Selection

end IncrementalDelivery
end GraphQL
