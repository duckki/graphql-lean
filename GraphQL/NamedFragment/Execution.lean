import GraphQL.Execution
import GraphQL.NamedFragment.Operation

/-! Fragment-aware execution for named-fragment operations. -/

namespace GraphQL
namespace NamedFragment
namespace Execution

abbrev ResolverValue (ObjectRef : Type := PUnit) :=
  GraphQL.Execution.ResolverValue ObjectRef

abbrev ResponseValue := GraphQL.Execution.ResponseValue
abbrev Response := GraphQL.Execution.Response
abbrev Result (α : Type) := GraphQL.Execution.Result α

abbrev Resolvers (ObjectRef : Type := PUnit) :=
  GraphQL.Execution.Resolvers ObjectRef

abbrev VariableValues := GraphQL.Execution.VariableValues

variable {ObjectRef : Type}

-- Fragment-aware operation entry point for the modeled default-value portion of spec
-- 6.1.2 `CoerceVariableValues`.
def coerceVariableValues (operation : Operation) (variableValues : VariableValues)
    : VariableValues :=
  operation.variableDefinitions.foldl
    (fun coercedValues variableDefinition =>
      match GraphQL.Execution.lookupVariableValue? coercedValues
              variableDefinition.name with
      | some _value => coercedValues
      | none =>
          match variableDefinition.defaultValue with
          | some defaultValue =>
              (variableDefinition.name, defaultValue.toInputValue) :: coercedValues
          | none => coercedValues)
    variableValues

structure ExecutableField where
  parentType : Name
  responseName : Name
  fieldName : Name
  arguments : List Argument
  selectionSet : List Selection
  availableFragments : List FragmentDefinition
deriving Repr

def addExecutableGroup (group : Name × List ExecutableField)
    : List (Name × List ExecutableField) -> List (Name × List ExecutableField)
  | [] => [group]
  | (responseName, fields) :: rest =>
      if responseName == group.fst then
        (responseName, fields ++ group.snd) :: rest
      else
        (responseName, fields) :: addExecutableGroup group rest

def mergeExecutableGroups (left right : List (Name × List ExecutableField))
    : List (Name × List ExecutableField) :=
  right.foldl (fun grouped group => addExecutableGroup group grouped) left

-- Spec 6.3.2 `CollectFields` mutates `visitedFragments` while traversing a selection
-- set. The executable model returns that context explicitly so sibling selections can
-- continue with the fragment names visited by earlier selections.
structure CollectFieldsResult where
  groupedFields : List (Name × List ExecutableField)
  visitedFragments : List Name
deriving Repr

mutual
  def collectSelection (schema : Schema) (variableValues : VariableValues)
      : List FragmentDefinition -> List Name -> Name -> ResolverValue ObjectRef
        -> Selection -> CollectFieldsResult
    | fragments,
      visitedFragments,
      parentType,
      _source,
      .field responseName fieldName arguments directives selectionSet =>
        if GraphQL.Execution.selectionDirectivesAllowBool variableValues directives then
          {
            groupedFields :=
              [(
                responseName,
                [{
                  parentType := parentType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet,
                  availableFragments := fragments
                }]
              )]
            visitedFragments := visitedFragments
          }
        else
          { groupedFields := [], visitedFragments := visitedFragments }
    | fragments,
      visitedFragments,
      parentType,
      source,
      .inlineFragment none directives selectionSet =>
        if GraphQL.Execution.selectionDirectivesAllowBool variableValues directives then
          collectFields schema variableValues fragments visitedFragments parentType source
            selectionSet
        else
          { groupedFields := [], visitedFragments := visitedFragments }
    | fragments,
      visitedFragments,
      parentType,
      source,
      .inlineFragment (some typeCondition) directives selectionSet =>
        if GraphQL.Execution.selectionDirectivesAllowBool variableValues directives then
          if GraphQL.Execution.doesFragmentTypeApplyBool schema parentType
              source typeCondition then
            collectFields schema variableValues fragments visitedFragments parentType
              source selectionSet
          else
            { groupedFields := [], visitedFragments := visitedFragments }
        else
          { groupedFields := [], visitedFragments := visitedFragments }
    | fragments,
      visitedFragments,
      parentType,
      source,
      .fragmentSpread fragmentName directives =>
        if GraphQL.Execution.selectionDirectivesAllowBool variableValues directives then
          if fragmentName ∈ visitedFragments then
            { groupedFields := [], visitedFragments := visitedFragments }
          else
            let visitedFragments := fragmentName :: visitedFragments
            match lookupFragmentAndRestLt? fragmentName fragments with
            | none => { groupedFields := [], visitedFragments := visitedFragments }
            | some (fragment, remainingFragments) =>
                if GraphQL.Execution.doesFragmentTypeApplyBool schema
                    parentType source fragment.typeCondition then
                  collectFields schema variableValues remainingFragments.val
                    visitedFragments parentType source fragment.selectionSet
                else
                  { groupedFields := [], visitedFragments := visitedFragments }
        else
          { groupedFields := [], visitedFragments := visitedFragments }
  termination_by fragments _visitedFragments _parentType _source selection =>
    (fragments.length, sizeOf selection, 0)
  decreasing_by
    all_goals
      simp_wf
      try
        first
        | apply Prod.Lex.left
          exact remainingFragments.property
        | apply Prod.Lex.right
          apply Prod.Lex.left
          omega
        | apply Prod.Lex.right
          apply Prod.Lex.right
          omega

  def collectFields (schema : Schema) (variableValues : VariableValues)
      : List FragmentDefinition -> List Name -> Name -> ResolverValue ObjectRef
        -> List Selection -> CollectFieldsResult
    | _fragments, visitedFragments, _parentType, _source, [] =>
        { groupedFields := [], visitedFragments := visitedFragments }
    | fragments, visitedFragments, parentType, source, selection :: rest =>
        let selected :=
          collectSelection schema variableValues fragments visitedFragments parentType
            source selection
        let remaining :=
          collectFields schema variableValues fragments selected.visitedFragments
            parentType source rest
        {
          groupedFields :=
            mergeExecutableGroups selected.groupedFields remaining.groupedFields
          visitedFragments := remaining.visitedFragments
        }
  termination_by fragments _visitedFragments _parentType _source selectionSet =>
    (fragments.length, sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

def collectSubfields
    (schema : Schema) (variableValues : VariableValues)
    (objectType : Name) (objectValue : ResolverValue ObjectRef)
    : List ExecutableField -> List (Name × List ExecutableField)
  | [] => []
  | field :: fields =>
      mergeExecutableGroups
        (collectFields schema variableValues field.availableFragments [] objectType
          objectValue field.selectionSet).groupedFields
        (collectSubfields schema variableValues objectType objectValue fields)

mutual
  def executeCollectedFields
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (source : ResolverValue ObjectRef)
      : List (Name × List ExecutableField) -> Result (List (Name × ResponseValue))
    | [] => .ok ([], 0)
    | (responseName, fields) :: rest =>
        let head :=
          executeField schema resolvers variableValues fuel source responseName fields
        let tail :=
          executeCollectedFields schema resolvers variableValues fuel source rest
        GraphQL.Execution.Result.combine List.append head tail

  def executeField
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (source : ResolverValue ObjectRef)
      (responseName : Name)
      : List ExecutableField -> Result (List (Name × ResponseValue))
    | [] => .error 1
    | field :: fields =>
        match fuel with
        | 0 => GraphQL.Execution.outOfFuel
        | fuel' + 1 =>
            match schema.lookupField field.parentType field.fieldName with
            | none => .error 1
            | some fieldDefinition =>
                match resolvers.resolve field.parentType field.fieldName
                        field.arguments source with
                | none =>
                    GraphQL.Execution.singleFieldResult responseName
                      (GraphQL.Execution.handleFieldError fieldDefinition.outputType)
                | some resolved =>
                    GraphQL.Execution.singleFieldResult responseName
                      (completeValue schema resolvers variableValues
                        fuel' fieldDefinition.outputType (field :: fields)
                        resolved)

  def completeValue
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : Nat -> TypeRef -> List ExecutableField -> ResolverValue ObjectRef
        -> Result ResponseValue
    | 0, _fieldType, _fields, _value =>
        GraphQL.Execution.outOfFuel
    | fuel, .nonNull inner, fields, value =>
        GraphQL.Execution.nonNullCompletion
          (completeValue schema resolvers variableValues fuel inner fields value)
    | _fuel + 1, _fieldType, _fields, .null =>
        .ok (.null, 0)
    | _fuel + 1, .named typeName, _fields, .scalar value =>
        if (TypeRef.named typeName).isCompositeBool schema then
          .error 1
        else
          .ok (.scalar value, 0)
    | fuel + 1,
      .named parentType,
      fields,
      source@(.object runtimeType _ref) =>
        if schema.typeIncludesObjectBool parentType runtimeType then
          let completed :=
            executeCollectedFields schema resolvers variableValues fuel
              source
              (collectSubfields schema variableValues runtimeType source fields)
          GraphQL.Execution.catchBubbleAsNull
            GraphQL.Execution.ResponseValue.object completed
        else
          .error 1
    | fuel + 1, .list inner, fields, .list values =>
        let completed :=
          completeValueList schema resolvers variableValues fuel inner fields values
        GraphQL.Execution.catchBubbleAsNull GraphQL.Execution.ResponseValue.list completed
    | _fuel + 1, .named _typeName, _fields, .list _values =>
        .error 1
    | _fuel + 1, .list _inner, _fields, _value =>
        .error 1

  def completeValueList
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (fuel : Nat) (itemType : TypeRef)
      (fields : List ExecutableField)
      : List (ResolverValue ObjectRef) -> Result (List ResponseValue)
    | [] => .ok ([], 0)
    | value :: values =>
        let head :=
          completeValue schema resolvers variableValues fuel itemType fields value
        let tail :=
          completeValueList schema resolvers variableValues fuel itemType fields values
        GraphQL.Execution.Result.combine List.cons head tail
end

def executeRootSelectionSet
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    (fragments : List FragmentDefinition)
    : List Selection -> Result (List (Name × ResponseValue))
  | selectionSet =>
      executeCollectedFields schema resolvers variableValues
        fuel source
        (collectFields schema variableValues fragments [] parentType source
          selectionSet).groupedFields

def executeQueryFuelBound (operation : Operation) : Nat :=
  operation.size * 3 + 1

def rootSourceAppliesBool
    (schema : Schema) (operation : Operation)
    (source : ResolverValue ObjectRef)
    : Bool :=
  match GraphQL.Execution.runtimeObjectType? source with
  | some objectName =>
      schema.typeIncludesObjectBool (operation.rootType schema) objectName
  | none => false

def executeQueryWithFuel
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    : Response :=
  let coercedVariableValues := coerceVariableValues operation variableValues
  if rootSourceAppliesBool schema operation source then
    let completed :=
      executeRootSelectionSet schema resolvers coercedVariableValues
        fuel (operation.rootType schema) source operation.fragmentDefinitions
        operation.selectionSet
    match completed with
    | .error errors => { data := .null, errors := errors }
    | .ok (fields, errors) => { data := .object fields, errors := errors }
  else
    { data := .null, errors := 1 }

def executeQuery
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectRef)
    : Response :=
  executeQueryWithFuel schema resolvers variableValues operation
    (executeQueryFuelBound operation) source

end Execution

namespace Semantics

def operationsEquivalent (schema : Schema) (left right : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
      variableValues fuel (source : Execution.ResolverValue ObjectRef),
    Execution.executeQueryWithFuel schema resolvers variableValues left fuel source
    = Execution.executeQueryWithFuel schema resolvers variableValues right fuel source

def operationsSemanticallyEquivalent (schema : Schema) (left right : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
      variableValues fuel (source : Execution.ResolverValue ObjectRef),
    GraphQL.Execution.Response.semanticEquivalent
      (Execution.executeQueryWithFuel schema resolvers variableValues left fuel source)
      (Execution.executeQueryWithFuel schema resolvers variableValues right fuel source)

end Semantics
end NamedFragment
end GraphQL
