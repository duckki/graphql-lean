import GraphQL.NamedFragment.Operation
import GraphQL.Validation

/-! Validation predicates for fragment-aware operations. -/

namespace GraphQL
namespace NamedFragment

namespace Validation

def fragmentNamesUnique (fragments : List FragmentDefinition) : Prop :=
  (fragments.map FragmentDefinition.name).Nodup

mutual
  def selectionFragmentSpreadNames : Selection -> List Name
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        selectionSetFragmentSpreadNames selectionSet
    | .inlineFragment _typeCondition _directives selectionSet =>
        selectionSetFragmentSpreadNames selectionSet
    | .fragmentSpread fragmentName _directives => [fragmentName]

  def selectionSetFragmentSpreadNames : List Selection -> List Name
    | [] => []
    | selection :: rest =>
        selectionFragmentSpreadNames selection ++ selectionSetFragmentSpreadNames rest
end

def fragmentReachableBool (fragments : List FragmentDefinition)
    : Nat -> Name -> Name -> Bool
  | 0, _source, _target => false
  | fuel + 1, source, target =>
      match GraphQL.NamedFragment.lookupFragment? fragments source with
      | none => false
      | some fragment =>
          let direct := selectionSetFragmentSpreadNames fragment.selectionSet
          direct.any (fun next => next == target)
          || direct.any
              (fun next =>
                fragmentReachableBool fragments fuel next target)

def fragmentsAcyclicBool (fragments : List FragmentDefinition) : Bool :=
  fragments.all
    (fun fragment =>
      !(fragmentReachableBool fragments fragments.length fragment.name fragment.name))

def fragmentsAcyclic (fragments : List FragmentDefinition) : Prop :=
  fragmentsAcyclicBool fragments = true

def fragmentSpreadNameReachableFromSelectionSetBool (fragments : List FragmentDefinition)
    : Nat -> List Name -> Name -> Bool
  | 0, _frontier, _target => false
  | fuel + 1, frontier, target =>
      frontier.any (fun name => name == target)
      || frontier.any
          (fun name =>
            match GraphQL.NamedFragment.lookupFragment? fragments name with
            | none => false
            | some fragment =>
                fragmentSpreadNameReachableFromSelectionSetBool fragments fuel
                  (selectionSetFragmentSpreadNames fragment.selectionSet) target)

def fragmentDefinitionUsed (operation : Operation) (fragment : FragmentDefinition)
    : Prop :=
  fragmentSpreadNameReachableFromSelectionSetBool operation.fragmentDefinitions
    operation.fragmentDefinitions.length
    (selectionSetFragmentSpreadNames operation.selectionSet)
    fragment.name
  = true

def allFragmentDefinitionsUsed (operation : Operation) : Prop :=
  ∀ fragment,
    fragment ∈ operation.fragmentDefinitions -> fragmentDefinitionUsed operation fragment

mutual
  -- Spec 5.8.4 variable uses in an operation scope. Following a fragment spread
  -- removes the found definition just as inlining does, so this traversal is
  -- structurally terminating and includes transitively referenced fragments.
  def selectionVariables : List FragmentDefinition -> Selection -> List Name
    | fragments,
      .field _responseName _fieldName arguments directives selectionSet =>
        GraphQL.Validation.argumentsVariables arguments
        ++ GraphQL.Validation.directivesVariables directives
        ++ selectionSetVariables fragments selectionSet
    | fragments, .inlineFragment _typeCondition directives selectionSet =>
        GraphQL.Validation.directivesVariables directives
        ++ selectionSetVariables fragments selectionSet
    | fragments, .fragmentSpread fragmentName directives =>
        GraphQL.Validation.directivesVariables directives
        ++ match lookupFragmentAndRestLt? fragmentName fragments with
            | none => []
            | some (fragment, remainingFragments) =>
                selectionSetVariables remainingFragments.val fragment.selectionSet
  termination_by fragments selection => (fragments.length, sizeOf selection, 0)
  decreasing_by
    all_goals
      try subst fragments
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

  def selectionSetVariables : List FragmentDefinition -> List Selection -> List Name
    | _fragments, [] => []
    | fragments, selection :: rest =>
        selectionVariables fragments selection ++ selectionSetVariables fragments rest
  termination_by fragments selectionSet => (fragments.length, sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      try subst fragments
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

-- Spec 5.8.4 All Variables Used, including transitively referenced fragments.
def operationVariablesUsed (operation : Operation) : Prop :=
  ∀ variableDefinition,
    variableDefinition ∈ operation.variableDefinitions
    -> variableDefinition.name
        ∈ selectionSetVariables operation.fragmentDefinitions operation.selectionSet

mutual
  def selectionValid (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (fragments : List FragmentDefinition)
      (parentType : Name)
      : Selection -> Prop
    | .field _responseName fieldName arguments directives selectionSet =>
        GraphQL.Validation.directivesValid schema variableDefinitions directives
        ∧ ∃ fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
            ∧ GraphQL.Validation.argumentsValid schema
                fieldDefinition.arguments variableDefinitions arguments
            ∧ fieldSelectionSetValid schema variableDefinitions fragments
                fieldDefinition selectionSet
    | .inlineFragment none directives selectionSet =>
        GraphQL.Validation.directivesValid schema variableDefinitions directives
        ∧ selectionSet ≠ []
        ∧ selectionSetValid schema variableDefinitions fragments parentType selectionSet
    | .inlineFragment (some typeCondition) directives selectionSet =>
        GraphQL.Validation.directivesValid schema variableDefinitions directives
        ∧ schema.isCompositeType typeCondition
        ∧ schema.typesOverlap parentType typeCondition
        ∧ selectionSet ≠ []
        ∧ selectionSetValid schema variableDefinitions fragments
            typeCondition selectionSet
    | .fragmentSpread fragmentName directives =>
        GraphQL.Validation.directivesValid schema variableDefinitions directives
        ∧ ∃ fragment,
            GraphQL.NamedFragment.lookupFragment? fragments fragmentName = some fragment
            ∧ schema.isCompositeType fragment.typeCondition
            ∧ schema.typesOverlap parentType fragment.typeCondition

  def selectionSetValid (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (fragments : List FragmentDefinition)
      (parentType : Name) (selectionSet : List Selection)
      : Prop :=
    ∀ selection,
      selection ∈ selectionSet
      -> selectionValid schema variableDefinitions fragments parentType selection

  def fieldSelectionSetValid (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (fragments : List FragmentDefinition)
      (fieldDefinition : FieldDefinition) (selectionSet : List Selection)
      : Prop :=
    let returnType := fieldDefinition.outputType.namedType
    fieldDefinition.outputType.isOutputType schema
    ∧ ((schema.isLeafType returnType ∧ selectionSet = [])
        ∨ (schema.isCompositeType returnType
            ∧ selectionSet ≠ []
            ∧ selectionSetValid schema variableDefinitions fragments
                returnType selectionSet))
end

def fragmentDefinitionValid (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (fragments : List FragmentDefinition)
    (fragment : FragmentDefinition)
    : Prop :=
  schema.isCompositeType fragment.typeCondition
  ∧ fragment.selectionSet ≠ []
  ∧ selectionSetValid schema variableDefinitions fragments
      fragment.typeCondition fragment.selectionSet

def allFragmentDefinitionsValid (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (fragments : List FragmentDefinition)
    : Prop :=
  ∀ fragment,
    fragment ∈ fragments
    -> fragmentDefinitionValid schema variableDefinitions fragments fragment

namespace FieldMerge

structure ScopedField where
  parentType : Name
  responseName : Name
  fieldName : Name
  arguments : List Argument
  outputType : TypeRef
  selectionSet : List Selection
  availableFragments : List FragmentDefinition
deriving Repr

mutual
  def collectSelection (schema : Schema)
      : List FragmentDefinition -> Name -> Selection -> List ScopedField
    | fragments,
      parentType,
      .field responseName fieldName arguments _directives selectionSet =>
        match schema.lookupField parentType fieldName with
        | none => []
        | some fieldDefinition =>
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              outputType := fieldDefinition.outputType,
              selectionSet := selectionSet,
              availableFragments := fragments
            }]
    | fragments,
      parentType,
      .inlineFragment none _directives selectionSet =>
        collectFields schema fragments parentType selectionSet
    | fragments,
      _parentType,
      .inlineFragment (some typeCondition) _directives selectionSet =>
        collectFields schema fragments typeCondition selectionSet
    | fragments,
      _parentType,
      .fragmentSpread fragmentName _directives =>
        match lookupFragmentAndRestLt? fragmentName fragments with
        | none => []
        | some (fragment, remainingFragments) =>
            collectFields schema remainingFragments.val fragment.typeCondition
              fragment.selectionSet
  termination_by fragments _parentType selection =>
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

  def collectFields (schema : Schema)
      : List FragmentDefinition -> Name -> List Selection -> List ScopedField
    | _fragments, _parentType, [] => []
    | fragments, parentType, selection :: rest =>
        collectSelection schema fragments parentType selection
        ++ collectFields schema fragments parentType rest
  termination_by fragments _parentType selectionSet =>
    (fragments.length, sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

mutual
  inductive FieldsInSetCanMerge (schema : Schema) (fragments : List FragmentDefinition)
      : Name -> List Selection -> Prop where
    | intro (parentType : Name) (selectionSet : List Selection)
      (hfields
        : let fields := collectFields schema fragments parentType selectionSet
          ∀ left,
            left ∈ fields
            -> ∀ right,
                right ∈ fields
                -> left.responseName = right.responseName
                -> FieldsForNameCanMerge schema fragments left right)
      : FieldsInSetCanMerge schema fragments parentType selectionSet

  inductive FieldsForNameCanMerge (schema : Schema) (fragments : List FragmentDefinition)
      : ScopedField -> ScopedField -> Prop where
    | intro (left right : ScopedField)
      (hshape
        : GraphQL.FieldMerge.sameResponseShape schema left.outputType right.outputType)
      (hidentity
        : (left.parentType = right.parentType
            ∨ ¬ schema.objectType left.parentType
            ∨ ¬ schema.objectType right.parentType)
          -> left.fieldName = right.fieldName
              ∧ Argument.argumentsEquivalent left.arguments right.arguments)
      (hsubfields
        : (left.parentType = right.parentType
            ∨ ¬ schema.objectType left.parentType
            ∨ ¬ schema.objectType right.parentType)
          -> ∀ objectType,
              let fields :=
                collectFields schema left.availableFragments objectType left.selectionSet
                ++ collectFields schema right.availableFragments objectType
                    right.selectionSet
              ∀ subLeft,
                subLeft ∈ fields
                -> ∀ subRight,
                    subRight ∈ fields
                    -> subLeft.responseName = subRight.responseName
                    -> FieldsForNameCanMerge schema fragments subLeft subRight)
      : FieldsForNameCanMerge schema fragments left right
end

def fieldsInSetCanMerge (schema : Schema)
    (fragments : List FragmentDefinition)
    (parentType : Name) (selectionSet : List Selection)
    : Prop :=
  FieldsInSetCanMerge schema fragments parentType selectionSet

end FieldMerge

def operationDefinitionValid (schema : Schema) (operation : Operation) : Prop :=
  operation.operationType = .query
  ∧ schema.isCompositeType (operation.rootType schema)
  ∧ GraphQL.Validation.variableDefinitionsValid schema operation.variableDefinitions
  ∧ fragmentNamesUnique operation.fragmentDefinitions
  ∧ fragmentsAcyclic operation.fragmentDefinitions
  ∧ allFragmentDefinitionsUsed operation
  ∧ allFragmentDefinitionsValid schema operation.variableDefinitions
      operation.fragmentDefinitions
  ∧ operation.selectionSet ≠ []
  ∧ selectionSetValid schema operation.variableDefinitions
      operation.fragmentDefinitions (operation.rootType schema) operation.selectionSet
  ∧ FieldMerge.fieldsInSetCanMerge schema operation.fragmentDefinitions
      (operation.rootType schema) operation.selectionSet
  ∧ operationVariablesUsed operation

end Validation
end NamedFragment
end GraphQL
