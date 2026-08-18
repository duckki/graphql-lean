import GraphQL.SchemaWellFormedness
import GraphQL.Theories.ExecutionReadiness
import GraphQL.Validation

/-! GraphQL operation normal forms -/

namespace GraphQL

namespace NormalForm

export GraphQL (
  BoolVar BoolCase boolCaseVariableValues
  inputValueBooleanVariables inputValuesBooleanVariables
  inputObjectFieldsBooleanVariables directiveBooleanVariables
  directivesBooleanVariables selectionBooleanVariables
  selectionSetBooleanVariables boolVariableMem dedupBoolVars
  operationBoolVars boolVarsComplete operationBoolVarsComplete
)

-----------------------------------------------------------------------------------------
-- Ground Type Normalization
-----------------------------------------------------------------------------------------

-- Spec 5.5.2.3 `GetPossibleTypes` helper for deciding whether an already-unwrapped
-- named return type can be normalized directly, or must be grounded through object cases.
def objectTypeNameBool (schema : Schema) (typeName : Name) : Bool :=
  match schema.lookupType typeName with
  | some (.object _) => true
  | _ => false

-- Spec 3.4 leaf-type category helper used by proof-facing normalizer validity facts.
def leafTypeNameBool (schema : Schema) (typeName : Name) : Bool :=
  match schema.lookupType typeName with
  | some (.builtinScalar _) => true
  | some (.customScalar _) => true
  | some (.enum _) => true
  | _ => false

-- Spec 6.3.2 `CollectSubfields` analogue over selections, written
-- structurally so termination and size reasoning can reduce it directly.
def mergeSelectionSets : List Selection -> List Selection
  | [] => []
  | selection :: rest => selection.subselections ++ mergeSelectionSets rest

section NormalizeSelectionSetTermination

/-! Private termination support for `normalizeSelectionSet`. -/

private theorem selectionSet_size_append (left right : List Selection)
    : SelectionSet.size (left ++ right)
      = SelectionSet.size left + SelectionSet.size right := by
  induction left with
  | nil => simp [SelectionSet.size]
  | cons selection rest ih =>
      simp [SelectionSet.size, ih, Nat.add_assoc]

private theorem mergeSelectionSets_append (left right : List Selection)
    : mergeSelectionSets (left ++ right)
      = mergeSelectionSets left ++ mergeSelectionSets right := by
  induction left with
  | nil => simp [mergeSelectionSets]
  | cons selection rest ih =>
      simp [mergeSelectionSets, ih, List.append_assoc]

mutual
  -- Spec 6.3.2 field collection helper: finds field selections with one response name,
  -- descending
  -- through inline fragments that can contribute selections in the current type scope.
  def fieldSelectionsWithResponseNameInScope (schema : Schema)
      (parentType responseName : Name)
      : List Selection -> List Selection
    | [] => []
    | selection :: rest =>
        match selection with
        | .field fieldResponseName _fieldName _arguments _directives _selectionSet =>
            let restFields :=
              fieldSelectionsWithResponseNameInScope schema parentType responseName rest
            if fieldResponseName == responseName then
              selection :: restFields
            else
              restFields
        | .inlineFragment none _directives selectionSet =>
            fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet
            ++ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
        | .inlineFragment (some typeCondition) _directives selectionSet =>
            let restFields :=
              fieldSelectionsWithResponseNameInScope schema parentType responseName rest
            if schema.typesOverlapBool parentType typeCondition then
              fieldSelectionsWithResponseNameInScope schema parentType responseName
                selectionSet
              ++ restFields
            else
              restFields

  -- Spec 6.3.2 field collection helper: removes field selections with one response name
  -- recursively so later fragment lifting cannot reintroduce a duplicate field group.
  def withoutFieldSelectionsWithResponseName (schema : Schema) (responseName : Name)
      : List Selection -> List Selection
    | [] => []
    | selection :: rest =>
        match selection with
        | .field fieldResponseName _fieldName _arguments _directives _selectionSet =>
            let filteredRest :=
              withoutFieldSelectionsWithResponseName schema responseName rest
            if fieldResponseName == responseName then
              filteredRest
            else
              selection :: filteredRest
        | .inlineFragment typeCondition directives selectionSet =>
            .inlineFragment typeCondition directives
              (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
            :: withoutFieldSelectionsWithResponseName schema responseName rest
end

private theorem size_withoutFieldSelectionsWithResponseName_le (schema : Schema)
    (responseName : Name)
    : ∀ selectionSet,
        SelectionSet.size
          (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
        ≤ SelectionSet.size selectionSet
  | [] => by
      simp [withoutFieldSelectionsWithResponseName, SelectionSet.size]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hrest :=
            size_withoutFieldSelectionsWithResponseName_le schema responseName rest
          by_cases h : (fieldResponseName == responseName) = true
          · simp [withoutFieldSelectionsWithResponseName, h, SelectionSet.size,
              Selection.size]
            omega
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldSelectionsWithResponseName, hfalse, SelectionSet.size,
              Selection.size]
            omega
      | inlineFragment typeCondition directives selectionSet =>
          have hselectionSet :=
            size_withoutFieldSelectionsWithResponseName_le schema responseName selectionSet
          have hrest :=
            size_withoutFieldSelectionsWithResponseName_le schema responseName rest
          cases typeCondition <;>
            simp [withoutFieldSelectionsWithResponseName, SelectionSet.size,
              Selection.size]
          all_goals omega
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

private theorem size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le
    (schema : Schema) (parentType responseName : Name)
    : ∀ selectionSet,
        SelectionSet.size
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet))
        ≤ SelectionSet.size selectionSet
  | [] => by
      simp [fieldSelectionsWithResponseNameInScope, mergeSelectionSets,
        SelectionSet.size]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hrest :=
            size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le
              schema parentType responseName rest
          by_cases h : (fieldResponseName == responseName) = true
          · simp [fieldSelectionsWithResponseNameInScope, mergeSelectionSets, h,
              selectionSet_size_append, SelectionSet.size,
              Selection.size, Selection.subselections]
            omega
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse,
              SelectionSet.size, Selection.size]
            omega
      | inlineFragment typeCondition directives selectionSet =>
          have hselectionSet :=
            size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le
              schema parentType responseName selectionSet
          have hrest :=
            size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le
              schema parentType responseName rest
          cases typeCondition with
          | none =>
              simp [fieldSelectionsWithResponseNameInScope, mergeSelectionSets_append,
                selectionSet_size_append, SelectionSet.size,
                Selection.size]
              omega
          | some typeCondition =>
              by_cases h : (schema.typesOverlapBool parentType typeCondition) = true
              · simp [fieldSelectionsWithResponseNameInScope, h, mergeSelectionSets_append,
                  selectionSet_size_append, SelectionSet.size,
                  Selection.size]
                omega
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse, SelectionSet.size,
                  Selection.size]
                omega
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

end NormalizeSelectionSetTermination

-- Normalized fields are retained even when a composite child selection normalizes to
-- empty; execution still produces the parent response name with an empty object.
def normalizedField
    (_schema : Schema) (_returnType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (normalizedSubselections : List Selection)
    : Selection :=
  .field responseName fieldName arguments directives normalizedSubselections

-- Spec 5.3.2 field merging / 6.3.2 subfield collection: total normalizer; merges
-- same-response-name fields, recursively normalizes child selections, and grounds
-- abstract field return types through possible object types. This is terminating by
-- selection-set size.
def normalizeSelectionSet (schema : Schema) (parentType : Name)
    : List Selection -> List Selection
  | [] => []
  | selection :: rest =>
      match selection with
      | .field responseName fieldName arguments directives subselections =>
          let normalizedRest :=
            normalizeSelectionSet schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName rest)
          match schema.lookupField parentType fieldName with
          | none => normalizedRest
          | some fieldDefinition =>
              let matching :=
                fieldSelectionsWithResponseNameInScope schema parentType responseName rest
              let mergedSubselections := subselections ++ mergeSelectionSets matching
              let returnType := fieldDefinition.outputType.namedType
              let normalizedSubselections :=
                if objectTypeNameBool schema returnType then
                  normalizeSelectionSet schema returnType mergedSubselections
                else
                  (schema.getPossibleTypes returnType).filterMap
                    (fun objectType =>
                      match normalizeSelectionSet schema objectType
                              mergedSubselections with
                      | [] => none
                      | selection :: rest =>
                          some (.inlineFragment (some objectType) [] (selection :: rest)))
              normalizedField schema returnType responseName fieldName
                arguments directives normalizedSubselections
              :: normalizedRest
      | .inlineFragment none _directives subselections =>
          normalizeSelectionSet schema parentType (subselections ++ rest)
      | .inlineFragment (some typeCondition) _directives subselections =>
          let normalizedRest := normalizeSelectionSet schema parentType rest
          if schema.typesOverlapBool parentType typeCondition then
            normalizeSelectionSet schema parentType (subselections ++ rest)
          else
            normalizedRest
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    first
    | exact Nat.lt_of_le_of_lt
        (size_withoutFieldSelectionsWithResponseName_le schema responseName rest)
        (by
          simp [SelectionSet.size, Selection.size]
          omega)
    | (have hmerge :=
        size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le
          schema parentType responseName rest
       simp [selectionSet_size_append, SelectionSet.size,
         Selection.size]
       omega)
    | (simp [SelectionSet.size, Selection.size]
       omega)
    | (rw [selectionSet_size_append subselections rest]
       simp [SelectionSet.size, Selection.size]
       try omega)

-- Ground-type normalization of an operation
def normalizeOperation (schema : Schema) (operation : Operation) : Operation :=
  {
    operation with
      selectionSet :=
        normalizeSelectionSet schema (operation.rootType schema) operation.selectionSet
  }

-----------------------------------------------------------------------------------------
-- Ground Type Normalization Semantics Preservation
-----------------------------------------------------------------------------------------

mutual
  -- Proof-facing predicate for directive-free ground normalization: every modeled
  -- directive list in a selection is empty.
  def selectionDirectiveFree : Selection -> Prop
    | .field _responseName _fieldName _arguments directives selectionSet =>
        directives = [] ∧ selectionSetDirectiveFree selectionSet
    | .inlineFragment _typeCondition directives selectionSet =>
        directives = [] ∧ selectionSetDirectiveFree selectionSet

  -- Structural list form, chosen so hypotheses reduce directly on selection sets.
  def selectionSetDirectiveFree : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionDirectiveFree selection ∧ selectionSetDirectiveFree rest
end

-- Operation-level wrapper for the directive-free source-operation assumption.
def operationDirectiveFree (operation : Operation) : Prop :=
  selectionSetDirectiveFree operation.selectionSet

def operationsEquivalent (schema : Schema) (left right : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    variableValues fuel (source : Execution.ResolverValue ObjectRef),
    Execution.executeQueryWithFuel schema resolvers variableValues left fuel source
    = Execution.executeQueryWithFuel schema resolvers variableValues right fuel source

-- Final resolver-parametric correctness statement for the ground-type normalizer.
-- Operation-level proof wrappers live in
-- `Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.OperationSemantics`.
def groundTypeNormalFormSemanticsPreservation (schema : Schema) (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> operationDirectiveFree operation
  -> operationsEquivalent schema operation (normalizeOperation schema operation)

-----------------------------------------------------------------------------------------
-- Ground Type Normal Predicate
-----------------------------------------------------------------------------------------

-- Spec-inspired normal-form invariant: non-spec predicate requiring a flat field-only
-- selection layer.
def selectionsAllFields (selectionSet : List Selection) : Prop :=
  ∀ selection, selection ∈ selectionSet -> Selection.isField selection

-- Spec-inspired normal-form invariant: non-spec predicate requiring a flat
-- inline-fragment-only selection layer.
def selectionsAllInlineFragments (selectionSet : List Selection) : Prop :=
  ∀ selection, selection ∈ selectionSet -> Selection.isInlineFragment selection

-- Spec-inspired `GetPossibleTypes` grounding: non-spec predicate for object-grounded
-- selections. Object scopes are field-only; abstract scopes are lists of object-grounded
-- inline fragments.
mutual
  def selectionGroundTyped (schema : Schema) (parentType : Name) : Selection -> Prop
    | .field _responseName fieldName _arguments _directives selectionSet =>
        ∃ returnType,
          schema.fieldReturnType? parentType fieldName = some returnType
          ∧ selectionSetGroundTyped schema returnType selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        schema.objectType typeCondition
        ∧ selectionSetGroundTyped schema typeCondition selectionSet
    | .inlineFragment none _directives _selectionSet =>
        False

  def selectionSetGroundTyped (schema : Schema)
      (parentType : Name) (selectionSet : List Selection)
      : Prop :=
    (if objectTypeNameBool schema parentType then
        selectionsAllFields selectionSet
      else
        selectionsAllInlineFragments selectionSet)
    ∧ ∀ selection,
        selection ∈ selectionSet -> selectionGroundTyped schema parentType selection
end

-- Spec-inspired non-redundancy helper: response names are unique at one
-- selection-set layer.
def responseNamesNodup (selectionSet : List Selection) : Prop :=
  (selectionSet.filterMap Selection.responseName?).Nodup

-- Spec-inspired fragment grounding invariant: non-spec uniqueness predicate for
-- inline-fragment type conditions.
def inlineFragmentTypeCondition? : Selection -> Option Name
  | .inlineFragment (some typeCondition) _directives _selectionSet =>
      some typeCondition
  | _ => none

def inlineFragmentTypeConditionsNodup (selectionSet : List Selection) : Prop :=
  (selectionSet.filterMap inlineFragmentTypeCondition?).Nodup

-- Spec-inspired non-redundancy: non-spec predicate used by this project's normal form
-- rather than by GraphQL itself.
mutual
  def selectionNonRedundant : Selection -> Prop
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        selectionSetNonRedundant selectionSet
    | .inlineFragment _typeCondition _directives selectionSet =>
        selectionSetNonRedundant selectionSet

  def selectionSetNonRedundant (selectionSet : List Selection) : Prop :=
    responseNamesNodup selectionSet
    ∧ inlineFragmentTypeConditionsNodup selectionSet
    ∧ ∀ selection, selection ∈ selectionSet -> selectionNonRedundant selection
end

-- Spec-inspired normal-form invariant: combines type-aware object grounding with this
-- project's response-name/type-condition non-redundancy predicate.
def selectionSetNormal (schema : Schema)
    (parentType : Name) (selectionSet : List Selection)
    : Prop :=
  selectionSetGroundTyped schema parentType selectionSet
  ∧ selectionSetNonRedundant selectionSet

-- Spec-inspired operation normality.
def operationNormal (schema : Schema) (operation : Operation) : Prop :=
  selectionSetNormal schema (operation.rootType schema) operation.selectionSet

-- Public normality statement for the ground-type normalizer. The theorem witness is
-- `GraphQL.NormalForm.GroundTypeNormalization.normalizeOperation_normal`.
def normalizeOperationNormal (schema : Schema) (operation : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> operationNormal schema (normalizeOperation schema operation)

-----------------------------------------------------------------------------------------
-- Ground Type Normalization Validity
-----------------------------------------------------------------------------------------

-- Proof-facing validity-preservation assumption: when normalization grounds an
-- abstract field return through concrete object branches, the original child
-- selections must already be valid in each possible object scope.
mutual
  def selectionValidInPossibleTypes (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (parentType : Name)
      : Selection -> Prop
    | fieldSelection@(
          .field _responseName fieldName _arguments _directives selectionSet) =>
        Validation.selectionValid schema variableDefinitions parentType fieldSelection
        ∧ match schema.lookupField parentType fieldName with
          | none => False
          | some fieldDefinition =>
              ∀ objectType,
                objectType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
                -> selectionSetValidInPossibleTypes schema
                    variableDefinitions objectType selectionSet
    | .inlineFragment none _directives selectionSet =>
        ∀ objectType,
          objectType ∈ schema.getPossibleTypes parentType
          -> selectionSetValidInPossibleTypes schema variableDefinitions
              objectType selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        schema.typesOverlapBool parentType typeCondition = true
        -> ∀ objectType,
            objectType ∈ schema.getPossibleTypes typeCondition
            -> selectionSetValidInPossibleTypes schema variableDefinitions
                objectType selectionSet

  def selectionSetValidInPossibleTypes (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (parentType : Name)
      : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionValidInPossibleTypes schema variableDefinitions parentType selection
        ∧ selectionSetValidInPossibleTypes schema variableDefinitions parentType rest
end

-- Assumptions for normalizeOperationValid: selections validated under an abstract scope
-- must also be valid in every concrete object scope where normalization may ground them.
-- This is not a GraphQL validation rule; it is an operation-specific proof assumption
-- needed because the normalized operation explicitly contains those concrete branches.
-- Without it, normalization can change the field definition used for argument coercion
-- and therefore change the semantic argument map passed to a resolver.
-- Related spec issue: https://github.com/graphql/graphql-spec/issues/1121
def operationFieldsValidInPossibleTypes (schema : Schema) (operation : Operation)
    : Prop :=
  selectionSetValidInPossibleTypes schema
    operation.variableDefinitions (operation.rootType schema) operation.selectionSet

-- Type-condition feasibility for one field occurrence: the inline-fragment type
-- conditions between the field and its nearest parent field/root selection set,
-- including that parent type itself, have a nonempty possible-object intersection.
def typeConditionStackFeasible (schema : Schema) (typeConditions : List Name) : Prop :=
  ∃ objectType,
    ∀ typeCondition,
      typeCondition ∈ typeConditions -> objectType ∈ schema.getPossibleTypes typeCondition

-- Recursive validity-preservation assumption: every selected field has a feasible
-- enclosing type-condition stack. Every nonempty child selection set has at least
-- one possible concrete object type and satisfies the condition in every concrete
-- object scope introduced by ground normalization.
mutual
  def selectionTypeConditionFeasible (schema : Schema)
      (parentType : Name) (typeConditions : List Name)
      : Selection -> Prop
    | .field _responseName fieldName _arguments _directives selectionSet =>
        typeConditionStackFeasible schema typeConditions
        ∧ match selectionSet with
          | [] => True
          | _ :: _ =>
              match schema.lookupField parentType fieldName with
              | none => False
              | some fieldDefinition =>
                  let possibleTypes :=
                    schema.getPossibleTypes fieldDefinition.outputType.namedType
                  possibleTypes ≠ []
                  ∧ ∀ objectType,
                      objectType ∈ possibleTypes
                      -> selectionSetTypeConditionFeasible schema objectType
                          [objectType] selectionSet
    | .inlineFragment none _directives selectionSet =>
        selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        selectionSetTypeConditionFeasible schema parentType
          (typeCondition :: typeConditions) selectionSet

  def selectionSetTypeConditionFeasible (schema : Schema)
      (parentType : Name) (typeConditions : List Name)
      : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionTypeConditionFeasible schema parentType typeConditions selection
        ∧ selectionSetTypeConditionFeasible schema parentType typeConditions rest
end

-- Operation assumption for validity preservation: every selected field has a feasible
-- enclosing type-condition stack in every concrete scope introduced by ground
-- normalization, and every nonempty child has a possible concrete scope.
def operationTypeConditionFeasible (schema : Schema) (operation : Operation) : Prop :=
  selectionSetTypeConditionFeasible schema (operation.rootType schema)
    [operation.rootType schema] operation.selectionSet

-- Public validity-preservation statement for the ground-type normalizer. The theorem
-- witness is `GraphQL.NormalForm.GroundTypeNormalization.normalizeOperation_valid`.
def normalizeOperationValid (schema : Schema) (operation : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> operationDirectiveFree operation
  -> operationFieldsValidInPossibleTypes schema operation
  -> operationTypeConditionFeasible schema operation
  -> Validation.operationDefinitionValid schema (normalizeOperation schema operation)

-----------------------------------------------------------------------------------------
-- Ground Type Normalization Uniqueness
--
-- Let ≈ and ≡ be defined over two operations φ and ψ as follows:
-- * φ ≈ ψ: Semantic equivalence of φ and ψ up to reordering of response fields
-- * φ ≡ ψ: Syntactic equivalence of φ and ψ up to reordering of selections/arguments
--          after coercion.
--
-- Then, the normalization operation N has the following soundness and uniqueness
-- properties:
-- * N(φ) ≡ N(ψ) → φ ≈ ψ
-- * φ ≈ ψ → N(φ) ≡ N(ψ)
-- The uniqueness direction has extra feasibility assumptions ensuring that normalization
-- preserves operation validity.
-----------------------------------------------------------------------------------------

-- Operation semantic equivalence (`≈`): a relaxed version of `operationsEquivalent`,
-- where fields can be reordered in the response values. The relation is restricted to
-- supplied variable environments under which both operations' field arguments coerce
-- successfully. Ordinary execution errors remain observable through
-- `Execution.Response.semanticEquivalent`, including equality of error counts.
def operationsSemanticallyEquivalent (schema : Schema) (left right : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    variableValues fuel (source : Execution.ResolverValue ObjectRef),
    operationArgumentsCoercible schema variableValues left
    -> operationArgumentsCoercible schema variableValues right
    -> Execution.Response.semanticEquivalent
        (Execution.executeQueryWithFuel schema resolvers variableValues left fuel source)
        (Execution.executeQueryWithFuel schema resolvers variableValues right fuel source)

mutual
  -- Selection equality at the resolver boundary. Corresponding fields expose
  -- equivalent argument maps, while sibling order remains irrelevant.
  inductive SelectionEqualUpToReorderingWithCoercion
      (schema : Schema)
      (leftVariableValues rightVariableValues : Execution.VariableValues)
      : Name -> Selection -> Selection -> Prop where
    | field
      (parentType responseName fieldName : Name)
      {leftArguments rightArguments : List Argument}
      (directives : List DirectiveApplication)
      {leftSelectionSet rightSelectionSet : List Selection}
      (fieldDefinition : FieldDefinition)
      : schema.lookupField parentType fieldName = some fieldDefinition
        -> Execution.ArgumentCoercionResult.equivalent
            (Execution.coerceArgumentValues schema leftVariableValues
              fieldDefinition.arguments leftArguments)
            (Execution.coerceArgumentValues schema rightVariableValues
              fieldDefinition.arguments rightArguments)
        -> ((Execution.coerceArgumentValues schema leftVariableValues
                fieldDefinition.arguments leftArguments).isSuccess
              = true
            -> SelectionSetEqualUpToReorderingWithCoercion
                schema leftVariableValues rightVariableValues
                fieldDefinition.outputType.namedType leftSelectionSet rightSelectionSet)
        -> SelectionEqualUpToReorderingWithCoercion
            schema leftVariableValues rightVariableValues parentType
            (.field responseName fieldName leftArguments directives leftSelectionSet)
            (.field responseName fieldName rightArguments directives rightSelectionSet)
    | inlineFragment
      (parentType : Name)
      (typeCondition : Option Name)
      (directives : List DirectiveApplication)
      {leftSelectionSet rightSelectionSet : List Selection}
      : SelectionSetEqualUpToReorderingWithCoercion
          schema leftVariableValues rightVariableValues
          (typeCondition.getD parentType) leftSelectionSet rightSelectionSet
        -> SelectionEqualUpToReorderingWithCoercion
            schema leftVariableValues rightVariableValues parentType
            (.inlineFragment typeCondition directives leftSelectionSet)
            (.inlineFragment typeCondition directives rightSelectionSet)

  inductive SelectionSetEqualUpToReorderingWithCoercion
      (schema : Schema)
      (leftVariableValues rightVariableValues : Execution.VariableValues)
      : Name -> List Selection -> List Selection -> Prop where
    | paired {left right : List Selection} (pairs : List (Selection × Selection))
      : (pairs.map Prod.fst).Perm left -> (pairs.map Prod.snd).Perm right
        -> (∀ pair,
              pair ∈ pairs
              -> SelectionEqualUpToReorderingWithCoercion
                  schema leftVariableValues rightVariableValues parentType pair.1 pair.2)
        -> SelectionSetEqualUpToReorderingWithCoercion
            schema leftVariableValues rightVariableValues parentType left right
end

-- Operation syntactic equality (`≡`) up to reordering.
-- Operation defaults are applied separately before field arguments are coerced against
-- the shared schema.
def operationsEqualUpToReorderingWithCoercion (schema : Schema) (left right : Operation)
    : Prop :=
  left.operationType = right.operationType
  ∧ ∀ variableValues,
      operationArgumentsCoercible schema variableValues left
      -> operationArgumentsCoercible schema variableValues right
      -> SelectionSetEqualUpToReorderingWithCoercion schema
          (Execution.coerceVariableValues left variableValues)
          (Execution.coerceVariableValues right variableValues)
          (left.rootType schema) left.selectionSet right.selectionSet

-- States: Two syntactically equal normal operations are semantically equivalent.
-- The theorem witness is
-- `GroundTypeNormalization.normal_operations_equalUpToReordering_semanticallyEquivalent`
-- in `Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness`.
def normalOperationsEqualUpToReorderingSemanticallyEquivalent
    (schema : Schema) (left right : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> operationDirectiveFree left
  -> operationDirectiveFree right
  -> operationNormal schema left
  -> operationNormal schema right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions
      right.variableDefinitions
  -> operationsEqualUpToReorderingWithCoercion schema left right
  -> operationsSemanticallyEquivalent schema left right

-- States: N(φ) ≡ N(ψ) → φ ≈ ψ
-- The theorem witness is
-- `GroundTypeNormalization.normalizeOperations_equalUpToReordering_semanticallyEquivalent`
-- in `Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness`.
def normalizeOperationsEqualUpToReorderingSemanticallyEquivalent
    (schema : Schema) (left right : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> operationDirectiveFree left
  -> operationDirectiveFree right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions
      right.variableDefinitions
  -> operationsEqualUpToReorderingWithCoercion schema
      (normalizeOperation schema left)
      (normalizeOperation schema right)
  -> operationsSemanticallyEquivalent schema left right

-- States: Two semantically equivalent normal operations are syntactically equal.
-- The theorem witness is
-- `GroundTypeNormalization.normal_operations_semanticallyEquivalent_equalUpToReordering`
-- in `Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness`.
def normalOperationsSemanticallyEquivalentEqualUpToReordering
    (schema : Schema) (left right : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> operationDirectiveFree left
  -> operationDirectiveFree right
  -> operationNormal schema left
  -> operationNormal schema right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions
      right.variableDefinitions
  -> operationsSemanticallyEquivalent schema left right
  -> operationsEqualUpToReorderingWithCoercion schema left right

-- States: φ ≈ ψ → N(φ) ≡ N(ψ)
-- The theorem witness is
-- `GroundTypeNormalization.normalizeOperation_uniqueUpToReordering` in
-- `Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness`.
def normalizeOperationUniqueUpToReordering (schema : Schema) (left right : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> operationDirectiveFree left
  -> operationDirectiveFree right
  -> operationFieldsValidInPossibleTypes schema left
  -> operationFieldsValidInPossibleTypes schema right
  -> operationTypeConditionFeasible schema left
  -> operationTypeConditionFeasible schema right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions
      right.variableDefinitions
  -> operationsSemanticallyEquivalent schema left right
  -> operationsEqualUpToReorderingWithCoercion schema
      (normalizeOperation schema left) (normalizeOperation schema right)

-----------------------------------------------------------------------------------------
-- Complete Normalization
-----------------------------------------------------------------------------------------

namespace CompleteNormalization

def allBoolCases : List BoolVar -> List BoolCase
  | [] => [[]]
  | varName :: rest =>
      let restCases := allBoolCases rest
      restCases.map (fun boolCase => (varName, false) :: boolCase)
      ++ restCases.map (fun boolCase => (varName, true) :: boolCase)

def BoolCase.lookup? (boolCase : BoolCase) (varName : BoolVar) : Option Bool :=
  match boolCase with
  | [] => none
  | (candidate, value) :: rest =>
      if candidate == varName then some value else BoolCase.lookup? rest varName

def variableValuesAgreeWithCase
    (variableValues : Execution.VariableValues)
    (boolCase : BoolCase)
    (variables : List BoolVar)
    : Prop :=
  ∀ varName,
    varName ∈ variables
    -> Execution.inputValueBoolean? variableValues (.variable varName)
        = BoolCase.lookup? boolCase varName

def inputValueBoolIn? (boolCase : BoolCase) : InputValue -> Option Bool
  | .variable varName => BoolCase.lookup? boolCase varName
  | value => value.staticBoolean?

-- Mirrors `Execution.directiveAllowsSelectionBool` with case-supplied variable values:
-- a condition that does not resolve to a Boolean behaves like `false` for both
-- directives, so `@skip` keeps the selection and `@include` drops it.
def directiveAllowsIn (boolCase : BoolCase) : DirectiveApplication -> Bool
  | .skip ifArgument =>
      match inputValueBoolIn? boolCase ifArgument with
      | some value => !value
      | none => true
  | .include ifArgument =>
      match inputValueBoolIn? boolCase ifArgument with
      | some value => value
      | none => false

def directivesAllowIn (boolCase : BoolCase) (directives : List DirectiveApplication)
    : Bool :=
  directives.all
    (fun directive =>
      directiveAllowsIn boolCase directive)

def directiveForBit (varName : BoolVar) (value : Bool) : DirectiveApplication :=
  if value then
    .include (.variable varName)
  else
    .skip (.variable varName)

def wrapWithBoolCase (boolCase : BoolCase) : List Selection -> List Selection
  | selectionSet =>
      match boolCase with
      | [] => selectionSet
      | (varName, value) :: rest =>
          [.inlineFragment none [directiveForBit varName value]
            (wrapWithBoolCase rest selectionSet)]

section FilterSelectionSetBoolCaseTermination

/-! Private termination support for `filterSelectionSetBoolCase`. -/

private theorem selection_size_pos (selection : Selection) : 0 < selection.size := by
  cases selection <;> simp [Selection.size] <;> omega

private theorem selectionSet_size_tail_lt_cons
    (selection : Selection) (rest : List Selection)
    : SelectionSet.size rest < SelectionSet.size (selection :: rest) := by
  simp [SelectionSet.size]
  exact Nat.lt_add_of_pos_left (selection_size_pos selection)

private theorem selectionSet_size_child_lt_cons_field
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : SelectionSet.size selectionSet
      < SelectionSet.size
          (Selection.field responseName fieldName arguments directives selectionSet
            :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

private theorem selectionSet_size_child_lt_cons_inline
    (typeCondition : Option Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : SelectionSet.size selectionSet
      < SelectionSet.size
          (Selection.inlineFragment typeCondition directives selectionSet :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

end FilterSelectionSetBoolCaseTermination

def filterSelectionSetBoolCase (boolCase : BoolCase) : List Selection -> List Selection
  | [] => []
  | selection :: rest =>
      let collectedRest := filterSelectionSetBoolCase boolCase rest
      match selection with
      | .field responseName fieldName arguments directives selectionSet =>
          if directivesAllowIn boolCase directives then
            let filteredSelectionSet := filterSelectionSetBoolCase boolCase selectionSet
            match selectionSet, filteredSelectionSet with
            | [], _ =>
                .field responseName fieldName arguments [] [] :: collectedRest
            | _ :: _, [] =>
                .field responseName fieldName arguments [] [] :: collectedRest
            | _ :: _, child :: children =>
                .field responseName fieldName arguments [] (child :: children)
                :: collectedRest
          else
            collectedRest
      | .inlineFragment typeCondition directives selectionSet =>
          if directivesAllowIn boolCase directives then
            match filterSelectionSetBoolCase boolCase selectionSet with
            | [] => collectedRest
            | child :: children =>
                .inlineFragment typeCondition [] (child :: children) :: collectedRest
          else
            collectedRest
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    first
    | exact selectionSet_size_tail_lt_cons selection rest
    | exact selectionSet_size_child_lt_cons_field responseName fieldName
        arguments directives selectionSet rest
    | exact selectionSet_size_child_lt_cons_inline typeCondition
        directives selectionSet rest

def normalizeBoolCaseForType
    (schema : Schema) (boolCase : BoolCase) (returnType : Name)
    (selectionSet : List Selection)
    : List Selection :=
  normalizeSelectionSet schema returnType
    (filterSelectionSetBoolCase boolCase selectionSet)

def completeNormalizeRootSelectionSet
    (schema : Schema) (variables : List BoolVar)
    (parentType : Name) (selectionSet : List Selection)
    : List Selection :=
  List.flatten
    ((allBoolCases variables).map
      (fun boolCase =>
        match normalizeSelectionSet schema parentType
                (filterSelectionSetBoolCase boolCase selectionSet) with
        | [] => []
        | selection :: rest =>
            wrapWithBoolCase boolCase (selection :: rest)))

def completeNormalizeOperation (schema : Schema) (operation : Operation) : Operation :=
  let variables := operationBoolVars operation
  {
    operation with
      selectionSet :=
        completeNormalizeRootSelectionSet schema variables (operation.rootType schema)
          operation.selectionSet
  }

end CompleteNormalization

export CompleteNormalization (
  allBoolCases BoolCase.lookup?
  inputValueBoolIn? directiveAllowsIn
  directivesAllowIn directiveForBit
  wrapWithBoolCase
  filterSelectionSetBoolCase normalizeBoolCaseForType
  completeNormalizeRootSelectionSet
  completeNormalizeOperation
)

-----------------------------------------------------------------------------------------
-- Complete Normalization Semantics Preservation
-----------------------------------------------------------------------------------------

-- Public semantics-preservation statement for complete normalization. The theorem
-- witness is
-- `GraphQL.NormalForm.CompleteNormalization.completeNormalizationSemanticsPreserved`.
def completeNormalizationSemanticsPreserved (schema : Schema) (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
        variableValues fuel (source : Execution.ResolverValue ObjectRef),
      operationBoolVarsComplete operation
        (Execution.coerceVariableValues operation variableValues)
      -> Execution.executeQueryWithFuel schema resolvers variableValues operation
            fuel source
          = Execution.executeQueryWithFuel schema resolvers variableValues
              (completeNormalizeOperation schema operation) fuel source

-----------------------------------------------------------------------------------------
-- Complete Normal Predicate And Normalization Statement
-----------------------------------------------------------------------------------------

namespace CompleteNormalization

-- Complete Boolean minterm: every operation Boolean variable appears exactly once.
-- The order in the `BoolCase` is intentionally irrelevant to the variable list order.
def completeNormalBoolCase (variables : List BoolVar) (boolCase : BoolCase) : Prop :=
  variables.Nodup
  ∧ (boolCase.map Prod.fst).Nodup
  ∧ ∀ varName, varName ∈ boolCase.map Prod.fst ↔ varName ∈ variables

-- Boolean conditions are compared extensionally, so different stem orders can denote
-- the same minterm.
def completeNormalBoolCasesEquivalent (left right : BoolCase) : Prop :=
  ∀ varName value, (varName, value) ∈ left ↔ (varName, value) ∈ right

-- A Boolean case stem is a chain of anonymous inline fragments, one singleton
-- skip/include directive per variable, ending in the branch body.
def completeNormalBooleanStem : BoolCase -> Selection -> List Selection -> Prop
  | [], _selection, _body => False
  | [(varName, value)],
    .inlineFragment none [directive] body,
    branchBody =>
      directive = directiveForBit varName value ∧ body = branchBody
  | (varName, value) :: rest,
    .inlineFragment none [directive] [child],
    branchBody =>
      directive = directiveForBit varName value
      ∧ completeNormalBooleanStem rest child branchBody
  | _, _, _ => False

-- Complete DNF over Boolean directive variables for the nonempty cases. Branch
-- order is irrelevant; stem variable order is irrelevant; empty cases are omitted;
-- repeated branch selections are rejected.
def completeNormalSelectionSet
    (schema : Schema) (variables : List BoolVar) (parentType : Name)
    (selectionSet : List Selection)
    : Prop :=
  variables.Nodup
  ∧ match variables with
    | [] =>
        selectionSetNormal schema parentType selectionSet
        ∧ selectionSetDirectiveFree selectionSet
    | _ :: _ =>
        selectionSet.Nodup
        ∧ (∀ selection,
            selection ∈ selectionSet
            -> ∃ boolCase body,
                completeNormalBoolCase variables boolCase
                ∧ completeNormalBooleanStem boolCase selection body
                ∧ selectionSetNormal schema parentType body
                ∧ selectionSetDirectiveFree body)
        ∧ (∀ left right leftCase rightCase leftBody rightBody,
            left ∈ selectionSet
            -> right ∈ selectionSet
            -> completeNormalBoolCase variables leftCase
            -> completeNormalBoolCase variables rightCase
            -> completeNormalBooleanStem leftCase left leftBody
            -> completeNormalBooleanStem rightCase right rightBody
            -> selectionSetDirectiveFree leftBody
            -> selectionSetDirectiveFree rightBody
            -> completeNormalBoolCasesEquivalent leftCase rightCase
            -> left = right)

def completeNormalOperation (schema : Schema) (operation : Operation) : Prop :=
  completeNormalSelectionSet schema
    (operationBoolVars operation) (operation.rootType schema) operation.selectionSet

end CompleteNormalization

export CompleteNormalization (
  completeNormalBoolCase completeNormalBoolCasesEquivalent
  completeNormalBooleanStem completeNormalSelectionSet completeNormalOperation
)

-- Public normality statement for complete normalization. The theorem witness is
-- `GraphQL.NormalForm.CompleteNormalization.completeNormalizeOperation_normal`.
def completeNormalizeOperationNormal (schema : Schema) (operation : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> completeNormalOperation schema (completeNormalizeOperation schema operation)

-----------------------------------------------------------------------------------------
-- Complete Normalization Validity
-----------------------------------------------------------------------------------------

namespace CompleteNormalization

def selectionAllowsIn (boolCase : BoolCase) : Selection -> Bool
  | .field _responseName _fieldName _arguments directives _selectionSet =>
      directivesAllowIn boolCase directives
  | .inlineFragment _typeCondition directives _selectionSet =>
      directivesAllowIn boolCase directives

private theorem selection_size_le_selectionSet_size_of_mem
    {selection : Selection} {selectionSet : List Selection}
    (hmem : selection ∈ selectionSet)
    : selection.size ≤ SelectionSet.size selectionSet := by
  induction selectionSet with
  | nil =>
      cases hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with rfl | hrest
      · simp [SelectionSet.size]
      · have := ih hrest
        simp [SelectionSet.size]
        omega

mutual
  /--
  Every selection has a feasible type-condition stack and survives in at least one
  Boolean case still admitted by its ancestors. Composite child sets are checked in
  exactly the cases where their parent survives.
  -/
  def selectionBoolTypeConditionFeasible
      (schema : Schema) (parentType : Name)
      (typeConditions : List Name) (boolCases : List BoolCase)
      : Selection -> Prop
    | .field _responseName fieldName _arguments directives selectionSet =>
        let allowedCases :=
          boolCases.filter (fun boolCase => directivesAllowIn boolCase directives)
        allowedCases ≠ []
        ∧ typeConditionStackFeasible schema typeConditions
        ∧ (selectionSet = []
            ∨ match schema.lookupField parentType fieldName with
              | none => False
              | some fieldDefinition =>
                  let possibleTypes :=
                    schema.getPossibleTypes fieldDefinition.outputType.namedType
                  possibleTypes ≠ []
                  ∧ ∀ objectType,
                      objectType ∈ possibleTypes
                      -> selectionSetBoolTypeConditionFeasible schema objectType
                          [objectType] allowedCases selectionSet)
    | .inlineFragment none directives selectionSet =>
        let allowedCases :=
          boolCases.filter (fun boolCase => directivesAllowIn boolCase directives)
        allowedCases ≠ []
        ∧ selectionSetBoolTypeConditionFeasible schema parentType
            typeConditions allowedCases selectionSet
    | .inlineFragment (some typeCondition) directives selectionSet =>
        let allowedCases :=
          boolCases.filter (fun boolCase => directivesAllowIn boolCase directives)
        allowedCases ≠ []
        ∧ selectionSetBoolTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions) allowedCases selectionSet
  termination_by selection => 2 * selection.size
  decreasing_by
    all_goals
      simp [Selection.size]
      omega

  /--
  Every child selection is feasible, and every Boolean case admitted by the parent
  leaves at least one child selection. The caller supplies a nonempty list of
  admitted cases, so case coverage also establishes that the selection set is
  nonempty.
  -/
  def selectionSetBoolTypeConditionFeasible
      (schema : Schema) (parentType : Name)
      (typeConditions : List Name) (boolCases : List BoolCase)
      (selectionSet : List Selection)
      : Prop :=
    (∀ selection,
      selection ∈ selectionSet
      -> selectionBoolTypeConditionFeasible schema parentType
          typeConditions boolCases selection)
    ∧ ∀ boolCase,
        boolCase ∈ boolCases
        -> ∃ selection,
            selection ∈ selectionSet ∧ selectionAllowsIn boolCase selection = true
  termination_by 2 * SelectionSet.size selectionSet + 1
  decreasing_by
    have hsize :=
        selection_size_le_selectionSet_size_of_mem
          (selection := selection) (selectionSet := selectionSet)
          ‹selection ∈ selectionSet›
    omega
end

/--
Operation-local feasibility assumption for complete-normalization validity.

Every root selection has a feasible type-condition stack and survives under at
least one complete Boolean case. Recursively, every source selection survives
some case admitted by its ancestors, and every surviving composite selection
retains a child in each case where its parent survives.
-/
def operationBoolTypeConditionFeasible (schema : Schema) (operation : Operation) : Prop :=
  ∀ selection,
    selection ∈ operation.selectionSet
    -> selectionBoolTypeConditionFeasible schema (operation.rootType schema)
        [operation.rootType schema]
        (allBoolCases (operationBoolVars operation)) selection

end CompleteNormalization

export CompleteNormalization (
  operationBoolTypeConditionFeasible selectionAllowsIn
  selectionBoolTypeConditionFeasible
  selectionSetBoolTypeConditionFeasible
)

-- Final validity-preservation statement for complete normalization. The theorem witness
-- is `GraphQL.NormalForm.CompleteNormalization.completeNormalizeOperation_valid`.
def completeNormalizeOperationValid (schema : Schema) (operation : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> operationFieldsValidInPossibleTypes schema operation
  -> operationBoolTypeConditionFeasible schema operation
  -> Validation.operationDefinitionValid schema
      (completeNormalizeOperation schema operation)

-----------------------------------------------------------------------------------------
-- Complete Normalization Uniqueness
--
-- Let ≈ and ≡ be defined over two operations φ and ψ as follows:
-- * φ ≈ ψ: Semantic equivalence of φ and ψ up to reordering of response fields
-- * φ ≡ ψ: Syntactic equivalence of φ and ψ up to reordering of selections/arguments
--          after coercion.
--
-- Then, the normalization operation N has the following soundness and uniqueness
-- properties:
-- * N(φ) ≡ N(ψ) → φ ≈ ψ
-- * φ ≈ ψ → N(φ) ≡ N(ψ)
-- * The soundness direction of the implication uses a slightly relaxed version of `≈`
--   that requires all Boolean variables to be assigned in the input environment to ensure
--   the normalized operations are validity preserving.
-- * The uniqueness direction has extra feasibility assumptions ensuring that
--   normalization preserves operation validity.
-----------------------------------------------------------------------------------------

-- States: two operations have the same set of Boolean variables.
def operationBoolVarsEquivalent (left right : Operation) : Prop :=
  ∀ varName, varName ∈ operationBoolVars left ↔ varName ∈ operationBoolVars right

/--
Every complete Boolean case has a shared supplied-variable environment that makes
both operations' field arguments coercible. The surrounding theorem assumptions
require the operations to have equivalent Boolean-variable support, so enumerating
the left operation's cases covers both sides. The base values may supply non-Boolean
variables needed by field arguments.
-/
def completeBoolCasesJointlyCoercible (schema : Schema) (left right : Operation) : Prop :=
  ∀ boolCase,
    completeNormalBoolCase (operationBoolVars left) boolCase
    -> ∃ baseValues,
        operationArgumentsCoercible schema
          (boolCaseVariableValues boolCase baseValues) left
        ∧ operationArgumentsCoercible schema
            (boolCaseVariableValues boolCase baseValues) right

def CompleteNormalSelectionEqualUpToReorderingWithCoercion
    (schema : Schema) (leftOperation rightOperation : Operation)
    (parentType : Name) (leftVariables rightVariables : List BoolVar)
    (left right : Selection)
    : Prop :=
  ∃ leftCase rightCase leftBody rightBody,
    completeNormalBoolCase leftVariables leftCase
    ∧ completeNormalBoolCase rightVariables rightCase
    ∧ completeNormalBooleanStem leftCase left leftBody
    ∧ completeNormalBooleanStem rightCase right rightBody
    ∧ completeNormalBoolCasesEquivalent leftCase rightCase
    ∧ ∀ variableValues,
        operationArgumentsCoercible schema variableValues leftOperation
        -> operationArgumentsCoercible schema variableValues rightOperation
        -> boolVarsComplete leftVariables variableValues
        -> CompleteNormalization.variableValuesAgreeWithCase
            (Execution.coerceVariableValues leftOperation variableValues)
            leftCase leftVariables
        -> CompleteNormalization.variableValuesAgreeWithCase
            (Execution.coerceVariableValues rightOperation variableValues)
            rightCase rightVariables
        -> SelectionSetEqualUpToReorderingWithCoercion schema
            (Execution.coerceVariableValues leftOperation variableValues)
            (Execution.coerceVariableValues rightOperation variableValues)
            parentType leftBody rightBody

def CompleteNormalSelectionSetEqualUpToReorderingWithCoercion
    (schema : Schema) (leftOperation rightOperation : Operation)
    (parentType : Name) (leftVariables rightVariables : List BoolVar)
    (left right : List Selection)
    : Prop :=
  ∃ pairs : List (Selection × Selection),
    (pairs.map Prod.fst).Perm left
    ∧ (pairs.map Prod.snd).Perm right
    ∧ ∀ pair,
        pair ∈ pairs
        -> CompleteNormalSelectionEqualUpToReorderingWithCoercion
            schema leftOperation rightOperation parentType
            leftVariables rightVariables pair.1 pair.2

-- Syntactic equality (`≡`) up to reordering for complete-normal operations. Boolean
-- support is explicit because children below failed argument coercion are unobservable
-- in the guarded selection relation.
def completeNormalOperationsEqualUpToReorderingWithCoercion
    (schema : Schema) (left right : Operation)
    : Prop :=
  left.operationType = right.operationType
  ∧ operationBoolVarsEquivalent left right
  ∧ match operationBoolVars left with
    | [] =>
        ∀ variableValues,
          operationArgumentsCoercible schema variableValues left
          -> operationArgumentsCoercible schema variableValues right
          -> SelectionSetEqualUpToReorderingWithCoercion schema
              (Execution.coerceVariableValues left variableValues)
              (Execution.coerceVariableValues right variableValues)
              (left.rootType schema) left.selectionSet right.selectionSet
    | _ :: _ =>
        CompleteNormalSelectionSetEqualUpToReorderingWithCoercion
          schema left right (left.rootType schema)
          (operationBoolVars left) (operationBoolVars right)
          left.selectionSet right.selectionSet

-- `operationsSemanticallyEquivalent` with an additional assumption that the input
-- variables include complete Boolean variable assignments. As in the unrestricted
-- relation, both operations' field arguments must coerce successfully; response error
-- counts from ordinary execution remain observable.
-- The completeness assumption is necessary to utilize the semantic equivalence of an
-- operation and its normalized form.
def operationsSemanticallyEquivalentForCompleteBoolVars
    (schema : Schema) (variables : List BoolVar)
    (left right : Operation)
    : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    variableValues fuel (source : Execution.ResolverValue ObjectRef),
    boolVarsComplete variables variableValues
    -> operationArgumentsCoercible schema variableValues left
    -> operationArgumentsCoercible schema variableValues right
    -> Execution.Response.semanticEquivalent
        (Execution.executeQueryWithFuel schema resolvers variableValues left fuel source)
        (Execution.executeQueryWithFuel schema resolvers variableValues right fuel source)

-- States: φ ≡ ψ → φ ≈ ψ (when φ and ψ are normal)
-- The theorem witness is
-- `CompleteNormalization.complete_normal_operations_equalUpToReordering_semanticallyEquivalent`
-- in `Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness`.
-- The conclusion is restricted to complete Boolean environments. A condition variable
-- that does not resolve to a Boolean behaves like `false` during field collection while
-- argument coercion still observes it as undefined, so reordering equality, whose
-- guarded-body comparisons pin condition variables to their case values, does not
-- constrain such environments: `{ f(a: $v) }` and `{ f(a: false) }` guarded by the
-- `$v = false` case coerce equivalently at every complete environment but produce
-- different resolver calls when `$v` is undefined.
def completeNormalOperationsEqualUpToReorderingSemanticallyEquivalent
    (schema : Schema) (left right : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> completeNormalOperation schema left
  -> completeNormalOperation schema right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions
      right.variableDefinitions
  -> completeNormalOperationsEqualUpToReorderingWithCoercion schema left right
  -> operationsSemanticallyEquivalentForCompleteBoolVars
      schema (operationBoolVars left) left right

-- States: N(φ) ≡ N(ψ) → φ ≈ ψ
-- The theorem witness is
-- `CompleteNormalization.completeNormalizeOperations_equalUpToReordering_semanticallyEquivalent`
-- in `Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness`.
def completeNormalizeOperationsEqualUpToReorderingSemanticallyEquivalent
    (schema : Schema) (left right : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions
      right.variableDefinitions
  -> operationBoolVarsEquivalent left right
  -> completeNormalOperationsEqualUpToReorderingWithCoercion schema
      (completeNormalizeOperation schema left)
      (completeNormalizeOperation schema right)
  -> operationsSemanticallyEquivalentForCompleteBoolVars
      schema (operationBoolVars left) left right

-- States: φ ≈ ψ → φ ≡ ψ (when φ and ψ are normal)
-- The theorem witness is
-- `CompleteNormalization.complete_normal_operations_semanticallyEquivalent_equalUpToReordering`
-- in `Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness`.
def completeNormalOperationsSemanticallyEquivalentEqualUpToReordering
    (schema : Schema) (left right : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> completeNormalOperation schema left
  -> completeNormalOperation schema right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions
      right.variableDefinitions
  -> operationBoolVarsEquivalent left right
  -> completeBoolCasesJointlyCoercible schema left right
  -> operationsSemanticallyEquivalent schema left right
  -> completeNormalOperationsEqualUpToReorderingWithCoercion schema left right

-- States: φ ≈ ψ → N(φ) ≡ N(ψ)
-- The theorem witness is
-- `CompleteNormalization.completeNormalizeOperation_uniqueUpToReordering` in
-- `Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness`.
def completeNormalizeOperationUniqueUpToReordering
    (schema : Schema) (left right : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> operationFieldsValidInPossibleTypes schema left
  -> operationFieldsValidInPossibleTypes schema right
  -> operationBoolTypeConditionFeasible schema left
  -> operationBoolTypeConditionFeasible schema right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions
      right.variableDefinitions
  -> operationBoolVarsEquivalent left right
  -> completeBoolCasesJointlyCoercible schema
      (completeNormalizeOperation schema left)
      (completeNormalizeOperation schema right)
  -> operationsSemanticallyEquivalent schema left right
  -> completeNormalOperationsEqualUpToReorderingWithCoercion schema
      (completeNormalizeOperation schema left)
      (completeNormalizeOperation schema right)

end NormalForm

end GraphQL
