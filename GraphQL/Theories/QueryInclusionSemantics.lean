import GraphQL.Theories.QueryInclusion
import GraphQL.Theories.NormalForm
import GraphQL.Theories.AnnotatedExecution

/-! Execution-based interpretation of syntactic query inclusion. -/

namespace GraphQL
namespace QueryInclusionSemantics

open Execution
open AnnotatedExecution
open QueryInclusion
open scoped SyntacticEquivalence

-----------------------------------------------------------------------------------------
-- Semantic query inclusion statement
-----------------------------------------------------------------------------------------

-- The annotated executor records the representative field call for every response-name
-- group. Provenance uses the nominal arguments from the selected field;
-- `ResolvedFieldProvenance.coercedArguments` separately records whether argument coercion
-- succeeded and, when it did, the coerced arguments. GraphQL argument order is
-- immaterial, so compare nominal arguments by the syntactic equivalence relation.
def sameFieldProvenance (left right : ResolvedFieldProvenance) : Prop :=
  left.parentType = right.parentType
  ∧ left.fieldName = right.fieldName
  ∧ left.originalArguments ≡ right.originalArguments

instance sameFieldProvenanceDecidable : DecidableRel sameFieldProvenance :=
  fun left right => by
    unfold sameFieldProvenance
    infer_instance

-- `left.includes right` recursively preserves every response field of `right` in
-- `left`. Object fields are matched by response name and concrete resolver-call
-- provenance. List elements are matched recursively at their response positions.
-- Leaves must agree exactly. For executed response pairs the parent-level provenance
-- match already forces equal leaf values, so the explicit leaf equations keep the
-- relation self-contained without changing `includes`.
def annotatedResponseValueIncludes
    : AnnotatedResponseValue -> AnnotatedResponseValue -> Prop
  | .object _ leftFields, .object _ rightFields =>
      ∀ rightName rightCall rightValue,
        (hmember : .resolved rightName rightCall rightValue ∈ rightFields)
        -> ∃ leftName leftCall leftValue,
            .resolved leftName leftCall leftValue ∈ leftFields
            ∧ leftName = rightName
            ∧ sameFieldProvenance leftCall rightCall
            ∧ annotatedResponseValueIncludes leftValue rightValue
  | .list leftValues, .list rightValues =>
      ∀ (index : Nat) rightValue,
        (hmember : rightValues[index]? = some rightValue)
        -> ∃ leftValue,
            leftValues[index]? = some leftValue
            ∧ annotatedResponseValueIncludes leftValue rightValue
  | _, .object _ _ => False
  | _, .list _ => False
  | left, .null => left = .null
  | left, .scalar value => left = .scalar value
termination_by _left right => right.structuralSize
decreasing_by
  all_goals
    first
    | exact AnnotatedResponseValue.structuralSize_lt_of_object_field_mem hmember
    | exact AnnotatedResponseValue.structuralSize_lt_of_list_get? hmember

-- Query `left` includes query `right` when shared variable definitions have the same
-- types and equivalent defaults and every pair of error-free concrete executions
-- recursively preserves right response fields. One-sided definitions are unrestricted.
-- Every variable environment is constrained, including environments whose condition
-- variables do not all resolve to Booleans: an unresolvable `@skip`/`@include`
-- condition behaves like `false` during field collection, so those executions are
-- ordinary error-free executions. Resolver failures and null bubbling can erase
-- otherwise present response structure, so executions with errors are deliberately
-- outside this relation.
def includes (schema : Schema) (left right : Operation) : Prop :=
  sharedVariableDefinitionsSyntacticallyCompatible left.variableDefinitions
    right.variableDefinitions
  ∧ ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (source : ResolverValue ObjectRef),
      let leftResponse :=
        executeQueryAnnotated schema resolvers variableValues left source
      let rightResponse :=
        executeQueryAnnotated schema resolvers variableValues right source
      leftResponse.errors = 0
      -> rightResponse.errors = 0
      -> annotatedResponseValueIncludes leftResponse.data rightResponse.data

-----------------------------------------------------------------------------------------
-- Agreement between syntactic and semantic query inclusion
-----------------------------------------------------------------------------------------

-- Valid syntactic inclusion implies inclusion of error-free annotated executions.
-- Its theorem witness is `QueryInclusionSemantics.includesSyntacticToSemantic`.
def IncludesSyntacticToSemantic (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> QueryInclusion.includes schema left right
  -> includes schema left right

-- Compare only the resolved Boolean values of the listed variables. The branch
-- premise below ensures that its right-hand environment resolves every listed name.
def boolVarsAgreeOn (variables : List BoolVar) (left right : VariableValues) : Prop :=
  ∀ variableName,
    variableName ∈ variables
    -> inputValueBoolean? left (.variable variableName)
        = inputValueBoolean? right (.variable variableName)

-- Each complete Boolean branch has a coercible supplied environment for both
-- operations. The environment must agree with the branch on comparison conditions;
-- unrelated entries in the branch do not constrain argument values.
def comparisonBranchesArgumentCoercible (schema : Schema) (left right : Operation)
    : Prop :=
  let variables := comparisonConditionVariables left.selectionSet right.selectionSet
  ∀ (assignment : BoolCase),
    let assignmentValues := boolCaseVariableValues assignment
    boolVarsComplete variables assignmentValues
    -> ∃ suppliedValues,
        boolVarsAgreeOn variables suppliedValues assignmentValues
        ∧ operationArgumentsCoercible schema suppliedValues left
        ∧ operationArgumentsCoercible schema suppliedValues right

-- In the reverse direction, an error-free witness is needed for each checked path.
-- Possible-type field validity supplies argument coercibility. Non-null, non-list
-- composite-return inhabitance supplies realizable output values.
-- Its theorem witness is `QueryInclusionSemantics.includesSemanticToSyntactic`.
def IncludesSemanticToSyntactic (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> NormalForm.operationFieldsValidInPossibleTypes schema left
  -> NormalForm.operationFieldsValidInPossibleTypes schema right
  -> operationCompositeFieldTypesInhabited schema left
  -> operationCompositeFieldTypesInhabited schema right
  -> includes schema left right
  -> QueryInclusion.includes schema left right

-----------------------------------------------------------------------------------------
-- `includesUnannotated`: Unannotated query inclusion
-- * Annotated execution records resolver-call provenance, which plain responses omit.
-- * `includes` implies `includesUnannotated`, but not the other way around.
-----------------------------------------------------------------------------------------

-- Unannotated counterpart of `annotatedResponseValueIncludes` over plain response
-- values. Plain responses carry no resolver-call provenance, so agreement is stated on
-- the values themselves: leaves must be equal, object fields are matched by response
-- name, and list elements are matched at their response positions.
def responseValueIncludes : ResponseValue -> ResponseValue -> Prop
  | .object leftFields, .object rightFields =>
      ∀ rightName rightValue,
        (hmember : (rightName, rightValue) ∈ rightFields)
        -> ∃ leftValue,
            (rightName, leftValue) ∈ leftFields
            ∧ responseValueIncludes leftValue rightValue
  | .list leftValues, .list rightValues =>
      ∀ (index : Nat) rightValue,
        (hmember : rightValues[index]? = some rightValue)
        -> ∃ leftValue,
            leftValues[index]? = some leftValue
            ∧ responseValueIncludes leftValue rightValue
  | _, .object _ => False
  | _, .list _ => False
  | left, .null => left = .null
  | left, .scalar value => left = .scalar value
termination_by _left right => right.structuralSize
decreasing_by
  all_goals
    first
    | exact ResponseValue.structuralSize_lt_of_object_field_mem hmember
    | exact ResponseValue.structuralSize_lt_of_list_get? hmember

-- Unannotated query inclusion: the statement of `includes` with executions taken from
-- the spec executor `executeQuery` and inclusion checked on plain response values.
-- Resolver provenance is not observable in plain responses, so leaf-value agreement
-- takes its place.
def includesUnannotated (schema : Schema) (left right : Operation) : Prop :=
  sharedVariableDefinitionsSyntacticallyCompatible left.variableDefinitions
    right.variableDefinitions
  ∧ ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (source : ResolverValue ObjectRef),
      let leftResponse := executeQuery schema resolvers variableValues left source
      let rightResponse := executeQuery schema resolvers variableValues right source
      leftResponse.errors = 0
      -> rightResponse.errors = 0
      -> responseValueIncludes leftResponse.data rightResponse.data

-- Public agreement statement: for valid operations, semantic query inclusion implies
-- unannotated query inclusion. Only well-formedness and validity are required: the
-- implication is pointwise, transferring the annotated relation onto the projected plain
-- responses of the same execution pair, so no execution witnesses need to be constructed.
-- Its theorem witness is `QueryInclusionSemantics.includesToIncludesUnannotated` in the
-- corresponding proof module.
def IncludesToIncludesUnannotated (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> includes schema left right
  -> includesUnannotated schema left right

-- Note: `includesUnannotated` cannot imply `includes`: the annotated relation observes
-- the resolver call behind every response field, while plain responses expose calls only
-- through values. A non-null composite field whose subselections collect no fields at
-- any runtime type produces the empty object under every error-free execution, so two
-- such fields with different names are indistinguishable in every plain response even
-- though semantic `includes` fails for the pair and `QueryInclusion.includesBool`
-- rejects it. The response-unobservable guard in
-- `Tests.GraphQL.Theories.QueryInclusion` witnesses this limitation.

end QueryInclusionSemantics
end GraphQL
