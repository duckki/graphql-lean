import GraphQL.Theories.TreeSummary.ResponseFold
import GraphQL.Theories.TreeSummary.ExactCasesOptimality
import GraphQL.Theories.TreeSummary.Syntactic
import GraphQL.SchemaWellFormedness
import GraphQL.Validation

/-! Static analysis for the IBM GraphQL Cost Directives specification.

The core schema syntax deliberately omits custom directives. `CostModel` supplies the
information that an IBM cost-directive schema would carry through `@cost` and
`@listSize`, plus a finite fallback for lists that the specification otherwise treats as
unbounded. The analysis folds a condition tree and returns maximum IBM type and field
costs for a query. This formalization uses integral costs instead of the specification's
decimal weights.
-/

namespace GraphQL
namespace TreeSummary
namespace StaticCost

open GraphQL.AnnotatedExecution

-----------------------------------------------------------------------------------------
-- External cost and list-size model
-----------------------------------------------------------------------------------------

-- A schema field coordinate, used as the target of field metadata.
structure FieldCoordinate where
  parentType : Name
  fieldName : Name
deriving Repr, DecidableEq

-- A schema location supported by IBM's `@cost` directive in the scoped syntax.
inductive CostCoordinate where
  | typeDefinition (typeName : Name)
  | fieldDefinition (field : FieldCoordinate)
  | argumentDefinition (field : FieldCoordinate) (argumentName : Name)
  | inputFieldDefinition (inputType : Name) (fieldName : Name)
deriving Repr, DecidableEq

-- The information represented by one IBM `@listSize` application. Names are already
-- parsed instead of being stored in their SDL string form.
structure ListSize where
  assumedSize : Option Nat := none
  slicingArguments : List Name := []
  sizedFields : List Name := []
  requireOneSlicingArgument : Bool := true
deriving Repr

-- Static-cost metadata kept separate from `Schema` because this project does not
-- model custom schema directives. Cost weights are signed so argument and input-field
-- weights can reduce a resolver's call cost; each complete field cost is clamped at zero.
structure CostModel where
  defaultListSize : Nat
  cost : CostCoordinate -> Option Int := fun _coordinate => none
  listSize : FieldCoordinate -> Option ListSize := fun _field => none

-- IBM reports type cost and field cost independently. Type cost is signed because the
-- specification permits negative type weights. Field cost remains nonnegative because
-- every complete field-call cost is clamped at zero.
structure Cost where
  typeCost : Int
  fieldCost : Nat
deriving Repr, DecidableEq

namespace Cost

def zero : Cost := { typeCost := 0, fieldCost := 0 }

def add (left right : Cost) : Cost :=
  {
    typeCost := left.typeCost + right.typeCost
    fieldCost := left.fieldCost + right.fieldCost
  }

instance : LE Cost where
  le lower upper :=
    lower.typeCost ≤ upper.typeCost ∧ lower.fieldCost ≤ upper.fieldCost

instance : DecidableRel (fun lower upper : Cost => lower ≤ upper) :=
  fun lower upper => by
    change Decidable
      (lower.typeCost ≤ upper.typeCost ∧ lower.fieldCost ≤ upper.fieldCost)
    infer_instance

instance : OfNat Cost 0 where
  ofNat := zero

instance : Add Cost where
  add := add

end Cost

-- Static query analysis bounds every response, including executions where a nullable
-- value or an error contributes no returned type. Its synthesized contributions are
-- therefore nonnegative even though the concrete IBM type cost is signed. Keeping this
-- invariant in the carrier lets the generic tree-summary order use zero as its bottom.
structure Bound where
  typeCost : Nat
  fieldCost : Nat
deriving Repr, DecidableEq

namespace Bound

def zero : Bound := { typeCost := 0, fieldCost := 0 }

def add (left right : Bound) : Bound :=
  {
    typeCost := left.typeCost + right.typeCost
    fieldCost := left.fieldCost + right.fieldCost
  }

def max (left right : Bound) : Bound :=
  {
    typeCost := Nat.max left.typeCost right.typeCost
    fieldCost := Nat.max left.fieldCost right.fieldCost
  }

def scale (count : Nat) (bound : Bound) : Bound :=
  {
    typeCost := count * bound.typeCost
    fieldCost := count * bound.fieldCost
  }

instance : LE Bound where
  le lower upper :=
    lower.typeCost ≤ upper.typeCost ∧ lower.fieldCost ≤ upper.fieldCost

instance : DecidableRel (fun lower upper : Bound => lower ≤ upper) :=
  fun lower upper => by
    change Decidable
      (lower.typeCost ≤ upper.typeCost ∧ lower.fieldCost ≤ upper.fieldCost)
    infer_instance

def toCost (bound : Bound) : Cost :=
  {
    typeCost := Int.ofNat bound.typeCost
    fieldCost := bound.fieldCost
  }

instance : OfNat Bound 0 where
  ofNat := zero

end Bound

-----------------------------------------------------------------------------------------
-- Input and schema cost helpers
-----------------------------------------------------------------------------------------

def typeRefIsListOutput : TypeRef -> Bool
  | .named _typeName => false
  | .list _inner => true
  | .nonNull inner => typeRefIsListOutput inner

def fieldCoordinate (parentType fieldName : Name) : FieldCoordinate :=
  { parentType, fieldName }

def CostModel.costWeight (model : CostModel) (coordinate : CostCoordinate) : Int :=
  (model.cost coordinate).getD 0

def defaultTypeCost (typeDefinition : TypeDefinition) : Nat :=
  match typeDefinition with
  | .object _objectType => 1
  | .interface _interfaceType => 1
  | .union _unionType => 1
  | .inputObject _inputObjectType => 1
  | .builtinScalar _scalar => 0
  | .customScalar _scalar => 0
  | .enum _enumType => 0

-- Object, scalar, and enum weights use the modeled signed `@cost` value when present.
-- Abstract return types use the maximum possible concrete-object weight, as required
-- for a static upper bound. In particular, the maximum is not seeded with zero: a set
-- of exclusively negative possible-type weights remains negative.
def namedTypeCost (schema : Schema) (model : CostModel) (typeName : Name) : Int :=
  match schema.lookupType typeName with
  | none => 0
  | some (.interface _interfaceType)
  | some (.union _unionType) =>
      let possibleTypes := schema.getPossibleTypes typeName
      (possibleTypes.map
        fun objectName =>
          (model.cost (.typeDefinition objectName)).getD 1)
      |>.max?
      |>.getD 1
  | some typeDefinition =>
      match model.cost (.typeDefinition typeName) with
      | some weight => weight
      | none => Int.ofNat (defaultTypeCost typeDefinition)

def outputTypeCost (schema : Schema) (model : CostModel) (outputType : TypeRef) : Int :=
  namedTypeCost schema model outputType.namedType

-- The syntactic backend factors common field transfers. That transformation duplicates
-- return-type contributions and is order-preserving only when type costs are
-- nonnegative. Negative argument and input-field weights do not affect this predicate:
-- they are already combined and clamped at the field-call boundary.
def TypeCostsNonnegative (schema : Schema) (model : CostModel) : Prop :=
  ∀ typeName, 0 ≤ namedTypeCost schema model typeName

def defaultFieldWeight (schema : Schema) (outputType : TypeRef) : Nat :=
  match schema.lookupType outputType.namedType with
  | some typeDefinition => defaultTypeCost typeDefinition
  | none => 0

-- StaticCost consumes the successful schema-coerced argument map produced by
-- `Execution.coerceArgumentValues`. A coercion error invokes no resolver and therefore
-- contributes no argument values; the containing field transfer still accounts for the
-- response field itself.
def argumentCoercionResultArguments : Execution.ArgumentCoercionResult -> List Argument
  | .success arguments => arguments.map Execution.CoercedArgument.toArgument
  | .error => []

-- Keeping every value for a name leaves this
-- low-level helper total on arbitrary argument maps; execution-produced maps have
-- unique names. The cost fold is proved semantically insensitive to input-object field
-- order.
def argumentValues (arguments : List Argument) (argumentName : Name) : List InputValue :=
  (arguments.filterMap
    fun argument =>
      if argument.name == argumentName then some argument.value else none)

-- IBM slicing arguments have type `Int` (possibly non-null). Negative values are
-- conservatively clamped to zero by the integral model.
def inferListSize? (value : InputValue) : Option Nat :=
  match value with
  | .int size => some size.toNat
  | _ => none

def maximum? (values : List Nat) : Option Nat :=
  values.max?

def slicingArgumentSize? (arguments : List Argument) (argumentName : Name)
    : Option Nat := do
  maximum? ((argumentValues arguments argumentName).filterMap inferListSize?)

-- Slicing values take precedence over `assumedSize`; when several are available their
-- maximum preserves the static upper bound. `requireOneSlicingArgument` is validation
-- metadata and does not make this total estimator partial.
def ListSize.expectedSize? (listSize : ListSize) (arguments : List Argument)
    : Option Nat :=
  maximum? (listSize.slicingArguments.filterMap (slicingArgumentSize? arguments))
  |>.orElse (fun _unit => listSize.assumedSize)

private def inputCoordinateWeight (schema : Schema) (model : CostModel)
    (coordinate : CostCoordinate) (definition : InputValueDefinition)
    : Int :=
  match model.cost coordinate with
  | some weight => weight
  | none =>
      match schema.lookupType definition.inputType.namedType with
      | some typeDefinition => Int.ofNat (defaultTypeCost typeDefinition)
      | none => 0

-- Cost of one effective argument or input field. Its coordinate weight is paid once;
-- list values then sum the costs of input fields used inside their elements without
-- repeating the containing argument or input-field weight. Missing/default semantics
-- have already been materialized, so this fold is structural even for recursive input
-- object types.
mutual
  def resolvedInputValueCost (schema : Schema) (model : CostModel)
      (includeOwnWeight : Bool) (coordinate : CostCoordinate)
      (definition : InputValueDefinition)
      : InputValue -> Int
    | .list values =>
        let ownWeight :=
          if includeOwnWeight then
            inputCoordinateWeight schema model coordinate definition
          else
            0
        ownWeight + resolvedInputValuesCost schema model coordinate definition values
    | .object fields =>
        let ownWeight :=
          if includeOwnWeight then
            inputCoordinateWeight schema model coordinate definition
          else
            0
        match schema.lookupInputObject definition.inputType.namedType with
        | none => ownWeight
        | some inputObject =>
            ownWeight + resolvedInputObjectFieldsCost schema model inputObject fields
    | _ =>
        if includeOwnWeight then
          inputCoordinateWeight schema model coordinate definition
        else
          0
  termination_by value => sizeOf value
  decreasing_by
    all_goals
      simp_wf

  def resolvedInputValuesCost (schema : Schema) (model : CostModel)
      (coordinate : CostCoordinate) (definition : InputValueDefinition)
      : List InputValue -> Int
    | [] => 0
    | value :: rest =>
        resolvedInputValueCost schema model false coordinate definition value
        + resolvedInputValuesCost schema model coordinate definition rest
  termination_by values => sizeOf values
  decreasing_by
    all_goals
      simp_wf
      omega

  def resolvedInputObjectFieldsCost (schema : Schema) (model : CostModel)
      (inputObject : InputObjectType)
      : List (Name × InputValue) -> Int
    | [] => 0
    | (fieldName, value) :: rest =>
        (match Schema.lookupArgumentDefinition inputObject.inputFields fieldName with
          | none => 0
          | some fieldDefinition =>
              resolvedInputValueCost schema model true
                (.inputFieldDefinition inputObject.name fieldName) fieldDefinition value)
        + resolvedInputObjectFieldsCost schema model inputObject rest
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals
      simp_wf
      omega
end

def inputValueCost (schema : Schema) (model : CostModel)
    (coordinate : CostCoordinate) (definition : InputValueDefinition) (value : InputValue)
    : Int :=
  resolvedInputValueCost schema model true coordinate definition value

def maximumInt? (values : List Int) : Option Int :=
  values.max?

def argumentsCost (schema : Schema) (model : CostModel)
    (field : FieldCoordinate)
    (definitions : List InputValueDefinition) (arguments : List Argument)
    : Int :=
  definitions.foldl
    (fun cost definition =>
      let values := argumentValues arguments definition.name
      let argumentCost :=
        maximumInt?
          (values.map
            fun value =>
              inputValueCost schema model
                (.argumentDefinition field definition.name) definition value)
        |>.getD 0
      cost + argumentCost)
    0

-----------------------------------------------------------------------------------------
-- Tree-summary algebra for cost analysis
-----------------------------------------------------------------------------------------

-- A resolved `sizedFields` entry waiting to be applied to a direct child field.
structure SizedField where
  fieldName : Name
  size : Nat
deriving Repr

abbrev Summary := List SizedField -> Bound

-- Pointwise order on synthesized static-cost summaries.
def SummaryBound (lower upper : Summary) : Prop :=
  ∀ sizedFields, lower sizedFields ≤ upper sizedFields

def sizesForField (fieldName : Name) (sizedFields : List SizedField) : List Nat :=
  sizedFields.filterMap
    fun sizedField =>
      if sizedField.fieldName == fieldName then some sizedField.size else none

def inheritedSize? (fieldName : Name) (sizedFields : List SizedField) : Option Nat :=
  maximum? (sizesForField fieldName sizedFields)

def ListSize.resolvedSizedFields (listSize : ListSize) (expectedSize : Option Nat)
    : List SizedField :=
  match expectedSize with
  | none => []
  | some size =>
      listSize.sizedFields.map fun fieldName => { fieldName, size }

def selectionFieldUse? : Selection -> Option (Name × List Argument)
  | .field _responseName fieldName arguments _directives _selectionSet =>
      some (fieldName, arguments)
  | .inlineFragment _typeCondition _directives _selectionSet => none

def expectedListSize? (model : CostModel) (coordinate : FieldCoordinate)
    (arguments : List Argument)
    : Option Nat :=
  (model.listSize coordinate).bind fun annotation => annotation.expectedSize? arguments

def childSizedFields (model : CostModel) (coordinate : FieldCoordinate)
    (expectedSize : Option Nat)
    : List SizedField :=
  match model.listSize coordinate with
  | some annotation => annotation.resolvedSizedFields expectedSize
  | none => []

def staticInstanceCount (model : CostModel) (coordinate : FieldCoordinate)
    (fieldName : Name)
    (definition : FieldDefinition) (expectedSize : Option Nat)
    (inheritedSizedFields : List SizedField)
    : Nat :=
  if typeRefIsListOutput definition.outputType then
    let ownExpectedSize :=
      match model.listSize coordinate with
      | some annotation =>
          if annotation.sizedFields.isEmpty then expectedSize else none
      | none => expectedSize
    (inheritedSize? fieldName inheritedSizedFields).getD
      (ownExpectedSize.getD model.defaultListSize)
  else
    1

def fieldCallWeight (schema : Schema) (model : CostModel)
    (coordinate : FieldCoordinate)
    (definition : FieldDefinition) (arguments : List Argument)
    : Int :=
  let ownWeight :=
    match model.cost (.fieldDefinition coordinate) with
    | some weight => weight
    | none => Int.ofNat (defaultFieldWeight schema definition.outputType)
  ownWeight + argumentsCost schema model coordinate definition.arguments arguments

def fieldCallCost (schema : Schema) (model : CostModel)
    (coordinate : FieldCoordinate)
    (definition : FieldDefinition) (arguments : List Argument)
    : Nat :=
  (fieldCallWeight schema model coordinate definition arguments).toNat

-- Low-level field transfer over the already-coerced resolver argument map.
def fieldUseCostAtParentType (schema : Schema) (model : CostModel)
    (parentType : Name)
    (childSummary : Summary) (inheritedSizedFields : List SizedField)
    (fieldName : Name) (arguments : List Argument)
    : Bound :=
  let coordinate := fieldCoordinate parentType fieldName
  match schema.lookupField parentType fieldName with
  | none => childSummary []
  | some definition =>
      let expectedSize := expectedListSize? model coordinate arguments
      let childCost := childSummary (childSizedFields model coordinate expectedSize)
      let instanceCount :=
        staticInstanceCount model coordinate fieldName definition expectedSize
          inheritedSizedFields
      {
        typeCost :=
          (Int.ofNat instanceCount
            * (outputTypeCost schema model definition.outputType
                + Int.ofNat childCost.typeCost)).toNat
        fieldCost :=
          fieldCallCost schema model coordinate definition arguments
          + instanceCount * childCost.fieldCost
      }

-- Request-aware entry to one parent-type transfer. Argument coercion happens exactly
-- where the schema field definition becomes known, matching `resolveFieldValue` and
-- annotated execution.
def fieldUseCostAtParentTypeWithVariables (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (parentType : Name)
    (childSummary : Summary) (inheritedSizedFields : List SizedField)
    (fieldName : Name) (arguments : List Argument)
    : Bound :=
  match schema.lookupField parentType fieldName with
  | none => childSummary []
  | some definition =>
      fieldUseCostAtParentType schema model parentType childSummary
        inheritedSizedFields fieldName
        (argumentCoercionResultArguments
          (Execution.coerceArgumentValues schema variableValues definition.arguments
            arguments))

-- A condition group can denote any of its possible runtime object parents. Static
-- analysis takes their maximum; concrete execution selects exactly one of them.
def fieldUseCost (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (group : CollectedFieldGroup)
    (childSummary : Summary) (inheritedSizedFields : List SizedField)
    (fieldName : Name) (arguments : List Argument)
    : Bound :=
  group.condition.possibleTypes.foldl
    (fun cost parentType =>
      Bound.max cost
        (fieldUseCostAtParentTypeWithVariables schema model variableValues parentType
          childSummary inheritedSizedFields fieldName arguments))
    .zero

def groupCost (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (group : CollectedFieldGroup)
    (childSummary : Summary) (inheritedSizedFields : List SizedField)
    : Bound :=
  group.selections.foldl
    (fun cost selection =>
      match selectionFieldUse? selection with
      | none => cost
      | some (fieldName, arguments) =>
          Bound.max cost
            (fieldUseCost schema model variableValues group childSummary
              inheritedSizedFields fieldName arguments))
    .zero

-- The synthesized summary is a function of inherited, already-resolved `sizedFields`
-- metadata. This lets a bottom-up fold apply a parent field's list-size annotation to a
-- selected direct-child list.
abbrev algebra (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues)
    : Algebra :=
  {
    Summary := Summary
    empty := fun _sizedFields => .zero
    field :=
      fun group childSummary sizedFields =>
        groupCost schema model variableValues group childSummary sizedFields
    combine :=
      fun left right sizedFields => Bound.add (left sizedFields) (right sizedFields)
    join :=
      fun left right sizedFields => Bound.max (left sizedFields) (right sizedFields)
  }

-----------------------------------------------------------------------------------------
-- Public analysis entry points
-----------------------------------------------------------------------------------------

namespace ExactCases

-- Exact-case estimate after applying operation-variable defaults and supplied values.
def estimateOperationWithVariables (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : Cost :=
  let selectionCost :=
    (TreeSummary.ExactCases.summarizeOperationWithVariables
      (algebra schema model) schema variableValues operation)
      []
  {
    typeCost :=
      max 0
        (namedTypeCost schema model schema.queryType + Int.ofNat selectionCost.typeCost)
    fieldCost := selectionCost.fieldCost
  }

end ExactCases

namespace Syntactic

-- Fast syntactic estimate after applying defaults and supplied variable values.
def estimateOperationWithVariables (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : Cost :=
  let selectionCost :=
    (TreeSummary.Syntactic.summarizeOperationWithVariables
      (algebra schema model) schema variableValues operation)
      []
  {
    typeCost :=
      max 0
        (namedTypeCost schema model schema.queryType + Int.ofNat selectionCost.typeCost)
    fieldCost := selectionCost.fieldCost
  }

end Syntactic

-----------------------------------------------------------------------------------------
-- Concrete response semantics and soundness obligations
-----------------------------------------------------------------------------------------

-- Analysis-specific multiplicity of returned, non-null cost-bearing values after list
-- wrappers are traversed. Null is still observed by the enclosing field rule, which
-- pays its resolver-call cost, but contributes no returned type or child cost.
mutual
  def actualInstanceCount : AnnotatedResponseValue -> Nat
    | .null => 0
    | .scalar _value => 1
    | .object _runtimeType _fields => 1
    | .list values => actualInstanceCountList values

  def actualInstanceCountList : List AnnotatedResponseValue -> Nat
    | [] => 0
    | value :: rest =>
        actualInstanceCount value + actualInstanceCountList rest
end

-- The concrete value produced after one response boundary has been observed. It carries
-- both IBM actual costs and the response-list bound needed to relate actual
-- cardinalities to static estimates.
structure ResponseObservation where
  cost : List SizedField -> Cost
  admissible : List SizedField -> Prop

def ResponseObservation.empty : ResponseObservation :=
  {
    cost := fun _sizedFields => .zero
    admissible := fun _sizedFields => True
  }

def ResponseObservation.combine (left right : ResponseObservation)
    : ResponseObservation :=
  {
    cost := fun sizedFields => Cost.add (left.cost sizedFields) (right.cost sizedFields)
    admissible :=
      fun sizedFields =>
        left.admissible sizedFields ∧ right.admissible sizedFields
  }

-- IBM type cost counts returned values. Execution only produces scalar leaves for
-- scalar or enum output types; using the output-type cost directly also keeps this
-- concrete fold total on arbitrary annotated values.
def responseLeafTypeCost (schema : Schema) (model : CostModel) (outputType : TypeRef)
    : Int :=
  outputTypeCost schema model outputType

-- Exact type cost contributed by the completed value. Child field costs are synthesized
-- separately by the concrete response algebra.
mutual
  def responseValueTypeCost (schema : Schema) (model : CostModel) (outputType : TypeRef)
      : AnnotatedResponseValue -> Int
    | .null => 0
    | .scalar _value => responseLeafTypeCost schema model outputType
    | .object _runtimeType _fields => outputTypeCost schema model outputType
    | .list values =>
        responseValuesTypeCost schema model outputType values

  def responseValuesTypeCost (schema : Schema) (model : CostModel) (outputType : TypeRef)
      : List AnnotatedResponseValue -> Int
    | [] => 0
    | value :: rest =>
        responseValueTypeCost schema model outputType value
        + responseValuesTypeCost schema model outputType rest
end

def responseFieldCost (schema : Schema) (model : CostModel)
    (definition : ResolvedFieldProvenance)
    (value : AnnotatedResponseValue) (children : ResponseObservation)
    (_inheritedSizedFields : List SizedField)
    : Cost :=
  let coordinate := fieldCoordinate definition.parentType definition.fieldName
  match schema.lookupField definition.parentType definition.fieldName with
  | none => .zero
  | some schemaDefinition =>
      let arguments := argumentCoercionResultArguments definition.coercedArguments
      let expectedSize := expectedListSize? model coordinate arguments
      let childContext := childSizedFields model coordinate expectedSize
      let callWeight := fieldCallWeight schema model coordinate schemaDefinition arguments
      match value with
      | .list values =>
          {
            typeCost :=
              responseValuesTypeCost schema model schemaDefinition.outputType values
              + (children.cost childContext).typeCost
            fieldCost := callWeight.toNat + (children.cost childContext).fieldCost
          }
      | .null =>
          { typeCost := 0, fieldCost := callWeight.toNat }
      | .scalar _scalar =>
          {
            typeCost := responseLeafTypeCost schema model schemaDefinition.outputType
            fieldCost := callWeight.toNat
          }
      | .object _runtimeType _fields =>
          {
            typeCost :=
              outputTypeCost schema model schemaDefinition.outputType
              + (children.cost childContext).typeCost
            fieldCost := callWeight.toNat + (children.cost childContext).fieldCost
          }

def responseFieldAdmissible (schema : Schema) (model : CostModel)
    (definition : ResolvedFieldProvenance)
    (value : AnnotatedResponseValue) (children : ResponseObservation)
    (inheritedSizedFields : List SizedField)
    : Prop :=
  let coordinate := fieldCoordinate definition.parentType definition.fieldName
  match schema.lookupField definition.parentType definition.fieldName with
  | none => children.admissible inheritedSizedFields
  | some schemaDefinition =>
      let arguments := argumentCoercionResultArguments definition.coercedArguments
      let expectedSize := expectedListSize? model coordinate arguments
      actualInstanceCount value
        ≤ staticInstanceCount model coordinate definition.fieldName schemaDefinition
            expectedSize inheritedSizedFields
      ∧ children.admissible (childSizedFields model coordinate expectedSize)

def responseFieldObservation (schema : Schema) (model : CostModel)
    (definition : ResolvedFieldProvenance)
    (value : AnnotatedResponseValue) (children : ResponseObservation)
    : ResponseObservation :=
  {
    cost :=
      fun sizedFields =>
        responseFieldCost schema model definition value children sizedFields
    admissible :=
      fun sizedFields =>
        responseFieldAdmissible schema model definition value children sizedFields
  }

-- Concrete static-cost semantics.
abbrev concreteAlgebra (schema : Schema) (model : CostModel) : ConcreteAlgebra :=
  {
    Summary := ResponseObservation
    empty := .empty
    combine := ResponseObservation.combine
    field := responseFieldObservation schema model
  }

-----------------------------------------------------------------------------------------
-- Soundness statements
-----------------------------------------------------------------------------------------

def evaluateAnnotatedResponse (schema : Schema) (model : CostModel)
    (response : AnnotatedResponse)
    : ResponseObservation :=
  TreeSummary.foldAnnotatedResponse (concreteAlgebra schema model) response

def responseRootCost (schema : Schema) (model : CostModel) (response : AnnotatedResponse)
    : Cost :=
  match response.data with
  | .object _runtimeType _fields =>
      { typeCost := namedTypeCost schema model schema.queryType, fieldCost := 0 }
  | _ => .zero

-- IBM query-response costs calculated from the annotated response. Field and argument
-- costs are paid once per resolver; returned values determine type counts, including
-- the query root.
def actualCost (schema : Schema) (model : CostModel) (response : AnnotatedResponse)
    : Cost :=
  Cost.add (responseRootCost schema model response)
    ((evaluateAnnotatedResponse schema model response).cost [])

-- The concrete response satisfies every list-size estimate encountered while matching
-- the operation to the response. This assumption is necessary: an estimated list size
-- is not an upper bound when a resolver returns more items than the model predicts.
def ResponseWithinEstimatedSizes (schema : Schema) (model : CostModel)
    (response : AnnotatedResponse)
    : Prop :=
  (evaluateAnnotatedResponse schema model response).admissible []

namespace ExactCases

-- Execution soundness for the variable-aware exact-case estimator at explicit fuel. Its
-- theorem witness is `StaticCost.ExactCases.soundWithVariablesWithFuel` in
-- `Proofs.GraphQL.Theories.TreeSummary.StaticCost`.
def SoundWithVariablesWithFuel (schema : Schema) (model : CostModel)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Execution.Resolvers ObjectRef)
        (variableValues : Execution.VariableValues) (fuel : Nat)
        (source : Execution.ResolverValue ObjectRef),
      ResponseWithinEstimatedSizes schema model
        (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
          source)
      -> actualCost schema model
            (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
              source)
          ≤ estimateOperationWithVariables schema model variableValues operation

-- Default-executor soundness target, quantified over all resolvers, variable conditions,
-- and root source values. Its theorem witness is
-- `StaticCost.ExactCases.soundWithVariables` in the static-cost proof module.
def SoundWithVariables (schema : Schema) (model : CostModel) (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Execution.Resolvers ObjectRef)
        (variableValues : Execution.VariableValues)
        (source : Execution.ResolverValue ObjectRef),
      ResponseWithinEstimatedSizes schema model
        (executeQueryAnnotated schema resolvers variableValues operation source)
      -> actualCost schema model
            (executeQueryAnnotated schema resolvers variableValues operation source)
          ≤ estimateOperationWithVariables schema model variableValues operation

end ExactCases

namespace Syntactic

-- Execution soundness for the variable-aware syntactic estimator at explicit fuel,
-- assuming nonnegative type costs so factored field transfers remain subadditive. Its
-- theorem witness is `StaticCost.Syntactic.soundWithVariablesWithFuel` in the proof
-- module.
def SoundWithVariablesWithFuel (schema : Schema) (model : CostModel)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> TypeCostsNonnegative schema model
  -> ∀ (ObjectRef : Type) (resolvers : Execution.Resolvers ObjectRef)
        (variableValues : Execution.VariableValues) (fuel : Nat)
        (source : Execution.ResolverValue ObjectRef),
      ResponseWithinEstimatedSizes schema model
        (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
          source)
      -> actualCost schema model
            (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
              source)
          ≤ estimateOperationWithVariables schema model variableValues operation

-- Default-executor soundness for the variable-aware syntactic estimator under the same
-- nonnegative-type-cost premise. Its theorem witness is
-- `StaticCost.Syntactic.soundWithVariables` in the static-cost proof module.
def SoundWithVariables (schema : Schema) (model : CostModel) (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> TypeCostsNonnegative schema model
  -> ∀ (ObjectRef : Type) (resolvers : Execution.Resolvers ObjectRef)
        (variableValues : Execution.VariableValues)
        (source : Execution.ResolverValue ObjectRef),
      ResponseWithinEstimatedSizes schema model
        (executeQueryAnnotated schema resolvers variableValues operation source)
      -> actualCost schema model
            (executeQueryAnnotated schema resolvers variableValues operation source)
          ≤ estimateOperationWithVariables schema model variableValues operation

end Syntactic

-----------------------------------------------------------------------------------------
-- Optimality statements
-----------------------------------------------------------------------------------------

namespace ExactCases

-- Local static-cost semantics used by the exact-case optimality theorem. Each field
-- outcome applies one deterministic modeled field transfer; condition alternatives
-- remain separate outcomes.
abbrev caseSemantics (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues)
    : TreeSummary.ExactCases.CaseSemantics :=
  {
    Summary := Summary
    empty := fun _sizedFields => .zero
    combine :=
      fun left right sizedFields => Bound.add (left sizedFields) (right sizedFields)
    fieldOutcomes :=
      fun group childSummary =>
        OutcomeSet.singleton
          (fun sizedFields =>
            groupCost schema model variableValues group childSummary sizedFields)
  }

-- The variable-aware exact-case summary is the pointwise least bound of its recursively
-- feasible modeled outcomes. Its witness is
-- `StaticCost.ExactCases.summaryOptimalWithVariables` in the static-cost proof module.
def SummaryOptimalWithVariables (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : Prop :=
  let coercedVariableValues := Execution.coerceVariableValues operation variableValues
  Optimality.BestBound SummaryBound SummaryBound
    (TreeSummary.ExactCases.operationOutcomesWithVariables
      (caseSemantics schema model coercedVariableValues)
      schema variableValues operation)
    (TreeSummary.ExactCases.summarizeOperationWithVariables
      (algebra schema model) schema variableValues operation)

end ExactCases

end StaticCost
end TreeSummary
end GraphQL
