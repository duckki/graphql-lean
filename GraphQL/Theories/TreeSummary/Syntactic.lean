import GraphQL.Theories.TreeSummary.ResponseFold
import GraphQL.Theories.ConditionTree.Execution

/-! Fast syntactic tree-summary traversal.

Each condition-tree node evaluates its local type branches over the nonempty symbolic
regions induced by their conditions and factors its local Boolean branches directly by
variable. Selected child subtrees are summarized recursively without globally regrouping
response names across syntactic nodes. Neither local path constructs a Cartesian product
with the other.
-/

namespace GraphQL
namespace TreeSummary
namespace Syntactic

open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open GraphQL.Execution
open GraphQL.AnnotatedExecution
open TreeSummary.Measure

universe u v

-----------------------------------------------------------------------------------------
-- Branch condition helpers
-----------------------------------------------------------------------------------------

-- Resolves a condition-tree Boolean literal against already-coerced variable values.
-- `none` leaves the literal unknown and therefore conservatively included.
def evaluateBooleanLiteral? (variableValues : Execution.VariableValues)
    (literal : BooleanLiteral)
    : Option Bool := do
  let value ← Execution.inputValueBoolean? variableValues (.variable literal.variableName)
  pure (value == literal.requiredValue)

-- A widened summary for one feasible immediate Boolean branch.
structure BooleanBranchSummary (Summary : Type u) where
  literal : BooleanLiteral
  summary : Summary

-- The simultaneous contributions selected by each value of one Boolean variable.
-- `none` means that the value selects no branch, rather than an algebra summary that
-- happens to equal `empty`.
structure BooleanAlternatives (Summary : Type u) where
  whenFalse : Option Summary := none
  whenTrue : Option Summary := none

def combineOptional (algebra : Algebra.{u})
    : Option algebra.Summary -> Option algebra.Summary -> Option algebra.Summary
  | none, right => right
  | left, none => left
  | some left, some right => some (algebra.combine left right)

def joinOptional (algebra : Algebra.{u})
    : Option algebra.Summary -> Option algebra.Summary -> Option algebra.Summary
  | none, right => right
  | left, none => left
  | some left, some right => some (algebra.join left right)

def BooleanAlternatives.add (algebra : Algebra.{u}) (requiredValue : Bool)
    (summary : algebra.Summary) (alternatives : BooleanAlternatives algebra.Summary)
    : BooleanAlternatives algebra.Summary :=
  if requiredValue then
    {
      alternatives with
        whenTrue := combineOptional algebra alternatives.whenTrue (some summary)
    }
  else
    {
      alternatives with
        whenFalse := combineOptional algebra alternatives.whenFalse (some summary)
    }

-- Inserts one branch into the syntax-ordered association list for its variable.
def addBooleanBranchSummary (algebra : Algebra.{u})
    (branch : BooleanBranchSummary algebra.Summary)
    : List (Name × BooleanAlternatives algebra.Summary)
      -> List (Name × BooleanAlternatives algebra.Summary)
  | [] =>
      [(
        branch.literal.variableName,
        ({} : BooleanAlternatives algebra.Summary).add algebra
          branch.literal.requiredValue branch.summary
      )]
  | (variableName, alternatives) :: rest =>
      if branch.literal.variableName == variableName then
        (
          variableName,
          alternatives.add algebra branch.literal.requiredValue branch.summary
        )
        :: rest
      else
        (variableName, alternatives) :: addBooleanBranchSummary algebra branch rest

def collectBooleanAlternatives (algebra : Algebra.{u})
    (branches : List (BooleanBranchSummary algebra.Summary))
    : List (Name × BooleanAlternatives algebra.Summary) :=
  branches.foldl
    (fun alternatives branch => addBooleanBranchSummary algebra branch alternatives) []

def summarizeBooleanAlternatives? (algebra : Algebra.{u})
    (variableValues : Execution.VariableValues)
    (entry : Name × BooleanAlternatives algebra.Summary)
    : Option algebra.Summary :=
  match Execution.inputValueBoolean? variableValues (.variable entry.1) with
  | some false => entry.2.whenFalse
  | some true => entry.2.whenTrue
  | none => joinOptional algebra entry.2.whenFalse entry.2.whenTrue

-- Each variable chooses between its false and true branch products. Choices for
-- distinct variables are independent and therefore combine, without constructing the
-- `2^N` complete assignments or syntax-aligned masks.
def summarizeBooleanBranchSummaries (algebra : Algebra.{u})
    (variableValues : Execution.VariableValues)
    (branches : List (BooleanBranchSummary algebra.Summary))
    : algebra.Summary :=
  combineMap algebra (collectBooleanAlternatives algebra branches)
    fun entry _hentry =>
      (summarizeBooleanAlternatives? algebra variableValues entry).getD algebra.empty

-- Cached applicability and widened summary for one feasible immediate type branch.
structure TypeBranchSummary (Summary : Type u) where
  possibleTypes : PossibleTypes
  summary : Summary

-- Compact summaries of the two independent immediate-branch families at one tree node.
-- Each source branch contributes to exactly one list; infeasible type scopes and known-
-- false Boolean branches contribute to neither.
structure ImmediateBranchSummaries (Summary : Type u) where
  typeBranches : List (TypeBranchSummary Summary) := []
  booleanBranches : List (BooleanBranchSummary Summary) := []

-----------------------------------------------------------------------------------------
-- Widened syntactic traversal
-----------------------------------------------------------------------------------------

-- Sparse product of the summaries active for one runtime object. `none` means that no
-- type branch is active, so callers can omit that alternative without a second scan.
def summarizeTypeBranchCase? (algebra : Algebra.{u}) (runtimeType : Name)
    : List (TypeBranchSummary algebra.Summary) -> Option algebra.Summary
  | [] => none
  | branch :: branches =>
      let rest := summarizeTypeBranchCase? algebra runtimeType branches
      if branch.possibleTypes.contains runtimeType then
        match rest with
        | none => some branch.summary
        | some tail => some (algebra.combine branch.summary tail)
      else
        rest

def typeBranchPossibleTypes {Summary : Type u}
    (branches : List (TypeBranchSummary Summary))
    : List PossibleTypes :=
  branches.filterMap
    fun branch =>
      if branch.possibleTypes.isEmpty then none else some branch.possibleTypes

-- Only nonempty, materializable activation patterns are represented. Several concrete
-- object names that satisfy exactly the same branch conditions remain in one region.
def typeBranchRegions {Summary : Type u} (typeScope : PossibleTypes)
    (branches : List (TypeBranchSummary Summary))
    : List PossibleTypeRegion :=
  possibleTypeRegions typeScope (typeBranchPossibleTypes branches)

-- Region construction guarantees nonemptiness, but this helper remains total for
-- arbitrary callers. Condition membership is constant within a generated region, so
-- its first runtime type represents the entire region's branch product.
def summarizeTypeBranchRegion? (algebra : Algebra.{u})
    (region : PossibleTypeRegion)
    (branches : List (TypeBranchSummary algebra.Summary))
    : Option algebra.Summary :=
  match region with
  | [] => none
  | runtimeType :: _rest => summarizeTypeBranchCase? algebra runtimeType branches

def typeRuntimeCaseSummaries (algebra : Algebra.{u})
    (typeScope : PossibleTypes) (branches : List (TypeBranchSummary algebra.Summary))
    : List algebra.Summary :=
  (typeBranchRegions typeScope branches).filterMap
    fun region => summarizeTypeBranchRegion? algebra region branches

-- Evaluates every distinct feasible type-condition product using the cached branch
-- scopes. Runtime object types with the same product are joined only once; impossible
-- products and inactive alternatives are never materialized.
def summarizeTypeRuntimeCases (algebra : Algebra.{u})
    (typeScope : PossibleTypes) (branches : List (TypeBranchSummary algebra.Summary))
    : algebra.Summary :=
  let cases := typeRuntimeCaseSummaries algebra typeScope branches
  joinMap algebra cases fun summary _hsummary => summary

private def treePhase : Nat := 0
private def branchPhase : Nat := 0
private def fieldGroupsPhase : Nat := 1
private def childTypesPhase : Nat := 0

mutual
  -- Partitions and synthesizes every immediate branch in one pass under its own
  -- condition and the node's widened context. Concrete type alternatives and
  -- per-variable Boolean alternatives are evaluated independently; they never form a
  -- Cartesian product.
  def summarizeTree (algebra : Algebra) (schema : Schema)
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (tree : Tree) (variableValues : Execution.VariableValues)
      (typeScope : PossibleTypes := tree.condition.possibleTypes)
      : algebra.Summary :=
    let groups := collectFieldGroups inheritedBooleanCondition tree.condition tree.fields
    let branchSummaries :=
      summarizeBranches algebra schema parentType inheritedBooleanCondition tree.branches
        variableValues typeScope
    algebra.combine
      (summarizeFieldGroups algebra schema groups variableValues)
      branchSummaries
  termination_by
    (conditionTreeResponseDepth tree, sizeOf tree, treePhase, 0)
  decreasing_by
    · simp only [conditionTreeResponseDepth]
      apply quadruple_lt_of_depth_le_of_control_lt
      · exact Nat.le_max_right _ _
      · cases tree
        simp_wf
        omega
    · simp only [conditionTreeResponseDepth]
      rw [collectedFieldGroupsResponseDepth_collectFieldGroups]
      apply quadruple_lt_of_depth_le_of_control_lt
      · exact Nat.le_max_left _ _
      · cases tree
        simp_wf
        omega

  def summarizeBranches (algebra : Algebra) (schema : Schema)
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (branches : List (Branch Tree)) (variableValues : Execution.VariableValues)
      (typeScope : PossibleTypes)
      : algebra.Summary :=
    let summaries :=
      summarizeImmediateBranches algebra schema parentType inheritedBooleanCondition
        branches variableValues typeScope
    algebra.combine
      (summarizeTypeRuntimeCases algebra typeScope summaries.typeBranches)
      (summarizeBooleanBranchSummaries algebra variableValues summaries.booleanBranches)
  termination_by
    (conditionBranchesResponseDepth branches, sizeOf branches, fieldGroupsPhase, 0)
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · decide

  def summarizeImmediateBranches (algebra : Algebra) (schema : Schema)
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (branches : List (Branch Tree)) (variableValues : Execution.VariableValues)
      (typeScope : PossibleTypes)
      : ImmediateBranchSummaries algebra.Summary :=
    match branches with
    | [] => {}
    | branch :: rest =>
        let tail :=
          summarizeImmediateBranches algebra schema parentType
            inheritedBooleanCondition rest variableValues typeScope
        match branch.condition with
        | .typeCondition typeName =>
            -- Reuse the cumulative set stored by extraction instead of querying the
            -- schema again. Empty intersections are omitted before recursion.
            let branchScope :=
              intersectPossibleTypes typeScope branch.body.condition.possibleTypes
            if branchScope.isEmpty then
              tail
            else
              {
                tail with
                  typeBranches :=
                    {
                      possibleTypes := branchScope
                      summary :=
                        summarizeTree algebra schema typeName inheritedBooleanCondition
                          branch.body variableValues branchScope
                    }
                    :: tail.typeBranches
              }
        | .booleanLiteral literal =>
            match evaluateBooleanLiteral? variableValues literal with
            | some false => tail
            | some true | none =>
                -- Unresolved literals remain symbolic in the cached branch summary.
                {
                  tail with
                    booleanBranches :=
                      {
                        literal
                        summary :=
                          summarizeTree algebra schema parentType
                            inheritedBooleanCondition branch.body variableValues typeScope
                      }
                      :: tail.booleanBranches
                }
  termination_by
    (conditionBranchesResponseDepth branches, sizeOf branches, branchPhase, 0)
  decreasing_by
    · simp only [conditionBranchesResponseDepth]
      apply quadruple_lt_of_depth_le_of_control_lt
      · exact Nat.le_max_right _ _
      · simp_wf
        omega
    · simp only [conditionBranchesResponseDepth]
      apply quadruple_lt_of_depth_le_of_control_lt
      · exact Nat.le_max_left _ _
      · cases branch
        simp_wf
        omega
    · simp only [conditionBranchesResponseDepth]
      apply quadruple_lt_of_depth_le_of_control_lt
      · exact Nat.le_max_left _ _
      · cases branch
        simp_wf
        omega

  def summarizeFieldGroups (algebra : Algebra) (schema : Schema)
      (groups : List CollectedFieldGroup)
      (variableValues : Execution.VariableValues)
      : algebra.Summary :=
    combineMap algebra groups
      (fun group _hgroup =>
        algebra.field group
          (summarizeChildTypes algebra schema group
            (childParentTypes schema group) variableValues))
  termination_by
    (collectedFieldGroupsResponseDepth groups, 0, fieldGroupsPhase, sizeOf groups)
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
    · exact collectedFieldGroupResponseDepth_le_of_mem group groups _hgroup
    · exact Nat.le_refl _
    · decide

  def summarizeChildTypes (algebra : Algebra) (schema : Schema)
      (group : CollectedFieldGroup) (parentTypes : TypeNames)
      (variableValues : Execution.VariableValues)
      : algebra.Summary :=
    joinMap algebra parentTypes
      (fun childParentType _hparentType =>
        summarizeTree algebra schema childParentType
          group.childInheritedBooleanCondition
          (group.childTreeWithKnownFalsePruning schema childParentType variableValues)
          variableValues)
  termination_by
    (collectedFieldGroupResponseDepth group, 0, childTypesPhase, sizeOf parentTypes)
  decreasing_by
    apply Prod.Lex.left
    have hchild :=
      conditionTreeResponseDepth_ofSelectionSetInScopeWithKnownFalsePruning schema
        childParentType group.childInheritedBooleanCondition variableValues
        group.mergedSelectionSet
    exact Nat.lt_of_le_of_lt hchild (Nat.lt_succ_self _)
end

-- Supplies the Boolean literals already fixed by the parent field as runtime values.
def booleanConditionValues (inheritedBooleanCondition : List BooleanLiteral)
    : Execution.VariableValues :=
  inheritedBooleanCondition.map
    fun literal =>
      (literal.variableName, .boolean literal.requiredValue)

-- Summarizes one extracted condition tree by its node-local type and Boolean cases.
def summarizeConditionTree (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (variableValues : Execution.VariableValues := [])
    : algebra.Summary :=
  summarizeTree algebra schema parentType inheritedBooleanCondition tree
    (booleanConditionValues inheritedBooleanCondition ++ variableValues)

-----------------------------------------------------------------------------------------
-- Public entry points
-----------------------------------------------------------------------------------------

def summarizeSelectionSet (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    (variableValues : Execution.VariableValues := [])
    : algebra.Summary :=
  let tree :=
    ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition variableValues selectionSet
  summarizeConditionTree algebra schema parentType inheritedBooleanCondition tree
    variableValues

def summarizeOperation (algebra : Algebra) (schema : Schema) (operation : Operation)
    : algebra.Summary :=
  summarizeSelectionSet algebra schema (operation.rootType schema) []
    operation.selectionSet []

-- Summarizes an operation after applying its variable defaults and supplied values.
-- Known Boolean conditions are pruned; unresolved conditions remain conservative.
def summarizeOperationWithVariables
    (algebraFor : Execution.VariableValues -> Algebra) (schema : Schema)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : (algebraFor (Execution.coerceVariableValues operation variableValues)).Summary :=
  let coercedVariableValues := Execution.coerceVariableValues operation variableValues
  summarizeSelectionSet (algebraFor coercedVariableValues) schema
    (operation.rootType schema) [] operation.selectionSet coercedVariableValues

-----------------------------------------------------------------------------------------
-- Soundness contract
-----------------------------------------------------------------------------------------

-- Combines already-synthesized child summaries for several syntactic pieces of one
-- executed response field. This is a local transfer combinator, not another tree fold.
def foldChildSummaries (algebra : Algebra)
    (children : CollectedFieldGroup -> algebra.Summary)
    : List CollectedFieldGroup -> algebra.Summary
  | [] => algebra.empty
  | group :: rest =>
      algebra.combine (children group) (foldChildSummaries algebra children rest)

-- Applies the field transfer to those same pieces using their supplied child summaries.
def foldFieldGroups (algebra : Algebra)
    (children : CollectedFieldGroup -> algebra.Summary)
    : List CollectedFieldGroup -> algebra.Summary
  | [] => algebra.empty
  | group :: rest =>
      algebra.combine (algebra.field group (children group))
        (foldFieldGroups algebra children rest)

def groupCoversField {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    (source : ResolverValue ObjectRef)
    (group : CollectedFieldGroup) (field : ExecutableField)
    : Prop :=
  group.condition.allows variableValues runtimeType = true
  ∧ field
    ∈ collectFlatFields schema variableValues executionParentType source group.selections
  ∧ field.responseName = group.responseName
  ∧ ∀ selection,
      selection ∈ group.selections -> selection.responseName? = some group.responseName

def groupsCoverFields {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    (source : ResolverValue ObjectRef)
    (availableGroups : List CollectedFieldGroup)
    (fields : List ExecutableField)
    : Prop :=
  ∀ field,
    field ∈ fields
    -> ∃ group,
        group ∈ availableGroups
        ∧ groupCoversField schema variableValues executionParentType runtimeType source
            group field

def groupsRepresentField {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (runtimeType : Name) (ref : ObjectRef)
    (groups : List CollectedFieldGroup) (field : ExecutableField)
    : Prop :=
  ∀ group,
    group ∈ groups
    -> ∃ candidate,
        groupCoversField schema variableValues runtimeType runtimeType
          (.object runtimeType ref) group candidate
        ∧ candidate.fieldName = field.fieldName
        ∧ Argument.argumentsEquivalent candidate.arguments field.arguments
        ∧ ∃ selection,
            selection ∈ group.selections
            ∧ selection
              = .field group.responseName candidate.fieldName candidate.arguments []
                  candidate.selectionSet

def inheritedConditionsAllowGroups (variableValues : VariableValues)
    (groups : List CollectedFieldGroup)
    : Prop :=
  ∀ group,
    group ∈ groups
    -> booleanConditionAllows variableValues group.inheritedBooleanCondition = true

def conditionsAllowGroupsAt (variableValues : VariableValues) (runtimeType : Name)
    (groups : List CollectedFieldGroup)
    : Prop :=
  ∀ group, group ∈ groups -> group.condition.allows variableValues runtimeType = true

-- Direct local soundness contract for the syntactic backend. Unlike the exact backend's
-- single-group field obligation, `field_related` may summarize several syntactic groups
-- that jointly represent one executed response field.
structure Compatible
    (concrete : ConcreteAlgebra.{u}) (abstract : Algebra.{v})
    (schema : Schema) (variableValues : VariableValues)
    extends CompatibilityCore concrete abstract where
  field_related
    : ∀ (ObjectRef : Type) (runtimeType : Name) (ref : ObjectRef)
        (_responseName : Name)
        (field : ExecutableField) (rest : List ExecutableField)
        (definition : FieldDefinition) (value : AnnotatedResponseValue)
        (children : concrete.Summary) (groups : List CollectedFieldGroup)
        (abstractChildren : CollectedFieldGroup -> abstract.Summary),
        field.parentType = runtimeType
        -> schema.lookupField field.parentType field.fieldName = some definition
        -> (field.arguments.map Argument.name).Nodup
        -> groups ≠ []
        -> inheritedConditionsAllowGroups variableValues groups
        -> conditionsAllowGroupsAt variableValues runtimeType groups
        -> groupsCoverFields schema variableValues runtimeType runtimeType
            (.object runtimeType ref) groups (field :: rest)
        -> groupsRepresentField schema variableValues runtimeType ref groups field
        -> related children
            (foldChildSummaryForValue abstract
              (foldChildSummaries abstract abstractChildren groups) value)
        -> related
            (concrete.field
              (resolvedFieldProvenance schema variableValues definition field)
              value children)
            (foldFieldGroups abstract abstractChildren groups)

-- Soundness for a variable-indexed syntactic algebra at explicit execution fuel. Its
-- theorem witness is `Syntactic.operationWithVariablesSoundWithFuel` in
-- `Proofs.GraphQL.Theories.TreeSummary.Syntactic.Soundness`.
def OperationWithVariablesSoundWithFuel
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete (algebraFor values) schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (fuel : Nat)
        (source : ResolverValue ObjectRef),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      (compatibleFor coercedVariableValues).related
        (foldAnnotatedResponse concrete
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
        (summarizeOperationWithVariables algebraFor schema variableValues operation)

-- Default-executor form of `OperationWithVariablesSoundWithFuel`. Its theorem witness
-- is `Syntactic.operationWithVariablesSound` in the syntactic soundness proof module.
def OperationWithVariablesSound
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete (algebraFor values) schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (source : ResolverValue ObjectRef),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      (compatibleFor coercedVariableValues).related
        (foldAnnotatedResponse concrete
          (executeQueryAnnotated schema resolvers variableValues operation source))
        (summarizeOperationWithVariables algebraFor schema variableValues operation)

-- Every variable-indexed syntactic analysis supplying compatible concrete semantics is
-- sound. Its theorem witness is `Syntactic.analysisWithVariablesSound` in the syntactic
-- soundness proof module.
def AnalysisWithVariablesSound
    (algebraFor : VariableValues -> Algebra.{v}) (schema : Schema)
    (operation : Operation)
    : Prop :=
  ∀ (concrete : ConcreteAlgebra.{u})
    (compatibleFor : ∀ values, Compatible concrete (algebraFor values) schema values),
    OperationWithVariablesSound algebraFor compatibleFor operation

-- Direct soundness for the fuel-parameterized executor. Its theorem witness is
-- `Syntactic.operationSoundWithFuel` in the syntactic soundness proof module.
def OperationSoundWithFuel
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete abstract schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (fuel : Nat)
        (source : ResolverValue ObjectRef),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      (compatibleFor coercedVariableValues).related
        (foldAnnotatedResponse concrete
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
        (summarizeOperation abstract schema operation)

-- Direct soundness for the default executor. Its theorem witness is
-- `Syntactic.operationSound` in the syntactic soundness proof module.
def OperationSound
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete abstract schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (source : ResolverValue ObjectRef),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      (compatibleFor coercedVariableValues).related
        (foldAnnotatedResponse concrete
          (executeQueryAnnotated schema resolvers variableValues operation source))
        (summarizeOperation abstract schema operation)

-- Every analysis that supplies the local syntactic compatibility contract for each
-- coerced variable environment is sound. Its generic theorem witness is
-- `Syntactic.analysisSound` in the syntactic soundness proof module.
def AnalysisSound (abstract : Algebra.{v}) (schema : Schema) (operation : Operation)
    : Prop :=
  ∀ (concrete : ConcreteAlgebra.{u})
    (compatibleFor
      : ∀ variableValues, Compatible concrete abstract schema variableValues),
    OperationSound compatibleFor operation

end Syntactic
end TreeSummary
end GraphQL
