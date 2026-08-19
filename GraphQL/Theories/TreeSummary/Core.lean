import GraphQL.Execution
import GraphQL.Theories.ConditionTree
import GraphQL.Theories.ConditionTree.Termination

/-! Core definitions for GraphQL condition-tree summaries.

Both traversal backends consume the same `Algebra`, collected response-name groups,
proof-facing order, and structural termination measures. Exact-case construction and its
specialized measures live in `GraphQL.Theories.TreeSummary.ExactCases`.

Condition resolution remains framework-owned. Algebras see only collected fields,
simultaneous composition, and alternative joins.
-/

namespace GraphQL
namespace TreeSummary

open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination

universe u v

-- Semantic aliases distinguish GraphQL type-name collections from other `Name` lists.
abbrev PossibleTypes := List Name
abbrev TypeNames := List Name
abbrev BooleanVariableNames := List Name

-----------------------------------------------------------------------------------------
-- Tree summary algebra
-----------------------------------------------------------------------------------------

-- The statically collected fields for one response name at one condition-tree node.
-- `fieldGroup` makes the two invariants supplied by condition-tree extraction part of
-- the type: the group is nonempty and every member is field syntax. `fields` exposes
-- those typed fields; `selections` reconstructs selection syntax for analyses that need
-- executable field shape or merged children.
structure CollectedFieldGroup where
  inheritedBooleanCondition : List BooleanLiteral
  condition : Condition
  fieldGroup : ConditionTree.FieldGroup
deriving Repr

namespace CollectedFieldGroup

def responseName (group : CollectedFieldGroup) : Name :=
  group.fieldGroup.responseName

def fields (group : CollectedFieldGroup) : List Field :=
  group.fieldGroup.fields

def selections (group : CollectedFieldGroup) : List Selection :=
  group.fieldGroup.selections

-- Spec 6.3.2 `CollectSubfields` shape, before runtime condition filtering.
def mergedSelectionSet (group : CollectedFieldGroup) : List Selection :=
  group.fieldGroup.mergedSelectionSet

-- Boolean scope inherited by the merged selection set below this response field.
def childInheritedBooleanCondition (group : CollectedFieldGroup) : List BooleanLiteral :=
  (canonicalBooleanCondition
    (group.inheritedBooleanCondition ++ group.condition.booleanCondition)).getD
    group.inheritedBooleanCondition

-- Condition tree for the merged selection set under one possible child parent type.
def childTree (group : CollectedFieldGroup) (schema : Schema) (childParentType : Name)
    : Tree :=
  ConditionTree.ofSelectionSetInScope schema childParentType
    group.childInheritedBooleanCondition group.mergedSelectionSet

-- Known-false-pruned child extraction removes only branches inactive after operation
-- defaults have been applied. The canonical child tree remains available to generic
-- variable-independent traversals and proof statements.
def childTreeWithKnownFalsePruning (group : CollectedFieldGroup) (schema : Schema)
    (childParentType : Name) (variableValues : Execution.VariableValues)
    : Tree :=
  ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema childParentType
    group.childInheritedBooleanCondition variableValues group.mergedSelectionSet

-- Field names retained by this response-name group.
def fieldNames (group : CollectedFieldGroup) : List Name :=
  group.fields.map Field.fieldName

-- Declared outputs of the fields actually retained by this response-name group, looked
-- up on every runtime parent type allowed by its condition. This remains conservative
-- for mutually exclusive fields merged under one response name without importing output
-- types of unrelated schema fields.
def fieldOutputTypes (schema : Schema) (group : CollectedFieldGroup) : List TypeRef :=
  let fieldNames := group.fieldNames
  group.condition.possibleTypes.flatMap
    fun parentType =>
      fieldNames.filterMap
        fun fieldName =>
          (schema.lookupField parentType fieldName).map FieldDefinition.outputType

end CollectedFieldGroup

-- Child selection sets are interpreted once for every output type that this collected
-- group can resolve to. The alternatives belong to the framework, not an analysis.
def childParentTypes (schema : Schema) (group : CollectedFieldGroup) : TypeNames :=
  ((group.fieldOutputTypes schema).map TypeRef.namedType).eraseDups

def possibleTypesSubset (left right : PossibleTypes) : Bool :=
  left.all right.contains

-- One realizable equivalence class of runtime object types. Refining the current scope
-- by cumulative type-condition sets groups object names exactly when they activate the
-- same conditions; consumers can therefore evaluate one representative per region.
abbrev PossibleTypeRegion := PossibleTypes

def splitPossibleTypeRegion (region allowed : PossibleTypeRegion)
    : List PossibleTypeRegion :=
  let included := region.filter allowed.contains
  let excluded := region.filter fun typeName => !allowed.contains typeName
  (if included.isEmpty then [] else [included])
  ++ (if excluded.isEmpty then [] else [excluded])

def refinePossibleTypeRegions (allowed : PossibleTypes)
    (regions : List PossibleTypeRegion)
    : List PossibleTypeRegion :=
  regions.flatMap fun region => splitPossibleTypeRegion region allowed

def possibleTypeRegions (scope : PossibleTypes) (conditions : List PossibleTypes)
    : List PossibleTypeRegion :=
  conditions.foldl
    (fun regions allowed => refinePossibleTypeRegions allowed regions)
    (if scope.isEmpty then [] else [scope])

-- Algebra for a contextual fold over a condition tree.
--
-- `field` receives one statically collected response-name group and the synthesized
-- summary of its merged child selection set. `combine` composes contributions that may
-- occur together; `join` merges alternative Boolean assignments and type-condition
-- possible-type cases.
structure Algebra where
  Summary : Type u
  empty : Summary
  field : CollectedFieldGroup -> Summary -> Summary
  combine : Summary -> Summary -> Summary
  join : Summary -> Summary -> Summary

-- A constructor-by-constructor logical relation between two summary algebras. Generic
-- fold lemmas lift these local obligations through `combineMap` and `joinMap`; clients
-- choose the relation appropriate to soundness, refinement, or least-bound proofs.
structure Algebra.Relation (left : Algebra.{u}) (right : Algebra.{v})
    : Type (max u v) where
  related : left.Summary -> right.Summary -> Prop
  empty_related : related left.empty right.empty
  combine_related
    : ∀ leftValue leftEstimate rightValue rightEstimate,
        related leftValue leftEstimate
        -> related rightValue rightEstimate
        -> related (left.combine leftValue rightValue)
            (right.combine leftEstimate rightEstimate)
  field_related
    : ∀ group leftChildren rightChildren,
        related leftChildren rightChildren
        -> related (left.field group leftChildren) (right.field group rightChildren)
  join_related
    : ∀ leftValue leftEstimate rightValue rightEstimate,
        related leftValue leftEstimate
        -> related rightValue rightEstimate
        -> related (left.join leftValue rightValue)
            (right.join leftEstimate rightEstimate)

-- Proof-facing order and algebraic laws for soundness and refinement. The order remains
-- outside `Algebra` so executable summaries pay no extra contract.
structure Algebra.Lawful (algebra : Algebra.{v}) : Type v where
  le : algebra.Summary -> algebra.Summary -> Prop
  le_refl : ∀ value, le value value
  le_trans : ∀ left middle right, le left middle -> le middle right -> le left right
  combine_assoc
    : ∀ left middle right,
        algebra.combine (algebra.combine left middle) right
        = algebra.combine left (algebra.combine middle right)
  combine_comm : ∀ left right, algebra.combine left right = algebra.combine right left
  empty_combine : ∀ value, algebra.combine algebra.empty value = value
  combine_empty : ∀ value, algebra.combine value algebra.empty = value
  empty_le : ∀ value, le algebra.empty value
  combine_mono
    : ∀ left lower right upper,
        le left lower
        -> le right upper
        -> le (algebra.combine left right) (algebra.combine lower upper)
  le_join_left : ∀ left right, le left (algebra.join left right)
  le_join_right : ∀ left right, le right (algebra.join left right)

-- Maps simultaneous items to summaries and combines all of them. The empty list is
-- the algebra's empty contribution.
def combineMap (algebra : Algebra) (items : List α)
    (summarize : ∀ item, item ∈ items -> algebra.Summary)
    : algebra.Summary :=
  match items with
  | [] => algebra.empty
  | item :: rest =>
      algebra.combine
        (summarize item (by simp))
        (combineMap algebra rest
          fun candidate hcandidate =>
            summarize candidate (by simp [hcandidate]))
termination_by items

-- Maps alternative items to summaries and joins them. A singleton is returned
-- directly: `empty` means no alternative, not an additional feasible alternative.
def joinMap (algebra : Algebra) (items : List α)
    (summarize : ∀ item, item ∈ items -> algebra.Summary)
    : algebra.Summary :=
  match items with
  | [] => algebra.empty
  | item :: [] => summarize item (by simp)
  | item :: next :: rest =>
      algebra.join
        (summarize item (by simp))
        (joinMap algebra (next :: rest)
          fun candidate hcandidate =>
            summarize candidate (by simp [hcandidate]))
termination_by items

-- Adds summary context to response-name groups already collected by a traversal.
-- Cross-node grouping, when needed, happens before this decoration step.
def collectFieldGroups (inheritedBooleanCondition : List BooleanLiteral)
    (condition : Condition)
    (fieldGroups : List ConditionTree.FieldGroup)
    : List CollectedFieldGroup :=
  fieldGroups.map
    fun group =>
      {
        inheritedBooleanCondition
        condition
        fieldGroup := group
      }

-----------------------------------------------------------------------------------------
-- Termination measure
-----------------------------------------------------------------------------------------

namespace Measure

def collectedFieldGroupResponseDepth (group : CollectedFieldGroup) : Nat :=
  selectionSetResponseDepth group.mergedSelectionSet + 1

def collectedFieldGroupsResponseDepth : List CollectedFieldGroup -> Nat
  | [] => 0
  | group :: rest =>
      max (collectedFieldGroupResponseDepth group)
        (collectedFieldGroupsResponseDepth rest)

theorem collectedFieldGroupResponseDepth_le_of_mem
    (group : CollectedFieldGroup) (groups : List CollectedFieldGroup)
    (hgroup : group ∈ groups)
    : collectedFieldGroupResponseDepth group
      ≤ collectedFieldGroupsResponseDepth groups := by
  induction groups with
  | nil => simp at hgroup
  | cons head rest ih =>
      simp only [collectedFieldGroupsResponseDepth]
      rcases List.mem_cons.mp hgroup with rfl | htail
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

private theorem mergedFieldSelections_responseDepth_succ
    (responseName : Name) (first : Field) (rest : List Field)
    : selectionSetResponseDepth
          (SelectionSet.mergeSelectionSets
            ((first :: rest).map (Field.toSelection responseName)))
        + 1
      = selectionSetResponseDepth
          ((first :: rest).map (Field.toSelection responseName)) := by
  induction rest generalizing first with
  | nil =>
      simp [SelectionSet.mergeSelectionSets, Field.toSelection,
        Selection.subselections, selectionSetResponseDepth, selectionResponseDepth]
  | cons next tail ih =>
      rw [show
          (first :: next :: tail).map (Field.toSelection responseName)
            = [first.toSelection responseName]
              ++ (next :: tail).map (Field.toSelection responseName) by rfl]
      rw [mergeSelectionSets_append, selectionSetResponseDepth_append]
      have hsingle :
          SelectionSet.mergeSelectionSets [first.toSelection responseName]
            = first.selectionSet := by
        simp [SelectionSet.mergeSelectionSets, Field.toSelection,
          Selection.subselections]
      rw [hsingle, selectionSetResponseDepth_append]
      simp only [selectionSetResponseDepth, selectionResponseDepth,
        Field.toSelection, Nat.max_zero]
      rw [← ih next]
      omega

theorem collectedFieldGroupsResponseDepth_collectFieldGroups
    (inheritedBooleanCondition : List BooleanLiteral)
    (condition : Condition) (fieldGroups : List ConditionTree.FieldGroup)
    : collectedFieldGroupsResponseDepth
        (collectFieldGroups inheritedBooleanCondition condition fieldGroups)
      = conditionFieldGroupsResponseDepth fieldGroups := by
  induction fieldGroups with
  | nil =>
      simp [collectFieldGroups, collectedFieldGroupsResponseDepth,
        conditionFieldGroupsResponseDepth]
  | cons group rest ih =>
      simp only [collectFieldGroups, List.map_cons, collectedFieldGroupsResponseDepth,
        conditionFieldGroupsResponseDepth]
      change
        max
            (selectionSetResponseDepth group.mergedSelectionSet + 1)
            (collectedFieldGroupsResponseDepth
              (collectFieldGroups inheritedBooleanCondition condition rest))
          = max (conditionFieldGroupResponseDepth group)
              (conditionFieldGroupsResponseDepth rest)
      rw [ih]
      congr 1
      simpa [FieldGroup.mergedSelectionSet, FieldGroup.selections, FieldGroup.fields,
        conditionFieldGroupResponseDepth] using
        mergedFieldSelections_responseDepth_succ group.responseName group.first
          group.rest

theorem quadruple_lt_of_depth_le_of_control_lt
    {leftDepth rightDepth leftControl rightControl leftPhase rightPhase leftTail rightTail
      : Nat}
    (hdepth : leftDepth ≤ rightDepth)
    (hcontrol : leftControl < rightControl)
    : Prod.Lex (fun left right : Nat => left < right)
        (Prod.Lex (fun left right : Nat => left < right)
          (Prod.Lex (fun left right : Nat => left < right)
            (fun left right : Nat => left < right)))
        (leftDepth, leftControl, leftPhase, leftTail)
        (rightDepth, rightControl, rightPhase, rightTail) := by
  rcases Nat.lt_or_eq_of_le hdepth with hstrict | hequal
  · exact Prod.Lex.left _ _ hstrict
  · subst rightDepth
    exact Prod.Lex.right leftDepth (Prod.Lex.left _ _ hcontrol)

theorem quadruple_lt_of_depth_le_of_control_le_of_phase_lt
    {leftDepth rightDepth leftControl rightControl leftPhase rightPhase leftTail rightTail
      : Nat}
    (hdepth : leftDepth ≤ rightDepth)
    (hcontrol : leftControl ≤ rightControl)
    (hphase : leftPhase < rightPhase)
    : Prod.Lex (fun left right : Nat => left < right)
        (Prod.Lex (fun left right : Nat => left < right)
          (Prod.Lex (fun left right : Nat => left < right)
            (fun left right : Nat => left < right)))
        (leftDepth, leftControl, leftPhase, leftTail)
        (rightDepth, rightControl, rightPhase, rightTail) := by
  rcases Nat.lt_or_eq_of_le hdepth with hstrict | hequal
  · exact Prod.Lex.left _ _ hstrict
  · subst rightDepth
    apply Prod.Lex.right leftDepth
    rcases Nat.lt_or_eq_of_le hcontrol with hstrict | hequal
    · exact Prod.Lex.left _ _ hstrict
    · subst rightControl
      exact Prod.Lex.right leftControl (Prod.Lex.left _ _ hphase)

theorem quadruple_lt_of_depth_le_of_tail_lt
    {leftDepth rightDepth control phase leftTail rightTail : Nat}
    (hdepth : leftDepth ≤ rightDepth) (htail : leftTail < rightTail)
    : Prod.Lex (fun left right : Nat => left < right)
        (Prod.Lex (fun left right : Nat => left < right)
          (Prod.Lex (fun left right : Nat => left < right)
            (fun left right : Nat => left < right)))
        (leftDepth, control, phase, leftTail)
        (rightDepth, control, phase, rightTail) := by
  rcases Nat.lt_or_eq_of_le hdepth with hstrict | hequal
  · exact Prod.Lex.left _ _ hstrict
  · subst rightDepth
    exact Prod.Lex.right leftDepth
      (Prod.Lex.right control (Prod.Lex.right phase htail))

end Measure

open Measure

end TreeSummary
end GraphQL
