import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Operation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.SubselectionsNonempty

/-!
Complete normalization preserves the September 2025 non-emptiness rule.

`completeNormalizeOperation_subselectionsNonempty` shows that complete normalization of a
source operation that meets `operationSubselectionsNonemptyInPossibleTypes` produces an
operation that meets `operationSubselectionsNonempty`.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

open GroundTypeNormalization in
mutual
  theorem selectionInlineFragmentsNonempty_filterSelectionSetBoolCase
      (boolCase : BoolCase)
      : ∀ selection,
          selectionSetInlineFragmentsNonempty
            (filterSelectionSetBoolCase boolCase [selection])
    | .field responseName fieldName arguments directives selectionSet => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow,
                selectionSetInlineFragmentsNonempty, selectionInlineFragmentsNonempty]
          | cons child children =>
              cases hchild : filterSelectionSetBoolCase boolCase (child :: children) with
              | nil =>
                  simp [filterSelectionSetBoolCase, hallow, hchild,
                    selectionSetInlineFragmentsNonempty, selectionInlineFragmentsNonempty]
              | cons filteredChild filteredChildren =>
                  have hbody :=
                    selectionSetInlineFragmentsNonempty_filterSelectionSetBoolCase
                      boolCase (child :: children)
                  rw [hchild] at hbody
                  simp only [filterSelectionSetBoolCase, hallow, hchild, ↓reduceIte]
                  simp only [selectionSetInlineFragmentsNonempty, List.mem_cons,
                    List.mem_nil_iff, or_false, forall_eq]
                  simpa [selectionInlineFragmentsNonempty] using hbody
        · have hfalse : directivesAllowIn boolCase directives = false := by
            cases h : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse, selectionSetInlineFragmentsNonempty]
    | .inlineFragment typeCondition directives selectionSet => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchild : filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetInlineFragmentsNonempty]
          | cons filteredChild filteredChildren =>
              have hbody :=
                selectionSetInlineFragmentsNonempty_filterSelectionSetBoolCase
                  boolCase selectionSet
              rw [hchild] at hbody
              simp only [filterSelectionSetBoolCase, hallow, hchild, ↓reduceIte]
              simp only [selectionSetInlineFragmentsNonempty, List.mem_cons,
                List.mem_nil_iff, or_false, forall_eq]
              simp only [selectionInlineFragmentsNonempty]
              exact ⟨by simp, hbody⟩
        · have hfalse : directivesAllowIn boolCase directives = false := by
            cases h : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse, selectionSetInlineFragmentsNonempty]

  theorem selectionSetInlineFragmentsNonempty_filterSelectionSetBoolCase
      (boolCase : BoolCase)
      : ∀ selectionSet,
          selectionSetInlineFragmentsNonempty
            (filterSelectionSetBoolCase boolCase selectionSet)
    | [] => by
        simp [filterSelectionSetBoolCase, selectionSetInlineFragmentsNonempty]
    | selection :: rest => by
        rw [filterSelectionSetBoolCase_cons]
        exact selectionSetInlineFragmentsNonempty_append
          (selectionInlineFragmentsNonempty_filterSelectionSetBoolCase boolCase selection)
          (selectionSetInlineFragmentsNonempty_filterSelectionSetBoolCase boolCase rest)
end

open GroundTypeNormalization in
mutual
  theorem selectionSubselectionsNonemptyOnObjectPaths_filterSelectionSetBoolCase
      (schema : Schema) (boolCase : BoolCase)
      : ∀ parentType typeConditions selection,
          selectionSubselectionsNonemptyOnObjectPaths schema parentType selection
          -> selectionBoolTypeConditionFeasibleInCase schema parentType typeConditions
              boolCase selection
          -> selectionSetSubselectionsNonemptyOnObjectPaths schema parentType
              (filterSelectionSetBoolCase boolCase [selection])
    | parentType, typeConditions,
      .field responseName fieldName arguments directives selectionSet,
      hnonempty, hfeasible => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · simp only [selectionSubselectionsNonemptyOnObjectPaths] at hnonempty
          cases selectionSet with
          | nil =>
              simp only [filterSelectionSetBoolCase, hallow, ↓reduceIte]
              simp only [selectionSetSubselectionsNonemptyOnObjectPaths,
                selectionSubselectionsNonemptyOnObjectPaths, and_true]
              intro fieldDefinition hlookup
              refine ⟨(hnonempty fieldDefinition hlookup).1, ?_, ?_⟩
              · unfold selectionSetInlineFragmentsNonempty
                intro selection hselection
                cases hselection
              · intro objectType _hobjectType
                simp
          | cons child children =>
              cases hchild : filterSelectionSetBoolCase boolCase (child :: children) with
              | nil =>
                  exact False.elim
                    ((fieldFilteredCompositeChild_empty_of_boolTypeConditionFeasible_all
                      schema boolCase parentType typeConditions responseName
                      fieldName arguments directives child children
                      hfeasible hallow hchild) (hfeasible hallow).1)
              | cons filteredChild filteredChildren =>
                  simp only [filterSelectionSetBoolCase, hallow, hchild, ↓reduceIte]
                  simp only [selectionSetSubselectionsNonemptyOnObjectPaths,
                    selectionSubselectionsNonemptyOnObjectPaths, and_true]
                  intro fieldDefinition hlookup
                  have hparts := hnonempty fieldDefinition hlookup
                  have hsource := (hfeasible hallow).2
                  simp only [hlookup] at hsource
                  refine ⟨fun _ => by simp, ?_, ?_⟩
                  · have hinline :=
                      selectionSetInlineFragmentsNonempty_filterSelectionSetBoolCase
                        boolCase (child :: children)
                    simpa [hchild] using hinline
                  · intro objectType hobjectType
                    have hchildFiltered :=
                      selectionSetSubselectionsNonemptyOnObjectPaths_filterSelectionSetBoolCase
                        schema boolCase objectType [objectType] (child :: children)
                        (hparts.2.2 objectType hobjectType)
                        (hsource.2 objectType hobjectType).2
                    rw [hchild] at hchildFiltered
                    simpa [selectionSetSubselectionsNonemptyOnObjectPaths] using
                      hchildFiltered
        · have hfalse : directivesAllowIn boolCase directives = false := by
            cases h : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetSubselectionsNonemptyOnObjectPaths]
    | parentType, typeConditions, .inlineFragment none directives selectionSet,
      hnonempty, hfeasible => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · simp only [selectionSubselectionsNonemptyOnObjectPaths] at hnonempty
          have hbodyFeasible := hfeasible hallow
          have hbody :=
            selectionSetSubselectionsNonemptyOnObjectPaths_filterSelectionSetBoolCase
              schema boolCase parentType typeConditions selectionSet hnonempty
              hbodyFeasible
          cases hchild : filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetSubselectionsNonemptyOnObjectPaths]
          | cons filteredChild filteredChildren =>
              rw [hchild] at hbody
              simp only [filterSelectionSetBoolCase, hallow, hchild, ↓reduceIte]
              simp only [selectionSetSubselectionsNonemptyOnObjectPaths,
                selectionSubselectionsNonemptyOnObjectPaths, and_true]
              exact hbody
        · have hfalse : directivesAllowIn boolCase directives = false := by
            cases h : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetSubselectionsNonemptyOnObjectPaths]
    | parentType, typeConditions,
      .inlineFragment (some typeCondition) directives selectionSet,
      hnonempty, hfeasible => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · simp only [selectionSubselectionsNonemptyOnObjectPaths] at hnonempty
          have hbodyFeasible := hfeasible hallow
          cases hchild : filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetSubselectionsNonemptyOnObjectPaths]
          | cons filteredChild filteredChildren =>
              simp only [filterSelectionSetBoolCase, hallow, hchild, ↓reduceIte]
              simp only [selectionSetSubselectionsNonemptyOnObjectPaths,
                selectionSubselectionsNonemptyOnObjectPaths, and_true]
              intro hoverlap
              have hbody :=
                selectionSetSubselectionsNonemptyOnObjectPaths_filterSelectionSetBoolCase
                  schema boolCase parentType (typeCondition :: typeConditions)
                  selectionSet (hnonempty hoverlap) hbodyFeasible
              rw [hchild] at hbody
              exact hbody
        · have hfalse : directivesAllowIn boolCase directives = false := by
            cases h : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetSubselectionsNonemptyOnObjectPaths]

  theorem selectionSetSubselectionsNonemptyOnObjectPaths_filterSelectionSetBoolCase
      (schema : Schema) (boolCase : BoolCase)
      : ∀ parentType typeConditions selectionSet,
          selectionSetSubselectionsNonemptyOnObjectPaths schema parentType selectionSet
          -> selectionSetBoolTypeConditionFeasibleInCase schema parentType
              typeConditions boolCase selectionSet
          -> selectionSetSubselectionsNonemptyOnObjectPaths schema parentType
              (filterSelectionSetBoolCase boolCase selectionSet)
    | _parentType, _typeConditions, [], _hnonempty, _hfeasible => by
        simp [filterSelectionSetBoolCase, selectionSetSubselectionsNonemptyOnObjectPaths]
    | parentType, typeConditions, selection :: rest, hnonempty, hfeasible => by
        simp only [selectionSetSubselectionsNonemptyOnObjectPaths] at hnonempty
        simp only [selectionSetBoolTypeConditionFeasibleInCase] at hfeasible
        rw [filterSelectionSetBoolCase_cons]
        exact selectionSetSubselectionsNonemptyOnObjectPaths_append
          (selectionSubselectionsNonemptyOnObjectPaths_filterSelectionSetBoolCase schema
            boolCase parentType typeConditions selection hnonempty.1 hfeasible.1)
          (selectionSetSubselectionsNonemptyOnObjectPaths_filterSelectionSetBoolCase schema
            boolCase parentType typeConditions rest hnonempty.2 hfeasible.2)
end

theorem selectionSetSubselectionsNonempty_wrapWithBoolCase
    {schema : Schema} {parentType : Name}
    : ∀ boolCase selectionSet,
        selectionSetSubselectionsNonempty schema parentType selectionSet
        -> selectionSet ≠ []
        -> selectionSetSubselectionsNonempty schema parentType
            (wrapWithBoolCase boolCase selectionSet)
  | [], selectionSet, hnonempty, _hne => by
      simpa [wrapWithBoolCase] using hnonempty
  | (varName, value) :: rest, selectionSet, hnonempty, hne => by
      have hchild :=
        selectionSetSubselectionsNonempty_wrapWithBoolCase rest selectionSet hnonempty hne
      refine GroundTypeNormalization.selectionSetSubselectionsNonempty_iff.mpr ?_
      intro selection hselection
      simp only [wrapWithBoolCase, List.mem_singleton] at hselection
      subst selection
      simp only [selectionSubselectionsNonempty, Option.getD_none]
      exact ⟨wrapWithBoolCase_ne_nil rest selectionSet hne, hchild⟩

theorem completeNormalizeOperation_subselectionsNonempty
    (schema : Schema) (operation : Operation)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> operationFieldsValidInPossibleTypes schema operation
      -> operationBoolTypeConditionFeasible schema operation
      -> operationSubselectionsNonemptyInPossibleTypes schema operation
      -> operationSubselectionsNonempty schema
          (completeNormalizeOperation schema operation) := by
  intro hschema hoperation hfields hboolFeasible hnonempty
  have hrootObject : schema.objectType (operation.rootType schema) :=
    operation_root_object_of_valid hschema hoperation
  have hready :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    operation_selectionSetSemanticsReady_of_valid hschema hoperation
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
  have hsourceOnPaths :=
    GroundTypeNormalization.selectionSetSubselectionsNonemptyOnObjectPaths_of_inPossibleTypes
      schema operation.variableDefinitions hschema (operation.rootType schema)
      operation.selectionSet hrootObject hfields hnonempty
  have hbranch :
      ∀ boolCase,
        boolCase ∈ allBoolCases (operationBoolVars operation)
        -> selectionSetSubselectionsNonempty schema (operation.rootType schema)
            (normalizeSelectionSet schema (operation.rootType schema)
              (filterSelectionSetBoolCase boolCase operation.selectionSet)) := by
    intro boolCase hcase
    have hcaseFeasible :=
      operationBoolTypeConditionFeasible_inCase hboolFeasible hcase
    exact
      GroundTypeNormalization.normalizeSelectionSet_subselectionsNonempty_of_typeConditionFeasible
        schema hschema (operation.rootType schema)
        (filterSelectionSetBoolCase boolCase operation.selectionSet)
        [(operation.rootType schema)] hrootObject
        (GroundTypeNormalization.objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
          schema hrootObject)
        (filterSelectionSetBoolCase_selectionSetSemanticsReady schema boolCase
          (operation.rootType schema) operation.selectionSet hready)
        (runtimeMergeSource_of_declaredLookupReady schema hrootObject
          (object_typeIncludesObjectBool_self schema hrootObject)
          (selectionSetDeclaredLookupReady_filter schema boolCase
            (operation.rootType schema) operation.selectionSet
            (selectionSetDeclaredLookupReady_of_valid schema operation.variableDefinitions
              (operation.rootType schema) operation.selectionSet
              (Validation.operationDefinitionValid_selectionSetValid hoperation)))
          (fieldsInSetCanMerge_filterSelectionSetBoolCase schema boolCase hmerge))
        (filterSelectionSetBoolCase_directiveFree schema boolCase operation.selectionSet)
        (selectionSetTypeConditionFeasible_filterSelectionSetBoolCase schema boolCase
          (operation.rootType schema) [(operation.rootType schema)] operation.selectionSet
          hcaseFeasible)
        (selectionSetSubselectionsNonemptyOnObjectPaths_filterSelectionSetBoolCase schema
          boolCase (operation.rootType schema) [(operation.rootType schema)]
          operation.selectionSet hsourceOnPaths hcaseFeasible)
  refine GroundTypeNormalization.selectionSetSubselectionsNonempty_iff.mpr ?_
  intro selection hselection
  simp only [completeNormalizeOperation, completeNormalizeRootSelectionSet,
    List.mem_flatten, List.mem_map] at hselection
  rcases hselection with ⟨branch, ⟨boolCase, hcase, rfl⟩, hselectionMem⟩
  have hbranchCase := hbranch boolCase hcase
  cases hnormalized
        : normalizeSelectionSet schema (operation.rootType schema)
            (filterSelectionSetBoolCase boolCase operation.selectionSet) with
  | nil =>
      simp [hnormalized] at hselectionMem
  | cons head tail =>
      rw [hnormalized] at hselectionMem hbranchCase
      have hwrapped :=
        selectionSetSubselectionsNonempty_wrapWithBoolCase boolCase (head :: tail)
          hbranchCase (by simp)
      simpa [completeNormalizeOperation, Operation.rootType]
        using GroundTypeNormalization.selectionSetSubselectionsNonempty_of_mem hwrapped
          (by simpa using hselectionMem)

end CompleteNormalization

end NormalForm

end GraphQL
