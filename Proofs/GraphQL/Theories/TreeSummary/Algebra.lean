import GraphQL.Theories.TreeSummary

/-! Reusable algebraic consequences of lawful tree-summary constructors. -/

namespace GraphQL
namespace TreeSummary

universe u v

-- A constructor-by-constructor logical relation used to transport proof obligations
-- between two summary algebras.
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

namespace CollectedFieldGroup

@[simp]
theorem fields_ne_nil (group : CollectedFieldGroup) : group.fields ≠ [] := by
  simp [fields, ConditionTree.FieldGroup.fields]

theorem selections_ne_nil (group : CollectedFieldGroup) : group.selections ≠ [] := by
  simp [selections, ConditionTree.FieldGroup.selections,
    ConditionTree.FieldGroup.fields]

@[simp]
theorem representativeField_mem_fields (group : CollectedFieldGroup)
    : group.representativeField ∈ group.fields := by
  simp [representativeField, fields, ConditionTree.FieldGroup.fields]

theorem representativeOutputType_mem_fieldOutputTypes
    (schema : Schema) (variableValues : Execution.VariableValues)
    (runtimeType : Name) (group : CollectedFieldGroup)
    (definition : FieldDefinition)
    (hallows : group.condition.allows variableValues runtimeType = true)
    (hlookup
      : schema.lookupField runtimeType group.representativeField.fieldName
        = some definition)
    : definition.outputType ∈ group.fieldOutputTypes schema := by
  have hruntime : runtimeType ∈ group.condition.possibleTypes :=
    List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp hallows).1
  unfold fieldOutputTypes
  apply List.mem_filterMap.mpr
  refine ⟨runtimeType, hruntime, ?_⟩
  simp [hlookup]

end CollectedFieldGroup

namespace Algebra.Lawful

theorem combine_left_mono {algebra : Algebra.{v}} (lawful : algebra.Lawful)
    {left lower : algebra.Summary} (hleft : lawful.le left lower)
    (right : algebra.Summary)
    : lawful.le (algebra.combine left right) (algebra.combine lower right) :=
  lawful.combine_mono left lower right right hleft (lawful.le_refl right)

theorem combine_right_mono {algebra : Algebra.{v}} (lawful : algebra.Lawful)
    (left : algebra.Summary) {right upper : algebra.Summary}
    (hright : lawful.le right upper)
    : lawful.le (algebra.combine left right) (algebra.combine left upper) :=
  lawful.combine_mono left left right upper (lawful.le_refl left) hright

theorem combine_interchange {algebra : Algebra.{v}} (lawful : algebra.Lawful)
    (leftCommon leftDelta rightCommon rightDelta : algebra.Summary)
    : algebra.combine
        (algebra.combine leftCommon leftDelta)
        (algebra.combine rightCommon rightDelta)
      = algebra.combine
          (algebra.combine leftCommon rightCommon)
          (algebra.combine leftDelta rightDelta) := by
  rw [lawful.combine_assoc]
  rw [← lawful.combine_assoc leftDelta rightCommon rightDelta]
  rw [lawful.combine_comm leftDelta rightCommon]
  rw [lawful.combine_assoc rightCommon leftDelta rightDelta]
  rw [← lawful.combine_assoc]

theorem le_joinMap_of_mem {algebra : Algebra.{v}} (lawful : algebra.Lawful)
    {items : List α}
    (summarize : ∀ item, item ∈ items -> algebra.Summary)
    {selected : α} (hselected : selected ∈ items)
    : lawful.le (summarize selected hselected) (joinMap algebra items summarize) := by
  cases items with
  | nil => simp at hselected
  | cons item rest =>
      cases rest with
      | nil =>
          simp only [List.mem_singleton] at hselected
          subst selected
          simpa [joinMap] using lawful.le_refl (summarize item (by simp))
      | cons next tail =>
          simp only [List.mem_cons] at hselected
          rw [joinMap]
          rcases hselected with rfl | hselected
          · exact lawful.le_join_left _ _
          · exact lawful.le_trans _ _ _
              (le_joinMap_of_mem lawful
                (items := next :: tail)
                (fun candidate hcandidate =>
                  summarize candidate (by simp [hcandidate]))
                (by simpa only [List.mem_cons] using hselected))
              (lawful.le_join_right _ _)
termination_by items.length

end Algebra.Lawful

namespace Algebra.Relation

theorem combineMap_related
    {left : Algebra.{u}} {right : Algebra.{v}}
    (relation : Algebra.Relation left right) (items : List α)
    (leftSummary : α -> left.Summary) (rightSummary : α -> right.Summary)
    (hitem
      : ∀ item, item ∈ items -> relation.related (leftSummary item) (rightSummary item))
    : relation.related
        (combineMap left items fun item _hitem => leftSummary item)
        (combineMap right items fun item _hitem => rightSummary item) := by
  induction items with
  | nil => simpa [combineMap] using relation.empty_related
  | cons item rest ih =>
      simpa [combineMap]
        using relation.combine_related _ _ _ _
          (hitem item (by simp))
          (ih fun candidate hcandidate => hitem candidate (by simp [hcandidate]))

theorem joinMap_related
    {left : Algebra.{u}} {right : Algebra.{v}}
    (relation : Algebra.Relation left right) (items : List α)
    (leftSummary : α -> left.Summary) (rightSummary : α -> right.Summary)
    (hitem
      : ∀ item, item ∈ items -> relation.related (leftSummary item) (rightSummary item))
    : relation.related
        (joinMap left items fun item _hitem => leftSummary item)
        (joinMap right items fun item _hitem => rightSummary item) := by
  cases items with
  | nil => simpa [joinMap] using relation.empty_related
  | cons item rest =>
      cases rest with
      | nil => simpa [joinMap] using hitem item (by simp)
      | cons next tail =>
          simpa [joinMap]
            using relation.join_related _ _ _ _
              (hitem item (by simp))
              (joinMap_related relation (next :: tail) leftSummary rightSummary
                fun candidate hcandidate => hitem candidate (by simp [hcandidate]))
termination_by items.length

end Algebra.Relation
end TreeSummary
end GraphQL
