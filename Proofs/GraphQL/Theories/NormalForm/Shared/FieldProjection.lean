import Proofs.GraphQL.Theories.NormalForm.Shared.FieldMerge
import Proofs.GraphQL.Execution.ArgumentCoercion

/-! Recursive declared-scope source projections for transformed field groups. -/

namespace GraphQL.NormalForm

def fieldProjectionChildren (schema : Schema) (sources : List FieldMerge.ScopedField)
    : List FieldMerge.ScopedField :=
  sources.flatMap
    (fun source =>
      FieldMerge.collectFields schema source.outputType.namedType source.selectionSet)

mutual
  inductive FieldProjection (schema : Schema)
      : List FieldMerge.ScopedField -> FieldMerge.ScopedField -> Prop where
    | intro {sources : List FieldMerge.ScopedField} {target : FieldMerge.ScopedField}
      (nonempty : sources ≠ [])
      (types
        : ∀ source,
            source ∈ sources
            -> FieldMerge.sameTypeShape schema source.outputType target.outputType)
      (metadata
        : ∀ source,
            source ∈ sources
            -> source.responseName = target.responseName
                ∧ source.fieldName = target.fieldName
                ∧ Argument.argumentsEquivalent source.arguments target.arguments
                ∧ (source.parentType = target.parentType
                    ∨ ¬ schema.objectType source.parentType))
      (children
        : ∀ child,
            child
              ∈ FieldMerge.collectFields schema target.outputType.namedType
                  target.selectionSet
            -> FieldProjectionSources schema sources child)
      : FieldProjection schema sources target

  inductive FieldProjectionSources (schema : Schema)
      : List FieldMerge.ScopedField -> FieldMerge.ScopedField -> Prop where
    | intro {sources childSources : List FieldMerge.ScopedField}
      {target : FieldMerge.ScopedField}
      (subset : childSources ⊆ fieldProjectionChildren schema sources)
      (projection : FieldProjection schema childSources target)
      : FieldProjectionSources schema sources target
end

theorem FieldProjection.nonempty {schema : Schema}
    {sources : List FieldMerge.ScopedField} {target : FieldMerge.ScopedField}
    (h : FieldProjection schema sources target)
    : sources ≠ [] := by
  cases h with
  | intro h _ _ _ => exact h

theorem FieldProjection.types {schema : Schema}
    {sources : List FieldMerge.ScopedField} {target : FieldMerge.ScopedField}
    (h : FieldProjection schema sources target) {source : FieldMerge.ScopedField}
    (hsource : source ∈ sources)
    : FieldMerge.sameTypeShape schema source.outputType target.outputType := by
  cases h with
  | intro _ h _ _ => exact h source hsource

theorem FieldProjection.metadata {schema : Schema}
    {sources : List FieldMerge.ScopedField} {target : FieldMerge.ScopedField}
    (h : FieldProjection schema sources target) {source : FieldMerge.ScopedField}
    (hsource : source ∈ sources)
    : source.responseName = target.responseName
      ∧ source.fieldName = target.fieldName
      ∧ Argument.argumentsEquivalent source.arguments target.arguments
      ∧ (source.parentType = target.parentType
          ∨ ¬ schema.objectType source.parentType) := by
  cases h with
  | intro _ _ h _ => exact h source hsource

theorem FieldProjection.children {schema : Schema}
    {sources : List FieldMerge.ScopedField} {target : FieldMerge.ScopedField}
    (h : FieldProjection schema sources target) {child : FieldMerge.ScopedField}
    (hchild
      : child
        ∈ FieldMerge.collectFields schema target.outputType.namedType target.selectionSet)
    : ∃ childSources,
        childSources ⊆ fieldProjectionChildren schema sources
        ∧ FieldProjection schema childSources child := by
  cases h with
  | intro _ _ _ h =>
      cases h child hchild with
      | intro hsubset hprojection => exact ⟨_, hsubset, hprojection⟩

theorem fieldMerge_collectFields_children_size_lt (schema : Schema)
    : ∀ parentType selectionSet field,
        field ∈ FieldMerge.collectFields schema parentType selectionSet
        -> SelectionSet.size field.selectionSet < SelectionSet.size selectionSet
  | parentType, [], field, hfield => by simp [FieldMerge.collectFields] at hfield
  | parentType, selection :: rest, field, hfield => by
      cases selection with
      | field responseName fieldName arguments directives children =>
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp only [FieldMerge.collectFields, hlookup, List.nil_append] at hfield
              have h := fieldMerge_collectFields_children_size_lt schema parentType rest field hfield
              simp only [SelectionSet.size, Selection.size]
              omega
          | some definition =>
              simp only [FieldMerge.collectFields, hlookup, List.singleton_append,
                List.mem_cons] at hfield
              rcases hfield with rfl | hfield
              · simp only [SelectionSet.size, Selection.size]
                omega
              · have h := fieldMerge_collectFields_children_size_lt schema parentType rest field hfield
                simp only [SelectionSet.size, Selection.size]
                omega
      | inlineFragment condition directives children =>
          cases condition with
          | none =>
              simp only [FieldMerge.collectFields, List.mem_append] at hfield
              rcases hfield with hfield | hfield
              · have h := fieldMerge_collectFields_children_size_lt schema parentType children field hfield
                simp only [SelectionSet.size, Selection.size]
                omega
              · have h := fieldMerge_collectFields_children_size_lt schema parentType rest field hfield
                simp only [SelectionSet.size, Selection.size]
                omega
          | some condition =>
              simp only [FieldMerge.collectFields, List.mem_append] at hfield
              rcases hfield with hfield | hfield
              · have h := fieldMerge_collectFields_children_size_lt schema condition children field hfield
                simp only [SelectionSet.size, Selection.size]
                omega
              · have h := fieldMerge_collectFields_children_size_lt schema parentType rest field hfield
                simp only [SelectionSet.size, Selection.size]
                omega

private theorem projectionChildren_subset_append (schema : Schema)
    (left right : List FieldMerge.ScopedField)
    : fieldProjectionChildren schema left ⊆ fieldProjectionChildren schema (left ++ right)
      ∧ fieldProjectionChildren schema right
        ⊆ fieldProjectionChildren schema (left ++ right) := by
  simp only [fieldProjectionChildren, List.flatMap_append]
  exact ⟨List.subset_append_left _ _, List.subset_append_right _ _⟩

private theorem FieldProjection.pair_children {schema : Schema}
    {left right : FieldMerge.ScopedField}
    {leftSources rightSources : List FieldMerge.ScopedField}
    (hleft : FieldProjection schema leftSources left)
    (hright : FieldProjection schema rightSources right) {child : FieldMerge.ScopedField}
    (hchild : child ∈ FieldMerge.collectSubfields schema left right)
    : ∃ childSources,
        childSources ⊆ fieldProjectionChildren schema (leftSources ++ rightSources)
        ∧ FieldProjection schema childSources child := by
  rcases List.mem_append.mp hchild with hchild | hchild
  · rcases hleft.children hchild with ⟨sources, hsubset, hprojection⟩
    exact ⟨sources, fun source hsource =>
      (projectionChildren_subset_append schema leftSources rightSources).1 (hsubset hsource),
      hprojection⟩
  · rcases hright.children hchild with ⟨sources, hsubset, hprojection⟩
    exact ⟨sources, fun source hsource =>
      (projectionChildren_subset_append schema leftSources rightSources).2 (hsubset hsource),
      hprojection⟩

private theorem pair_child_size_lt {schema : Schema}
    {left right child : FieldMerge.ScopedField}
    (hchild : child ∈ FieldMerge.collectSubfields schema left right)
    : SelectionSet.size child.selectionSet
      < max (SelectionSet.size left.selectionSet)
          (SelectionSet.size right.selectionSet) := by
  rcases List.mem_append.mp hchild with hchild | hchild
  · have h := fieldMerge_collectFields_children_size_lt schema _ _ child hchild
    omega
  · have h := fieldMerge_collectFields_children_size_lt schema _ _ child hchild
    omega

theorem FieldProjection.sameResponseShape (schema : Schema)
    (left right : FieldMerge.ScopedField)
    {leftSources rightSources : List FieldMerge.ScopedField}
    (hleft : FieldProjection schema leftSources left)
    (hright : FieldProjection schema rightSources right)
    (hresponse : left.responseName = right.responseName)
    (hsources
      : ∀ sourceLeft,
          sourceLeft ∈ leftSources ++ rightSources
          -> ∀ sourceRight,
              sourceRight ∈ leftSources ++ rightSources
              -> sourceLeft.responseName = sourceRight.responseName
              -> FieldMerge.sameResponseShape schema sourceLeft sourceRight)
    : FieldMerge.sameResponseShape schema left right := by
  obtain ⟨sourceLeft, hsourceLeft⟩ := List.exists_mem_of_ne_nil leftSources hleft.nonempty
  obtain ⟨sourceRight, hsourceRight⟩ := List.exists_mem_of_ne_nil rightSources hright.nonempty
  have hsourceShape := hsources sourceLeft (List.mem_append_left _ hsourceLeft)
    sourceRight (List.mem_append_right _ hsourceRight)
    ((hleft.metadata hsourceLeft).1.trans (hresponse.trans (hright.metadata hsourceRight).1.symm))
  refine .intro left right ?_ ?_
  · exact FieldMerge.sameTypeShape_trans schema left.outputType sourceLeft.outputType
      right.outputType
      (FieldMerge.sameTypeShape_symm schema _ _ (hleft.types hsourceLeft))
      (FieldMerge.sameTypeShape_trans schema sourceLeft.outputType sourceRight.outputType
        right.outputType (FieldMerge.sameResponseShape_sameTypeShape hsourceShape)
        (hright.types hsourceRight))
  · intro hleftComposite hrightComposite childLeft hchildLeft childRight hchildRight hchildResponse
    rcases hleft.pair_children hright hchildLeft with ⟨childLeftSources, hlsubset, hlprojection⟩
    rcases hleft.pair_children hright hchildRight with ⟨childRightSources, hrsubset, hrprojection⟩
    have hparentComposite (source : FieldMerge.ScopedField)
        (hsource : source ∈ leftSources ++ rightSources)
        : schema.isCompositeType source.outputType.namedType := by
      rcases List.mem_append.mp hsource with hsource | hsource
      · exact FieldMerge.sameTypeShape_composite_left schema
          (hleft.types hsource) hleftComposite
      · exact FieldMerge.sameTypeShape_composite_left schema
          (hright.types hsource) hrightComposite
    have hchildSources : ∀ sourceLeft,
        sourceLeft ∈ fieldProjectionChildren schema (leftSources ++ rightSources) ->
        ∀ sourceRight,
          sourceRight ∈ fieldProjectionChildren schema (leftSources ++ rightSources) ->
          sourceLeft.responseName = sourceRight.responseName ->
          FieldMerge.sameResponseShape schema sourceLeft sourceRight := by
      intro sourceLeft hsourceLeft sourceRight hsourceRight hresponse'
      rcases List.mem_flatMap.mp hsourceLeft with ⟨parentLeft, hparentLeft, hsourceLeft⟩
      rcases List.mem_flatMap.mp hsourceRight with ⟨parentRight, hparentRight, hsourceRight⟩
      have hparentResponse : parentLeft.responseName = parentRight.responseName := by
        have hresponseOf (parent : FieldMerge.ScopedField)
            (hparent : parent ∈ leftSources ++ rightSources)
            : parent.responseName = left.responseName := by
          rcases List.mem_append.mp hparent with hparent | hparent
          · exact (hleft.metadata hparent).1
          · exact (hright.metadata hparent).1.trans hresponse.symm
        exact (hresponseOf parentLeft hparentLeft).trans (hresponseOf parentRight hparentRight).symm
      exact FieldMerge.sameResponseShape_subfields
        (subLeft := sourceLeft) (subRight := sourceRight)
        (hsources parentLeft hparentLeft parentRight hparentRight hparentResponse)
        (hparentComposite parentLeft hparentLeft) (hparentComposite parentRight hparentRight)
        (List.mem_append_left _ hsourceLeft) (List.mem_append_right _ hsourceRight) hresponse'
    have hlSize := pair_child_size_lt hchildLeft
    have hrSize := pair_child_size_lt hchildRight
    apply FieldProjection.sameResponseShape schema childLeft childRight
      hlprojection hrprojection hchildResponse
    intro sourceLeft hsourceLeft sourceRight hsourceRight hresponse'
    have hsubset : childLeftSources ++ childRightSources ⊆
        fieldProjectionChildren schema (leftSources ++ rightSources) := by
      intro source hsource
      exact (List.mem_append.mp hsource).elim (fun h => hlsubset h) (fun h => hrsubset h)
    exact hchildSources sourceLeft (hsubset hsourceLeft) sourceRight (hsubset hsourceRight) hresponse'
termination_by
  max (SelectionSet.size left.selectionSet) (SelectionSet.size right.selectionSet)
decreasing_by omega

private theorem projectedParentCondition {schema : Schema}
    {sourceLeft sourceRight targetLeft targetRight : Name}
    (hleft : sourceLeft = targetLeft ∨ ¬ schema.objectType sourceLeft)
    (hright : sourceRight = targetRight ∨ ¬ schema.objectType sourceRight)
    (htarget
      : targetLeft = targetRight
        ∨ ¬ schema.objectType targetLeft
        ∨ ¬ schema.objectType targetRight)
    : sourceLeft = sourceRight
      ∨ ¬ schema.objectType sourceLeft
      ∨ ¬ schema.objectType sourceRight := by
  rcases hleft with hleft | hleft
  · rcases hright with hright | hright
    · simpa [← hleft, ← hright] using htarget
    · exact Or.inr (Or.inr hright)
  · exact Or.inr (Or.inl hleft)

theorem FieldProjection.canMerge (schema : Schema) (left right : FieldMerge.ScopedField)
    {leftSources rightSources : List FieldMerge.ScopedField}
    (hleft : FieldProjection schema leftSources left)
    (hright : FieldProjection schema rightSources right)
    (hresponse : left.responseName = right.responseName)
    (hsources
      : ∀ sourceLeft,
          sourceLeft ∈ leftSources ++ rightSources
          -> ∀ sourceRight,
              sourceRight ∈ leftSources ++ rightSources
              -> sourceLeft.responseName = sourceRight.responseName
              -> FieldMerge.fieldsForNameCanMerge schema sourceLeft sourceRight)
    : FieldMerge.fieldsForNameCanMerge schema left right := by
  have hresponseOf (source : FieldMerge.ScopedField)
      (hsource : source ∈ leftSources ++ rightSources)
      : source.responseName = left.responseName := by
    rcases List.mem_append.mp hsource with hsource | hsource
    · exact (hleft.metadata hsource).1
    · exact (hright.metadata hsource).1.trans hresponse.symm
  have hparentsOf
      (htarget : left.parentType = right.parentType
        ∨ ¬ schema.objectType left.parentType ∨ ¬ schema.objectType right.parentType)
      (sourceLeft : FieldMerge.ScopedField) (hsourceLeft : sourceLeft ∈ leftSources ++ rightSources)
      (sourceRight : FieldMerge.ScopedField) (hsourceRight : sourceRight ∈ leftSources ++ rightSources)
      : sourceLeft.parentType = sourceRight.parentType
        ∨ ¬ schema.objectType sourceLeft.parentType ∨ ¬ schema.objectType sourceRight.parentType := by
    rcases List.mem_append.mp hsourceLeft with hsourceLeft | hsourceLeft
    · rcases List.mem_append.mp hsourceRight with hsourceRight | hsourceRight
      · exact projectedParentCondition (hleft.metadata hsourceLeft).2.2.2
          (hleft.metadata hsourceRight).2.2.2 (Or.inl rfl)
      · exact projectedParentCondition (hleft.metadata hsourceLeft).2.2.2
          (hright.metadata hsourceRight).2.2.2 htarget
    · rcases List.mem_append.mp hsourceRight with hsourceRight | hsourceRight
      · have hreverse : right.parentType = left.parentType
            ∨ ¬ schema.objectType right.parentType ∨ ¬ schema.objectType left.parentType := by
          rcases htarget with h | h | h
          · exact Or.inl h.symm
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)
        exact projectedParentCondition (hright.metadata hsourceLeft).2.2.2
          (hleft.metadata hsourceRight).2.2.2 hreverse
      · exact projectedParentCondition (hright.metadata hsourceLeft).2.2.2
          (hright.metadata hsourceRight).2.2.2 (Or.inl rfl)
  refine .intro left right ?_ ?_ ?_
  · apply FieldProjection.sameResponseShape schema left right hleft hright hresponse
    intro sourceLeft hsourceLeft sourceRight hsourceRight hresponse'
    exact FieldMerge.fieldsForNameCanMerge_sameResponseShape
      (hsources sourceLeft hsourceLeft sourceRight hsourceRight hresponse')
  · intro htarget
    obtain ⟨sourceLeft, hsourceLeft⟩ := List.exists_mem_of_ne_nil leftSources hleft.nonempty
    obtain ⟨sourceRight, hsourceRight⟩ := List.exists_mem_of_ne_nil rightSources hright.nonempty
    have hleftMem := List.mem_append_left rightSources hsourceLeft
    have hrightMem := List.mem_append_right leftSources hsourceRight
    have hpair := hsources sourceLeft hleftMem sourceRight hrightMem
      ((hresponseOf sourceLeft hleftMem).trans (hresponseOf sourceRight hrightMem).symm)
    have hidentity := FieldMerge.fieldsForNameCanMerge_identity hpair
      (hparentsOf htarget sourceLeft hleftMem sourceRight hrightMem)
    refine ⟨(hleft.metadata hsourceLeft).2.1.symm.trans
      (hidentity.1.trans (hright.metadata hsourceRight).2.1), ?_⟩
    exact Execution.argumentsEquivalent_trans_forCoercion
      (FieldMerge.argumentsEquivalent_symm (hleft.metadata hsourceLeft).2.2.1)
      (Execution.argumentsEquivalent_trans_forCoercion hidentity.2
        (hright.metadata hsourceRight).2.2.1)
  · intro htarget childLeft hchildLeft childRight hchildRight hchildResponse
    rcases hleft.pair_children hright hchildLeft with ⟨childLeftSources, hlsubset, hlprojection⟩
    rcases hleft.pair_children hright hchildRight with ⟨childRightSources, hrsubset, hrprojection⟩
    have hchildSources : ∀ sourceLeft,
        sourceLeft ∈ fieldProjectionChildren schema (leftSources ++ rightSources) ->
        ∀ sourceRight,
          sourceRight ∈ fieldProjectionChildren schema (leftSources ++ rightSources) ->
          sourceLeft.responseName = sourceRight.responseName ->
          FieldMerge.fieldsForNameCanMerge schema sourceLeft sourceRight := by
      intro sourceLeft hsourceLeft sourceRight hsourceRight hresponse'
      rcases List.mem_flatMap.mp hsourceLeft with ⟨parentLeft, hparentLeft, hsourceLeft⟩
      rcases List.mem_flatMap.mp hsourceRight with ⟨parentRight, hparentRight, hsourceRight⟩
      have hpair := hsources parentLeft hparentLeft parentRight hparentRight
        ((hresponseOf parentLeft hparentLeft).trans (hresponseOf parentRight hparentRight).symm)
      exact FieldMerge.fieldsForNameCanMerge_collected_subfields hpair
        (hparentsOf htarget parentLeft hparentLeft parentRight hparentRight)
        sourceLeft (List.mem_append_left _ hsourceLeft)
        sourceRight (List.mem_append_right _ hsourceRight) hresponse'
    have hlSize := pair_child_size_lt hchildLeft
    have hrSize := pair_child_size_lt hchildRight
    apply FieldProjection.canMerge schema childLeft childRight
      hlprojection hrprojection hchildResponse
    intro sourceLeft hsourceLeft sourceRight hsourceRight hresponse'
    have hsubset : childLeftSources ++ childRightSources ⊆
        fieldProjectionChildren schema (leftSources ++ rightSources) := by
      intro source hsource
      exact (List.mem_append.mp hsource).elim (fun h => hlsubset h) (fun h => hrsubset h)
    exact hchildSources sourceLeft (hsubset hsourceLeft) sourceRight (hsubset hsourceRight) hresponse'
termination_by
  max (SelectionSet.size left.selectionSet) (SelectionSet.size right.selectionSet)
decreasing_by omega

end GraphQL.NormalForm
