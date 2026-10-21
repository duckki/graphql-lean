import GraphQL.Validation
import Proofs.GraphQL.SchemaWellFormedness.TypeShape

/-!
Facts for same-response-name field merge validation.
-/

namespace GraphQL

namespace FieldMerge

theorem fieldsInSetCanMerge_pair
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {left right : ScopedField}
    : fieldsInSetCanMerge schema parentType selectionSet
      -> left ∈ collectFields schema parentType selectionSet
      -> right ∈ collectFields schema parentType selectionSet
      -> left.responseName = right.responseName
      -> fieldsForNameCanMerge schema left right := by
  intro hmerge hleft hright hresponse
  unfold fieldsInSetCanMerge at hmerge
  cases hmerge with
  | intro _ _ hfields =>
      exact hfields left hleft right hright hresponse

theorem fieldsForNameCanMerge_sameTypeShape {schema : Schema} {left right : ScopedField}
    : fieldsForNameCanMerge schema left right
      -> SchemaWellFormedness.sameTypeShape schema left.outputType right.outputType := by
  intro hmerge
  unfold fieldsForNameCanMerge at hmerge
  cases hmerge with
  | intro _ _ hshape _hidentity _hsubfields =>
      cases hshape with
      | intro _ _ htypes _hsubfields => exact htypes

theorem fieldsForNameCanMerge_identity {schema : Schema} {left right : ScopedField}
    : fieldsForNameCanMerge schema left right
      -> (left.parentType = right.parentType
          ∨ ¬ schema.objectType left.parentType
          ∨ ¬ schema.objectType right.parentType)
      -> left.fieldName = right.fieldName
          ∧ Argument.argumentsEquivalent left.arguments right.arguments := by
  intro hmerge hparents
  unfold fieldsForNameCanMerge at hmerge
  cases hmerge with
  | intro _ _ _hshape hidentity _hsubfields =>
      exact hidentity hparents

theorem fieldsForNameCanMerge_same_parent_identity
    {schema : Schema} {left right : ScopedField}
    : fieldsForNameCanMerge schema left right
      -> left.parentType = right.parentType
      -> left.fieldName = right.fieldName
          ∧ Argument.argumentsEquivalent left.arguments right.arguments := by
  intro hmerge hparent
  exact fieldsForNameCanMerge_identity hmerge (Or.inl hparent)

theorem fieldsForNameCanMerge_collected_subfields {schema : Schema}
    {left right : ScopedField}
    : fieldsForNameCanMerge schema left right
      -> (left.parentType = right.parentType
          ∨ ¬ schema.objectType left.parentType
          ∨ ¬ schema.objectType right.parentType)
      -> ∀ subLeft,
          subLeft ∈ collectSubfields schema left right
          -> ∀ subRight,
              subRight ∈ collectSubfields schema left right
              -> subLeft.responseName = subRight.responseName
              -> fieldsForNameCanMerge schema subLeft subRight := by
  intro hmerge hparents
  unfold fieldsForNameCanMerge at hmerge
  cases hmerge with
  | intro _ _ _hshape _hidentity hsubfields =>
      exact hsubfields hparents

theorem fieldsForNameCanMerge_sameResponseShape {schema : Schema}
    {left right : ScopedField} (hmerge : fieldsForNameCanMerge schema left right)
    : sameResponseShape schema left right := by
  cases hmerge with
  | intro _ _ hshape _ _ => exact hshape

theorem collectFields_append (schema : Schema) (parentType : Name)
    : ∀ left right,
        collectFields schema parentType (left ++ right)
        = collectFields schema parentType left ++ collectFields schema parentType right
  | [], _right => by
      simp [collectFields]
  | selection :: rest, right => by
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [collectFields, hlookup,
                collectFields_append schema parentType rest right]
          | some fieldDefinition =>
              simp [collectFields, hlookup,
                collectFields_append schema parentType rest right]
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [collectFields,
                collectFields_append schema parentType rest right,
                List.append_assoc]
          | some typeCondition =>
              simp [collectFields,
                collectFields_append schema parentType rest right,
                List.append_assoc]

theorem fieldsForNameCanMerge_subfields {schema : Schema} {left right : ScopedField}
    (hmerge : fieldsForNameCanMerge schema left right)
    (hparents
      : left.parentType = right.parentType
        ∨ ¬ schema.objectType left.parentType
        ∨ ¬ schema.objectType right.parentType)
    (parentType : Name)
    (hleft : left.outputType.namedType = parentType)
    (hright : right.outputType.namedType = parentType)
    : fieldsInSetCanMerge schema parentType
        (left.selectionSet ++ right.selectionSet) := by
  refine FieldsInSetCanMerge.intro _ _ ?_
  dsimp
  intro subLeft hsubLeft subRight hsubRight hresponse
  apply fieldsForNameCanMerge_collected_subfields hmerge hparents subLeft ?_ subRight ?_ hresponse
  · simpa [collectSubfields, hleft, hright, collectFields_append] using hsubLeft
  · simpa [collectSubfields, hleft, hright, collectFields_append] using hsubRight

theorem collectSubfields_swap_mem {schema : Schema} {left right field : ScopedField}
    : field ∈ collectSubfields schema right left
      ↔ field ∈ collectSubfields schema left right := by
  simp only [collectSubfields, List.mem_append, or_comm]

theorem sameResponseShape_symm {schema : Schema} {left right : ScopedField}
    (hshape : sameResponseShape schema left right)
    : sameResponseShape schema right left := by
  cases hshape with
  | intro _ _ htypes hchildren =>
      refine .intro _ _ (SchemaWellFormedness.sameTypeShape_symm schema _ _ htypes) ?_
      intro hright hleft subLeft hsubLeft subRight hsubRight hresponse
      exact hchildren hleft hright subLeft (collectSubfields_swap_mem.mp hsubLeft)
        subRight (collectSubfields_swap_mem.mp hsubRight) hresponse

theorem sameResponseShape_sameTypeShape {schema : Schema} {left right : ScopedField}
    (hshape : sameResponseShape schema left right)
    : SchemaWellFormedness.sameTypeShape schema left.outputType right.outputType := by
  cases hshape with
  | intro _ _ htypes _ => exact htypes

theorem sameResponseShape_subfields {schema : Schema} {left right : ScopedField}
    (hshape : sameResponseShape schema left right)
    (hleft : schema.isCompositeType left.outputType.namedType)
    (hright : schema.isCompositeType right.outputType.namedType)
    {subLeft subRight : ScopedField}
    (hsubLeft : subLeft ∈ collectSubfields schema left right)
    (hsubRight : subRight ∈ collectSubfields schema left right)
    (hresponse : subLeft.responseName = subRight.responseName)
    : sameResponseShape schema subLeft subRight := by
  cases hshape with
  | intro _ _ _ hchildren =>
      exact hchildren hleft hright subLeft hsubLeft subRight hsubRight hresponse

mutual
  theorem inputValue_structuralEquivalent_symm
      : ∀ left right,
          InputValue.structuralEquivalent left right
          -> InputValue.structuralEquivalent right left
    | .null, .null, h => by
        simp [InputValue.structuralEquivalent]
    | .int left, .int right, h => by
        simpa [InputValue.structuralEquivalent] using h.symm
    | .float left, .float right, h => by
        simpa [InputValue.structuralEquivalent] using h.symm
    | .string left, .string right, h => by
        simpa [InputValue.structuralEquivalent] using h.symm
    | .boolean left, .boolean right, h => by
        simpa [InputValue.structuralEquivalent] using h.symm
    | .enum left, .enum right, h => by
        simpa [InputValue.structuralEquivalent] using h.symm
    | .variable left, .variable right, h => by
        simpa [InputValue.structuralEquivalent] using h.symm
    | .list left, .list right, h => by
        exact inputValue_structuralValuesEquivalent_symm left right h
    | .object left, .object right, h => by
        exact inputValue_structuralObjectFieldsEquivalent_symm left right h
    | .null, .int _, h => by simp [InputValue.structuralEquivalent] at h
    | .null, .float _, h => by simp [InputValue.structuralEquivalent] at h
    | .null, .string _, h => by simp [InputValue.structuralEquivalent] at h
    | .null, .boolean _, h => by simp [InputValue.structuralEquivalent] at h
    | .null, .enum _, h => by simp [InputValue.structuralEquivalent] at h
    | .null, .list _, h => by simp [InputValue.structuralEquivalent] at h
    | .null, .object _, h => by simp [InputValue.structuralEquivalent] at h
    | .null, .variable _, h => by simp [InputValue.structuralEquivalent] at h
    | .int _, .null, h => by simp [InputValue.structuralEquivalent] at h
    | .int _, .float _, h => by simp [InputValue.structuralEquivalent] at h
    | .int _, .string _, h => by simp [InputValue.structuralEquivalent] at h
    | .int _, .boolean _, h => by simp [InputValue.structuralEquivalent] at h
    | .int _, .enum _, h => by simp [InputValue.structuralEquivalent] at h
    | .int _, .list _, h => by simp [InputValue.structuralEquivalent] at h
    | .int _, .object _, h => by simp [InputValue.structuralEquivalent] at h
    | .int _, .variable _, h => by simp [InputValue.structuralEquivalent] at h
    | .float _, .null, h => by simp [InputValue.structuralEquivalent] at h
    | .float _, .int _, h => by simp [InputValue.structuralEquivalent] at h
    | .float _, .string _, h => by simp [InputValue.structuralEquivalent] at h
    | .float _, .boolean _, h => by simp [InputValue.structuralEquivalent] at h
    | .float _, .enum _, h => by simp [InputValue.structuralEquivalent] at h
    | .float _, .list _, h => by simp [InputValue.structuralEquivalent] at h
    | .float _, .object _, h => by simp [InputValue.structuralEquivalent] at h
    | .float _, .variable _, h => by simp [InputValue.structuralEquivalent] at h
    | .string _, .null, h => by simp [InputValue.structuralEquivalent] at h
    | .string _, .int _, h => by simp [InputValue.structuralEquivalent] at h
    | .string _, .float _, h => by simp [InputValue.structuralEquivalent] at h
    | .string _, .boolean _, h => by simp [InputValue.structuralEquivalent] at h
    | .string _, .enum _, h => by simp [InputValue.structuralEquivalent] at h
    | .string _, .list _, h => by simp [InputValue.structuralEquivalent] at h
    | .string _, .object _, h => by simp [InputValue.structuralEquivalent] at h
    | .string _, .variable _, h => by simp [InputValue.structuralEquivalent] at h
    | .boolean _, .null, h => by simp [InputValue.structuralEquivalent] at h
    | .boolean _, .int _, h => by simp [InputValue.structuralEquivalent] at h
    | .boolean _, .float _, h => by simp [InputValue.structuralEquivalent] at h
    | .boolean _, .string _, h => by simp [InputValue.structuralEquivalent] at h
    | .boolean _, .enum _, h => by simp [InputValue.structuralEquivalent] at h
    | .boolean _, .list _, h => by simp [InputValue.structuralEquivalent] at h
    | .boolean _, .object _, h => by simp [InputValue.structuralEquivalent] at h
    | .boolean _, .variable _, h => by simp [InputValue.structuralEquivalent] at h
    | .enum _, .null, h => by simp [InputValue.structuralEquivalent] at h
    | .enum _, .int _, h => by simp [InputValue.structuralEquivalent] at h
    | .enum _, .float _, h => by simp [InputValue.structuralEquivalent] at h
    | .enum _, .string _, h => by simp [InputValue.structuralEquivalent] at h
    | .enum _, .boolean _, h => by simp [InputValue.structuralEquivalent] at h
    | .enum _, .list _, h => by simp [InputValue.structuralEquivalent] at h
    | .enum _, .object _, h => by simp [InputValue.structuralEquivalent] at h
    | .enum _, .variable _, h => by simp [InputValue.structuralEquivalent] at h
    | .list _, .null, h => by simp [InputValue.structuralEquivalent] at h
    | .list _, .int _, h => by simp [InputValue.structuralEquivalent] at h
    | .list _, .float _, h => by simp [InputValue.structuralEquivalent] at h
    | .list _, .string _, h => by simp [InputValue.structuralEquivalent] at h
    | .list _, .boolean _, h => by simp [InputValue.structuralEquivalent] at h
    | .list _, .enum _, h => by simp [InputValue.structuralEquivalent] at h
    | .list _, .object _, h => by simp [InputValue.structuralEquivalent] at h
    | .list _, .variable _, h => by simp [InputValue.structuralEquivalent] at h
    | .object _, .null, h => by simp [InputValue.structuralEquivalent] at h
    | .object _, .int _, h => by simp [InputValue.structuralEquivalent] at h
    | .object _, .float _, h => by simp [InputValue.structuralEquivalent] at h
    | .object _, .string _, h => by simp [InputValue.structuralEquivalent] at h
    | .object _, .boolean _, h => by simp [InputValue.structuralEquivalent] at h
    | .object _, .enum _, h => by simp [InputValue.structuralEquivalent] at h
    | .object _, .list _, h => by simp [InputValue.structuralEquivalent] at h
    | .object _, .variable _, h => by simp [InputValue.structuralEquivalent] at h
    | .variable _, .null, h => by simp [InputValue.structuralEquivalent] at h
    | .variable _, .int _, h => by simp [InputValue.structuralEquivalent] at h
    | .variable _, .float _, h => by simp [InputValue.structuralEquivalent] at h
    | .variable _, .string _, h => by simp [InputValue.structuralEquivalent] at h
    | .variable _, .boolean _, h => by simp [InputValue.structuralEquivalent] at h
    | .variable _, .enum _, h => by simp [InputValue.structuralEquivalent] at h
    | .variable _, .list _, h => by simp [InputValue.structuralEquivalent] at h
    | .variable _, .object _, h => by simp [InputValue.structuralEquivalent] at h

  theorem inputValue_structuralValuesEquivalent_symm
      : ∀ left right,
          InputValue.structuralValuesEquivalent left right
          -> InputValue.structuralValuesEquivalent right left
    | [], [], h => by
        simp [InputValue.structuralValuesEquivalent]
    | left :: lefts, right :: rights, h => by
        simp [InputValue.structuralValuesEquivalent] at h ⊢
        exact ⟨inputValue_structuralEquivalent_symm left right h.1,
          inputValue_structuralValuesEquivalent_symm lefts rights h.2⟩
    | [], _ :: _, h => by
        simp [InputValue.structuralValuesEquivalent] at h
    | _ :: _, [], h => by
        simp [InputValue.structuralValuesEquivalent] at h

  theorem inputValue_structuralObjectFieldsEquivalent_symm
      : ∀ left right,
          InputValue.structuralObjectFieldsEquivalent left right
          -> InputValue.structuralObjectFieldsEquivalent right left
    | [], [], h => by
        simp [InputValue.structuralObjectFieldsEquivalent]
    | (leftName, leftValue) :: lefts,
      (rightName, rightValue) :: rights, h => by
        simp [InputValue.structuralObjectFieldsEquivalent] at h ⊢
        exact ⟨h.1.symm,
          inputValue_structuralEquivalent_symm leftValue rightValue h.2.1,
          inputValue_structuralObjectFieldsEquivalent_symm lefts rights
            h.2.2⟩
    | [], _ :: _, h => by
        simp [InputValue.structuralObjectFieldsEquivalent] at h
    | _ :: _, [], h => by
        simp [InputValue.structuralObjectFieldsEquivalent] at h
end

theorem inputValue_equivalent_symm {left right : InputValue}
    : left.equivalent right -> right.equivalent left := by
  intro h
  exact inputValue_structuralEquivalent_symm left.canonical right.canonical h

theorem argumentEquivalent_symm {left right : Argument}
    : left.equivalent right -> right.equivalent left := by
  intro h
  exact ⟨h.1.symm, inputValue_equivalent_symm h.2⟩

theorem argumentsEquivalent_symm {left right : List Argument}
    : Argument.argumentsEquivalent left right
      -> Argument.argumentsEquivalent right left := by
  intro h
  exact ⟨
    by
      intro argument hargument
      rcases h.2 argument hargument with
        ⟨argument', hargument', hequivalent⟩
      exact ⟨argument', hargument',
        argumentEquivalent_symm hequivalent⟩,
    by
      intro argument hargument
      rcases h.1 argument hargument with
        ⟨argument', hargument', hequivalent⟩
      exact ⟨argument', hargument',
        argumentEquivalent_symm hequivalent⟩
  ⟩

theorem fieldsInSetCanMerge_append_comm
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : fieldsInSetCanMerge schema parentType (left ++ right)
      -> fieldsInSetCanMerge schema parentType (right ++ left) := by
  intro hmerge
  unfold fieldsInSetCanMerge
  refine FieldsInSetCanMerge.intro parentType (right ++ left) ?_
  dsimp
  intro sourceLeft hleft sourceRight hright hresponse
  rw [collectFields_append] at hleft hright
  rcases List.mem_append.mp hleft with hleftRight | hleftLeft
  · rcases List.mem_append.mp hright with hrightRight | hrightLeft
    · exact fieldsInSetCanMerge_pair hmerge
        (by
          rw [collectFields_append]
          exact List.mem_append_right
            (collectFields schema parentType left) hleftRight)
        (by
          rw [collectFields_append]
          exact List.mem_append_right
            (collectFields schema parentType left) hrightRight)
        hresponse
    · exact fieldsInSetCanMerge_pair hmerge
        (by
          rw [collectFields_append]
          exact List.mem_append_right
            (collectFields schema parentType left) hleftRight)
        (by
          rw [collectFields_append]
          exact List.mem_append_left
            (collectFields schema parentType right) hrightLeft)
        hresponse
  · rcases List.mem_append.mp hright with hrightRight | hrightLeft
    · exact fieldsInSetCanMerge_pair hmerge
        (by
          rw [collectFields_append]
          exact List.mem_append_left
            (collectFields schema parentType right) hleftLeft)
        (by
          rw [collectFields_append]
          exact List.mem_append_right
            (collectFields schema parentType left) hrightRight)
        hresponse
    · exact fieldsInSetCanMerge_pair hmerge
        (by
          rw [collectFields_append]
          exact List.mem_append_left
            (collectFields schema parentType right) hleftLeft)
        (by
          rw [collectFields_append]
          exact List.mem_append_left
            (collectFields schema parentType right) hrightLeft)
        hresponse

theorem fieldsForNameCanMerge_symm {schema : Schema} {left right : ScopedField}
    : fieldsForNameCanMerge schema left right
      -> fieldsForNameCanMerge schema right left := by
  intro hmerge
  unfold fieldsForNameCanMerge at hmerge ⊢
  cases hmerge with
  | intro _ _ hshape hidentity hsubfields =>
      refine FieldsForNameCanMerge.intro right left ?_ ?_ ?_
      · exact sameResponseShape_symm hshape
      · intro hparents
        have hsourceParents :
            left.parentType = right.parentType
              ∨ ¬ schema.objectType left.parentType
              ∨ ¬ schema.objectType right.parentType := by
          rcases hparents with hparentEq | hnotObject
          · exact Or.inl hparentEq.symm
          · rcases hnotObject with hrightNotObject | hleftNotObject
            · exact Or.inr (Or.inr hrightNotObject)
            · exact Or.inr (Or.inl hleftNotObject)
        rcases hidentity hsourceParents with ⟨hfieldName, harguments⟩
        exact ⟨hfieldName.symm, argumentsEquivalent_symm harguments⟩
      · intro hparents subLeft hsubLeft subRight hsubRight hresponse
        have hsourceParents :
            left.parentType = right.parentType
              ∨ ¬ schema.objectType left.parentType
              ∨ ¬ schema.objectType right.parentType := by
          rcases hparents with hparentEq | hnotObject
          · exact Or.inl hparentEq.symm
          · rcases hnotObject with hrightNotObject | hleftNotObject
            · exact Or.inr (Or.inr hrightNotObject)
            · exact Or.inr (Or.inl hleftNotObject)
        exact hsubfields hsourceParents subLeft (collectSubfields_swap_mem.mp hsubLeft)
          subRight (collectSubfields_swap_mem.mp hsubRight) hresponse

/-- Merge checks survive transformations preserving field metadata and tracing every
collected child back to its original declared scope. -/
theorem fieldsInSetCanMerge_transport
    {schema : Schema} (relation : ScopedField -> ScopedField -> Prop)
    (hmetadata
      : ∀ source target,
          relation source target
          -> target.parentType = source.parentType
              ∧ target.responseName = source.responseName
              ∧ target.fieldName = source.fieldName
              ∧ target.arguments = source.arguments
              ∧ target.outputType = source.outputType)
    (hchildren
      : ∀ sourceLeft sourceRight targetLeft targetRight,
          relation sourceLeft targetLeft
          -> relation sourceRight targetRight
          -> ∀ child,
              child ∈ collectSubfields schema targetLeft targetRight
              -> ∃ sourceChild,
                  sourceChild ∈ collectSubfields schema sourceLeft sourceRight
                  ∧ relation sourceChild child)
    {parentType : Name} {selectionSet : List Selection}
    (hmerge : fieldsInSetCanMerge schema parentType selectionSet)
    (targetParent : Name) (targetSet : List Selection)
    (hfields
      : ∀ field,
          field ∈ collectFields schema targetParent targetSet
          -> ∃ sourceField,
              sourceField ∈ collectFields schema parentType selectionSet
              ∧ relation sourceField field)
    : fieldsInSetCanMerge schema targetParent targetSet := by
  revert targetParent targetSet hfields
  refine FieldsInSetCanMerge.rec
    (motive_1 := fun parentType selectionSet _ =>
      ∀ targetParent targetSet,
        (∀ field, field ∈ collectFields schema targetParent targetSet ->
          ∃ sourceField, sourceField ∈ collectFields schema parentType selectionSet
            ∧ relation sourceField field) ->
        fieldsInSetCanMerge schema targetParent targetSet)
    (motive_2 := fun left right _ => ∀ targetLeft targetRight,
      relation left targetLeft -> relation right targetRight ->
      fieldsForNameCanMerge schema targetLeft targetRight)
    (motive_3 := fun left right _ => ∀ targetLeft targetRight,
      relation left targetLeft -> relation right targetRight ->
      SameResponseShape schema targetLeft targetRight)
    ?_ ?_ ?_ hmerge
  · intro parentType selectionSet _ ihFields targetParent targetSet hfields
    refine .intro _ _ ?_
    dsimp
    intro left hleft right hright hresponse
    rcases hfields left hleft with ⟨sourceLeft, hsourceLeft, hleftRelation⟩
    rcases hfields right hright with ⟨sourceRight, hsourceRight, hrightRelation⟩
    have hl := hmetadata _ _ hleftRelation
    have hr := hmetadata _ _ hrightRelation
    exact ihFields sourceLeft hsourceLeft sourceRight hsourceRight
      (hl.2.1.symm.trans (hresponse.trans hr.2.1))
      left right hleftRelation hrightRelation
  · intro left right _ hidentity _ ihShape ihChildren
      targetLeft targetRight hleftRelation hrightRelation
    have hl := hmetadata _ _ hleftRelation
    have hr := hmetadata _ _ hrightRelation
    refine .intro _ _ (ihShape _ _ hleftRelation hrightRelation) ?_ ?_
    · intro hparents
      have hsourceParents : left.parentType = right.parentType
          ∨ ¬ schema.objectType left.parentType ∨ ¬ schema.objectType right.parentType := by
        simpa only [hl.1, hr.1] using hparents
      rcases hidentity hsourceParents with ⟨hnames, harguments⟩
      exact ⟨
        hl.2.2.1.trans (hnames.trans hr.2.2.1.symm),
        by simpa only [hl.2.2.2.1, hr.2.2.2.1] using harguments
      ⟩
    · intro hparents childLeft hchildLeft childRight hchildRight hresponse
      have hsourceParents : left.parentType = right.parentType
          ∨ ¬ schema.objectType left.parentType ∨ ¬ schema.objectType right.parentType := by
        simpa only [hl.1, hr.1] using hparents
      rcases hchildren _ _ _ _ hleftRelation hrightRelation _ hchildLeft with
        ⟨sourceLeft, hsourceLeft, hleft⟩
      rcases hchildren _ _ _ _ hleftRelation hrightRelation _ hchildRight with
        ⟨sourceRight, hsourceRight, hright⟩
      exact ihChildren hsourceParents sourceLeft hsourceLeft sourceRight hsourceRight
        ((hmetadata _ _ hleft).2.1.symm.trans
          (hresponse.trans (hmetadata _ _ hright).2.1))
        _ _ hleft hright
  · intro left right htypes _ ihChildren targetLeft targetRight hleftRelation hrightRelation
    have hl := hmetadata _ _ hleftRelation
    have hr := hmetadata _ _ hrightRelation
    refine .intro _ _ (by simpa only [hl.2.2.2.2, hr.2.2.2.2] using htypes) ?_
    intro hleftComposite hrightComposite childLeft hchildLeft childRight hchildRight hresponse
    rcases hchildren _ _ _ _ hleftRelation hrightRelation _ hchildLeft with
      ⟨sourceLeft, hsourceLeft, hleft⟩
    rcases hchildren _ _ _ _ hleftRelation hrightRelation _ hchildRight with
      ⟨sourceRight, hsourceRight, hright⟩
    exact ihChildren (by simpa only [hl.2.2.2.2] using hleftComposite)
      (by simpa only [hr.2.2.2.2] using hrightComposite)
      sourceLeft hsourceLeft sourceRight hsourceRight
      ((hmetadata _ _ hleft).2.1.symm.trans
        (hresponse.trans (hmetadata _ _ hright).2.1))
      _ _ hleft hright

theorem fieldsForNameCanMerge_self_of_children {schema : Schema} {field : ScopedField}
    (htype : SchemaWellFormedness.sameTypeShape schema field.outputType field.outputType)
    (harguments : Argument.argumentsEquivalent field.arguments field.arguments)
    (hchildren
      : fieldsInSetCanMerge schema field.outputType.namedType
          (field.selectionSet ++ field.selectionSet))
    : fieldsForNameCanMerge schema field field := by
  have hpairs : ∀ left, left ∈ collectSubfields schema field field ->
      ∀ right, right ∈ collectSubfields schema field field ->
      left.responseName = right.responseName -> fieldsForNameCanMerge schema left right := by
    intro left hleft right hright hresponse
    exact fieldsInSetCanMerge_pair hchildren
      (by simpa [collectSubfields, collectFields_append] using hleft)
      (by simpa [collectSubfields, collectFields_append] using hright) hresponse
  refine .intro field field (.intro field field htype ?_) (fun _ => ⟨rfl, harguments⟩)
    (fun _ => hpairs)
  intro _ _ left hleft right hright hresponse
  exact fieldsForNameCanMerge_sameResponseShape (hpairs left hleft right hright hresponse)

end FieldMerge

end GraphQL
