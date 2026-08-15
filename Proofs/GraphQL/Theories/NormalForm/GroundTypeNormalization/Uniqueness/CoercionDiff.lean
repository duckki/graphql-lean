import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.SyntaxDiff

/-!
Resolver-visible differences for normal selection sets.

Unlike `NormalSelectionSetDiff`, field argument differences are measured at the
resolver boundary for one effective variable environment.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

inductive NormalSelectionSetResolverDiff (schema : Schema)
    (variableValues : Execution.VariableValues)
    : Name -> List Selection -> List Selection -> Prop where
  | objectLeftResponseName
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> NormalSelectionSetResolverDiff schema variableValues parentType left right

  | objectRightResponseName
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> NormalSelectionSetResolverDiff schema variableValues parentType left right
  | objectFieldName
    {parentType : Name} {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> leftFieldName ≠ rightFieldName
      -> NormalSelectionSetResolverDiff schema variableValues parentType left right
  | objectArguments
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    (fieldDefinition : FieldDefinition)
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> ¬ Execution.ArgumentCoercionResult.equivalent
            (Execution.coerceArgumentValues schema variableValues
              fieldDefinition.arguments leftArguments)
            (Execution.coerceArgumentValues schema variableValues
              fieldDefinition.arguments rightArguments)
      -> NormalSelectionSetResolverDiff schema variableValues parentType left right
  | objectChild
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    (fieldDefinition : FieldDefinition)
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> Execution.ArgumentCoercionResult.equivalent
          (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments leftArguments)
          (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments rightArguments)
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments leftArguments).isSuccess
          = true
      -> NormalSelectionSetResolverDiff schema variableValues
          fieldDefinition.outputType.namedType leftChildSelectionSet
          rightChildSelectionSet
      -> NormalSelectionSetResolverDiff schema variableValues parentType left right
  | abstractLeftTypeCondition
    {parentType : Name} {left right : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet ∈ left
      -> typeCondition ∉ right.filterMap inlineFragmentTypeCondition?
      -> NormalSelectionSetResolverDiff schema variableValues parentType left right
  | abstractRightTypeCondition
    {parentType : Name} {left right : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ right
      -> typeCondition ∉ left.filterMap inlineFragmentTypeCondition?
      -> NormalSelectionSetResolverDiff schema variableValues parentType left right
  | abstractChild
    {parentType typeCondition : Name} {left right : List Selection}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.inlineFragment (some typeCondition) rightDirectives
            rightChildSelectionSet
          ∈ right
      -> NormalSelectionSetResolverDiff schema variableValues typeCondition
          leftChildSelectionSet rightChildSelectionSet
      -> NormalSelectionSetResolverDiff schema variableValues parentType left right

theorem normalSelectionSetResolverDiff_left_or_right_nonempty
    {schema : Schema} {variableValues : Execution.VariableValues}
    {parentType : Name} {left right : List Selection}
    : NormalSelectionSetResolverDiff schema variableValues parentType left right
      -> left ≠ [] ∨ right ≠ [] := by
  intro hdiff
  cases hdiff with
  | objectLeftResponseName _ hmem _ => exact Or.inl (by rintro rfl; simp at hmem)
  | objectRightResponseName _ hmem _ => exact Or.inr (by rintro rfl; simp at hmem)
  | objectFieldName _ hleft _ _ => exact Or.inl (by rintro rfl; simp at hleft)
  | objectArguments _ _ hleft _ _ _ => exact Or.inl (by rintro rfl; simp at hleft)
  | objectChild _ _ hleft _ _ _ _ => exact Or.inl (by rintro rfl; simp at hleft)
  | abstractLeftTypeCondition _ hmem _ => exact Or.inl (by rintro rfl; simp at hmem)
  | abstractRightTypeCondition _ hmem _ => exact Or.inr (by rintro rfl; simp at hmem)
  | abstractChild _ hleft _ _ => exact Or.inl (by rintro rfl; simp at hleft)

theorem selectionSetEqualUpToReordering_of_no_diff
    (schema : Schema) (variableValues : Execution.VariableValues)
    : ∀ parentType left right,
        selectionSetDirectiveFree left
        -> selectionSetDirectiveFree right
        -> selectionSetNormal schema parentType left
        -> selectionSetNormal schema parentType right
        -> ¬ NormalSelectionSetResolverDiff schema variableValues parentType left right
        -> SelectionSetEqualUpToReorderingWithCoercion schema variableValues
            variableValues parentType left right := by
  intro parentType left right hleftFree hrightFree hleftNormal hrightNormal hnoDiff
  by_cases hobject : objectTypeNameBool schema parentType = true
  · rcases selectionSetPairedBy_of_field_responseName_matches
        (relation := SelectionEqualUpToReorderingWithCoercion schema
          variableValues variableValues parentType)
        left right
        (selectionSetNormal_allFields_of_object hleftNormal hobject)
        (selectionSetNormal_allFields_of_object hrightNormal hobject)
        (selectionSetNormal_responseNamesNodup hleftNormal)
        (selectionSetNormal_responseNamesNodup hrightNormal) (by
          intro responseName fieldName arguments directives childSelectionSet
            hleftMem
          by_cases hrightName :
              responseName ∈ right.filterMap Selection.responseName?
          · rcases selectionSetNormal_field_mem_of_object_responseName_mem
                hrightNormal hobject hrightName with
              ⟨rightFieldName, rightArguments, rightDirectives,
                rightChildSelectionSet, hrightMem⟩
            have hfieldName : fieldName = rightFieldName := by
              by_cases hsame : fieldName = rightFieldName
              · exact hsame
              · exact False.elim
                  (hnoDiff
                    (NormalSelectionSetResolverDiff.objectFieldName hobject
                      hleftMem hrightMem hsame))
            subst rightFieldName
            rcases selectionSetNormal_field_child_of_mem_with_returnType
                hleftNormal hleftMem with
              ⟨returnType, hreturnType, hleftChildNormal⟩
            cases hlookup : schema.lookupField parentType fieldName with
            | none =>
                simp [Schema.fieldReturnType?, hlookup] at hreturnType
            | some fieldDefinition =>
                have hnamedType : fieldDefinition.outputType.namedType = returnType := by
                  simpa [Schema.fieldReturnType?, hlookup] using hreturnType
                have hcoercion :
                    Execution.ArgumentCoercionResult.equivalent
                      (Execution.coerceArgumentValues schema variableValues
                        fieldDefinition.arguments arguments)
                      (Execution.coerceArgumentValues schema variableValues
                        fieldDefinition.arguments rightArguments) := by
                  exact Classical.byContradiction fun hne =>
                    hnoDiff
                      (NormalSelectionSetResolverDiff.objectArguments
                        fieldDefinition hobject hleftMem hrightMem hlookup hne)
                have hrightChildNormal :
                    selectionSetNormal schema fieldDefinition.outputType.namedType
                      rightChildSelectionSet := by
                  rcases selectionSetNormal_field_child_of_mem_with_returnType
                      hrightNormal hrightMem with
                    ⟨rightReturnType, hrightReturnType, hnormal⟩
                  have hsameReturn : rightReturnType = returnType := by
                    rw [hreturnType] at hrightReturnType
                    exact (Option.some.inj hrightReturnType).symm
                  simpa [hnamedType, hsameReturn] using hnormal
                have hchildEq :
                    (Execution.coerceArgumentValues schema variableValues
                        fieldDefinition.arguments arguments).isSuccess = true
                    -> SelectionSetEqualUpToReorderingWithCoercion schema
                        variableValues variableValues
                        fieldDefinition.outputType.namedType childSelectionSet
                        rightChildSelectionSet := by
                  intro hsuccess
                  have hchildNoDiff :
                      ¬ NormalSelectionSetResolverDiff schema variableValues
                        fieldDefinition.outputType.namedType childSelectionSet
                          rightChildSelectionSet := by
                    intro hchildDiff
                    exact hnoDiff
                      (NormalSelectionSetResolverDiff.objectChild
                        fieldDefinition hobject hleftMem hrightMem hlookup hcoercion
                        hsuccess hchildDiff)
                  exact selectionSetEqualUpToReordering_of_no_diff schema
                    variableValues fieldDefinition.outputType.namedType
                    childSelectionSet rightChildSelectionSet
                    (selectionSetDirectiveFree_field_child_of_mem hleftFree hleftMem)
                    (selectionSetDirectiveFree_field_child_of_mem hrightFree hrightMem)
                    (by simpa [hnamedType] using hleftChildNormal)
                    hrightChildNormal hchildNoDiff
                have hleftDirectives : directives = [] :=
                  selectionSetDirectiveFree_field_directives_nil_of_mem hleftFree
                    hleftMem
                have hrightDirectivesNil : rightDirectives = [] :=
                  selectionSetDirectiveFree_field_directives_nil_of_mem hrightFree
                    hrightMem
                subst directives
                subst rightDirectives
                exact ⟨fieldName, rightArguments, [], rightChildSelectionSet,
                  hrightMem,
                  SelectionEqualUpToReorderingWithCoercion.field parentType
                    responseName fieldName [] fieldDefinition hlookup hcoercion
                    hchildEq⟩
          · exact False.elim
              (hnoDiff
                (NormalSelectionSetResolverDiff.objectLeftResponseName hobject
                  hleftMem hrightName))) (by
          intro responseName hrightName
          by_cases hleftName :
              responseName ∈ left.filterMap Selection.responseName?
          · exact hleftName
          · rcases selectionSetNormal_field_mem_of_object_responseName_mem
                hrightNormal hobject hrightName with
              ⟨fieldName, arguments, directives, childSelectionSet, hrightMem⟩
            exact False.elim
              (hnoDiff
                (NormalSelectionSetResolverDiff.objectRightResponseName hobject
                  hrightMem hleftName))) with
      ⟨pairs, hleftPerm, hrightPerm, hrelations⟩
    exact SelectionSetEqualUpToReorderingWithCoercion.paired pairs hleftPerm
      hrightPerm hrelations
  · have habstract : objectTypeNameBool schema parentType = false := by
      cases h : objectTypeNameBool schema parentType <;> simp_all
    rcases selectionSetPairedBy_of_inlineFragment_typeCondition_matches
        (relation := SelectionEqualUpToReorderingWithCoercion schema
          variableValues variableValues parentType)
        left right
        (selectionSetNormal_inlineFragmentTypeConditionsNodup hleftNormal)
        (selectionSetNormal_inlineFragmentTypeConditionsNodup hrightNormal) (by
          intro selection hmem
          have hinline :=
            selectionSetNormal_allInlineFragments_of_abstract hleftNormal
              habstract selection hmem
          cases selection with
          | field => simp [Selection.isInlineFragment] at hinline
          | inlineFragment maybeTypeCondition directives childSelectionSet =>
              cases maybeTypeCondition with
              | none =>
                  rcases hleftNormal with ⟨hground, _⟩
                  unfold selectionSetGroundTyped at hground
                  have hselectionGround := hground.2
                    (Selection.inlineFragment none directives childSelectionSet) hmem
                  simp [selectionGroundTyped] at hselectionGround
              | some typeCondition =>
                  exact ⟨typeCondition, directives, childSelectionSet, rfl⟩) (by
          intro selection hmem
          have hinline :=
            selectionSetNormal_allInlineFragments_of_abstract hrightNormal
              habstract selection hmem
          cases selection with
          | field => simp [Selection.isInlineFragment] at hinline
          | inlineFragment maybeTypeCondition directives childSelectionSet =>
              cases maybeTypeCondition with
              | none =>
                  rcases hrightNormal with ⟨hground, _⟩
                  unfold selectionSetGroundTyped at hground
                  have hselectionGround := hground.2
                    (Selection.inlineFragment none directives childSelectionSet) hmem
                  simp [selectionGroundTyped] at hselectionGround
              | some typeCondition =>
                  exact ⟨typeCondition, directives, childSelectionSet, rfl⟩) (by
          intro typeCondition directives childSelectionSet hleftMem
          by_cases hrightType :
              typeCondition ∈ right.filterMap inlineFragmentTypeCondition?
          · rcases
                selectionSetNormal_inlineFragment_mem_of_abstract_typeCondition_mem
                  hrightNormal habstract hrightType with
              ⟨rightDirectives, rightChildSelectionSet, hrightMem⟩
            rcases selectionSetNormal_inlineFragment_child_of_mem hleftNormal
                hleftMem with ⟨_, hleftChildNormal⟩
            rcases selectionSetNormal_inlineFragment_child_of_mem hrightNormal
                hrightMem with ⟨_, hrightChildNormal⟩
            have hchildNoDiff :
                ¬ NormalSelectionSetResolverDiff schema variableValues
                  typeCondition childSelectionSet rightChildSelectionSet := by
              intro hchildDiff
              exact hnoDiff
                (NormalSelectionSetResolverDiff.abstractChild habstract
                  hleftMem hrightMem hchildDiff)
            have hchildEq :=
              selectionSetEqualUpToReordering_of_no_diff schema
                variableValues typeCondition childSelectionSet
                rightChildSelectionSet
                (selectionSetDirectiveFree_inlineFragment_child_of_mem hleftFree
                  hleftMem)
                (selectionSetDirectiveFree_inlineFragment_child_of_mem hrightFree
                  hrightMem)
                hleftChildNormal hrightChildNormal hchildNoDiff
            have hleftDirectives : directives = [] :=
              selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
                hleftFree hleftMem
            have hrightDirectivesNil : rightDirectives = [] :=
              selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
                hrightFree hrightMem
            subst directives
            subst rightDirectives
            exact ⟨[], rightChildSelectionSet, hrightMem,
              SelectionEqualUpToReorderingWithCoercion.inlineFragment
                parentType (some typeCondition) [] hchildEq⟩
          · exact False.elim
              (hnoDiff
                (NormalSelectionSetResolverDiff.abstractLeftTypeCondition
                  habstract hleftMem hrightType))) (by
          intro typeCondition hrightType
          by_cases hleftType :
              typeCondition ∈ left.filterMap inlineFragmentTypeCondition?
          · exact hleftType
          · rcases
                selectionSetNormal_inlineFragment_mem_of_abstract_typeCondition_mem
                  hrightNormal habstract hrightType with
              ⟨directives, childSelectionSet, hrightMem⟩
            exact False.elim
              (hnoDiff
                (NormalSelectionSetResolverDiff.abstractRightTypeCondition
                  habstract hrightMem hleftType))) with
      ⟨pairs, hleftPerm, hrightPerm, hrelations⟩
    exact SelectionSetEqualUpToReorderingWithCoercion.paired pairs hleftPerm
      hrightPerm hrelations
termination_by _parentType left right =>
  SelectionSet.size left + SelectionSet.size right
decreasing_by
  all_goals
    first
    | have hleftLt :=
        selectionSet_size_field_child_lt_of_mem (selectionSet := left) hleftMem
      have hrightLt :=
        selectionSet_size_field_child_lt_of_mem (selectionSet := right) hrightMem
      omega
    | have hleftLt :=
        selectionSet_size_inlineFragment_child_lt_of_mem
          (selectionSet := left) hleftMem
      have hrightLt :=
        selectionSet_size_inlineFragment_child_lt_of_mem
          (selectionSet := right) hrightMem
      omega

theorem normalSelectionSetDiff_of_not_equal
    {schema : Schema} {variableValues : Execution.VariableValues}
    {parentType : Name} {left right : List Selection}
    : selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> ¬ SelectionSetEqualUpToReorderingWithCoercion schema variableValues
            variableValues parentType left right
      -> NormalSelectionSetResolverDiff schema variableValues parentType left right := by
  intro hleftFree hrightFree hleftNormal hrightNormal hnotEqual
  exact Classical.byContradiction fun hnoDiff =>
    hnotEqual
      (selectionSetEqualUpToReordering_of_no_diff schema
        variableValues parentType left right hleftFree hrightFree hleftNormal
        hrightNormal hnoDiff)

end GroundTypeNormalization

end NormalForm

end GraphQL
