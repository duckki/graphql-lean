import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.FilterReadiness
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity

/-!
Directive and wrapper validity facts for complete-normalization branches.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem directivesValid_nil
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    : Validation.directivesValid schema variableDefinitions [] := by
  simp [Validation.directivesValid]

theorem directiveIfArgumentValid_of_inputValueBooleanVariables
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (varName : BoolVar)
    : ∀ value,
        varName ∈ inputValueBooleanVariables value
        -> Validation.directiveIfArgumentValid schema variableDefinitions value
        -> Validation.directiveIfArgumentValid schema variableDefinitions
            (.variable varName)
  | .null, hmem, _hvalid => by
      simp [inputValueBooleanVariables] at hmem
  | .int _value, hmem, _hvalid => by
      simp [inputValueBooleanVariables] at hmem
  | .float _value, hmem, _hvalid => by
      simp [inputValueBooleanVariables] at hmem
  | .string _value, hmem, _hvalid => by
      simp [inputValueBooleanVariables] at hmem
  | .boolean _value, hmem, _hvalid => by
      simp [inputValueBooleanVariables] at hmem
  | .enum _value, hmem, _hvalid => by
      simp [inputValueBooleanVariables] at hmem
  | .variable name, hmem, hvalid => by
      simp [inputValueBooleanVariables] at hmem
      subst name
      exact hvalid
  | .list _values, _hmem, hvalid => by
      simp [Validation.directiveIfArgumentValid] at hvalid
  | .object _fields, _hmem, hvalid => by
      simp [Validation.directiveIfArgumentValid] at hvalid

theorem directiveIfArgumentValid_of_directiveBooleanVariables
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (varName : BoolVar)
    : ∀ directive,
        varName ∈ directiveBooleanVariables directive
        -> Validation.directiveValid schema variableDefinitions directive
        -> Validation.directiveIfArgumentValid schema variableDefinitions
            (.variable varName)
  | .skip ifArgument, hmem, hvalid => by
      exact directiveIfArgumentValid_of_inputValueBooleanVariables
        schema variableDefinitions varName ifArgument
        (by simpa [directiveBooleanVariables] using hmem)
        (by simpa [Validation.directiveValid] using hvalid)
  | .include ifArgument, hmem, hvalid => by
      exact directiveIfArgumentValid_of_inputValueBooleanVariables
        schema variableDefinitions varName ifArgument
        (by simpa [directiveBooleanVariables] using hmem)
        (by simpa [Validation.directiveValid] using hvalid)

theorem directiveIfArgumentValid_of_directivesBooleanVariables
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (varName : BoolVar)
    : ∀ directives,
        varName ∈ directivesBooleanVariables directives
        -> Validation.directivesValid schema variableDefinitions directives
        -> Validation.directiveIfArgumentValid schema variableDefinitions
            (.variable varName)
  | [], hmem, _hvalid => by
      simp [directivesBooleanVariables] at hmem
  | directive :: rest, hmem, hvalid => by
      rcases hvalid with ⟨hnodup, hall⟩
      have hdirectiveValid :
          Validation.directiveValid schema variableDefinitions directive :=
        hall directive (by simp)
      have hrestValid :
          Validation.directivesValid schema variableDefinitions rest := by
        constructor
        · simpa [Validation.directiveName] using
            (List.nodup_cons.mp hnodup).2
        · intro candidate hcandidate
          exact hall candidate (by simp [hcandidate])
      simp [directivesBooleanVariables] at hmem
      rcases hmem with hdirective | hrest
      · exact directiveIfArgumentValid_of_directiveBooleanVariables
          schema variableDefinitions varName directive hdirective
          hdirectiveValid
      · exact directiveIfArgumentValid_of_directivesBooleanVariables
          schema variableDefinitions varName rest hrest hrestValid

mutual
  theorem directiveIfArgumentValid_of_selectionBooleanVariables
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (varName : BoolVar)
      : ∀ parentType selection,
          varName ∈ selectionBooleanVariables selection
          -> Validation.selectionValid schema variableDefinitions parentType selection
          -> Validation.directiveIfArgumentValid schema variableDefinitions
              (.variable varName)
    | parentType,
      .field responseName fieldName arguments directives selectionSet,
      hmem, hvalid => by
        simp [selectionBooleanVariables] at hmem
        rcases hmem with hdirectives | hchild
        · exact directiveIfArgumentValid_of_directivesBooleanVariables
            schema variableDefinitions varName directives hdirectives
            (Validation.selectionValid_field_directivesValid hvalid)
        · rcases Validation.selectionValid_field_lookup hvalid with
            ⟨fieldDefinition, _hlookup, _harguments, hchildValid⟩
          have hparts :
              fieldDefinition.outputType.isOutputType schema
                ∧ ((schema.isLeafType
                      fieldDefinition.outputType.namedType
                        ∧ selectionSet = [])
                  ∨ (schema.isCompositeType
                      fieldDefinition.outputType.namedType
                    ∧ selectionSet ≠ []
                    ∧ Validation.selectionSetValid schema
                      variableDefinitions
                      fieldDefinition.outputType.namedType selectionSet)) := by
            simpa [Validation.fieldSelectionSetValid] using hchildValid
          rcases hparts.2 with hleaf | hcomposite
          · rw [hleaf.2] at hchild
            simp [selectionSetBooleanVariables] at hchild
          · exact directiveIfArgumentValid_of_selectionSetBooleanVariables
              schema variableDefinitions varName
              fieldDefinition.outputType.namedType selectionSet hchild
              hcomposite.2.2
    | parentType, .inlineFragment none directives selectionSet,
      hmem, hvalid => by
        simp [selectionBooleanVariables] at hmem
        rcases hmem with hdirectives | hchild
        · simp [Validation.selectionValid] at hvalid
          exact directiveIfArgumentValid_of_directivesBooleanVariables
            schema variableDefinitions varName directives hdirectives
            hvalid.1
        · exact directiveIfArgumentValid_of_selectionSetBooleanVariables
            schema variableDefinitions varName parentType selectionSet hchild
            (Validation.selectionValid_inlineFragment_none_selectionSetValid
              hvalid)
    | parentType,
      .inlineFragment (some typeCondition) directives selectionSet,
      hmem, hvalid => by
        simp [selectionBooleanVariables] at hmem
        rcases hmem with hdirectives | hchild
        · simp [Validation.selectionValid] at hvalid
          exact directiveIfArgumentValid_of_directivesBooleanVariables
            schema variableDefinitions varName directives hdirectives
            hvalid.1
        · exact directiveIfArgumentValid_of_selectionSetBooleanVariables
            schema variableDefinitions varName typeCondition selectionSet
            hchild
            (Validation.selectionValid_inlineFragment_some_selectionSetValid
              hvalid)

  theorem directiveIfArgumentValid_of_selectionSetBooleanVariables
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (varName : BoolVar)
      : ∀ parentType selectionSet,
          varName ∈ selectionSetBooleanVariables selectionSet
          -> Validation.selectionSetValid schema variableDefinitions parentType
              selectionSet
          -> Validation.directiveIfArgumentValid schema variableDefinitions
              (.variable varName)
    | _parentType, [], hmem, _hvalid => by
        simp [selectionSetBooleanVariables] at hmem
    | parentType, selection :: rest, hmem, hvalid => by
        simp [selectionSetBooleanVariables] at hmem
        rcases hmem with hselection | hrest
        · have hhead :
              Validation.selectionValid schema variableDefinitions
                parentType selection := by
            unfold Validation.selectionSetValid at hvalid
            exact hvalid selection (by simp)
          exact directiveIfArgumentValid_of_selectionBooleanVariables
            schema variableDefinitions varName parentType selection
            hselection hhead
        · have htail :
              Validation.selectionSetValid schema variableDefinitions
                parentType rest :=
            Validation.selectionSetValid_tail hvalid
          exact directiveIfArgumentValid_of_selectionSetBooleanVariables
            schema variableDefinitions varName parentType rest hrest htail
end

theorem directiveForBit_directivesValid_of_operationBoolVars
    (schema : Schema) (operation : Operation)
    {varName : BoolVar} {value : Bool}
    : Validation.operationDefinitionValid schema operation
      -> varName ∈ operationBoolVars operation
      -> Validation.directivesValid schema operation.variableDefinitions
          [directiveForBit varName value] := by
  intro hvalid hmem
  have hsourceMem :
      varName ∈ selectionSetBooleanVariables operation.selectionSet :=
    (mem_dedupBoolVars_iff varName
      (selectionSetBooleanVariables operation.selectionSet)).1 hmem
  have hif :
      Validation.directiveIfArgumentValid schema operation.variableDefinitions
        (.variable varName) :=
    directiveIfArgumentValid_of_selectionSetBooleanVariables schema
      operation.variableDefinitions varName operation.rootType
      operation.selectionSet hsourceMem
      (Validation.operationDefinitionValid_selectionSetValid hvalid)
  constructor
  · cases value <;> simp [directiveForBit, Validation.directiveName]
  · intro directive hdirective
    simp at hdirective
    subst directive
    cases value <;>
      simpa [directiveForBit, Validation.directiveValid] using hif

theorem wrapWithBoolCase_ne_nil
    : ∀ boolCase selectionSet,
        selectionSet ≠ [] -> wrapWithBoolCase boolCase selectionSet ≠ []
  | [], selectionSet, hne => by
      simpa [wrapWithBoolCase] using hne
  | (_varName, _value) :: rest, selectionSet, _hne => by
      simp [wrapWithBoolCase]

theorem wrapWithBoolCase_selectionSetValid
    (schema : Schema) (operation : Operation)
    (parentType : Name)
    : ∀ boolCase selectionSet,
        Validation.operationDefinitionValid schema operation
        -> (∀ varName,
              varName ∈ boolCase.map Prod.fst -> varName ∈ operationBoolVars operation)
        -> selectionSet ≠ []
        -> Validation.selectionSetValid schema operation.variableDefinitions
            parentType selectionSet
        -> Validation.selectionSetValid schema operation.variableDefinitions
            parentType (wrapWithBoolCase boolCase selectionSet)
  | [], selectionSet, _hoperation, _hvars, _hne, hvalid => by
      simpa [wrapWithBoolCase] using hvalid
  | (varName, value) :: rest, selectionSet, hoperation, hvars, hne,
    hvalid => by
      have hchildValid :
          Validation.selectionSetValid schema operation.variableDefinitions
            parentType (wrapWithBoolCase rest selectionSet) :=
        wrapWithBoolCase_selectionSetValid schema operation parentType rest
          selectionSet hoperation
          (by
            intro candidate hcandidate
            exact hvars candidate (by simp [hcandidate]))
          hne hvalid
      have hchildNonempty :
          wrapWithBoolCase rest selectionSet ≠ [] :=
        wrapWithBoolCase_ne_nil rest selectionSet hne
      unfold Validation.selectionSetValid
      intro selection hselection
      simp [wrapWithBoolCase] at hselection
      subst selection
      simp [Validation.selectionValid]
      exact ⟨
        directiveForBit_directivesValid_of_operationBoolVars
          schema operation hoperation (hvars varName (by simp)),
        hchildNonempty,
        hchildValid⟩

theorem wrapWithBoolCase_selectionSetValidInPossibleTypes
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (hparentObject : schema.objectType parentType)
    : ∀ boolCase selectionSet,
        Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType selectionSet
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType
            (wrapWithBoolCase boolCase selectionSet)
  | [], selectionSet, himplementation => by
      simpa [wrapWithBoolCase] using himplementation
  | (_varName, _value) :: rest, selectionSet, himplementation => by
      have hchild :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType
            (wrapWithBoolCase rest selectionSet) :=
        wrapWithBoolCase_selectionSetValidInPossibleTypes schema
          variableDefinitions parentType hparentObject rest selectionSet
          himplementation
      simp [wrapWithBoolCase,
        Validation.selectionSetValidInPossibleTypes,
        Validation.selectionValidInPossibleTypes]
      intro objectType hpossible
      have hinclude :
          schema.typeIncludesObjectBool parentType objectType = true :=
        List.contains_iff_mem.mpr hpossible
      have hobjectEq : objectType = parentType :=
        object_typeIncludesObjectBool_eq_self schema hparentObject hinclude
      simpa [hobjectEq] using hchild

theorem collectFields_wrapWithBoolCase (schema : Schema) (parentType : Name)
    : ∀ boolCase selectionSet,
        FieldMerge.collectFields schema parentType
          (wrapWithBoolCase boolCase selectionSet)
        = FieldMerge.collectFields schema parentType selectionSet
  | [], selectionSet => by
      simp [wrapWithBoolCase]
  | (_varName, _value) :: rest, selectionSet => by
      simp [wrapWithBoolCase, FieldMerge.collectFields,
        collectFields_wrapWithBoolCase schema parentType rest selectionSet]

theorem fieldsInSetCanMerge_wrapWithBoolCase (schema : Schema) (parentType : Name)
    : ∀ boolCase selectionSet,
        FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType
            (wrapWithBoolCase boolCase selectionSet)
  | boolCase, selectionSet, hmerge => by
      unfold FieldMerge.fieldsInSetCanMerge at hmerge ⊢
      cases hmerge with
      | intro _ _ hfields =>
          refine FieldMerge.FieldsInSetCanMerge.intro parentType
            (wrapWithBoolCase boolCase selectionSet) ?_
          dsimp
          intro left hleft right hright hresponse
          rw [collectFields_wrapWithBoolCase] at hleft hright
          exact hfields left hleft right hright hresponse

theorem fieldsInSetCanMerge_wrapWithBoolCase_pair
    (schema : Schema) (parentType : Name)
    (leftCase rightCase : BoolCase)
    (leftSet rightSet : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (wrapWithBoolCase leftCase leftSet ++ wrapWithBoolCase rightCase rightSet) := by
  intro hmerge
  unfold FieldMerge.fieldsInSetCanMerge at hmerge ⊢
  cases hmerge with
  | intro _ _ hfields =>
      refine FieldMerge.FieldsInSetCanMerge.intro parentType
        (wrapWithBoolCase leftCase leftSet
          ++ wrapWithBoolCase rightCase rightSet) ?_
      dsimp
      intro left hleft right hright hresponse
      rw [FieldMerge.collectFields_append] at hleft hright
      rcases List.mem_append.mp hleft with hleftMem | hleftMem
      · rw [collectFields_wrapWithBoolCase] at hleftMem
        rcases List.mem_append.mp hright with hrightMem | hrightMem
        · rw [collectFields_wrapWithBoolCase] at hrightMem
          exact hfields left
            (by
              rw [FieldMerge.collectFields_append]
              exact List.mem_append_left
                (FieldMerge.collectFields schema parentType rightSet)
                hleftMem)
            right
            (by
              rw [FieldMerge.collectFields_append]
              exact List.mem_append_left
                (FieldMerge.collectFields schema parentType rightSet)
                hrightMem)
            hresponse
        · rw [collectFields_wrapWithBoolCase] at hrightMem
          exact hfields left
            (by
              rw [FieldMerge.collectFields_append]
              exact List.mem_append_left
                (FieldMerge.collectFields schema parentType rightSet)
                hleftMem)
            right
            (by
              rw [FieldMerge.collectFields_append]
              exact List.mem_append_right
                (FieldMerge.collectFields schema parentType leftSet)
                hrightMem)
            hresponse
      · rw [collectFields_wrapWithBoolCase] at hleftMem
        rcases List.mem_append.mp hright with hrightMem | hrightMem
        · rw [collectFields_wrapWithBoolCase] at hrightMem
          exact hfields left
            (by
              rw [FieldMerge.collectFields_append]
              exact List.mem_append_right
                (FieldMerge.collectFields schema parentType leftSet)
                hleftMem)
            right
            (by
              rw [FieldMerge.collectFields_append]
              exact List.mem_append_left
                (FieldMerge.collectFields schema parentType rightSet)
                hrightMem)
            hresponse
        · rw [collectFields_wrapWithBoolCase] at hrightMem
          exact hfields left
            (by
              rw [FieldMerge.collectFields_append]
              exact List.mem_append_right
                (FieldMerge.collectFields schema parentType leftSet)
                hleftMem)
            right
            (by
              rw [FieldMerge.collectFields_append]
              exact List.mem_append_right
                (FieldMerge.collectFields schema parentType leftSet)
                hrightMem)
            hresponse

theorem fieldsInSetCanMerge_append_of_pairwise
    (schema : Schema) (parentType : Name)
    (leftSet rightSet : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema parentType leftSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType rightSet
      -> (∀ leftField,
            leftField ∈ FieldMerge.collectFields schema parentType leftSet
            -> ∀ rightField,
                rightField ∈ FieldMerge.collectFields schema parentType rightSet
                -> leftField.responseName = rightField.responseName
                -> FieldMerge.fieldsForNameCanMerge schema leftField rightField)
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet) := by
  intro hleftMerge hrightMerge hcross
  unfold FieldMerge.fieldsInSetCanMerge at hleftMerge hrightMerge ⊢
  cases hleftMerge with
  | intro _ _ hleftFields =>
      cases hrightMerge with
      | intro _ _ hrightFields =>
          refine FieldMerge.FieldsInSetCanMerge.intro parentType
            (leftSet ++ rightSet) ?_
          dsimp
          intro left hleft right hright hresponse
          rw [FieldMerge.collectFields_append] at hleft hright
          rcases List.mem_append.mp hleft with hleftMem | hleftMem
          · rcases List.mem_append.mp hright with hrightMem | hrightMem
            · exact hleftFields left hleftMem right hrightMem hresponse
            · exact hcross left hleftMem right hrightMem hresponse
          · rcases List.mem_append.mp hright with hrightMem | hrightMem
            · exact FieldMerge.fieldsForNameCanMerge_symm
                (hcross right hrightMem left hleftMem hresponse.symm)
            · exact hrightFields left hleftMem right hrightMem hresponse

end CompleteNormalization

end NormalForm

end GraphQL
