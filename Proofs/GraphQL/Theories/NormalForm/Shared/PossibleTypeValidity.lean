import Proofs.GraphQL.Theories.NormalForm.Shared.RuntimeTypes

/-! Valid object-grounded selections are valid in every possible runtime object scope. -/

namespace GraphQL.NormalForm

theorem selectionSetValidInPossibleTypes_of_groundTyped
    {schema : Schema} {definitions : List VariableDefinition}
    {parentType : Name} {selections : List Selection}
    (hground : selectionSetGroundTyped schema parentType selections)
    (hvalid : Validation.selectionSetValid schema definitions parentType selections)
    {runtimeType : Name} (hpossible : runtimeType ∈ schema.getPossibleTypes parentType)
    : selectionSetValidInPossibleTypes schema definitions runtimeType selections := by
  cases selections with
  | nil => trivial
  | cons selection rest =>
      unfold selectionSetGroundTyped at hground
      unfold Validation.selectionSetValid at hvalid
      have hselection := hground.2 selection (by simp)
      have hselectionValid := hvalid selection (by simp)
      constructor
      · cases selection with
        | field responseName fieldName arguments directives children =>
            unfold selectionGroundTyped at hselection
            have hobject : objectTypeNameBool schema parentType = true := by
              cases hobject : objectTypeNameBool schema parentType with
              | true => rfl
              | false =>
                  have hfragment := hground.1
                  simp only [hobject, Bool.false_eq_true, ↓reduceIte] at hfragment
                  exact False.elim
                    (hfragment
                      (.field responseName fieldName arguments directives children)
                      (by simp))
            have hruntime : runtimeType = parentType :=
              object_typeIncludesObjectBool_eq_self schema
                (objectType_of_objectTypeNameBool_eq_true schema hobject)
                (by simpa [Schema.typeIncludesObjectBool] using hpossible)
            subst runtimeType
            refine ⟨hselectionValid, ?_⟩
            obtain ⟨field, hlookup, _, hchildrenValid⟩ :=
              Validation.selectionValid_field_lookup hselectionValid
            rw [hlookup]
            intro childType hchildPossible
            obtain ⟨returnType, hreturn, hchildrenGround⟩ := hselection
            have hreturnEq : returnType = field.outputType.namedType := by
              simpa [Schema.fieldReturnType?, hlookup] using hreturn.symm
            subst returnType
            exact selectionSetValidInPossibleTypes_of_groundTyped hchildrenGround
              (fieldSelectionSetValid_child_of_possibleType hchildrenValid hchildPossible)
              hchildPossible
        | inlineFragment condition directives children =>
            cases condition with
            | none => simp [selectionGroundTyped] at hselection
            | some condition =>
                unfold selectionGroundTyped at hselection
                intro _ objectType hobjectPossible
                exact selectionSetValidInPossibleTypes_of_groundTyped hselection.2
                  (Validation.selectionValid_inlineFragment_some_selectionSetValid hselectionValid)
                  hobjectPossible
      · apply selectionSetValidInPossibleTypes_of_groundTyped (parentType := parentType)
          (selections := rest) ?_ ?_ hpossible
        · unfold selectionSetGroundTyped
          constructor
          · by_cases hobject : objectTypeNameBool schema parentType = true
            · simp only [hobject] at hground ⊢
              exact fun child hmem => hground.1 child (by simp [hmem])
            · simp only [hobject] at hground ⊢
              exact fun child hmem => hground.1 child (by simp [hmem])
          · exact fun child hmem => hground.2 child (by simp [hmem])
        · unfold Validation.selectionSetValid
          exact fun child hmem => hvalid child (by simp [hmem])
termination_by sizeOf selections

end GraphQL.NormalForm
