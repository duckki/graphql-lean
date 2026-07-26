import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationNormality
import Proofs.GraphQL.Theories.NormalForm.Shared.SemanticReadiness

/-!
Semantic-readiness facts for Boolean case filtering.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem filterSelectionSetBoolCase_cons
    (boolCase : BoolCase) (selection : Selection) (rest : List Selection)
    : filterSelectionSetBoolCase boolCase (selection :: rest)
      = filterSelectionSetBoolCase boolCase [selection]
        ++ filterSelectionSetBoolCase boolCase rest := by
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow]
        | cons child children =>
            cases hchild :
                filterSelectionSetBoolCase boolCase (child :: children) <;>
              simp [filterSelectionSetBoolCase, hallow, hchild]
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse]
  | inlineFragment typeCondition directives selectionSet =>
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases hchild :
          filterSelectionSetBoolCase boolCase selectionSet <;>
          simp [filterSelectionSetBoolCase, hallow, hchild]
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse]

theorem filterSelectionSetBoolCase_append (boolCase : BoolCase)
    : ∀ left right,
        filterSelectionSetBoolCase boolCase (left ++ right)
        = filterSelectionSetBoolCase boolCase left
          ++ filterSelectionSetBoolCase boolCase right
  | [], right => by
      simp [filterSelectionSetBoolCase]
  | selection :: rest, right => by
      calc
        filterSelectionSetBoolCase boolCase
            ((selection :: rest) ++ right)
            =
          filterSelectionSetBoolCase boolCase [selection]
            ++ filterSelectionSetBoolCase boolCase (rest ++ right) := by
              simpa [List.cons_append] using
                filterSelectionSetBoolCase_cons boolCase selection
                  (rest ++ right)
        _ =
          filterSelectionSetBoolCase boolCase [selection]
            ++ (filterSelectionSetBoolCase boolCase rest
              ++ filterSelectionSetBoolCase boolCase right) := by
              rw [filterSelectionSetBoolCase_append boolCase rest right]
        _ =
          (filterSelectionSetBoolCase boolCase [selection]
            ++ filterSelectionSetBoolCase boolCase rest)
              ++ filterSelectionSetBoolCase boolCase right := by
              simp [List.append_assoc]
        _ =
          filterSelectionSetBoolCase boolCase (selection :: rest)
              ++ filterSelectionSetBoolCase boolCase right := by
              rw [filterSelectionSetBoolCase_cons boolCase selection rest]

structure BoolFilteredScopedFieldSourceForMerge
    (schema : Schema) (boolCase : BoolCase)
    (source filtered : FieldMerge.ScopedField)
    : Prop where
  parentType : filtered.parentType = source.parentType
  responseName : filtered.responseName = source.responseName
  fieldName : filtered.fieldName = source.fieldName
  arguments : filtered.arguments = source.arguments
  outputType : filtered.outputType = source.outputType
  selectionSet
    : filtered.selectionSet = filterSelectionSetBoolCase boolCase source.selectionSet

theorem collectFields_filterSelectionSetBoolCase_mem_source_forMerge
    (schema : Schema) (boolCase : BoolCase)
    : ∀ parentType selectionSet filteredField,
        filteredField
          ∈ FieldMerge.collectFields schema parentType
              (filterSelectionSetBoolCase boolCase selectionSet)
        -> ∃ sourceField,
            sourceField ∈ FieldMerge.collectFields schema parentType selectionSet
            ∧ BoolFilteredScopedFieldSourceForMerge schema boolCase sourceField
                filteredField
  | _parentType, [], _filteredField, hfield => by
      simp [filterSelectionSetBoolCase, FieldMerge.collectFields] at hfield
  | parentType,
    Selection.field responseName fieldName arguments directives selectionSet
      :: rest,
    filteredField, hfield => by
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow,
              FieldMerge.collectFields] at hfield
            cases hlookup : schema.lookupField parentType fieldName with
            | none =>
                simp [hlookup] at hfield
                rcases
                  collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                    schema boolCase parentType rest filteredField hfield with
                  ⟨sourceField, hsourceMem, hsource⟩
                exact ⟨sourceField, by
                  simp [FieldMerge.collectFields, hlookup, hsourceMem],
                  hsource⟩
            | some fieldDefinition =>
                simp [hlookup] at hfield
                rcases hfield with hhead | htail
                · subst filteredField
                  refine ⟨{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    outputType := fieldDefinition.outputType,
                    selectionSet := []
                  }, ?_, ?_⟩
                  · simp [FieldMerge.collectFields, hlookup]
                  · exact ⟨rfl, rfl, rfl, rfl, rfl, by
                      simp [filterSelectionSetBoolCase]⟩
                · rcases
                    collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                      schema boolCase parentType rest filteredField htail with
                    ⟨sourceField, hsourceMem, hsource⟩
                  exact ⟨sourceField, by
                    simp [FieldMerge.collectFields, hlookup, hsourceMem],
                    hsource⟩
        | cons child children =>
            cases hchild :
                filterSelectionSetBoolCase boolCase
                  (child :: children) with
            | nil =>
                cases hlookup : schema.lookupField parentType fieldName with
                | none =>
                    simp [filterSelectionSetBoolCase, hallow, hchild,
                      FieldMerge.collectFields, hlookup] at hfield
                    rcases
                      collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                        schema boolCase parentType rest filteredField hfield with
                      ⟨sourceField, hsourceMem, hsource⟩
                    exact ⟨sourceField, by
                      simp [FieldMerge.collectFields, hlookup, hsourceMem],
                      hsource⟩
                | some fieldDefinition =>
                    simp [filterSelectionSetBoolCase, hallow, hchild,
                      FieldMerge.collectFields, hlookup] at hfield
                    rcases hfield with hhead | htail
                    · subst filteredField
                      refine ⟨{
                        parentType := parentType,
                        responseName := responseName,
                        fieldName := fieldName,
                        arguments := arguments,
                        outputType := fieldDefinition.outputType,
                        selectionSet := child :: children
                      }, ?_, ?_⟩
                      · simp [FieldMerge.collectFields, hlookup]
                      · exact ⟨rfl, rfl, rfl, rfl, rfl, hchild.symm⟩
                    · rcases
                        collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                          schema boolCase parentType rest filteredField htail with
                        ⟨sourceField, hsourceMem, hsource⟩
                      exact ⟨sourceField, by
                        simp [FieldMerge.collectFields, hlookup, hsourceMem],
                        hsource⟩
            | cons filteredChild filteredChildren =>
                simp [filterSelectionSetBoolCase, hallow, hchild,
                  FieldMerge.collectFields] at hfield
                cases hlookup : schema.lookupField parentType fieldName with
                | none =>
                    simp [hlookup] at hfield
                    rcases
                      collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                        schema boolCase parentType rest filteredField hfield with
                      ⟨sourceField, hsourceMem, hsource⟩
                    exact ⟨sourceField, by
                      simp [FieldMerge.collectFields, hlookup, hsourceMem],
                      hsource⟩
                | some fieldDefinition =>
                    simp [hlookup] at hfield
                    rcases hfield with hhead | htail
                    · subst filteredField
                      refine ⟨{
                        parentType := parentType,
                        responseName := responseName,
                        fieldName := fieldName,
                        arguments := arguments,
                        outputType := fieldDefinition.outputType,
                        selectionSet := child :: children
                      }, ?_, ?_⟩
                      · simp [FieldMerge.collectFields, hlookup]
                      · exact ⟨rfl, rfl, rfl, rfl, rfl, hchild.symm⟩
                    · rcases
                        collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                          schema boolCase parentType rest filteredField htail with
                        ⟨sourceField, hsourceMem, hsource⟩
                      exact ⟨sourceField, by
                        simp [FieldMerge.collectFields, hlookup, hsourceMem],
                        hsource⟩
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse] at hfield
        rcases
          collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema
            boolCase parentType rest filteredField hfield with
          ⟨sourceField, hsourceMem, hsource⟩
        exact ⟨sourceField, by
          cases hlookup : schema.lookupField parentType fieldName
          <;> simp [FieldMerge.collectFields, hlookup, hsourceMem],
          hsource⟩
  | parentType,
    Selection.inlineFragment none directives selectionSet :: rest,
    filteredField, hfield => by
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases hchild :
          filterSelectionSetBoolCase boolCase selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow, hchild] at hfield
            rcases
              collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                schema boolCase parentType rest filteredField hfield with
              ⟨sourceField, hsourceMem, hsource⟩
            exact ⟨sourceField, by
              simp [FieldMerge.collectFields, hsourceMem], hsource⟩
        | cons filteredChild filteredChildren =>
            simp [filterSelectionSetBoolCase, hallow, hchild,
              FieldMerge.collectFields] at hfield
            rcases hfield with hchildField | htail
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                  schema boolCase parentType selectionSet filteredField
                  (by simpa [hchild] using hchildField) with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                  schema boolCase parentType rest filteredField htail with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse] at hfield
        rcases
          collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema
            boolCase parentType rest filteredField hfield with
          ⟨sourceField, hsourceMem, hsource⟩
        exact ⟨sourceField, by
          simp [FieldMerge.collectFields, hsourceMem], hsource⟩
  | parentType,
    Selection.inlineFragment (some typeCondition) directives selectionSet
      :: rest,
    filteredField, hfield => by
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases hchild :
          filterSelectionSetBoolCase boolCase selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow, hchild] at hfield
            rcases
              collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                schema boolCase parentType rest filteredField hfield with
              ⟨sourceField, hsourceMem, hsource⟩
            exact ⟨sourceField, by
              simp [FieldMerge.collectFields, hsourceMem], hsource⟩
        | cons filteredChild filteredChildren =>
            simp [filterSelectionSetBoolCase, hallow, hchild,
              FieldMerge.collectFields] at hfield
            rcases hfield with hchildField | htail
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                  schema boolCase typeCondition selectionSet filteredField
                  (by simpa [hchild] using hchildField) with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                  schema boolCase parentType rest filteredField htail with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse] at hfield
        rcases
          collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema
            boolCase parentType rest filteredField hfield with
          ⟨sourceField, hsourceMem, hsource⟩
        exact ⟨sourceField, by
          simp [FieldMerge.collectFields, hsourceMem], hsource⟩

theorem fieldsInSetCanMerge_filterSelectionSetBoolCase_forSemantics
    (schema : Schema) (boolCase : BoolCase)
    {parentType : Name} {selectionSet : List Selection}
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet) := by
  intro hmerge
  refine
    FieldMerge.FieldsInSetCanMerge.rec
      (motive_1 := fun parentType selectionSet _hmerge =>
        FieldMerge.fieldsInSetCanMerge schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet))
      (motive_2 := fun sourceLeft sourceRight _hmerge =>
        ∀ left right,
          BoolFilteredScopedFieldSourceForMerge schema boolCase sourceLeft left ->
          BoolFilteredScopedFieldSourceForMerge schema boolCase sourceRight right ->
          left.responseName = right.responseName ->
            FieldMerge.fieldsForNameCanMerge schema left right)
      ?setCase ?fieldCase hmerge
  · intro parentType selectionSet hfields ihfields
    unfold FieldMerge.fieldsInSetCanMerge
    refine FieldMerge.FieldsInSetCanMerge.intro parentType
      (filterSelectionSetBoolCase boolCase selectionSet) ?_
    dsimp
    intro left hleft right hright hresponse
    rcases
      collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema
        boolCase parentType selectionSet left hleft with
      ⟨sourceLeft, hsourceLeft, hleftSource⟩
    rcases
      collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema
        boolCase parentType selectionSet right hright with
      ⟨sourceRight, hsourceRight, hrightSource⟩
    have hsourceResponse :
        sourceLeft.responseName = sourceRight.responseName :=
      hleftSource.responseName.symm.trans
        (hresponse.trans hrightSource.responseName)
    exact ihfields sourceLeft hsourceLeft sourceRight hsourceRight
      hsourceResponse left right hleftSource hrightSource hresponse
  · intro sourceLeft sourceRight hshape hidentity hsubfields ihsubfields
      left right hleftSource hrightSource _hresponse
    refine FieldMerge.FieldsForNameCanMerge.intro left right ?_ ?_ ?_
    · simpa [hleftSource.outputType, hrightSource.outputType] using
        hshape
    · intro hparents
      have hsourceParents :
          sourceLeft.parentType = sourceRight.parentType
            ∨ ¬ schema.objectType sourceLeft.parentType
            ∨ ¬ schema.objectType sourceRight.parentType := by
        rcases hparents with hparentEq | hnotObject
        · exact Or.inl
            (hleftSource.parentType.symm.trans
              (hparentEq.trans hrightSource.parentType))
        · rcases hnotObject with hleftNotObject | hrightNotObject
          · exact Or.inr (Or.inl (by
              intro hsourceObject
              exact hleftNotObject
                (by simpa [hleftSource.parentType] using hsourceObject)))
          · exact Or.inr (Or.inr (by
              intro hsourceObject
              exact hrightNotObject
                (by simpa [hrightSource.parentType] using hsourceObject)))
      rcases hidentity hsourceParents with ⟨hfieldName, harguments⟩
      exact ⟨hleftSource.fieldName.trans
          (hfieldName.trans hrightSource.fieldName.symm),
        by
          simpa [hleftSource.arguments, hrightSource.arguments]
            using harguments⟩
    · intro hparents objectType
      have hsourceParents :
          sourceLeft.parentType = sourceRight.parentType
            ∨ ¬ schema.objectType sourceLeft.parentType
            ∨ ¬ schema.objectType sourceRight.parentType := by
        rcases hparents with hparentEq | hnotObject
        · exact Or.inl
            (hleftSource.parentType.symm.trans
              (hparentEq.trans hrightSource.parentType))
        · rcases hnotObject with hleftNotObject | hrightNotObject
          · exact Or.inr (Or.inl (by
              intro hsourceObject
              exact hleftNotObject
                (by simpa [hleftSource.parentType] using hsourceObject)))
          · exact Or.inr (Or.inr (by
              intro hsourceObject
              exact hrightNotObject
                (by simpa [hrightSource.parentType] using hsourceObject)))
      have hfilteredSubfields :
          FieldMerge.fieldsInSetCanMerge schema objectType
            (filterSelectionSetBoolCase boolCase
              (sourceLeft.selectionSet ++ sourceRight.selectionSet)) :=
        ihsubfields hsourceParents objectType
      rw [filterSelectionSetBoolCase_append] at hfilteredSubfields
      simpa [FieldMerge.fieldsInSetCanMerge, hleftSource.selectionSet,
        hrightSource.selectionSet]
        using hfilteredSubfields

mutual
  theorem selectionLookupValid_filterSelectionSetBoolCase
      (schema : Schema) (boolCase : BoolCase)
      : ∀ parentType sourceSelection filteredSelection,
          filteredSelection ∈ filterSelectionSetBoolCase boolCase [sourceSelection]
          -> selectionLookupValid schema parentType sourceSelection
          -> selectionLookupValid schema parentType filteredSelection
    | parentType,
      .field responseName fieldName arguments directives selectionSet,
      filteredSelection, hfiltered, hlookupValid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow] at hfiltered
              subst filteredSelection
              simpa [selectionLookupValid] using hlookupValid
          | cons child children =>
              cases hchild :
                  filterSelectionSetBoolCase boolCase (child :: children) with
              | nil =>
                  simp [filterSelectionSetBoolCase, hallow, hchild]
                    at hfiltered
                  subst filteredSelection
                  simpa [selectionLookupValid] using hlookupValid
              | cons filteredChild filteredChildren =>
                  simp [filterSelectionSetBoolCase, hallow, hchild]
                    at hfiltered
                  subst filteredSelection
                  simpa [selectionLookupValid] using hlookupValid
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment none directives selectionSet,
      filteredSelection, hfiltered, hlookupValid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchild :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
              subst filteredSelection
              have hsourceChild :
                  selectionSetLookupValid schema parentType selectionSet := by
                simpa [selectionLookupValid] using hlookupValid
              have hfilteredChild :
                  selectionSetLookupValid schema parentType
                    (filteredChild :: filteredChildren) := by
                simpa [hchild] using
                  selectionSetLookupValid_filterSelectionSetBoolCase schema
                    boolCase parentType selectionSet hsourceChild
              simpa [selectionLookupValid] using hfilteredChild
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment (some typeCondition) directives selectionSet,
      filteredSelection, hfiltered, hlookupValid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchild :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
              subst filteredSelection
              have hsourceChild :
                  selectionSetLookupValid schema typeCondition selectionSet := by
                simpa [selectionLookupValid] using hlookupValid
              have hfilteredChild :
                  selectionSetLookupValid schema typeCondition
                    (filteredChild :: filteredChildren) := by
                simpa [hchild] using
                  selectionSetLookupValid_filterSelectionSetBoolCase schema
                    boolCase typeCondition selectionSet hsourceChild
              simpa [selectionLookupValid] using hfilteredChild
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered

  theorem selectionSetLookupValid_filterSelectionSetBoolCase
      (schema : Schema) (boolCase : BoolCase)
      : ∀ parentType selectionSet,
          selectionSetLookupValid schema parentType selectionSet
          -> selectionSetLookupValid schema parentType
              (filterSelectionSetBoolCase boolCase selectionSet)
    | parentType, [], _hlookupValid => by
        simp [filterSelectionSetBoolCase, selectionSetLookupValid]
    | parentType, selection :: rest, hlookupValid => by
        have hhead :
            selectionLookupValid schema parentType selection :=
          selectionSetLookupValid_head hlookupValid
        have htail :
            selectionSetLookupValid schema parentType rest :=
          selectionSetLookupValid_tail hlookupValid
        have hheadFiltered :
            selectionSetLookupValid schema parentType
              (filterSelectionSetBoolCase boolCase [selection]) := by
          unfold selectionSetLookupValid
          intro candidate hcandidate
          exact selectionLookupValid_filterSelectionSetBoolCase schema
            boolCase parentType selection candidate hcandidate hhead
        have hrestFiltered :
            selectionSetLookupValid schema parentType
              (filterSelectionSetBoolCase boolCase rest) :=
          selectionSetLookupValid_filterSelectionSetBoolCase schema
            boolCase parentType rest htail
        rw [filterSelectionSetBoolCase_cons]
        exact selectionSetLookupValid_append hheadFiltered hrestFiltered
end

mutual
  theorem selectionSemanticsReady_filterSelectionSetBoolCase
      (schema : Schema) (boolCase : BoolCase)
      : ∀ parentType sourceSelection filteredSelection,
          filteredSelection ∈ filterSelectionSetBoolCase boolCase [sourceSelection]
          -> selectionSemanticsReady schema parentType sourceSelection
          -> selectionSemanticsReady schema parentType filteredSelection
    | parentType,
      .field responseName fieldName arguments directives selectionSet,
      filteredSelection, hfiltered, hready => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow] at hfiltered
              subst filteredSelection
              simpa [selectionSemanticsReady] using hready
          | cons child children =>
              cases hchild :
                  filterSelectionSetBoolCase boolCase (child :: children) with
              | nil =>
                  simp [filterSelectionSetBoolCase, hallow, hchild]
                    at hfiltered
                  subst filteredSelection
                  rcases (by
                    simpa [selectionSemanticsReady] using hready) with
                    ⟨fieldDefinition, hlookup, _hchildrenReady⟩
                  simp [selectionSemanticsReady]
                  exact ⟨fieldDefinition, hlookup, by
                    intro runtimeType _hincludes
                    exact selectionSetSemanticsReady_nil schema runtimeType⟩
              | cons filteredChild filteredChildren =>
                  simp [filterSelectionSetBoolCase, hallow, hchild]
                    at hfiltered
                  subst filteredSelection
                  rcases (by
                    simpa [selectionSemanticsReady] using hready) with
                    ⟨fieldDefinition, hlookup, hchildrenReady⟩
                  simp [selectionSemanticsReady]
                  refine ⟨fieldDefinition, hlookup, ?_⟩
                  intro runtimeType hincludes
                  have hsourceChildReady :
                      selectionSetSemanticsReady schema runtimeType
                        (child :: children) :=
                    hchildrenReady runtimeType hincludes
                  simpa [hchild] using
                    selectionSetSemanticsReady_filterSelectionSetBoolCase
                      schema boolCase runtimeType (child :: children)
                      hsourceChildReady
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment none directives selectionSet,
      filteredSelection, hfiltered, hready => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchild :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
              subst filteredSelection
              have hsourceChildReady :
                  selectionSetSemanticsReady schema parentType selectionSet := by
                simpa [selectionSemanticsReady] using hready
              have hfilteredChildReady :
                  selectionSetSemanticsReady schema parentType
                    (filteredChild :: filteredChildren) := by
                simpa [hchild] using
                  selectionSetSemanticsReady_filterSelectionSetBoolCase
                    schema boolCase parentType selectionSet hsourceChildReady
              simpa [selectionSemanticsReady] using hfilteredChildReady
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment (some typeCondition) directives selectionSet,
      filteredSelection, hfiltered, hready => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchild :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
              subst filteredSelection
              have hreadyParts :
                  selectionSetLookupValid schema typeCondition selectionSet
                    ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                      selectionSetSemanticsReady schema parentType
                        selectionSet) := by
                simpa [selectionSemanticsReady] using hready
              simp [selectionSemanticsReady]
              constructor
              · simpa [hchild] using
                  selectionSetLookupValid_filterSelectionSetBoolCase schema
                    boolCase typeCondition selectionSet hreadyParts.1
              · intro hoverlap
                have hsourceChildReady :
                    selectionSetSemanticsReady schema parentType selectionSet :=
                  hreadyParts.2 hoverlap
                simpa [hchild] using
                  selectionSetSemanticsReady_filterSelectionSetBoolCase
                    schema boolCase parentType selectionSet hsourceChildReady
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered

  theorem selectionSetSemanticsReady_filterSelectionSetBoolCase
      (schema : Schema) (boolCase : BoolCase)
      : ∀ parentType selectionSet,
          selectionSetSemanticsReady schema parentType selectionSet
          -> selectionSetSemanticsReady schema parentType
              (filterSelectionSetBoolCase boolCase selectionSet)
    | parentType, [], _hready => by
        simpa [filterSelectionSetBoolCase] using
          selectionSetSemanticsReady_nil schema parentType
    | parentType, selection :: rest, hready => by
        have hhead :
            selectionSemanticsReady schema parentType selection := by
          unfold selectionSetSemanticsReady at hready
          exact hready selection (by simp)
        have htailReady :
            selectionSetSemanticsReady schema parentType rest :=
          selectionSetSemanticsReady_tail hready
        have hheadFiltered :
            selectionSetSemanticsReady schema parentType
              (filterSelectionSetBoolCase boolCase [selection]) := by
          unfold selectionSetSemanticsReady
          intro candidate hcandidate
          exact selectionSemanticsReady_filterSelectionSetBoolCase schema
            boolCase parentType selection candidate hcandidate hhead
        have hrestFiltered :
            selectionSetSemanticsReady schema parentType
              (filterSelectionSetBoolCase boolCase rest) :=
          selectionSetSemanticsReady_filterSelectionSetBoolCase schema
            boolCase parentType rest htailReady
        rw [filterSelectionSetBoolCase_cons]
        exact selectionSetSemanticsReady_append hheadFiltered hrestFiltered
end

end CompleteNormalization

end NormalForm

end GraphQL
