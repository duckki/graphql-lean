import Proofs.GraphQL.Theories.NormalForm.Shared.RuntimeMergeSource

/-! Declared child lookup evidence for runtime-scoped selection-set coverage. -/

namespace GraphQL.TreeSummary

private theorem outputTypeSubtype_namedType {schema : Schema}
    {implementation expected : TypeRef}
    (hsubtype : schema.outputTypeSubtype implementation expected)
    : schema.isSubType implementation.namedType expected.namedType := by
  induction implementation generalizing expected with
  | named name =>
      cases expected <;> simp_all [Schema.outputTypeSubtype, Schema.namedOutputTypeSubtype,
        TypeRef.namedType]
  | list inner ih =>
      cases expected <;> simp_all [Schema.outputTypeSubtype, TypeRef.namedType]
  | nonNull inner ih =>
      cases expected with
      | named name => exact ih hsubtype
      | list inner => exact ih hsubtype
      | nonNull expectedInner => exact ih (expected := expectedInner) hsubtype

private theorem isSubType_lookupField
    {schema : Schema} (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {parentType targetType fieldName : Name} {expected : FieldDefinition}
    (hsubtype : schema.isSubType targetType parentType)
    (hlookup : schema.lookupField parentType fieldName = some expected)
    : ∃ implementation,
        schema.lookupField targetType fieldName = some implementation
        ∧ schema.isSubType implementation.outputType.namedType
            expected.outputType.namedType := by
  rcases hsubtype with rfl | hsubtype
  · exact ⟨expected, hlookup, Or.inl rfl⟩
  cases htarget : schema.lookupType targetType <;>
    cases hparent : schema.lookupType parentType <;>
    simp only [htarget, hparent] at hsubtype
  all_goals try contradiction
  all_goals rename_i target parent
  all_goals cases target <;> cases parent <;> simp only at hsubtype
  all_goals try contradiction
  all_goals try (simp [Schema.lookupField, hparent, TypeDefinition.fields?] at hlookup)
  all_goals rename_i implementationType interfaceDefinition
  all_goals
    have hfieldName : expected.name = fieldName := by
      simpa using List.find?_some hlookup
    have hwell := SchemaWellFormedness.schemaWellFormed_lookupType_typeDefinitionWellFormed
      hschema htarget
    rcases hwell.2.2 _ hsubtype with ⟨interfaceType, hinterface, hfields⟩
    have heq : schema.lookupInterface parentType = some interfaceDefinition := by
      simp [Schema.lookupInterface, hparent]
    rw [heq] at hinterface
    cases hinterface
    have hmem : expected ∈ interfaceDefinition.fields := by
      exact List.mem_of_find?_eq_some (by
        simpa [Schema.lookupField, hparent, TypeDefinition.fields?,
          Schema.lookupFieldDefinition] using hlookup)
    rcases hfields expected hmem with ⟨implementation, himplementation, himplements⟩
    exact ⟨implementation, by
      simpa [Schema.lookupField, htarget, TypeDefinition.fields?,
        Schema.lookupFieldDefinition, hfieldName] using himplementation,
      outputTypeSubtype_namedType himplements.1⟩

private theorem selectionSetDeclaredLookupReady_of_covariantLookup
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ selections parentType targetType,
        NormalForm.selectionSetDeclaredLookupReady schema parentType selections
        -> (∀ fieldName expected,
              schema.lookupField parentType fieldName = some expected
              -> ∃ implementation,
                  schema.lookupField targetType fieldName = some implementation
                  ∧ schema.isSubType implementation.outputType.namedType
                      expected.outputType.namedType)
        -> NormalForm.selectionSetDeclaredLookupReady schema targetType selections
  | [], _, _, _, _ => by simp [NormalForm.selectionSetDeclaredLookupReady]
  | selection :: rest, parentType, targetType, hready, hlookup => by
      unfold NormalForm.selectionSetDeclaredLookupReady at hready ⊢
      have hhead := hready selection (by simp)
      have htail := selectionSetDeclaredLookupReady_of_covariantLookup schema hschema
        rest parentType targetType (by
          unfold NormalForm.selectionSetDeclaredLookupReady
          exact fun candidate hcandidate => hready candidate (by simp [hcandidate])) hlookup
      intro candidate hcandidate
      rcases List.mem_cons.mp hcandidate with heq | hcandidate
      · subst candidate
        cases selection with
        | field responseName fieldName arguments directives children =>
            simp only [NormalForm.selectionDeclaredLookupReady] at hhead ⊢
            rcases hhead with ⟨expected, hexpected, hchildren⟩
            rcases hlookup fieldName expected hexpected with
              ⟨implementation, himplementation, hsubtype⟩
            refine ⟨implementation, himplementation, ?_⟩
            exact selectionSetDeclaredLookupReady_of_covariantLookup schema hschema
              children expected.outputType.namedType implementation.outputType.namedType
              hchildren (fun _ _ hfield => isSubType_lookupField hschema hsubtype hfield)
        | inlineFragment condition directives children =>
            cases condition with
            | none =>
                simp only [NormalForm.selectionDeclaredLookupReady] at hhead ⊢
                exact selectionSetDeclaredLookupReady_of_covariantLookup schema hschema
                  children parentType targetType hhead hlookup
            | some condition =>
                simpa only [NormalForm.selectionDeclaredLookupReady] using hhead
      · unfold NormalForm.selectionSetDeclaredLookupReady at htail
        exact htail candidate hcandidate
termination_by selections _ _ _ _ => SelectionSet.size selections
decreasing_by
  all_goals cases selection <;> simp_all [SelectionSet.size, Selection.size] <;> omega

theorem runtimeMergeSource_of_valid_possibleObject
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    {parentType runtimeType : Name} {selectionSet : List Selection}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hobject : schema.objectType runtimeType)
    (hpossible : schema.typeIncludesObject parentType runtimeType)
    (hvalid
      : Validation.selectionSetValid schema variableDefinitions parentType selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema runtimeType selectionSet)
    : NormalForm.runtimeMergeSource schema runtimeType selectionSet := by
  apply NormalForm.runtimeMergeSource_of_declaredLookupReady schema hobject
    (NormalForm.object_typeIncludesObjectBool_self schema hobject) (hmerge := hmerge)
  apply selectionSetDeclaredLookupReady_of_covariantLookup schema hschema selectionSet
    parentType runtimeType
    (NormalForm.selectionSetDeclaredLookupReady_of_valid schema variableDefinitions
      parentType selectionSet hvalid)
  intro fieldName expected hlookup
  rcases SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_exists
      hschema hpossible hlookup with ⟨implementation, himplementation⟩
  exact ⟨implementation, himplementation,
    outputTypeSubtype_namedType
      (SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
        hschema hpossible hlookup himplementation)⟩

end GraphQL.TreeSummary
