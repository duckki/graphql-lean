import Proofs.GraphQL.Theories.ResponseShape.Compute.Totality
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.Reification

namespace GraphQL
namespace Tests
namespace ResponseShape

open GraphQL.ResponseShape

def minimalField : FieldDefinition :=
  { name := "left", outputType := .named "String" }

def minimalQueryType : ObjectType :=
  { name := "Query", fields := [minimalField] }

def minimalSchema : Schema :=
  { queryType := "Query"
    types := [.object minimalQueryType] }

def minimalOperation : Operation :=
  { selectionSet := [.field "left" "left" [] [] []] }

theorem minimalSchemaLookupQuery :
    minimalSchema.lookupType "Query" = some (.object minimalQueryType) := by
  simp [Schema.lookupType, Schema.allTypes, Schema.builtinScalarDefinitions,
    minimalSchema, minimalQueryType, TypeDefinition.name, BuiltinScalar.name,
    List.find?]

theorem minimalSchemaLookupString :
    minimalSchema.lookupType "String" = some (.builtinScalar .string) := by
  simp [Schema.lookupType, Schema.allTypes, Schema.builtinScalarDefinitions,
    minimalSchema, minimalQueryType, TypeDefinition.name, BuiltinScalar.name,
    List.find?]

theorem minimalSchemaQueryIsObject : minimalSchema.objectType "Query" :=
  ⟨minimalQueryType, minimalSchemaLookupQuery⟩

theorem minimalSchemaStringIsLeaf : minimalSchema.isLeafType "String" :=
  ⟨.builtinScalar .string, minimalSchemaLookupString, trivial⟩

theorem minimalSchemaStringIsOutput : minimalSchema.isOutputType "String" :=
  ⟨.builtinScalar .string, minimalSchemaLookupString, trivial⟩

theorem minimalSchemaLookupMember
    {typeName : Name} {typeDefinition : TypeDefinition}
    (hlookup : minimalSchema.lookupType typeName = some typeDefinition) :
    typeDefinition ∈ minimalSchema.allTypes
      ∧ typeDefinition.name = typeName := by
  refine ⟨List.mem_of_find?_eq_some hlookup, ?_⟩
  simpa [beq_iff_eq] using List.find?_some hlookup

theorem minimalSchemaPossibleTypes {typeName : Name} :
    minimalSchema.getPossibleTypes typeName = []
      ∨ (typeName = "Query"
        ∧ minimalSchema.getPossibleTypes typeName = ["Query"]) := by
  cases hlookup : minimalSchema.lookupType typeName with
  | none => exact .inl (by simp [Schema.getPossibleTypes, hlookup])
  | some typeDefinition =>
      rcases minimalSchemaLookupMember hlookup with ⟨hmem, hname⟩
      simp only [Schema.allTypes, Schema.builtinScalarDefinitions,
        minimalSchema, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h | h | h <;> subst h
      · exact .inl (by simp [Schema.getPossibleTypes, hlookup])
      · exact .inl (by simp [Schema.getPossibleTypes, hlookup])
      · exact .inl (by simp [Schema.getPossibleTypes, hlookup])
      · exact .inl (by simp [Schema.getPossibleTypes, hlookup])
      · exact .inl (by simp [Schema.getPossibleTypes, hlookup])
      · refine .inr ⟨?_, ?_⟩
        · simpa [minimalQueryType, TypeDefinition.name] using hname.symm
        · simp [Schema.getPossibleTypes, hlookup, minimalQueryType]

theorem minimalSchemaWellFormed :
    SchemaWellFormedness.schemaWellFormed minimalSchema := by
  refine ⟨?_, ⟨minimalQueryType, minimalSchemaLookupQuery⟩, ?_, ?_, ?_, ?_⟩
  · simp only [SchemaWellFormedness.namesAreUnique, Schema.allTypes,
      Schema.builtinScalarDefinitions, minimalSchema, minimalQueryType,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      TypeDefinition.name, BuiltinScalar.name]
    decide
  · intro typeDefinition hmem
    simp only [minimalSchema, List.mem_singleton] at hmem
    subst hmem
    refine ⟨⟨by simp [SchemaWellFormedness.listNonempty, minimalQueryType],
      ?_, ?_⟩, ?_, ?_⟩
    · simp only [SchemaWellFormedness.namesAreUnique, minimalQueryType,
        minimalField, List.map_cons, List.map_nil]
      decide
    · intro field hfield
      simp only [minimalQueryType, List.mem_singleton] at hfield
      subst hfield
      refine ⟨minimalSchemaStringIsOutput, ?_, ?_⟩
      · simp [SchemaWellFormedness.namesAreUnique, minimalField]
      · intro definition hdefinition
        simp [minimalField] at hdefinition
    · simp [SchemaWellFormedness.namesAreUnique, minimalQueryType]
    · intro interfaceName hinterface
      simp [minimalQueryType] at hinterface
  · intro typeName objectTypeName hmem
    rcases minimalSchemaPossibleTypes (typeName := typeName) with
      hpossible | ⟨_, hpossible⟩ <;> rw [hpossible] at hmem
    · simp at hmem
    · simp only [List.mem_singleton] at hmem
      subst hmem
      exact minimalSchemaQueryIsObject
  · intro typeName
    rcases minimalSchemaPossibleTypes (typeName := typeName) with
      hpossible | ⟨_, hpossible⟩ <;> simp [hpossible]
  · intro parentType objectTypeName fieldName expected hmem hlookup
    rcases minimalSchemaPossibleTypes (typeName := parentType) with
      hpossible | ⟨hquery, hpossible⟩
    · rw [hpossible] at hmem
      simp at hmem
    · subst hquery
      rw [hpossible] at hmem
      simp only [List.mem_singleton] at hmem
      subst hmem
      have hexpected : expected = minimalField ∧ fieldName = "left" := by
        simp only [Schema.lookupField, minimalSchemaLookupQuery, bind,
          Option.bind, TypeDefinition.fields?, minimalQueryType,
          List.find?_cons, List.find?_nil] at hlookup
        split at hlookup
        · rename_i hname
          refine ⟨(Option.some.inj hlookup).symm, ?_⟩
          simp only [minimalField, beq_iff_eq] at hname
          exact hname.symm
        · simp at hlookup
      rcases hexpected with ⟨hexpected, hfieldName⟩
      subst hexpected
      subst hfieldName
      refine ⟨minimalField, hlookup, ?_, ?_⟩
      · refine ⟨.inl ⟨minimalSchemaStringIsLeaf,
          minimalSchemaStringIsLeaf, rfl⟩, ?_, ?_⟩
        · intro expectedDefinition hdefinition
          simp [minimalField] at hdefinition
        · intro implementationDefinition hdefinition
          simp [minimalField] at hdefinition
      · exact ⟨minimalSchemaStringIsOutput,
          minimalSchemaStringIsOutput, fun _ => rfl⟩

theorem minimalSchemaLookupLeft :
    minimalSchema.lookupField "Query" "left" = some minimalField := by
  simp [Schema.lookupField, minimalSchemaLookupQuery, TypeDefinition.fields?,
    minimalQueryType, minimalField, List.find?]

theorem minimalOperationValid :
    Validation.operationDefinitionValid minimalSchema minimalOperation := by
  refine ⟨rfl, ⟨.object minimalQueryType, minimalSchemaLookupQuery, trivial⟩,
    ⟨by simp [minimalOperation], ?_⟩, by simp [minimalOperation], ?_, ?_, ?_⟩
  · intro variableDefinition hvariable
    simp [minimalOperation] at hvariable
  · unfold Validation.selectionSetValid
    intro selection hselection
    simp only [minimalOperation, List.mem_singleton] at hselection
    subst hselection
    have hroot : minimalOperation.rootType minimalSchema = "Query" := rfl
    unfold Validation.selectionValid
    rw [hroot]
    refine ⟨⟨by simp, ?_⟩, minimalField, minimalSchemaLookupLeft, ?_, ?_⟩
    · intro directive hdirective
      simp at hdirective
    · refine ⟨by simp, ?_, ?_⟩
      · intro argument hargument
        simp at hargument
      · intro definition hdefinition
        simp [minimalField] at hdefinition
    · unfold Validation.fieldSelectionSetValid
      exact ⟨minimalSchemaStringIsOutput,
        .inl ⟨minimalSchemaStringIsLeaf, rfl⟩⟩
  · have hcollect : FieldMerge.collectFields minimalSchema
        (minimalOperation.rootType minimalSchema) minimalOperation.selectionSet =
        [{ parentType := "Query", responseName := "left", fieldName := "left",
           arguments := [], outputType := .named "String",
           selectionSet := [] }] := by
      rw [show minimalOperation.rootType minimalSchema = "Query" from rfl]
      simp [FieldMerge.collectFields, minimalOperation, minimalSchemaLookupLeft,
        minimalField]
    refine .intro _ _ (fun left hleft right hright _ => ?_)
    rw [hcollect] at hleft hright
    simp only [List.mem_singleton] at hleft hright
    subst hleft
    subst hright
    refine .intro _ _ ?_ ?_ ?_
    · exact ⟨minimalSchemaStringIsOutput,
        minimalSchemaStringIsOutput, fun _ => rfl⟩
    · intro _
      exact ⟨rfl, fun argument hargument => by simp at hargument,
        fun argument hargument => by simp at hargument⟩
    · intro _ objectType
      exact .intro _ _ (fun left hleft =>
        False.elim (by simp [FieldMerge.collectFields] at hleft))
  · intro variableDefinition hvariable
    simp [minimalOperation] at hvariable

/-- A concrete well-formed schema and valid operation exercise totality. -/
theorem minimalOperationInstantiatesTotality :
    ∃ shape,
      computeOperationShape minimalSchema minimalOperation = .ok shape
      ∧ shape.WellFormed minimalSchema
      ∧ shape.FullMinterm
      ∧ shape.boolSupport = NormalForm.operationBoolVars minimalOperation :=
  computeOperationShape_total minimalSchema minimalOperation
    minimalSchemaWellFormed minimalOperationValid

/-- The same concrete premises instantiate the reification round trip. -/
theorem minimalOperationInstantiatesReification :
    ∃ shape,
      computeOperationShape minimalSchema minimalOperation = .ok shape
      ∧ NormalForm.completeNormalOperationsEqualUpToReordering
        (reifyOperation minimalSchema minimalOperation shape)
        (NormalForm.completeNormalizeOperation minimalSchema minimalOperation) := by
  rcases computeOperationShape_total minimalSchema minimalOperation
      minimalSchemaWellFormed minimalOperationValid with
    ⟨shape, hcompute, _hwellFormed, _hfullMinterm, _hsupport⟩
  exact ⟨shape, hcompute,
    reify_compute_equalUpToReordering minimalSchema minimalOperation shape
      minimalSchemaWellFormed minimalOperationValid hcompute⟩

end ResponseShape
end Tests
end GraphQL
