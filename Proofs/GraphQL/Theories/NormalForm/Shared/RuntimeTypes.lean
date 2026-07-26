import Proofs.GraphQL.Theories.NormalForm.Shared.DirectiveFree
import Proofs.GraphQL.SchemaWellFormedness.PossibleTypes
import Proofs.GraphQL.Validation.SelectionValidity

/-!
Schema and possible-type facts used by ground-type normalization proofs.
-/

namespace GraphQL

namespace NormalForm

-- Returns the object branches that can execute for an already-unwrapped composite return
-- type.
def groundObjectTypesForType (schema : Schema) (returnType : Name) : List Name :=
  if objectTypeNameBool schema returnType then
    [returnType]
  else
    schema.getPossibleTypes returnType

theorem objectTypeNameBool_eq_true_of_objectType_base (schema : Schema) {typeName : Name}
    : schema.objectType typeName -> objectTypeNameBool schema typeName = true := by
  intro hobject
  unfold Schema.objectType at hobject
  rcases hobject with ⟨objectType, hlookup⟩
  simp [objectTypeNameBool, hlookup]

theorem objectType_of_objectTypeNameBool_eq_true (schema : Schema) {typeName : Name}
    : objectTypeNameBool schema typeName = true -> schema.objectType typeName := by
  intro hobject
  unfold objectTypeNameBool at hobject
  cases hlookup : schema.lookupType typeName with
  | none =>
      simp [hlookup] at hobject
  | some typeDefinition =>
      cases typeDefinition with
      | object objectType =>
          exact ⟨objectType, hlookup⟩
      | builtinScalar scalar => simp [hlookup] at hobject
      | customScalar scalar => simp [hlookup] at hobject
      | interface interfaceType => simp [hlookup] at hobject
      | union unionType => simp [hlookup] at hobject
      | enum enumType => simp [hlookup] at hobject
      | inputObject inputObjectType => simp [hlookup] at hobject

theorem object_typeIncludesObjectBool_self (schema : Schema) {typeName : Name}
    : schema.objectType typeName
      -> schema.typeIncludesObjectBool typeName typeName = true := by
  intro hobject
  rcases hobject with ⟨objectType, hlookup⟩
  have hname : objectType.name = typeName := by
    have hmatch := List.find?_some hlookup
    simpa [Schema.lookupType, TypeDefinition.name] using hmatch
  simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes, hlookup,
    hname]

theorem object_typesOverlapBool_eq (schema : Schema) {left right : Name}
    : schema.objectType left
      -> schema.objectType right
      -> schema.typesOverlapBool left right = true
      -> right = left := by
  intro hleft hright hoverlap
  rcases hleft with ⟨leftObject, hleftLookup⟩
  have hleftName : leftObject.name = left := by
    have hmatch := List.find?_some hleftLookup
    simpa [Schema.lookupType, TypeDefinition.name] using hmatch
  simp [Schema.typesOverlapBool, Schema.getPossibleTypes, hleftLookup,
    hleftName] at hoverlap
  exact (object_typeIncludesObjectBool_eq_self schema
    (typeName := right) (objectName := left) hright hoverlap).symm

theorem object_typesOverlapBool_self (schema : Schema) {typeName : Name}
    : schema.objectType typeName -> schema.typesOverlapBool typeName typeName = true := by
  intro hobject
  rcases hobject with ⟨objectType, hlookup⟩
  have hname : objectType.name = typeName := by
    have hmatch := List.find?_some hlookup
    simpa [Schema.lookupType, TypeDefinition.name] using hmatch
  simp [Schema.typesOverlapBool, Schema.typeIncludesObjectBool,
    Schema.getPossibleTypes, hlookup, hname]

theorem typeIncludesObjectBool_of_object_typesOverlapBool
    (schema : Schema) {objectType typeCondition : Name}
    : schema.objectType objectType
      -> schema.typesOverlapBool objectType typeCondition = true
      -> schema.typeIncludesObjectBool typeCondition objectType = true := by
  intro hobject hoverlap
  rcases hobject with ⟨objectDefinition, hlookup⟩
  have hname : objectDefinition.name = objectType := by
    have hmatch := List.find?_some hlookup
    simpa [Schema.lookupType, TypeDefinition.name] using hmatch
  unfold Schema.typesOverlapBool at hoverlap
  simp [Schema.getPossibleTypes, hlookup, hname] at hoverlap
  exact hoverlap

theorem possibleTypes_eq_nil_of_isLeafType (schema : Schema) {typeName : Name}
    : schema.isLeafType typeName -> schema.getPossibleTypes typeName = [] := by
  intro hleaf
  rcases hleaf with ⟨typeDefinition, hlookup, hleafDefinition⟩
  cases typeDefinition with
  | builtinScalar scalar =>
      simp [Schema.getPossibleTypes, hlookup]
  | customScalar scalar =>
      simp [Schema.getPossibleTypes, hlookup]
  | object objectType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | interface interfaceType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | union unionType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | enum enumType =>
      simp [Schema.getPossibleTypes, hlookup]
  | inputObject inputObjectType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition

theorem fieldSelectionSetValid_child_of_possibleType
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fieldDefinition : FieldDefinition} {selectionSet : List Selection}
    {objectType : Name}
    : Validation.fieldSelectionSetValid schema variableDefinitions
        fieldDefinition selectionSet
      -> objectType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
      -> Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType selectionSet := by
  intro hvalid hpossible
  simp [Validation.fieldSelectionSetValid] at hvalid
  rcases hvalid with ⟨_houtput, hchild⟩
  rcases hchild with hleaf | hcomposite
  · rcases hleaf with ⟨hleaf, _hempty⟩
    have hnil :=
      possibleTypes_eq_nil_of_isLeafType schema hleaf
    rw [hnil] at hpossible
    cases hpossible
  · exact hcomposite.2.2

end NormalForm

end GraphQL
