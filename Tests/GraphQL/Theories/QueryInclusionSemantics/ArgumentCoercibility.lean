import GraphQL.Theories.QueryInclusionSemantics
import GraphQL.Theories.NormalForm

/-! A required argument can lose its default at a concrete implementation.

The interface permits omitting `a`, but execution uses the concrete field definition:

```
interface I { f(a: Int! = 1): String }
type Query implements I { f(a: Int!): String }
```

The operations `{ ... on I { left: f } }` and `{ ... on I { right: f } }` are
valid and satisfy composite-output inhabitance. Every execution has an argument
coercion error. Semantic inclusion is vacuous while their selected paths differ.
Thus output inhabitance alone cannot discharge the argument-coercibility premise.
-/

namespace GraphQL.Tests.QueryInclusionArgumentCoercibility

private def inheritedArg : InputValueDefinition :=
  { name := "a", inputType := .nonNull (.named "Int"), defaultValue := some (.int 1) }

private def concreteArg : InputValueDefinition :=
  { name := "a", inputType := .nonNull (.named "Int") }

private def interfaceField : FieldDefinition :=
  { name := "f", outputType := .named "String", arguments := [inheritedArg] }

private def concreteField : FieldDefinition :=
  { name := "f", outputType := .named "String", arguments := [concreteArg] }

private def interfaceType : InterfaceType :=
  { name := "I", fields := [interfaceField] }

private def queryObject : ObjectType :=
  { name := "Query", interfaces := ["I"], fields := [concreteField] }

private def exampleSchema : Schema :=
  { queryType := "Query", types := [.interface interfaceType, .object queryObject] }

private def scopedField (responseName : Name) : FieldMerge.ScopedField :=
  {
    parentType := "I",
    responseName := responseName,
    fieldName := "f",
    arguments := [],
    outputType := .named "String",
    selectionSet := []
  }

private def exampleOperation (responseName : Name) : Operation :=
  { selectionSet := [.inlineFragment (some "I") [] [.field responseName "f" [] [] []]] }

private theorem possibleTypes (typeName : Name)
    : exampleSchema.getPossibleTypes typeName
      = if typeName = "I" ∨ typeName = "Query" then ["Query"] else [] := by
  by_cases hI : typeName = "I"
  · subst typeName
    rfl
  by_cases hQ : typeName = "Query"
  · subst typeName
    rfl
  by_cases hInt : typeName = "Int"
  · subst typeName
    rfl
  by_cases hFloat : typeName = "Float"
  · subst typeName
    rfl
  by_cases hString : typeName = "String"
  · subst typeName
    rfl
  by_cases hBool : typeName = "Boolean"
  · subst typeName
    rfl
  by_cases hID : typeName = "ID"
  · subst typeName
    rfl
  have hbInt : ("Int" == typeName) = false := beq_eq_false_iff_ne.mpr (Ne.symm hInt)
  have hbFloat : ("Float" == typeName) = false := beq_eq_false_iff_ne.mpr (Ne.symm hFloat)
  have hbString : ("String" == typeName) = false := beq_eq_false_iff_ne.mpr (Ne.symm hString)
  have hbBool : ("Boolean" == typeName) = false := beq_eq_false_iff_ne.mpr (Ne.symm hBool)
  have hbID : ("ID" == typeName) = false := beq_eq_false_iff_ne.mpr (Ne.symm hID)
  have hbI : ("I" == typeName) = false := beq_eq_false_iff_ne.mpr (Ne.symm hI)
  have hbQ : ("Query" == typeName) = false := beq_eq_false_iff_ne.mpr (Ne.symm hQ)
  simp [Schema.getPossibleTypes, Schema.lookupType, Schema.allTypes,
    Schema.builtinScalarDefinitions, List.find?, TypeDefinition.name, BuiltinScalar.name,
    interfaceType, queryObject, exampleSchema, hbInt, hbFloat, hbString, hbBool, hbID, hbI, hbQ, hI, hQ]

private theorem argsImplement
    : SchemaWellFormedness.argumentDefinitionsImplement [concreteArg] [inheritedArg] := by
  simp [SchemaWellFormedness.argumentDefinitionsImplement,
    Schema.lookupArgumentDefinition, inheritedArg, concreteArg]

private theorem intInput : (TypeRef.named "Int").isInputType exampleSchema :=
  ⟨.builtinScalar .int, rfl, trivial⟩

private theorem stringOutput : (TypeRef.named "String").isOutputType exampleSchema :=
  ⟨.builtinScalar .string, rfl, trivial⟩

private theorem inheritedArgWellFormed
    : SchemaWellFormedness.inputValueDefinitionWellFormed exampleSchema inheritedArg := by
  constructor
  · exact intInput
  · apply Schema.ConstInputValueIsCorrectType.nonNull
    · exact intInput
    · intro h
      cases h
    · apply Schema.ConstInputValueIsCorrectType.namedNonInputObject
      · exact intInput
      · intro fields h
        cases h
      · intro h
        cases h
      · rfl

private theorem concreteArgWellFormed
    : SchemaWellFormedness.inputValueDefinitionWellFormed exampleSchema concreteArg := by
  exact ⟨intInput, trivial⟩

private theorem interfaceFieldWellFormed
    : SchemaWellFormedness.fieldDefinitionWellFormed exampleSchema interfaceField := by
  constructor
  · exact stringOutput
  · constructor
    · simp [SchemaWellFormedness.namesAreUnique, interfaceField, inheritedArg]
    · intro definition hmem
      have h : definition = inheritedArg := by simpa [interfaceField] using hmem
      subst definition
      exact inheritedArgWellFormed

private theorem concreteFieldWellFormed
    : SchemaWellFormedness.fieldDefinitionWellFormed exampleSchema concreteField := by
  constructor
  · exact stringOutput
  · constructor
    · simp [SchemaWellFormedness.namesAreUnique, concreteField, concreteArg]
    · intro definition hmem
      have h : definition = concreteArg := by simpa [concreteField] using hmem
      subst definition
      exact concreteArgWellFormed

private theorem stringLeaf : exampleSchema.isLeafType "String" :=
  ⟨.builtinScalar .string, rfl, trivial⟩

private theorem concreteImplementsInterface
    : SchemaWellFormedness.fieldDefinitionImplements exampleSchema
        concreteField interfaceField := by
  constructor
  · change exampleSchema.namedOutputTypeSubtype "String" "String"
    exact Or.inl ⟨stringLeaf, stringLeaf, rfl⟩
  · exact argsImplement

private theorem concreteImplementsSelf
    : SchemaWellFormedness.fieldDefinitionImplements exampleSchema
        concreteField concreteField := by
  constructor
  · change exampleSchema.namedOutputTypeSubtype "String" "String"
    exact Or.inl ⟨stringLeaf, stringLeaf, rfl⟩
  · simp [SchemaWellFormedness.argumentDefinitionsImplement,
      Schema.lookupArgumentDefinition, concreteField, concreteArg]

private theorem stringSameShape
    : FieldMerge.sameResponseShape exampleSchema (.named "String") (.named "String") := by
  exact ⟨stringOutput, stringOutput, by intro _; rfl⟩

private theorem interfaceTypeWellFormed
    : SchemaWellFormedness.interfaceTypeWellFormed exampleSchema interfaceType := by
  constructor
  · constructor
    · simp [SchemaWellFormedness.listNonempty, interfaceType]
    constructor
    · simp [SchemaWellFormedness.namesAreUnique, interfaceType, interfaceField]
    · intro field hmem
      have h : field = interfaceField := by simpa [interfaceType] using hmem
      subst field
      exact interfaceFieldWellFormed
  constructor
  · simp [SchemaWellFormedness.namesAreUnique, interfaceType]
  · intro interfaceName hmem
    simp [interfaceType] at hmem

private theorem queryObjectWellFormed
    : SchemaWellFormedness.objectTypeWellFormed exampleSchema queryObject := by
  constructor
  · constructor
    · simp [SchemaWellFormedness.listNonempty, queryObject]
    constructor
    · simp [SchemaWellFormedness.namesAreUnique, queryObject, concreteField]
    · intro field hmem
      have h : field = concreteField := by simpa [queryObject] using hmem
      subst field
      exact concreteFieldWellFormed
  constructor
  · simp [SchemaWellFormedness.namesAreUnique, queryObject]
  · intro interfaceName hmem
    have h : interfaceName = "I" := by simpa [queryObject] using hmem
    subst interfaceName
    refine ⟨interfaceType, rfl, ?_⟩
    intro field hfield
    have h : field = interfaceField := by simpa [interfaceType] using hfield
    subst field
    exact ⟨concreteField, rfl, concreteImplementsInterface⟩

private theorem lookupI (fieldName : Name)
    : exampleSchema.lookupField "I" fieldName
      = if fieldName = "f" then some interfaceField else none := by
  by_cases h : fieldName = "f"
  · subst fieldName
    rfl
  · have hb : ("f" == fieldName) = false :=
      beq_eq_false_iff_ne.mpr (Ne.symm h)
    unfold Schema.lookupField
    rw [show exampleSchema.lookupType "I" = some (.interface interfaceType) from rfl]
    simp [TypeDefinition.fields?, interfaceType, interfaceField, List.find?, hb, h]

private theorem lookupQuery (fieldName : Name)
    : exampleSchema.lookupField "Query" fieldName
      = if fieldName = "f" then some concreteField else none := by
  by_cases h : fieldName = "f"
  · subst fieldName
    rfl
  · have hb : ("f" == fieldName) = false :=
      beq_eq_false_iff_ne.mpr (Ne.symm h)
    unfold Schema.lookupField
    rw [show exampleSchema.lookupType "Query" = some (.object queryObject) from rfl]
    simp [TypeDefinition.fields?, queryObject, concreteField, List.find?, hb, h]

private theorem possibleObjectFieldsImplement
    : SchemaWellFormedness.possibleObjectFieldDefinitionsImplement exampleSchema := by
  intro parentType objectTypeName fieldName expected hpossible hlookup
  have hparent := possibleTypes parentType
  by_cases hI : parentType = "I"
  · subst parentType
    have hobject : objectTypeName = "Query" := by simpa [possibleTypes] using hpossible
    subst objectTypeName
    rw [lookupI] at hlookup
    by_cases hfield : fieldName = "f"
    · simp [hfield] at hlookup
      subst fieldName
      have hexpected : expected = interfaceField := by
        simpa using hlookup.symm
      subst expected
      exact ⟨concreteField, by rfl, concreteImplementsInterface, stringSameShape⟩
    · simp [hfield] at hlookup
  by_cases hQ : parentType = "Query"
  · subst parentType
    have hobject : objectTypeName = "Query" := by simpa [possibleTypes] using hpossible
    subst objectTypeName
    rw [lookupQuery] at hlookup
    by_cases hfield : fieldName = "f"
    · simp [hfield] at hlookup
      subst fieldName
      have hexpected : expected = concreteField := by
        simpa using hlookup.symm
      subst expected
      exact ⟨concreteField, by rfl, concreteImplementsSelf, stringSameShape⟩
    · simp [hfield] at hlookup
  have hfalse : exampleSchema.getPossibleTypes parentType = [] := by
    rw [hparent]
    simp [hI, hQ]
  rw [hfalse] at hpossible
  cases hpossible

private theorem schemaWellFormed
    : SchemaWellFormedness.schemaWellFormed exampleSchema := by
  unfold SchemaWellFormedness.schemaWellFormed
  constructor
  · change (["Int", "Float", "String", "Boolean", "ID", "I", "Query"] : List Name).Nodup
    cbv <;> simp
  constructor
  · exact ⟨queryObject, rfl⟩
  constructor
  · intro typeDefinition hmem
    have h : typeDefinition = .interface interfaceType ∨
        typeDefinition = .object queryObject := by
      simpa [exampleSchema] using hmem
    rcases h with h | h
    · subst typeDefinition
      exact interfaceTypeWellFormed
    · subst typeDefinition
      exact queryObjectWellFormed
  constructor
  · constructor
    · rfl
    · rfl
  constructor
  · intro typeName objectTypeName hmem
    rw [possibleTypes] at hmem
    by_cases h : typeName = "I" ∨ typeName = "Query"
    · simp [h] at hmem
      subst objectTypeName
      exact ⟨queryObject, rfl⟩
    · simp [h] at hmem
  constructor
  · intro typeName
    rw [possibleTypes]
    by_cases h : typeName = "I" ∨ typeName = "Query"
    · simp [h]
    · simp [h]
  · exact possibleObjectFieldsImplement

private theorem operationValid (responseName : Name)
    : Validation.operationDefinitionValid exampleSchema
        (exampleOperation responseName) := by
  unfold Validation.operationDefinitionValid
  constructor
  · rfl
  constructor
  · exact ⟨.object queryObject, rfl, trivial⟩
  constructor
  · simp [Validation.variableDefinitionsValid, exampleOperation]
  constructor
  · cbv <;> simp
  constructor
  · unfold Validation.selectionSetValid
    intro selection hmem
    simp only [exampleOperation, List.mem_singleton] at hmem
    subst selection
    unfold Validation.selectionValid
    constructor
    · simp [Validation.directivesValid]
    constructor
    · exact ⟨.interface interfaceType, rfl, trivial⟩
    constructor
    · exact ⟨"Query", by exact List.mem_cons_self,
      by exact List.mem_cons_self⟩
    constructor
    · cbv <;> simp
    unfold Validation.selectionSetValid
    intro field hfield
    simp only [List.mem_singleton] at hfield
    subst field
    unfold Validation.selectionValid
    constructor
    · simp [Validation.directivesValid]
    refine ⟨{ name := "f", outputType := .named "String", arguments := [inheritedArg] },
      rfl, ?_, ?_⟩
    · simp [Validation.argumentsValid, Validation.isRequiredArgument,
        Validation.isRequiredInputValueDefinition, InputValueDefinition.isRequired,
        inheritedArg]
    · unfold Validation.fieldSelectionSetValid
      constructor
      · exact ⟨.builtinScalar .string, rfl, trivial⟩
      left
      constructor
      · exact ⟨.builtinScalar .string, rfl, trivial⟩
      · rfl
  constructor
  · refine FieldMerge.FieldsInSetCanMerge.intro _ _ ?_
    dsimp
    intro left hleft right hright _
    have hcollect : FieldMerge.collectFields exampleSchema
        ((exampleOperation responseName).rootType exampleSchema) (exampleOperation responseName).selectionSet =
        [scopedField responseName] := by
      have hfield : exampleSchema.lookupField "I" "f" = some interfaceField := by rfl
      simp [FieldMerge.collectFields, exampleOperation, Operation.rootType,
        OperationType.rootType, hfield, scopedField, interfaceField]
    rw [hcollect] at hleft hright
    simp only [List.mem_singleton] at hleft hright
    subst left
    subst right
    refine FieldMerge.FieldsForNameCanMerge.intro _ _ ?_ ?_ ?_
    · change FieldMerge.sameResponseShape exampleSchema (.named "String") (.named "String")
      have houtput : (TypeRef.named "String").isOutputType exampleSchema :=
        ⟨.builtinScalar .string, rfl, trivial⟩
      exact ⟨houtput, houtput, by intro _; rfl⟩
    · intro _
      constructor
      · rfl
      · simp [Argument.argumentsEquivalent, scopedField]
    · intro _ objectType
      refine FieldMerge.FieldsInSetCanMerge.intro objectType [] ?_
      dsimp
      intro left hleft
      simp [FieldMerge.collectFields] at hleft
  · simp [Validation.operationVariablesUsed, exampleOperation]

private theorem concreteCoercionFails (values : Execution.VariableValues)
    : Execution.coerceArgumentValues exampleSchema values [concreteArg] [] = .error := by
  rfl

private theorem operationArgumentsFail (responseName : Name)
    (supplied : Execution.VariableValues)
    : ¬ operationArgumentsCoercible exampleSchema supplied
          (exampleOperation responseName) := by
  intro h
  have hfragment := h.1
  have hchildren := hfragment (by rfl) (by cbv <;> simp)
  have hf := hchildren.1 (by rfl)
    ({ name := "f", outputType := .named "String", arguments := [concreteArg] } : FieldDefinition)
    (by rfl)
  rw [concreteCoercionFails] at hf
  simp at hf

private theorem branchCoercionPremiseFails (responseName : Name)
    : ¬ QueryInclusionSemantics.comparisonBranchesArgumentCoercible exampleSchema
          (exampleOperation responseName) (exampleOperation responseName) := by
  intro h
  have hvars :
      QueryInclusion.comparisonConditionVariables (exampleOperation responseName).selectionSet
        (exampleOperation responseName).selectionSet = [] := by
    rfl
  have hc : boolVarsComplete
      (QueryInclusion.comparisonConditionVariables (exampleOperation responseName).selectionSet
        (exampleOperation responseName).selectionSet)
      (boolCaseVariableValues []) := by
    rw [hvars]
    intro variableName hmem
    simp at hmem
  obtain ⟨supplied, _, hargs, _⟩ := h [] hc
  exact operationArgumentsFail responseName supplied hargs

private theorem outputTypesInhabited (responseName : Name)
    : operationCompositeFieldTypesInhabited exampleSchema
        (exampleOperation responseName) := by
  unfold operationCompositeFieldTypesInhabited selectionSetCompositeFieldTypesInhabited
  intro values selection hmem
  have heq : selection = .inlineFragment (some "I") []
      [.field responseName "f" [] [] []] := by simpa [exampleOperation] using hmem
  subst selection
  unfold selectionCompositeFieldTypesInhabited selectionSetCompositeFieldTypesInhabited
  intro _ _ child hchild
  have heq : child = .field responseName "f" [] [] [] := by simpa using hchild
  subst child
  unfold selectionCompositeFieldTypesInhabited
  intro _ definition hlookup hcomposite
  have hconcrete : exampleSchema.lookupField "Query" "f" = some concreteField := rfl
  change exampleSchema.lookupField "Query" "f" = some definition at hlookup
  rw [hconcrete] at hlookup
  cases Option.some.inj hlookup
  change false = true at hcomposite
  cases hcomposite

private theorem executionAlwaysErrors (responseName : Name) {ObjectRef : Type}
    (resolvers : Execution.Resolvers ObjectRef) (values : Execution.VariableValues)
    (source : Execution.ResolverValue ObjectRef)
    : (AnnotatedExecution.executeQueryAnnotated exampleSchema resolvers values
        (exampleOperation responseName) source).errors
      = 1 := by
  unfold AnnotatedExecution.executeQueryAnnotated AnnotatedExecution.executeQueryAnnotatedWithFuel
  split
  next happlies =>
    cases source with
    | null => contradiction
    | scalar value => contradiction
    | list values => contradiction
    | object runtimeType ref =>
        have hroot : runtimeType = "Query" := by
          change (["Query"].contains runtimeType) = true at happlies
          simpa using happlies
        subst runtimeType
        cbv
  next => rfl

private theorem semanticInclusion
    : QueryInclusionSemantics.includes exampleSchema (exampleOperation "left")
        (exampleOperation "right") := by
  constructor
  · constructor <;> intro definition hmem <;> cases hmem
  · intro ObjectRef resolvers values source
    dsimp only
    intro hleft _
    have herror := executionAlwaysErrors "left" resolvers values source
    rw [herror] at hleft
    contradiction

private def rightStep : ResponsePath.PathStep :=
  {
    parentObject := "Query",
    responseName := "right",
    field :=
      { fieldName := "f", arguments := [], outputType := .named "String" }
  }

private theorem syntacticNonInclusion
    : ¬ QueryInclusion.includes exampleSchema (exampleOperation "left")
          (exampleOperation "right") := by
  intro hincludes
  have hcomplete : boolVarsComplete
      (QueryInclusion.comparisonConditionVariables (exampleOperation "left").selectionSet
        (exampleOperation "right").selectionSet) (boolCaseVariableValues []) := by
    intro name hmem; cases hmem
  have hright : ResponsePath.operationSelectsPath exampleSchema (exampleOperation "right") []
      [rightStep] := by
    cbv
    refine ⟨List.mem_cons_self, _, List.mem_cons_self, _, List.mem_cons_self,
      rfl, ?_, concreteField, rfl, rfl⟩
    simp [Argument.argumentsEquivalent]
  have hleft := hincludes.2 [] hcomplete [rightStep] hright
  cbv at hleft
  obtain ⟨fields, hfields, _⟩ := hleft.2
  simp at hfields

private theorem concreteDefaultMissing (responseName : Name)
    : ¬ operationCoercibleInPossibleTypes exampleSchema
          (exampleOperation responseName) := by
  intro h
  have hfield := ((h []).1 rfl (by cbv)).1 rfl
  have hdefault := hfield.1 concreteArg List.mem_cons_self rfl rfl
  cases hdefault

private def nullableVariable : VariableDefinition :=
  { name := "a", typeRef := .named "Int" }

private def suppliedArgument : Argument :=
  { name := "a", value := .variable "a" }

private theorem suppliedArgumentValidAtInterface
    : Validation.argumentsValid exampleSchema [inheritedArg] [nullableVariable]
        [suppliedArgument] := by
  refine ⟨by simp, ?_, ?_⟩
  · intro argument hmem
    have heq : argument = suppliedArgument := by simpa using hmem
    subst argument
    refine ⟨inheritedArg, rfl, ?_⟩
    apply Validation.ValueIsCorrectTypeAtLocation.variable "a" (.nonNull (.named "Int"))
      (some (.int 1)) nullableVariable (by exact intInput) rfl
    refine ⟨intInput, intInput, Or.inr ?_, rfl⟩
    exact ⟨.int 1, rfl, trivial⟩
  · intro definition hmem
    have heq : definition = inheritedArg := by simpa using hmem
    subst definition
    simp [Validation.isRequiredArgument, Validation.isRequiredInputValueDefinition,
      InputValueDefinition.isRequired, inheritedArg]

private theorem suppliedArgumentInvalidAtObject
    : ¬ Validation.argumentsValid exampleSchema [concreteArg] [nullableVariable]
          [suppliedArgument] := by
  intro hvalid
  obtain ⟨definition, hlookup, hvalue⟩ := hvalid.2.1 suppliedArgument List.mem_cons_self
  have heq : definition = concreteArg := by simpa [Schema.lookupArgumentDefinition,
    suppliedArgument, concreteArg] using hlookup.symm
  subst definition
  change Validation.ValueIsCorrectTypeAtLocation exampleSchema [nullableVariable]
    (.variable "a") (.nonNull (.named "Int")) none at hvalue
  cases hvalue with
  | «variable» _ _ _ definition _ hlookup husage =>
      have heq : definition = nullableVariable := by simpa [Validation.getVariableDefinition?,
        nullableVariable] using hlookup.symm
      subst definition
      simp [Validation.variableUsageAllowed, nullableVariable,
        Validation.defaultValueNonNull] at husage
  | nonNull _ _ _ _ _ hnotVariable _ => exact hnotVariable "a" rfl

-- The default-only readiness condition cannot replace concrete validation in the
-- normalization-validity theorem: grounding changes the variable's input location.
theorem suppliedArgumentNeedsNoConcreteDefault
    : SchemaWellFormedness.schemaWellFormed exampleSchema
      ∧ Validation.argumentsValid exampleSchema [inheritedArg] [nullableVariable]
          [suppliedArgument]
      ∧ omittedNonNullArgumentsHaveDefaults [concreteArg] [suppliedArgument]
      ∧ ¬ Validation.argumentsValid exampleSchema [concreteArg] [nullableVariable]
            [suppliedArgument]
      ∧ (Execution.coerceArgumentValues exampleSchema [("a", .int 1)] [concreteArg]
          [suppliedArgument]).isSuccess
        = true := by
  refine ⟨
    schemaWellFormed,
    suppliedArgumentValidAtInterface,
    ?_,
    suppliedArgumentInvalidAtObject,
    by cbv
  ⟩
  intro definition hmem _ hmissing
  have heq : definition = concreteArg := by simpa using hmem
  subst definition
  cases hmissing

example
    : NormalForm.normalizeOperation exampleSchema
        {
          variableDefinitions := [nullableVariable],
          selectionSet :=
            [.inlineFragment (some "I") [] [.field "f" "f" [suppliedArgument] [] []]]
        }
      = {
        variableDefinitions := [nullableVariable],
        selectionSet := [.field "f" "f" [suppliedArgument] [] []]
      } := by
  cbv

-- Output inhabitance cannot replace the argument-coercibility premise. Both
-- operations are valid, but their concrete field arguments always fail coercion.
theorem inhabitedValidOperationsNeedArgumentCoercibility
    : ∃ (schema : Schema) (left right : Operation),
        SchemaWellFormedness.schemaWellFormed schema
        ∧ Validation.operationDefinitionValid schema left
        ∧ Validation.operationDefinitionValid schema right
        ∧ operationCompositeFieldTypesInhabited schema left
        ∧ operationCompositeFieldTypesInhabited schema right
        ∧ QueryInclusionSemantics.includes schema left right
        ∧ ¬ QueryInclusion.includes schema left right := by
  exact ⟨exampleSchema, exampleOperation "left", exampleOperation "right",
    schemaWellFormed, operationValid "left", operationValid "right",
    outputTypesInhabited "left", outputTypesInhabited "right",
    semanticInclusion, syntacticNonInclusion⟩

theorem outputInhabitanceDoesNotEnsureCoercibleBranches
    : ∃ (schema : Schema) (operation : Operation),
        SchemaWellFormedness.schemaWellFormed schema
        ∧ Validation.operationDefinitionValid schema operation
        ∧ operationCompositeFieldTypesInhabited schema operation
        ∧ ¬ operationCoercibleInPossibleTypes schema operation
        ∧ ¬ QueryInclusionSemantics.comparisonBranchesArgumentCoercible
              schema operation operation := by
  exact ⟨exampleSchema, exampleOperation "f", schemaWellFormed, operationValid "f",
    outputTypesInhabited "f", concreteDefaultMissing "f", branchCoercionPremiseFails "f"⟩

end GraphQL.Tests.QueryInclusionArgumentCoercibility
