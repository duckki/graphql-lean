import Proofs.GraphQL.Theories.ResponseShape.Correspondence.Operation
import Proofs.GraphQL.Theories.ResponseShape.Compute.Totality
import Tests.GraphQL.Theories.ResponseShape.Compute

namespace GraphQL
namespace Tests
namespace ResponseShape

open GraphQL.ResponseShape
open GraphQL.NormalForm
open GraphQL.NormalForm.CompleteNormalization

def twoVariableAssignment : BoolCase :=
  [("x", true), ("y", false)]

def twoVariableSelectedPath : List PathStep :=
  [
    {
      parentObject := "Query",
      responseName := "hero",
      «field» := {
        fieldName := "hero",
        arguments := [],
        outputType := .named "Human"
      }
    },
    {
      parentObject := "Human",
      responseName := "name",
      «field» := {
        fieldName := "name",
        arguments := [],
        outputType := .named "String"
      }
    }
  ]

private def twoVariableShapeSucceeded : Bool :=
  match computeOperationShape NormalForm.groundTypingSchema
      NormalForm.completeNormalizationDirectiveInputQuery with
  | .ok _ => true
  | .error _ => false

private theorem twoVariableShapeSucceeds :
    twoVariableShapeSucceeded = true := by
  native_decide

/-- The selected two-variable fixture path is present in the source footprint. -/
theorem twoVariableFootprintSelectsPath :
    operationSelectsPath NormalForm.groundTypingSchema
      NormalForm.completeNormalizationDirectiveInputQuery
      twoVariableAssignment twoVariableSelectedPath := by
  simp [operationSelectsPath, twoVariableAssignment, twoVariableSelectedPath,
    NormalForm.completeNormalizationDirectiveInputQuery,
    NormalForm.operationWith, NormalForm.groundTypingSchema,
    NormalForm.rootType, NormalForm.objectFieldDefinition,
    NormalForm.stringFieldDefinition, NormalForm.boolCaseVariableValues,
    Operation.rootType, OperationType.rootType, Schema.typeIncludesObject,
    Schema.getPossibleTypes, Schema.lookupField, Schema.lookupType,
    TypeRef.namedType, InputValue.staticBoolean?, Schema.allTypes,
    Schema.builtinScalarDefinitions, List.find?, TypeDefinition.name,
    TypeDefinition.fields?, BuiltinScalar.name, Execution.collectFields,
    Execution.collectSelection, Execution.selectionDirectivesAllowBool,
    Execution.directiveAllowsSelectionBool, Execution.inputValueBoolean?,
    Execution.lookupVariableValue?, Execution.mergeExecutableGroups,
    Execution.addExecutableGroup, collectedFieldsSelectPath,
    executableFieldMatchesPathStep, Argument.argumentsEquivalent,
    Argument.equivalent, InputValue.equivalent]

/-- The two-variable fixture has positive witnesses on both sides and
instantiates both implication directions at a concrete assignment and path. -/
theorem twoVariableCorrespondenceSpotGuard
    (hschema : SchemaWellFormedness.schemaWellFormed
      NormalForm.groundTypingSchema)
    (hvalid : Validation.operationDefinitionValid
      NormalForm.groundTypingSchema
      NormalForm.completeNormalizationDirectiveInputQuery)
    (shape : OperationShape)
    (hcompute : computeOperationShape NormalForm.groundTypingSchema
      NormalForm.completeNormalizationDirectiveInputQuery = .ok shape) :
    shape.root.DenotesEquivalentPath NormalForm.groundTypingSchema
        twoVariableAssignment shape.rootType twoVariableSelectedPath
    ∧ operationSelectsPath NormalForm.groundTypingSchema
        NormalForm.completeNormalizationDirectiveInputQuery
        twoVariableAssignment twoVariableSelectedPath
    ∧ (shape.root.DenotesEquivalentPath NormalForm.groundTypingSchema
          twoVariableAssignment shape.rootType twoVariableSelectedPath ->
        operationSelectsPath NormalForm.groundTypingSchema
          NormalForm.completeNormalizationDirectiveInputQuery
          twoVariableAssignment twoVariableSelectedPath)
    ∧ (operationSelectsPath NormalForm.groundTypingSchema
          NormalForm.completeNormalizationDirectiveInputQuery
          twoVariableAssignment twoVariableSelectedPath ->
        shape.root.DenotesEquivalentPath NormalForm.groundTypingSchema
          twoVariableAssignment shape.rootType twoVariableSelectedPath) := by
  have hfields := computeOperationShape_fields NormalForm.groundTypingSchema
    NormalForm.completeNormalizationDirectiveInputQuery shape hcompute
  have hcomplete : completeNormalBoolCase shape.boolSupport
      twoVariableAssignment := by
    rw [hfields.2.2.1]
    simp [completeNormalBoolCase, twoVariableAssignment,
      operationBoolVars, NormalForm.completeNormalizationDirectiveInputQuery,
      NormalForm.operationWith, selectionSetBooleanVariables,
      selectionBooleanVariables, directivesBooleanVariables,
      directiveBooleanVariables, inputValueBooleanVariables,
      dedupBoolVars, boolVariableMem]
  have hiff :=
    computeOperationShape_denotesEquivalentPath_iff_operationSelectsPath
      NormalForm.groundTypingSchema
      NormalForm.completeNormalizationDirectiveInputQuery shape
      twoVariableAssignment twoVariableSelectedPath hschema hvalid hcompute
      hcomplete
  exact ⟨hiff.mpr twoVariableFootprintSelectsPath,
    twoVariableFootprintSelectsPath, hiff.mp, hiff.mpr⟩

def nestedAbstractAssignment : BoolCase := [("x", true)]

def nestedAbstractSelectedPath : List PathStep :=
  [
    {
      parentObject := "Query",
      responseName := "hero",
      «field» := {
        fieldName := "hero",
        arguments := [],
        outputType := .named "Human"
      }
    },
    {
      parentObject := "Human",
      responseName := "companion",
      «field» := {
        fieldName := "companion",
        arguments := [],
        outputType := .named "Character"
      }
    },
    {
      parentObject := "Human",
      responseName := "id",
      «field» := {
        fieldName := "id",
        arguments := [],
        outputType := .named "String"
      }
    }
  ]

private def nestedAbstractShapeSucceeded : Bool :=
  match computeOperationShape NormalForm.groundTypingSchema
      NormalForm.completeNormalizationNestedDirectiveInputQuery with
  | .ok _ => true
  | .error _ => false

private theorem nestedAbstractShapeSucceeds :
    nestedAbstractShapeSucceeded = true := by
  native_decide

/-- The selected nested abstract-return path is present in the source footprint. -/
theorem nestedAbstractFootprintSelectsPath :
    operationSelectsPath NormalForm.groundTypingSchema
      NormalForm.completeNormalizationNestedDirectiveInputQuery
      nestedAbstractAssignment nestedAbstractSelectedPath := by
  simp [operationSelectsPath, nestedAbstractAssignment,
    nestedAbstractSelectedPath,
    NormalForm.completeNormalizationNestedDirectiveInputQuery,
    NormalForm.operationWith, NormalForm.groundTypingSchema,
    NormalForm.rootType, NormalForm.objectFieldDefinition,
    NormalForm.stringFieldDefinition, NormalForm.boolCaseVariableValues,
    Operation.rootType, OperationType.rootType, Schema.typeIncludesObject,
    Schema.getPossibleTypes, Schema.lookupField, Schema.lookupType,
    Schema.objectTypesImplementingInterface, Schema.objectTypes,
    Schema.objectTypeImplementsInterfaceBool,
    Schema.interfaceTypeImplementsInterfaceBool,
    Schema.interfaceTypeImplementsInterfaceBoundedBool,
    TypeRef.namedType, InputValue.staticBoolean?, Schema.allTypes,
    Schema.builtinScalarDefinitions, List.find?, TypeDefinition.name,
    TypeDefinition.fields?, BuiltinScalar.name, Execution.collectFields,
    Execution.collectSelection, Execution.selectionDirectivesAllowBool,
    Execution.directiveAllowsSelectionBool, Execution.inputValueBoolean?,
    Execution.lookupVariableValue?, Execution.mergeExecutableGroups,
    collectedFieldsSelectPath, executableFieldMatchesPathStep,
    Argument.argumentsEquivalent, Argument.equivalent,
    InputValue.equivalent]

/-- The nested abstract-return fixture has positive witnesses on both sides and
instantiates both implication directions at a recursive concrete-object path. -/
theorem nestedAbstractCorrespondenceSpotGuard
    (hschema : SchemaWellFormedness.schemaWellFormed
      NormalForm.groundTypingSchema)
    (hvalid : Validation.operationDefinitionValid
      NormalForm.groundTypingSchema
      NormalForm.completeNormalizationNestedDirectiveInputQuery)
    (shape : OperationShape)
    (hcompute : computeOperationShape NormalForm.groundTypingSchema
      NormalForm.completeNormalizationNestedDirectiveInputQuery = .ok shape) :
    shape.root.DenotesEquivalentPath NormalForm.groundTypingSchema
        nestedAbstractAssignment shape.rootType nestedAbstractSelectedPath
    ∧ operationSelectsPath NormalForm.groundTypingSchema
        NormalForm.completeNormalizationNestedDirectiveInputQuery
        nestedAbstractAssignment nestedAbstractSelectedPath
    ∧ (shape.root.DenotesEquivalentPath NormalForm.groundTypingSchema
          nestedAbstractAssignment shape.rootType nestedAbstractSelectedPath ->
        operationSelectsPath NormalForm.groundTypingSchema
          NormalForm.completeNormalizationNestedDirectiveInputQuery
          nestedAbstractAssignment nestedAbstractSelectedPath)
    ∧ (operationSelectsPath NormalForm.groundTypingSchema
          NormalForm.completeNormalizationNestedDirectiveInputQuery
          nestedAbstractAssignment nestedAbstractSelectedPath ->
        shape.root.DenotesEquivalentPath NormalForm.groundTypingSchema
          nestedAbstractAssignment shape.rootType nestedAbstractSelectedPath) := by
  have hfields := computeOperationShape_fields NormalForm.groundTypingSchema
    NormalForm.completeNormalizationNestedDirectiveInputQuery shape hcompute
  have hcomplete : completeNormalBoolCase shape.boolSupport
      nestedAbstractAssignment := by
    rw [hfields.2.2.1]
    simp [completeNormalBoolCase, nestedAbstractAssignment,
      operationBoolVars,
      NormalForm.completeNormalizationNestedDirectiveInputQuery,
      NormalForm.operationWith, selectionSetBooleanVariables,
      selectionBooleanVariables, directivesBooleanVariables,
      directiveBooleanVariables, inputValueBooleanVariables,
      dedupBoolVars, boolVariableMem]
  have hiff :=
    computeOperationShape_denotesEquivalentPath_iff_operationSelectsPath
      NormalForm.groundTypingSchema
      NormalForm.completeNormalizationNestedDirectiveInputQuery shape
      nestedAbstractAssignment nestedAbstractSelectedPath hschema hvalid
      hcompute hcomplete
  exact ⟨hiff.mpr nestedAbstractFootprintSelectsPath,
    nestedAbstractFootprintSelectsPath, hiff.mp, hiff.mpr⟩

def twoArgumentFieldDefinition : FieldDefinition :=
  {
    name := "lookup"
    outputType := .named "String"
    arguments :=
      [
        { name := "first", inputType := .named "String" },
        { name := "second", inputType := .named "String" }
      ]
  }

def twoArgumentSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields := [twoArgumentFieldDefinition]
          }
      ]
  }

def storedArguments : List Argument :=
  [
    { name := "first", value := .string "one" },
    { name := "second", value := .string "two" }
  ]

def reorderedArguments : List Argument :=
  [
    { name := "second", value := .string "two" },
    { name := "first", value := .string "one" }
  ]

def argumentOrderOperation : Operation :=
  {
    name := some "ArgumentOrder"
    selectionSet :=
      [.field "lookup" "lookup" storedArguments [] []]
  }

private def twoArgumentQueryType : ObjectType :=
  { name := "Query", fields := [twoArgumentFieldDefinition] }

private theorem twoArgumentSchemaLookupQuery :
    twoArgumentSchema.lookupType "Query" =
      some (.object twoArgumentQueryType) := by
  simp [Schema.lookupType, Schema.allTypes,
    Schema.builtinScalarDefinitions, twoArgumentSchema,
    twoArgumentQueryType, TypeDefinition.name, BuiltinScalar.name, List.find?]

private theorem twoArgumentSchemaLookupString :
    twoArgumentSchema.lookupType "String" = some (.builtinScalar .string) := by
  simp [Schema.lookupType, Schema.allTypes,
    Schema.builtinScalarDefinitions, twoArgumentSchema,
    TypeDefinition.name, BuiltinScalar.name, List.find?]

private theorem twoArgumentSchemaQueryIsObject :
    twoArgumentSchema.objectType "Query" :=
  ⟨twoArgumentQueryType, twoArgumentSchemaLookupQuery⟩

private theorem twoArgumentSchemaStringIsInput :
    twoArgumentSchema.isInputType "String" :=
  ⟨.builtinScalar .string, twoArgumentSchemaLookupString, trivial⟩

private theorem twoArgumentSchemaStringIsLeaf :
    twoArgumentSchema.isLeafType "String" :=
  ⟨.builtinScalar .string, twoArgumentSchemaLookupString, trivial⟩

private theorem twoArgumentSchemaStringIsOutput :
    twoArgumentSchema.isOutputType "String" :=
  ⟨.builtinScalar .string, twoArgumentSchemaLookupString, trivial⟩

private theorem twoArgumentSchemaLookupMember
    {typeName : Name} {typeDefinition : TypeDefinition}
    (hlookup : twoArgumentSchema.lookupType typeName = some typeDefinition) :
    typeDefinition ∈ twoArgumentSchema.allTypes
      ∧ typeDefinition.name = typeName := by
  refine ⟨List.mem_of_find?_eq_some hlookup, ?_⟩
  simpa [beq_iff_eq] using List.find?_some hlookup

private theorem twoArgumentSchemaPossibleTypes {typeName : Name} :
    twoArgumentSchema.getPossibleTypes typeName = []
      ∨ (typeName = "Query"
        ∧ twoArgumentSchema.getPossibleTypes typeName = ["Query"]) := by
  cases hlookup : twoArgumentSchema.lookupType typeName with
  | none => exact .inl (by simp [Schema.getPossibleTypes, hlookup])
  | some typeDefinition =>
      rcases twoArgumentSchemaLookupMember hlookup with ⟨hmem, hname⟩
      simp only [Schema.allTypes, Schema.builtinScalarDefinitions,
        twoArgumentSchema, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h | h | h <;> subst h
      · exact .inl (by simp [Schema.getPossibleTypes, hlookup])
      · exact .inl (by simp [Schema.getPossibleTypes, hlookup])
      · exact .inl (by simp [Schema.getPossibleTypes, hlookup])
      · exact .inl (by simp [Schema.getPossibleTypes, hlookup])
      · exact .inl (by simp [Schema.getPossibleTypes, hlookup])
      · refine .inr ⟨?_, ?_⟩
        · simpa [twoArgumentQueryType, TypeDefinition.name] using hname.symm
        · simp [Schema.getPossibleTypes, hlookup]

theorem twoArgumentSchemaWellFormed :
    SchemaWellFormedness.schemaWellFormed twoArgumentSchema := by
  refine ⟨?_, ⟨twoArgumentQueryType, twoArgumentSchemaLookupQuery⟩,
    ?_, ?_, ?_, ?_⟩
  · simp only [SchemaWellFormedness.namesAreUnique, Schema.allTypes,
      Schema.builtinScalarDefinitions, twoArgumentSchema,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      TypeDefinition.name, BuiltinScalar.name]
    decide
  · intro typeDefinition hmem
    simp only [twoArgumentSchema, List.mem_singleton] at hmem
    subst hmem
    refine ⟨⟨by simp [SchemaWellFormedness.listNonempty], ?_, ?_⟩,
      ?_, ?_⟩
    · simp only [SchemaWellFormedness.namesAreUnique,
        twoArgumentFieldDefinition, List.map_cons, List.map_nil]
      decide
    · intro fieldDefinition hfield
      simp only [List.mem_singleton] at hfield
      subst hfield
      refine ⟨twoArgumentSchemaStringIsOutput, ?_, ?_⟩
      · simp [SchemaWellFormedness.namesAreUnique,
          twoArgumentFieldDefinition]
      · intro definition hdefinition
        simp only [twoArgumentFieldDefinition, List.mem_cons,
          List.not_mem_nil, or_false] at hdefinition
        rcases hdefinition with hdefinition | hdefinition <;>
          subst definition <;>
          exact ⟨twoArgumentSchemaStringIsInput, trivial⟩
    · simp [SchemaWellFormedness.namesAreUnique]
    · intro interfaceName hinterface
      simp at hinterface
  · intro typeName objectTypeName hmem
    rcases twoArgumentSchemaPossibleTypes (typeName := typeName) with
      hpossible | ⟨_, hpossible⟩ <;> rw [hpossible] at hmem
    · simp at hmem
    · simp only [List.mem_singleton] at hmem
      subst hmem
      exact twoArgumentSchemaQueryIsObject
  · intro typeName
    rcases twoArgumentSchemaPossibleTypes (typeName := typeName) with
      hpossible | ⟨_, hpossible⟩ <;> simp [hpossible]
  · intro parentType objectTypeName fieldName expected hmem hlookup
    rcases twoArgumentSchemaPossibleTypes (typeName := parentType) with
      hpossible | ⟨hquery, hpossible⟩
    · rw [hpossible] at hmem
      simp at hmem
    · subst hquery
      rw [hpossible] at hmem
      simp only [List.mem_singleton] at hmem
      subst hmem
      have hexpected :
          expected = twoArgumentFieldDefinition ∧ fieldName = "lookup" := by
        simp only [Schema.lookupField, twoArgumentSchemaLookupQuery, bind,
          Option.bind, TypeDefinition.fields?, twoArgumentQueryType,
          List.find?_cons, List.find?_nil] at hlookup
        split at hlookup
        · rename_i hname
          refine ⟨(Option.some.inj hlookup).symm, ?_⟩
          simp only [twoArgumentFieldDefinition, beq_iff_eq] at hname
          exact hname.symm
        · simp at hlookup
      rcases hexpected with ⟨hexpected, hfieldName⟩
      subst hexpected
      subst hfieldName
      refine ⟨twoArgumentFieldDefinition, hlookup, ?_, ?_⟩
      · refine ⟨.inl ⟨twoArgumentSchemaStringIsLeaf,
          twoArgumentSchemaStringIsLeaf, rfl⟩, ?_, ?_⟩
        · intro expectedDefinition hdefinition
          simp only [twoArgumentFieldDefinition, List.mem_cons,
            List.not_mem_nil, or_false] at hdefinition
          rcases hdefinition with hdefinition | hdefinition <;>
            subst expectedDefinition
          · refine ⟨{ name := "first", inputType := .named "String" }, ?_, rfl⟩
            simp [twoArgumentFieldDefinition,
              Schema.lookupArgumentDefinition]
          · refine ⟨{ name := "second", inputType := .named "String" }, ?_, rfl⟩
            simp [twoArgumentFieldDefinition,
              Schema.lookupArgumentDefinition]
        · intro implementationDefinition hdefinition _hmissing
          simp only [twoArgumentFieldDefinition, List.mem_cons,
            List.not_mem_nil, or_false] at hdefinition
          rcases hdefinition with hdefinition | hdefinition <;>
            subst implementationDefinition <;>
            simp [InputValueDefinition.isRequired]
      · exact ⟨twoArgumentSchemaStringIsOutput,
          twoArgumentSchemaStringIsOutput, fun _ => rfl⟩

private theorem twoArgumentSchemaLookupField :
    twoArgumentSchema.lookupField "Query" "lookup" =
      some twoArgumentFieldDefinition := by
  simp [Schema.lookupField, twoArgumentSchemaLookupQuery,
    TypeDefinition.fields?, twoArgumentQueryType,
    twoArgumentFieldDefinition, List.find?]

private theorem stringLiteralValidAtTwoArgumentSchema
    (value : String) :
    Validation.valueIsCorrectTypeAtLocation twoArgumentSchema []
      (.string value) (.named "String") none := by
  exact .namedNonInputObject (.string value) "String" none
    twoArgumentSchemaStringIsInput (by simp) (by simp) (by simp)
    (by simp [Schema.lookupInputObject, twoArgumentSchemaLookupString])

theorem argumentOrderOperationValid :
    Validation.operationDefinitionValid
      twoArgumentSchema argumentOrderOperation := by
  refine ⟨rfl,
    ⟨.object twoArgumentQueryType, twoArgumentSchemaLookupQuery, trivial⟩,
    ⟨by simp [argumentOrderOperation], ?_⟩,
    by simp [argumentOrderOperation], ?_, ?_, ?_⟩
  · intro variableDefinition hvariable
    simp [argumentOrderOperation] at hvariable
  · unfold Validation.selectionSetValid
    intro selection hselection
    simp only [argumentOrderOperation, List.mem_singleton] at hselection
    subst hselection
    have hroot : argumentOrderOperation.rootType twoArgumentSchema = "Query" :=
      rfl
    unfold Validation.selectionValid
    rw [hroot]
    refine ⟨⟨by simp, ?_⟩, twoArgumentFieldDefinition,
      twoArgumentSchemaLookupField, ?_, ?_⟩
    · intro directive hdirective
      simp at hdirective
    · refine ⟨?_, ?_, ?_⟩
      · simp [storedArguments]
      · intro argument hargument
        simp only [storedArguments, List.mem_cons, List.not_mem_nil,
          or_false] at hargument
        rcases hargument with hargument | hargument <;> subst argument
        · refine ⟨{ name := "first", inputType := .named "String" }, ?_,
              stringLiteralValidAtTwoArgumentSchema "one"⟩
          simp [twoArgumentFieldDefinition, Schema.lookupArgumentDefinition]
        · refine ⟨{ name := "second", inputType := .named "String" }, ?_,
              stringLiteralValidAtTwoArgumentSchema "two"⟩
          simp [twoArgumentFieldDefinition, Schema.lookupArgumentDefinition]
      · intro definition hdefinition hrequired
        simp only [twoArgumentFieldDefinition, List.mem_cons,
          List.not_mem_nil, or_false] at hdefinition
        rcases hdefinition with hdefinition | hdefinition <;>
          subst definition <;>
          simp [Validation.isRequiredArgument,
            Validation.isRequiredInputValueDefinition,
            InputValueDefinition.isRequired] at hrequired
    · unfold Validation.fieldSelectionSetValid
      exact ⟨twoArgumentSchemaStringIsOutput,
        .inl ⟨twoArgumentSchemaStringIsLeaf, rfl⟩⟩
  · have hcollect : FieldMerge.collectFields twoArgumentSchema
        (argumentOrderOperation.rootType twoArgumentSchema)
        argumentOrderOperation.selectionSet =
        [{ parentType := "Query", responseName := "lookup",
           fieldName := "lookup", arguments := storedArguments,
           outputType := .named "String", selectionSet := [] }] := by
      rw [show argumentOrderOperation.rootType twoArgumentSchema = "Query" from
        rfl]
      simp [FieldMerge.collectFields, argumentOrderOperation,
        twoArgumentSchemaLookupField, twoArgumentFieldDefinition]
    refine .intro _ _ (fun left hleft right hright _ => ?_)
    rw [hcollect] at hleft hright
    simp only [List.mem_singleton] at hleft hright
    subst hleft
    subst hright
    refine .intro _ _ ?_ ?_ ?_
    · exact ⟨twoArgumentSchemaStringIsOutput,
        twoArgumentSchemaStringIsOutput, fun _ => rfl⟩
    · intro _
      exact ⟨rfl,
        NormalForm.GroundTypeNormalization.argumentsEquivalent_refl
          storedArguments⟩
    · intro _ objectType
      exact .intro _ _ (fun left hleft =>
        False.elim (by simp [FieldMerge.collectFields] at hleft))
  · intro variableDefinition hvariable
    simp [argumentOrderOperation] at hvariable

def argumentOrderReorderedPath : List PathStep :=
  [{
    parentObject := "Query",
    responseName := "lookup",
    «field» := {
      fieldName := "lookup",
      arguments := reorderedArguments,
      outputType := .named "String"
    }
  }]

def argumentOrderComputedStoresSourceOrder : Bool :=
  match computeOperationShape twoArgumentSchema argumentOrderOperation with
  | .ok shape =>
      match shape.root.positions with
      | [position] =>
          match position.possibleDefinitions with
          | [possible] =>
              match possible.definitions with
              | [definition] =>
                  NormalForm.listEqBool NormalForm.argumentEqBool
                    definition.field.arguments storedArguments
              | _ => false
          | _ => false
      | _ => false
  | .error _ => false

private theorem argumentOrderComputedShapeRetainsSourceOrder :
    argumentOrderComputedStoresSourceOrder = true := by
  native_decide

theorem argumentOrderFootprintAcceptsReorderedPath :
    operationSelectsPath twoArgumentSchema argumentOrderOperation []
      argumentOrderReorderedPath := by
  simp [operationSelectsPath, argumentOrderReorderedPath,
    argumentOrderOperation, twoArgumentSchema, twoArgumentFieldDefinition,
    storedArguments, reorderedArguments, boolCaseVariableValues,
    Operation.rootType, OperationType.rootType, Schema.typeIncludesObject,
    Schema.getPossibleTypes, Schema.lookupField, Schema.lookupType,
    Schema.allTypes, Schema.builtinScalarDefinitions, List.find?,
    TypeDefinition.name, TypeDefinition.fields?, BuiltinScalar.name,
    Execution.collectFields, Execution.collectSelection,
    Execution.selectionDirectivesAllowBool, Execution.mergeExecutableGroups,
    collectedFieldsSelectPath, executableFieldMatchesPathStep,
    Argument.argumentsEquivalent, Argument.equivalent, InputValue.equivalent,
    InputValue.canonical, InputValue.structuralEquivalent]

/-- The computed shape retains the operation's concrete argument order and so
does not literally denote the reordered path accepted by field collection. -/
private theorem argumentOrderComputedShapeDoesNotDenoteReorderedPath
    (shape : OperationShape)
    (hcompute : computeOperationShape twoArgumentSchema argumentOrderOperation =
      .ok shape) :
    ¬ shape.root.DenotesPath twoArgumentSchema [] shape.rootType
      argumentOrderReorderedPath := by
  have hsource := argumentOrderComputedShapeRetainsSourceOrder
  rcases shape with ⟨operationType, rootType, boolSupport, root⟩
  cases root with
  | object positions =>
      simp only [argumentOrderComputedStoresSourceOrder, hcompute,
        ResponseShape.positions] at hsource
      cases positions with
      | nil => simp at hsource
      | cons position rest =>
          cases rest with
          | cons next tail => simp at hsource
          | nil =>
              rcases position with ⟨responseName, possibleDefinitions⟩
              cases possibleDefinitions with
              | nil =>
                  simp [ResponsePosition.possibleDefinitions] at hsource
              | cons possible rest =>
                  cases rest with
                  | cons next tail =>
                      simp [ResponsePosition.possibleDefinitions] at hsource
                  | nil =>
                      rcases possible with ⟨objectTypes, definitions⟩
                      cases definitions with
                      | nil =>
                          simp [ResponsePosition.possibleDefinitions,
                            PossibleDefinitions.definitions] at hsource
                      | cons definition rest =>
                          cases rest with
                          | cons next tail =>
                              simp [ResponsePosition.possibleDefinitions,
                                PossibleDefinitions.definitions] at hsource
                          | nil =>
                              simp only [ResponsePosition.possibleDefinitions,
                                PossibleDefinitions.definitions] at hsource
                              intro hdenotes
                              generalize hpath : argumentOrderReorderedPath = path
                                at hdenotes
                              cases hdenotes
                              case «field» =>
                                rename_i selectedPosition selectedPossible
                                  selectedDefinition runtimeObject possibleMem
                                  runtimeMem definitionMem clauseHolds
                                  runtimePossible positionMem
                                simp only [List.mem_singleton] at positionMem
                                subst selectedPosition
                                simp only [ResponsePosition.possibleDefinitions,
                                  List.mem_singleton] at possibleMem
                                subst selectedPossible
                                simp only [PossibleDefinitions.definitions,
                                  List.mem_singleton] at definitionMem
                                subst selectedDefinition
                                simp [argumentOrderReorderedPath] at hpath
                                have harguments := congrArg
                                  (fun head : FieldHead => head.arguments)
                                  hpath.2.2
                                rcases definition with ⟨clause, fieldHead,
                                  subshape⟩
                                rcases fieldHead with ⟨fieldName, arguments,
                                  outputType⟩
                                simp only [ShapeDefinition.field] at harguments
                                rw [← harguments] at hsource
                                simp [storedArguments, reorderedArguments,
                                  ShapeDefinition.field,
                                  NormalForm.listEqBool,
                                  NormalForm.argumentEqBool,
                                  NormalForm.inputValueEqBool] at hsource
                              case child =>
                                rename_i position possible selectedDefinition
                                  runtimeObject childShape childPath
                                  possibleMem runtimeMem definitionMem clauseHolds
                                  subshapeEq childDenotes runtimePossible positionMem
                                have hnonempty := childDenotes.nonempty
                                simp_all [argumentOrderReorderedPath,
                                  ResponsePosition.possibleDefinitions,
                                  PossibleDefinitions.definitions]

private theorem argumentOrderReorderedPathSeparatesFootprintFromExactShape :
    ∃ shape,
      computeOperationShape twoArgumentSchema argumentOrderOperation = .ok shape
      ∧ completeNormalBoolCase shape.boolSupport []
      ∧ operationSelectsPath twoArgumentSchema argumentOrderOperation []
          argumentOrderReorderedPath
      ∧ ¬ shape.root.DenotesPath twoArgumentSchema [] shape.rootType
          argumentOrderReorderedPath := by
  rcases computeOperationShape_total twoArgumentSchema argumentOrderOperation
      twoArgumentSchemaWellFormed argumentOrderOperationValid with
    ⟨shape, hcompute, _hwellFormed, _hfullMinterm, hsupport⟩
  have hcomplete : completeNormalBoolCase shape.boolSupport [] := by
    rw [hsupport]
    simp [completeNormalBoolCase, operationBoolVars, argumentOrderOperation,
      selectionSetBooleanVariables, selectionBooleanVariables,
      directivesBooleanVariables, dedupBoolVars]
  exact ⟨shape, hcompute, hcomplete,
    argumentOrderFootprintAcceptsReorderedPath,
    argumentOrderComputedShapeDoesNotDenoteReorderedPath shape hcompute⟩

end ResponseShape
end Tests
end GraphQL
