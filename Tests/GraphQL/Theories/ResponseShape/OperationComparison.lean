import Proofs.GraphQL.Theories.ResponseShape.Comparison.Operation
import Tests.GraphQL.Theories.ResponseShape.Correspondence

/-!
End-to-end guards for the source-operation comparator.

All fixtures use the established two-argument schema. Accepted pairs cover
selection order, argument order, Boolean directive-derived stem/support order,
and a genuine two-branch normalization permutation. Rejected pairs expose the
exact nested strict-comparison payload and are proved semantically distinct
under the normalizer's uniqueness premises.
-/

namespace GraphQL
namespace Tests
namespace ResponseShape
namespace OperationComparison

open GraphQL.ResponseShape

private def twoLookupOperation
    (operationName firstResponse secondResponse : Name)
    (arguments : List Argument)
    : Operation :=
  {
    name := some operationName
    selectionSet :=
      [
        .field firstResponse "lookup" arguments [] [],
        .field secondResponse "lookup" arguments [] []
      ]
  }

private def singleLookupOperation
    (operationName responseName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication := [])
    (variableDefinitions : List VariableDefinition := [])
    : Operation :=
  {
    name := some operationName
    variableDefinitions := variableDefinitions
    selectionSet := [.field responseName "lookup" arguments directives []]
  }

private def reorderedSelectionsLeft : Operation :=
  twoLookupOperation "ReorderedSelectionsLeft" "alpha" "beta" storedArguments

private def reorderedSelectionsRight : Operation :=
  twoLookupOperation "ReorderedSelectionsRight" "beta" "alpha" reorderedArguments

private def booleanVariableDefinitions : List VariableDefinition :=
  [NormalForm.booleanVariableDefinition "x", NormalForm.booleanVariableDefinition "y"]

private def booleanDirectivesLeft : Operation :=
  singleLookupOperation "BooleanDirectivesLeft" "lookup" storedArguments
    [.include (.variable "x"), .skip (.variable "y")]
    booleanVariableDefinitions

private def booleanDirectivesRight : Operation :=
  singleLookupOperation "BooleanDirectivesRight" "lookup" storedArguments
    [.skip (.variable "y"), .include (.variable "x")]
    booleanVariableDefinitions

private def reversedBooleanVariableDefinitions : List VariableDefinition :=
  [NormalForm.booleanVariableDefinition "y", NormalForm.booleanVariableDefinition "x"]

private def twoDirectedLookupOperation
    (operationName : Name) (variableDefinitions : List VariableDefinition)
    (alphaDirectives betaDirectives : List DirectiveApplication)
    : Operation :=
  {
    name := some operationName
    variableDefinitions := variableDefinitions
    selectionSet :=
      [
        .field "alpha" "lookup" storedArguments alphaDirectives [],
        .field "beta" "lookup" storedArguments betaDirectives []
      ]
  }

private def twoBranchBooleanPermutationLeft : Operation :=
  twoDirectedLookupOperation "TwoBranchBooleanPermutationLeft"
    booleanVariableDefinitions
    [.include (.variable "x"), .skip (.variable "y")]
    [.skip (.variable "x"), .include (.variable "y")]

private def twoBranchBooleanPermutationRight : Operation :=
  twoDirectedLookupOperation "TwoBranchBooleanPermutationRight"
    reversedBooleanVariableDefinitions
    [.skip (.variable "y"), .include (.variable "x")]
    [.include (.variable "y"), .skip (.variable "x")]

private def twoBranchBooleanPermutationLeftBranches : List Selection :=
  [
    .inlineFragment none [.skip (.variable "x")]
      [.inlineFragment none [.include (.variable "y")]
        [.field "beta" "lookup" storedArguments [] []]],
    .inlineFragment none [.include (.variable "x")]
      [.inlineFragment none [.skip (.variable "y")]
        [.field "alpha" "lookup" storedArguments [] []]]
  ]

private def twoBranchBooleanPermutationRightBranches : List Selection :=
  [
    .inlineFragment none [.skip (.variable "y")]
      [.inlineFragment none [.include (.variable "x")]
        [.field "alpha" "lookup" storedArguments [] []]],
    .inlineFragment none [.include (.variable "y")]
      [.inlineFragment none [.skip (.variable "x")]
        [.field "beta" "lookup" storedArguments [] []]]
  ]

private def aliasedLeft : Operation :=
  singleLookupOperation "AliasedLeft" "lookup" storedArguments

private def aliasedRight : Operation :=
  singleLookupOperation "AliasedRight" "renamed" storedArguments

private def changedArguments : List Argument :=
  [
    { name := "first", value := .string "one" },
    { name := "second", value := .string "changed" }
  ]

private def storedArgumentOperation : Operation :=
  singleLookupOperation "StoredArguments" "lookup" storedArguments

private def changedArgumentOperation : Operation :=
  singleLookupOperation "ChangedArguments" "lookup" changedArguments

private def leafShapePosition
    (responseName : Name) (arguments : List Argument)
    (literals : List BoolLiteral := [])
    : ResponsePosition :=
  .mk responseName
    [.mk ["Query"]
      [.mk { literals := literals }
        {
          fieldName := "lookup"
          arguments := arguments
          outputType := .named "String"
        }
        none]]

private def leafOperationShape
    (support : List NormalForm.BoolVar)
    (positions : List ResponsePosition)
    : OperationShape :=
  {
    operationType := .query
    rootType := "Query"
    boolSupport := support
    root := .object positions
  }

private def reorderedSelectionsLeftShape : OperationShape :=
  leafOperationShape []
    [leafShapePosition "alpha" storedArguments, leafShapePosition "beta" storedArguments]

private def reorderedSelectionsRightShape : OperationShape :=
  leafOperationShape []
    [
      leafShapePosition "beta" reorderedArguments,
      leafShapePosition "alpha" reorderedArguments
    ]

private def booleanDirectivesLeftShape : OperationShape :=
  leafOperationShape ["x", "y"]
    [leafShapePosition "lookup" storedArguments [("x", true), ("y", false)]]

private def booleanDirectivesRightShape : OperationShape :=
  leafOperationShape ["y", "x"]
    [leafShapePosition "lookup" storedArguments [("x", true), ("y", false)]]

private def twoBranchBooleanPermutationLeftShape : OperationShape :=
  leafOperationShape ["x", "y"]
    [
      leafShapePosition "beta" storedArguments [("x", false), ("y", true)],
      leafShapePosition "alpha" storedArguments [("x", true), ("y", false)]
    ]

private def twoBranchBooleanPermutationRightShape : OperationShape :=
  leafOperationShape ["y", "x"]
    [
      leafShapePosition "alpha" storedArguments [("x", true), ("y", false)],
      leafShapePosition "beta" storedArguments [("x", false), ("y", true)]
    ]

private def aliasedLeftShape : OperationShape :=
  leafOperationShape [] [leafShapePosition "lookup" storedArguments]

private def aliasedRightShape : OperationShape :=
  leafOperationShape [] [leafShapePosition "renamed" storedArguments]

private def storedArgumentShape : OperationShape :=
  leafOperationShape [] [leafShapePosition "lookup" storedArguments]

private def changedArgumentShape : OperationShape :=
  leafOperationShape [] [leafShapePosition "lookup" changedArguments]

private def localQueryType : ObjectType :=
  { name := "Query", fields := [twoArgumentFieldDefinition] }

private theorem schemaLookupQuery
    : twoArgumentSchema.lookupType "Query" = some (.object localQueryType) := by
  simp [Schema.lookupType, Schema.allTypes,
    Schema.builtinScalarDefinitions, twoArgumentSchema, localQueryType,
    TypeDefinition.name, BuiltinScalar.name, List.find?]

private theorem schemaLookupString
    : twoArgumentSchema.lookupType "String" = some (.builtinScalar .string) := by
  simp [Schema.lookupType, Schema.allTypes,
    Schema.builtinScalarDefinitions, twoArgumentSchema,
    TypeDefinition.name, BuiltinScalar.name, List.find?]

private theorem schemaLookupBoolean
    : twoArgumentSchema.lookupType "Boolean" = some (.builtinScalar .boolean) := by
  simp [Schema.lookupType, Schema.allTypes,
    Schema.builtinScalarDefinitions, twoArgumentSchema,
    TypeDefinition.name, BuiltinScalar.name, List.find?]

private theorem schemaStringIsInput : twoArgumentSchema.isInputType "String" :=
  ⟨.builtinScalar .string, schemaLookupString, trivial⟩

private theorem schemaStringIsLeaf : twoArgumentSchema.isLeafType "String" :=
  ⟨.builtinScalar .string, schemaLookupString, trivial⟩

private theorem schemaStringIsOutput : twoArgumentSchema.isOutputType "String" :=
  ⟨.builtinScalar .string, schemaLookupString, trivial⟩

private theorem schemaBooleanIsInput : twoArgumentSchema.isInputType "Boolean" :=
  ⟨.builtinScalar .boolean, schemaLookupBoolean, trivial⟩

private theorem schemaLookupField
    : twoArgumentSchema.lookupField "Query" "lookup"
      = some twoArgumentFieldDefinition := by
  simp [Schema.lookupField, schemaLookupQuery, TypeDefinition.fields?,
    localQueryType, twoArgumentFieldDefinition, List.find?]

private theorem stringLiteralValid
    (variableDefinitions : List VariableDefinition) (value : String)
    : Validation.valueIsCorrectTypeAtLocation twoArgumentSchema variableDefinitions
        (.string value) (.named "String") none := by
  exact .namedNonInputObject (.string value) "String" none
    schemaStringIsInput (by simp) (by simp) (by simp)
    (by simp [Schema.lookupInputObject, schemaLookupString])

private theorem orderedArgumentsValid
    (variableDefinitions : List VariableDefinition)
    (firstValue secondValue : String)
    : Validation.argumentsValid twoArgumentSchema
        twoArgumentFieldDefinition.arguments variableDefinitions
        [
          { name := "first", value := .string firstValue },
          { name := "second", value := .string secondValue }
        ] := by
  refine ⟨by simp, ?_, ?_⟩
  · intro argument hargument
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hargument
    rcases hargument with hargument | hargument <;> subst argument
    · exact ⟨{ name := "first", inputType := .named "String" },
        by simp [twoArgumentFieldDefinition, Schema.lookupArgumentDefinition],
        stringLiteralValid variableDefinitions firstValue⟩
    · exact ⟨{ name := "second", inputType := .named "String" },
        by simp [twoArgumentFieldDefinition, Schema.lookupArgumentDefinition],
        stringLiteralValid variableDefinitions secondValue⟩
  · intro definition hdefinition hrequired
    simp only [twoArgumentFieldDefinition, List.mem_cons,
      List.not_mem_nil, or_false] at hdefinition
    rcases hdefinition with hdefinition | hdefinition <;>
      subst definition <;>
      simp [Validation.isRequiredArgument,
        Validation.isRequiredInputValueDefinition,
        InputValueDefinition.isRequired] at hrequired

private theorem reorderedArgumentsValid
    (variableDefinitions : List VariableDefinition)
    (firstValue secondValue : String)
    : Validation.argumentsValid twoArgumentSchema
        twoArgumentFieldDefinition.arguments variableDefinitions
        [
          { name := "second", value := .string secondValue },
          { name := "first", value := .string firstValue }
        ] := by
  refine ⟨by simp, ?_, ?_⟩
  · intro argument hargument
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hargument
    rcases hargument with hargument | hargument <;> subst argument
    · exact ⟨{ name := "second", inputType := .named "String" },
        by simp [twoArgumentFieldDefinition, Schema.lookupArgumentDefinition],
        stringLiteralValid variableDefinitions secondValue⟩
    · exact ⟨{ name := "first", inputType := .named "String" },
        by simp [twoArgumentFieldDefinition, Schema.lookupArgumentDefinition],
        stringLiteralValid variableDefinitions firstValue⟩
  · intro definition hdefinition hrequired
    simp only [twoArgumentFieldDefinition, List.mem_cons,
      List.not_mem_nil, or_false] at hdefinition
    rcases hdefinition with hdefinition | hdefinition <;>
      subst definition <;>
      simp [Validation.isRequiredArgument,
        Validation.isRequiredInputValueDefinition,
        InputValueDefinition.isRequired] at hrequired

private theorem lookupSelectionValid
    (responseName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (variableDefinitions : List VariableDefinition)
    (harguments
      : Validation.argumentsValid twoArgumentSchema
          twoArgumentFieldDefinition.arguments variableDefinitions arguments)
    (hdirectives
      : Validation.directivesValid twoArgumentSchema variableDefinitions directives)
    : Validation.selectionValid twoArgumentSchema variableDefinitions "Query"
        (.field responseName "lookup" arguments directives []) := by
  unfold Validation.selectionValid
  refine ⟨hdirectives, twoArgumentFieldDefinition, schemaLookupField,
    harguments, ?_⟩
  unfold Validation.fieldSelectionSetValid
  exact ⟨schemaStringIsOutput, .inl ⟨schemaStringIsLeaf, rfl⟩⟩

private def scopedLookup (responseName : Name) (arguments : List Argument)
    : FieldMerge.ScopedField :=
  {
    parentType := "Query"
    responseName := responseName
    fieldName := "lookup"
    arguments := arguments
    outputType := .named "String"
    selectionSet := []
  }

private theorem scopedLookupSelfMerge (responseName : Name) (arguments : List Argument)
    : FieldMerge.fieldsForNameCanMerge twoArgumentSchema
        (scopedLookup responseName arguments) (scopedLookup responseName arguments) := by
  refine .intro _ _ ?_ ?_ ?_
  · exact ⟨schemaStringIsOutput, schemaStringIsOutput, fun _ => rfl⟩
  · intro _
    exact ⟨rfl,
      NormalForm.GroundTypeNormalization.argumentsEquivalent_refl arguments⟩
  · intro _ objectType
    exact .intro _ _ (fun left hleft =>
      False.elim (by
        simp [scopedLookup, FieldMerge.collectFields] at hleft))

private theorem twoLookupOperationValid
    (operationName firstResponse secondResponse : Name)
    (arguments : List Argument)
    (harguments
      : Validation.argumentsValid twoArgumentSchema
          twoArgumentFieldDefinition.arguments [] arguments)
    (hdifferent : firstResponse ≠ secondResponse)
    : Validation.operationDefinitionValid twoArgumentSchema
        (twoLookupOperation operationName firstResponse secondResponse arguments) := by
  refine ⟨rfl, ⟨.object localQueryType, schemaLookupQuery, trivial⟩,
    by simp [twoLookupOperation, Validation.variableDefinitionsValid],
    by simp [twoLookupOperation], ?_, ?_,
    by simp [twoLookupOperation, Validation.operationVariablesUsed]⟩
  · unfold Validation.selectionSetValid
    intro selection hselection
    simp only [twoLookupOperation, List.mem_cons,
      List.not_mem_nil, or_false] at hselection
    rcases hselection with hselection | hselection <;> subst selection <;>
      exact lookupSelectionValid _ arguments [] [] harguments
        (by simp [Validation.directivesValid])
  · refine .intro _ _ (fun left hleft right hright hresponse => ?_)
    change left ∈ FieldMerge.collectFields twoArgumentSchema "Query"
      (twoLookupOperation operationName firstResponse secondResponse arguments).selectionSet
      at hleft
    change right ∈ FieldMerge.collectFields twoArgumentSchema "Query"
      (twoLookupOperation operationName firstResponse secondResponse arguments).selectionSet
      at hright
    simp [twoLookupOperation, FieldMerge.collectFields, schemaLookupField,
      twoArgumentFieldDefinition] at hleft hright
    rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl
    · exact scopedLookupSelfMerge firstResponse arguments
    · exact False.elim (hdifferent (by simpa [scopedLookup] using hresponse))
    · exact False.elim (hdifferent (by simpa [scopedLookup] using hresponse.symm))
    · exact scopedLookupSelfMerge secondResponse arguments

private theorem singleLookupOperationValid
    (operationName responseName : Name) (arguments : List Argument)
    (harguments
      : Validation.argumentsValid twoArgumentSchema
          twoArgumentFieldDefinition.arguments [] arguments)
    : Validation.operationDefinitionValid twoArgumentSchema
        (singleLookupOperation operationName responseName arguments) := by
  refine ⟨rfl, ⟨.object localQueryType, schemaLookupQuery, trivial⟩,
    by simp [singleLookupOperation, Validation.variableDefinitionsValid],
    by simp [singleLookupOperation], ?_, ?_,
    by simp [singleLookupOperation, Validation.operationVariablesUsed]⟩
  · unfold Validation.selectionSetValid
    intro selection hselection
    simp only [singleLookupOperation, List.mem_singleton] at hselection
    subst selection
    exact lookupSelectionValid responseName arguments [] [] harguments
      (by simp [Validation.directivesValid])
  · refine .intro _ _ (fun left hleft right hright _ => ?_)
    change left ∈ FieldMerge.collectFields twoArgumentSchema "Query"
      (singleLookupOperation operationName responseName arguments).selectionSet
      at hleft
    change right ∈ FieldMerge.collectFields twoArgumentSchema "Query"
      (singleLookupOperation operationName responseName arguments).selectionSet
      at hright
    simp [singleLookupOperation, FieldMerge.collectFields, schemaLookupField,
      twoArgumentFieldDefinition] at hleft hright
    subst left
    subst right
    exact scopedLookupSelfMerge responseName arguments

private theorem booleanVariableDefinitionsValid
    : Validation.variableDefinitionsValid twoArgumentSchema
        booleanVariableDefinitions := by
  refine ⟨by simp [booleanVariableDefinitions,
    NormalForm.booleanVariableDefinition], ?_⟩
  intro variableDefinition hvariable
  simp only [booleanVariableDefinitions, List.mem_cons,
    List.not_mem_nil, or_false] at hvariable
  rcases hvariable with hvariable | hvariable <;>
    subst variableDefinition <;>
    exact ⟨schemaBooleanIsInput, trivial⟩

private theorem reversedBooleanVariableDefinitionsValid
    : Validation.variableDefinitionsValid twoArgumentSchema
        reversedBooleanVariableDefinitions := by
  refine ⟨by simp [reversedBooleanVariableDefinitions,
    NormalForm.booleanVariableDefinition], ?_⟩
  intro variableDefinition hvariable
  simp only [reversedBooleanVariableDefinitions, List.mem_cons,
    List.not_mem_nil, or_false] at hvariable
  rcases hvariable with hvariable | hvariable <;>
    subst variableDefinition <;>
    exact ⟨schemaBooleanIsInput, trivial⟩

private theorem booleanIfArgumentValid
    (varName : Name)
    (hlookup
      : Validation.getVariableDefinition? booleanVariableDefinitions varName
        = some (NormalForm.booleanVariableDefinition varName))
    : Validation.directiveIfArgumentValid twoArgumentSchema
        booleanVariableDefinitions (.variable varName) := by
  refine ⟨NormalForm.booleanVariableDefinition varName, hlookup, ?_⟩
  exact ⟨schemaBooleanIsInput, schemaBooleanIsInput, rfl⟩

private theorem reversedBooleanIfArgumentValid
    (varName : Name)
    (hlookup
      : Validation.getVariableDefinition? reversedBooleanVariableDefinitions varName
        = some (NormalForm.booleanVariableDefinition varName))
    : Validation.directiveIfArgumentValid twoArgumentSchema
        reversedBooleanVariableDefinitions (.variable varName) := by
  refine ⟨NormalForm.booleanVariableDefinition varName, hlookup, ?_⟩
  exact ⟨schemaBooleanIsInput, schemaBooleanIsInput, rfl⟩

private theorem leftDirectivesValid
    : Validation.directivesValid twoArgumentSchema booleanVariableDefinitions
        [.include (.variable "x"), .skip (.variable "y")] := by
  refine ⟨by decide, ?_⟩
  intro directive hdirective
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdirective
  rcases hdirective with hdirective | hdirective <;> subst directive
  · exact booleanIfArgumentValid "x"
      (by simp [booleanVariableDefinitions,
        NormalForm.booleanVariableDefinition,
        Validation.getVariableDefinition?])
  · exact booleanIfArgumentValid "y"
      (by simp [booleanVariableDefinitions,
        NormalForm.booleanVariableDefinition,
        Validation.getVariableDefinition?])

private theorem rightDirectivesValid
    : Validation.directivesValid twoArgumentSchema booleanVariableDefinitions
        [.skip (.variable "y"), .include (.variable "x")] := by
  refine ⟨by decide, ?_⟩
  intro directive hdirective
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdirective
  rcases hdirective with hdirective | hdirective <;> subst directive
  · exact booleanIfArgumentValid "y"
      (by simp [booleanVariableDefinitions,
        NormalForm.booleanVariableDefinition,
        Validation.getVariableDefinition?])
  · exact booleanIfArgumentValid "x"
      (by simp [booleanVariableDefinitions,
        NormalForm.booleanVariableDefinition,
        Validation.getVariableDefinition?])

private theorem leftOppositeMintermDirectivesValid
    : Validation.directivesValid twoArgumentSchema booleanVariableDefinitions
        [.skip (.variable "x"), .include (.variable "y")] := by
  refine ⟨by decide, ?_⟩
  intro directive hdirective
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdirective
  rcases hdirective with hdirective | hdirective <;> subst directive
  · exact booleanIfArgumentValid "x"
      (by simp [booleanVariableDefinitions,
        NormalForm.booleanVariableDefinition,
        Validation.getVariableDefinition?])
  · exact booleanIfArgumentValid "y"
      (by simp [booleanVariableDefinitions,
        NormalForm.booleanVariableDefinition,
        Validation.getVariableDefinition?])

private theorem rightFirstMintermDirectivesValid
    : Validation.directivesValid twoArgumentSchema
        reversedBooleanVariableDefinitions
        [.skip (.variable "y"), .include (.variable "x")] := by
  refine ⟨by decide, ?_⟩
  intro directive hdirective
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdirective
  rcases hdirective with hdirective | hdirective <;> subst directive
  · exact reversedBooleanIfArgumentValid "y"
      (by simp [reversedBooleanVariableDefinitions,
        NormalForm.booleanVariableDefinition,
        Validation.getVariableDefinition?])
  · exact reversedBooleanIfArgumentValid "x"
      (by simp [reversedBooleanVariableDefinitions,
        NormalForm.booleanVariableDefinition,
        Validation.getVariableDefinition?])

private theorem rightOppositeMintermDirectivesValid
    : Validation.directivesValid twoArgumentSchema
        reversedBooleanVariableDefinitions
        [.include (.variable "y"), .skip (.variable "x")] := by
  refine ⟨by decide, ?_⟩
  intro directive hdirective
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdirective
  rcases hdirective with hdirective | hdirective <;> subst directive
  · exact reversedBooleanIfArgumentValid "y"
      (by simp [reversedBooleanVariableDefinitions,
        NormalForm.booleanVariableDefinition,
        Validation.getVariableDefinition?])
  · exact reversedBooleanIfArgumentValid "x"
      (by simp [reversedBooleanVariableDefinitions,
        NormalForm.booleanVariableDefinition,
        Validation.getVariableDefinition?])

private theorem booleanOperationValid
    (operationName : Name) (directives : List DirectiveApplication)
    (hdirectives
      : Validation.directivesValid twoArgumentSchema
          booleanVariableDefinitions directives)
    (hused
      : Validation.operationVariablesUsed
          (singleLookupOperation operationName "lookup" storedArguments
            directives booleanVariableDefinitions))
    : Validation.operationDefinitionValid twoArgumentSchema
        (singleLookupOperation operationName "lookup" storedArguments
          directives booleanVariableDefinitions) := by
  have harguments : Validation.argumentsValid twoArgumentSchema
      twoArgumentFieldDefinition.arguments booleanVariableDefinitions
      storedArguments := by
    simpa [storedArguments] using
      (orderedArgumentsValid booleanVariableDefinitions "one" "two")
  refine ⟨rfl, ⟨.object localQueryType, schemaLookupQuery, trivial⟩,
    booleanVariableDefinitionsValid,
    by simp [singleLookupOperation], ?_, ?_, hused⟩
  · unfold Validation.selectionSetValid
    intro selection hselection
    simp only [singleLookupOperation, List.mem_singleton] at hselection
    subst selection
    exact lookupSelectionValid "lookup" storedArguments directives
      booleanVariableDefinitions harguments hdirectives
  · refine .intro _ _ (fun left hleft right hright _ => ?_)
    change left ∈ FieldMerge.collectFields twoArgumentSchema "Query"
      (singleLookupOperation operationName "lookup" storedArguments
        directives booleanVariableDefinitions).selectionSet at hleft
    change right ∈ FieldMerge.collectFields twoArgumentSchema "Query"
      (singleLookupOperation operationName "lookup" storedArguments
        directives booleanVariableDefinitions).selectionSet at hright
    simp [singleLookupOperation, FieldMerge.collectFields, schemaLookupField,
      twoArgumentFieldDefinition] at hleft hright
    subst left
    subst right
    exact scopedLookupSelfMerge "lookup" storedArguments

private theorem twoDirectedLookupOperationValid
    (operationName : Name) (variableDefinitions : List VariableDefinition)
    (alphaDirectives betaDirectives : List DirectiveApplication)
    (hdefinitions
      : Validation.variableDefinitionsValid twoArgumentSchema variableDefinitions)
    (halpha
      : Validation.directivesValid twoArgumentSchema variableDefinitions
          alphaDirectives)
    (hbeta
      : Validation.directivesValid twoArgumentSchema variableDefinitions
          betaDirectives)
    (hused
      : Validation.operationVariablesUsed
          (twoDirectedLookupOperation operationName variableDefinitions
            alphaDirectives betaDirectives))
    : Validation.operationDefinitionValid twoArgumentSchema
        (twoDirectedLookupOperation operationName variableDefinitions
          alphaDirectives betaDirectives) := by
  have harguments : Validation.argumentsValid twoArgumentSchema
      twoArgumentFieldDefinition.arguments variableDefinitions storedArguments := by
    simpa [storedArguments] using
      (orderedArgumentsValid variableDefinitions "one" "two")
  refine ⟨rfl, ⟨.object localQueryType, schemaLookupQuery, trivial⟩,
    hdefinitions, by simp [twoDirectedLookupOperation], ?_, ?_, hused⟩
  · unfold Validation.selectionSetValid
    intro selection hselection
    simp only [twoDirectedLookupOperation, List.mem_cons,
      List.not_mem_nil, or_false] at hselection
    rcases hselection with hselection | hselection <;> subst selection
    · exact lookupSelectionValid "alpha" storedArguments alphaDirectives
        variableDefinitions harguments halpha
    · exact lookupSelectionValid "beta" storedArguments betaDirectives
        variableDefinitions harguments hbeta
  · refine .intro _ _ (fun left hleft right hright hresponse => ?_)
    change left ∈ FieldMerge.collectFields twoArgumentSchema "Query"
      (twoDirectedLookupOperation operationName variableDefinitions
        alphaDirectives betaDirectives).selectionSet at hleft
    change right ∈ FieldMerge.collectFields twoArgumentSchema "Query"
      (twoDirectedLookupOperation operationName variableDefinitions
        alphaDirectives betaDirectives).selectionSet at hright
    simp [twoDirectedLookupOperation, FieldMerge.collectFields,
      schemaLookupField, twoArgumentFieldDefinition] at hleft hright
    rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl
    · exact scopedLookupSelfMerge "alpha" storedArguments
    · simp at hresponse
    · simp at hresponse
    · exact scopedLookupSelfMerge "beta" storedArguments

private theorem twoBranchBooleanPermutationLeftValid
    : Validation.operationDefinitionValid twoArgumentSchema
        twoBranchBooleanPermutationLeft := by
  apply twoDirectedLookupOperationValid
  · exact booleanVariableDefinitionsValid
  · exact leftDirectivesValid
  · exact leftOppositeMintermDirectivesValid
  · intro variableDefinition hvariable
    simp only [twoDirectedLookupOperation, booleanVariableDefinitions, List.mem_cons,
      List.not_mem_nil, or_false] at hvariable
    rcases hvariable with hvariable | hvariable <;>
      subst variableDefinition <;>
      simp [twoDirectedLookupOperation, storedArguments,
        Validation.selectionSetVariables, Validation.selectionVariables,
        Validation.argumentsVariables, Validation.argumentVariables,
        Validation.inputValueVariables, Validation.directivesVariables,
        Validation.directiveVariables, NormalForm.booleanVariableDefinition]

private theorem twoBranchBooleanPermutationRightValid
    : Validation.operationDefinitionValid twoArgumentSchema
        twoBranchBooleanPermutationRight := by
  apply twoDirectedLookupOperationValid
  · exact reversedBooleanVariableDefinitionsValid
  · exact rightFirstMintermDirectivesValid
  · exact rightOppositeMintermDirectivesValid
  · intro variableDefinition hvariable
    simp only [twoDirectedLookupOperation, reversedBooleanVariableDefinitions,
      List.mem_cons, List.not_mem_nil, or_false] at hvariable
    rcases hvariable with hvariable | hvariable <;>
      subst variableDefinition <;>
      simp [twoDirectedLookupOperation, storedArguments,
        Validation.selectionSetVariables, Validation.selectionVariables,
        Validation.argumentsVariables, Validation.argumentVariables,
        Validation.inputValueVariables, Validation.directivesVariables,
        Validation.directiveVariables, NormalForm.booleanVariableDefinition]

private theorem booleanDirectivesLeftValid
    : Validation.operationDefinitionValid twoArgumentSchema booleanDirectivesLeft := by
  apply booleanOperationValid
  · exact leftDirectivesValid
  · intro variableDefinition hvariable
    simp only [singleLookupOperation, booleanVariableDefinitions,
      List.mem_cons, List.not_mem_nil, or_false] at hvariable
    rcases hvariable with hvariable | hvariable <;> subst variableDefinition <;>
      simp [singleLookupOperation, storedArguments,
        Validation.selectionSetVariables, Validation.selectionVariables,
        Validation.argumentsVariables, Validation.argumentVariables,
        Validation.inputValueVariables, Validation.directivesVariables,
        Validation.directiveVariables, NormalForm.booleanVariableDefinition]

private theorem booleanDirectivesRightValid
    : Validation.operationDefinitionValid twoArgumentSchema booleanDirectivesRight := by
  apply booleanOperationValid
  · exact rightDirectivesValid
  · intro variableDefinition hvariable
    simp only [singleLookupOperation, booleanVariableDefinitions,
      List.mem_cons, List.not_mem_nil, or_false] at hvariable
    rcases hvariable with hvariable | hvariable <;> subst variableDefinition <;>
      simp [singleLookupOperation, storedArguments,
        Validation.selectionSetVariables, Validation.selectionVariables,
        Validation.argumentsVariables, Validation.argumentVariables,
        Validation.inputValueVariables, Validation.directivesVariables,
        Validation.directiveVariables, NormalForm.booleanVariableDefinition]

private theorem accepted_of_concrete_shapes
    (left right : Operation) (leftShape rightShape : OperationShape)
    (hleftCompute : computeOperationShape twoArgumentSchema left = .ok leftShape)
    (hrightCompute : computeOperationShape twoArgumentSchema right = .ok rightShape)
    (hready : ShapeComparisonReady twoArgumentSchema leftShape rightShape)
    (hstrict : StrictShapeEquivalent twoArgumentSchema leftShape rightShape)
    : ∃ proof basis,
        decideOperationEquivalence twoArgumentSchema left right
        = CertifiedVerdict.accepted proof basis := by
  exact (decideOperationEquivalence_accepted_iff_of_computed
    hleftCompute hrightCompute hready).mpr hstrict

private def expectedPath (responseName : Name) (arguments : List Argument)
    : List PathStep :=
  [{
    parentObject := "Query"
    responseName := responseName
    «field» :=
      {
        fieldName := "lookup"
        arguments := arguments
        outputType := .named "String"
      }
  }]

private theorem computeSingleLookupOperationShape
    (operationName responseName : Name) (arguments : List Argument)
    : computeOperationShape twoArgumentSchema
        (singleLookupOperation operationName responseName arguments)
      = .ok (leafOperationShape [] [leafShapePosition responseName arguments]) := by
  simp [computeOperationShape, NormalForm.completeNormalizeOperation,
    NormalForm.operationBoolVars, NormalForm.selectionSetBooleanVariables,
    NormalForm.selectionBooleanVariables, NormalForm.directivesBooleanVariables,
    NormalForm.dedupBoolVars, NormalForm.completeNormalizeRootSelectionSet,
    NormalForm.allBoolCases, NormalForm.normalizeSelectionSet.eq_1,
    NormalForm.normalizeSelectionSet.eq_2,
    NormalForm.withoutFieldSelectionsWithResponseName,
    NormalForm.fieldSelectionsWithResponseNameInScope,
    NormalForm.mergeSelectionSets, NormalForm.normalizedField,
    NormalForm.filterSelectionSetBoolCase, NormalForm.wrapWithBoolCase,
    NormalForm.directivesAllowIn, Operation.rootType, OperationType.rootType,
    decodeCompleteOperationShape, decodeCompleteRoot,
    foldGroundSelectionSet.eq_1, foldGroundSelectionSet.eq_2,
    singletonDefinitionShape, mergeResponseShapes,
    singleLookupOperation, leafOperationShape, leafShapePosition,
    twoArgumentSchema, twoArgumentFieldDefinition,
    NormalForm.objectTypeNameBool, NormalForm.leafTypeNameBool,
    TypeRef.isCompositeBool, TypeRef.namedType, Schema.getPossibleTypes,
    Schema.lookupType, Schema.lookupField, Schema.allTypes,
    Schema.builtinScalarDefinitions, TypeDefinition.name,
    TypeDefinition.fields?, BuiltinScalar.name, List.find?] <;> rfl

private theorem twoBranchBooleanPermutationLeftSupport
    : NormalForm.operationBoolVars twoBranchBooleanPermutationLeft = ["x", "y"] := by
  rfl

private theorem twoBranchBooleanPermutationRightSupport
    : NormalForm.operationBoolVars twoBranchBooleanPermutationRight = ["y", "x"] := by
  rfl

private theorem twoBranchBooleanPermutationLeftNormalized
    : (NormalForm.completeNormalizeOperation twoArgumentSchema
        twoBranchBooleanPermutationLeft).selectionSet
      = twoBranchBooleanPermutationLeftBranches := by
  simp [NormalForm.completeNormalizeOperation,
    NormalForm.operationBoolVars, NormalForm.selectionSetBooleanVariables,
    NormalForm.selectionBooleanVariables, NormalForm.directivesBooleanVariables,
    NormalForm.directiveBooleanVariables,
    NormalForm.inputValueBooleanVariables,
    NormalForm.dedupBoolVars, NormalForm.boolVariableMem,
    NormalForm.completeNormalizeRootSelectionSet,
    NormalForm.allBoolCases, NormalForm.normalizeSelectionSet.eq_1,
    NormalForm.normalizeSelectionSet.eq_2,
    NormalForm.withoutFieldSelectionsWithResponseName,
    NormalForm.fieldSelectionsWithResponseNameInScope,
    NormalForm.mergeSelectionSets, NormalForm.normalizedField,
    NormalForm.filterSelectionSetBoolCase, NormalForm.wrapWithBoolCase,
    NormalForm.directivesAllowIn, NormalForm.directiveAllowsIn,
    NormalForm.inputValueBoolIn?, NormalForm.BoolCase.lookup?,
    NormalForm.directiveForBit, Operation.rootType, OperationType.rootType,
    twoBranchBooleanPermutationLeft,
    twoBranchBooleanPermutationLeftBranches, twoDirectedLookupOperation,
    storedArguments, twoArgumentSchema, twoArgumentFieldDefinition,
    NormalForm.objectTypeNameBool, TypeRef.namedType, Schema.getPossibleTypes,
    Schema.lookupType, Schema.lookupField, Schema.allTypes,
    Schema.builtinScalarDefinitions, TypeDefinition.name,
    TypeDefinition.fields?, BuiltinScalar.name, List.find?] <;> rfl

private theorem twoBranchBooleanPermutationRightNormalized
    : (NormalForm.completeNormalizeOperation twoArgumentSchema
        twoBranchBooleanPermutationRight).selectionSet
      = twoBranchBooleanPermutationRightBranches := by
  simp [NormalForm.completeNormalizeOperation,
    NormalForm.operationBoolVars, NormalForm.selectionSetBooleanVariables,
    NormalForm.selectionBooleanVariables, NormalForm.directivesBooleanVariables,
    NormalForm.directiveBooleanVariables,
    NormalForm.inputValueBooleanVariables,
    NormalForm.dedupBoolVars, NormalForm.boolVariableMem,
    NormalForm.completeNormalizeRootSelectionSet,
    NormalForm.allBoolCases, NormalForm.normalizeSelectionSet.eq_1,
    NormalForm.normalizeSelectionSet.eq_2,
    NormalForm.withoutFieldSelectionsWithResponseName,
    NormalForm.fieldSelectionsWithResponseNameInScope,
    NormalForm.mergeSelectionSets, NormalForm.normalizedField,
    NormalForm.filterSelectionSetBoolCase, NormalForm.wrapWithBoolCase,
    NormalForm.directivesAllowIn, NormalForm.directiveAllowsIn,
    NormalForm.inputValueBoolIn?, NormalForm.BoolCase.lookup?,
    NormalForm.directiveForBit, Operation.rootType, OperationType.rootType,
    twoBranchBooleanPermutationRight,
    twoBranchBooleanPermutationRightBranches, twoDirectedLookupOperation,
    storedArguments, twoArgumentSchema, twoArgumentFieldDefinition,
    NormalForm.objectTypeNameBool, TypeRef.namedType, Schema.getPossibleTypes,
    Schema.lookupType, Schema.lookupField, Schema.allTypes,
    Schema.builtinScalarDefinitions, TypeDefinition.name,
    TypeDefinition.fields?, BuiltinScalar.name, List.find?] <;> rfl

private theorem computeTwoBranchBooleanPermutationLeftShape
    : computeOperationShape twoArgumentSchema twoBranchBooleanPermutationLeft
      = .ok twoBranchBooleanPermutationLeftShape := by
  simp only [computeOperationShape]
  rw [twoBranchBooleanPermutationLeftSupport]
  unfold decodeCompleteOperationShape
  rw [twoBranchBooleanPermutationLeftNormalized]
  simp [decodeCompleteRoot, decodeRootBranches, decodeCompleteStem,
    decodeStemDirective, clauseFromCompleteStem, firstDuplicate?,
    firstOutsideSupport?, firstMissingStemVariable?, clausesEqualBool,
    Clause.canonical, Clause.sortLiterals, Clause.insertLiteralSorted,
    Clause.completeMintermBool, Clause.validBool, namesStrictlyIncreasing,
    foldGroundSelectionSet.eq_1, foldGroundSelectionSet.eq_2,
    singletonDefinitionShape, mergeResponseShapes,
    Bind.bind, Except.bind,
    twoBranchBooleanPermutationLeft, twoBranchBooleanPermutationLeftBranches,
    twoBranchBooleanPermutationLeftShape, twoDirectedLookupOperation,
    leafOperationShape, leafShapePosition, storedArguments,
    twoArgumentSchema, twoArgumentFieldDefinition,
    NormalForm.objectTypeNameBool, NormalForm.leafTypeNameBool,
    TypeRef.isCompositeBool,
    Schema.lookupType, Schema.lookupField, Schema.allTypes,
    Schema.builtinScalarDefinitions, TypeDefinition.name,
    TypeDefinition.fields?, BuiltinScalar.name, List.find?] <;> rfl

private theorem computeTwoBranchBooleanPermutationRightShape
    : computeOperationShape twoArgumentSchema twoBranchBooleanPermutationRight
      = .ok twoBranchBooleanPermutationRightShape := by
  simp only [computeOperationShape]
  rw [twoBranchBooleanPermutationRightSupport]
  unfold decodeCompleteOperationShape
  rw [twoBranchBooleanPermutationRightNormalized]
  simp [decodeCompleteRoot, decodeRootBranches, decodeCompleteStem,
    decodeStemDirective, clauseFromCompleteStem, firstDuplicate?,
    firstOutsideSupport?, firstMissingStemVariable?, clausesEqualBool,
    Clause.canonical, Clause.sortLiterals, Clause.insertLiteralSorted,
    Clause.completeMintermBool, Clause.validBool, namesStrictlyIncreasing,
    foldGroundSelectionSet.eq_1, foldGroundSelectionSet.eq_2,
    singletonDefinitionShape, mergeResponseShapes,
    Bind.bind, Except.bind,
    twoBranchBooleanPermutationRight, twoBranchBooleanPermutationRightBranches,
    twoBranchBooleanPermutationRightShape, twoDirectedLookupOperation,
    leafOperationShape, leafShapePosition, storedArguments,
    twoArgumentSchema, twoArgumentFieldDefinition,
    NormalForm.objectTypeNameBool, NormalForm.leafTypeNameBool,
    TypeRef.isCompositeBool,
    Schema.lookupType, Schema.lookupField, Schema.allTypes,
    Schema.builtinScalarDefinitions, TypeDefinition.name,
    TypeDefinition.fields?, BuiltinScalar.name, List.find?] <;> rfl

private def aliasStrictCounterexample : StrictShapeEquivalentCounterexample :=
  .footprint
    (.leftNotSubsetRight
      (.uncovered
        { assignmentIndex := 0, pathIndex := 0 }
        { assignment := [], path := expectedPath "lookup" storedArguments }
        [expectedPath "renamed" storedArguments]))

private def argumentStrictCounterexample : StrictShapeEquivalentCounterexample :=
  .footprint
    (.leftNotSubsetRight
      (.uncovered
        { assignmentIndex := 0, pathIndex := 0 }
        { assignment := [], path := expectedPath "lookup" storedArguments }
        [expectedPath "lookup" changedArguments]))

private theorem aliasStrictRejected
    : ∃ proof,
        decideStrictShapeEquivalent twoArgumentSchema aliasedLeftShape aliasedRightShape
        = CertifiedVerdict.rejected proof aliasStrictCounterexample := by
  exact ⟨_, rfl⟩

private theorem argumentStrictRejected
    : ∃ proof,
        decideStrictShapeEquivalent twoArgumentSchema
          storedArgumentShape changedArgumentShape
        = CertifiedVerdict.rejected proof argumentStrictCounterexample := by
  exact ⟨_, rfl⟩

private theorem singleLookupFieldsValidInPossibleTypes
    (operationName responseName : Name) (arguments : List Argument)
    (harguments
      : Validation.argumentsValid twoArgumentSchema
          twoArgumentFieldDefinition.arguments [] arguments)
    : NormalForm.operationFieldsValidInPossibleTypes twoArgumentSchema
        (singleLookupOperation operationName responseName arguments) := by
  change (Validation.selectionValid twoArgumentSchema [] "Query"
      (.field responseName "lookup" arguments [] [])
    ∧ ∀ objectType,
        objectType ∈ twoArgumentSchema.getPossibleTypes "String" → True) ∧ True
  refine ⟨⟨lookupSelectionValid responseName arguments [] [] harguments
    (by simp [Validation.directivesValid]), ?_⟩, trivial⟩
  intro objectType hobject
  simp [Schema.getPossibleTypes, schemaLookupString] at hobject

private theorem singleLookupBoolTypeConditionFeasible
    (operationName responseName : Name) (arguments : List Argument)
    : NormalForm.operationBoolTypeConditionFeasible twoArgumentSchema
        (singleLookupOperation operationName responseName arguments) := by
  unfold NormalForm.operationBoolTypeConditionFeasible
  intro selection hselection
  simp only [singleLookupOperation, List.mem_singleton] at hselection
  subst selection
  unfold NormalForm.selectionBoolTypeConditionFeasible
  have hstack : NormalForm.typeConditionStackFeasible
      twoArgumentSchema ["Query"] := by
    refine ⟨"Query", ?_⟩
    intro typeCondition hcondition
    simp only [List.mem_singleton] at hcondition
    subst typeCondition
    simp [Schema.getPossibleTypes, schemaLookupQuery, localQueryType]
  simpa [singleLookupOperation, Operation.rootType, OperationType.rootType,
    NormalForm.operationBoolVars, NormalForm.selectionSetBooleanVariables,
    NormalForm.selectionBooleanVariables,
    NormalForm.directivesBooleanVariables, NormalForm.dedupBoolVars,
    NormalForm.allBoolCases, NormalForm.directivesAllowIn,
    twoArgumentSchema] using hstack

private theorem singleLookupSupportEquivalent
    (leftName leftResponse rightName rightResponse : Name)
    (leftArguments rightArguments : List Argument)
    : NormalForm.operationBoolVarsEquivalent
        (singleLookupOperation leftName leftResponse leftArguments)
        (singleLookupOperation rightName rightResponse rightArguments) := by
  intro varName
  simp [singleLookupOperation, NormalForm.operationBoolVars,
    NormalForm.selectionSetBooleanVariables,
    NormalForm.selectionBooleanVariables,
    NormalForm.directivesBooleanVariables, NormalForm.dedupBoolVars]

/-- Selection and argument order differ syntactically, while the comparator
accepts the valid pair. -/
theorem reorderedSelectionsAndArgumentsAccepted
    : Validation.operationDefinitionValid twoArgumentSchema reorderedSelectionsLeft
      ∧ Validation.operationDefinitionValid twoArgumentSchema reorderedSelectionsRight
      ∧ Algorithms.selectionSetEqBool
          reorderedSelectionsLeft.selectionSet reorderedSelectionsRight.selectionSet
        = false
      ∧ ∃ proof basis,
          decideOperationEquivalence twoArgumentSchema
            reorderedSelectionsLeft reorderedSelectionsRight
          = CertifiedVerdict.accepted proof basis := by
  have hstored : Validation.argumentsValid twoArgumentSchema
      twoArgumentFieldDefinition.arguments [] storedArguments := by
    simpa [storedArguments] using orderedArgumentsValid [] "one" "two"
  have hreordered : Validation.argumentsValid twoArgumentSchema
      twoArgumentFieldDefinition.arguments [] reorderedArguments := by
    simpa [reorderedArguments] using reorderedArgumentsValid [] "one" "two"
  have hleft : Validation.operationDefinitionValid twoArgumentSchema
      reorderedSelectionsLeft :=
    twoLookupOperationValid
      "ReorderedSelectionsLeft" "alpha" "beta" storedArguments
      hstored (by decide)
  have hright : Validation.operationDefinitionValid twoArgumentSchema
      reorderedSelectionsRight :=
    twoLookupOperationValid
      "ReorderedSelectionsRight" "beta" "alpha" reorderedArguments
      hreordered (by decide)
  have hleftCompute : computeOperationShape twoArgumentSchema
      reorderedSelectionsLeft = .ok reorderedSelectionsLeftShape := by
    simp [computeOperationShape, NormalForm.completeNormalizeOperation,
      NormalForm.operationBoolVars, NormalForm.selectionSetBooleanVariables,
      NormalForm.selectionBooleanVariables, NormalForm.directivesBooleanVariables,
      NormalForm.dedupBoolVars,
      NormalForm.completeNormalizeRootSelectionSet,
      NormalForm.allBoolCases, NormalForm.normalizeSelectionSet.eq_1,
      NormalForm.normalizeSelectionSet.eq_2,
      NormalForm.withoutFieldSelectionsWithResponseName,
      NormalForm.fieldSelectionsWithResponseNameInScope,
      NormalForm.mergeSelectionSets, NormalForm.normalizedField,
      NormalForm.filterSelectionSetBoolCase, NormalForm.wrapWithBoolCase,
      NormalForm.directivesAllowIn, NormalForm.directiveAllowsIn,
      NormalForm.inputValueBoolIn?, Operation.rootType, OperationType.rootType,
      decodeCompleteOperationShape, decodeCompleteRoot,
      foldGroundSelectionSet.eq_1, foldGroundSelectionSet.eq_2,
      singletonDefinitionShape, mergeResponseShapes,
      reorderedSelectionsLeft, reorderedSelectionsLeftShape,
      twoLookupOperation, leafOperationShape, leafShapePosition,
      storedArguments, twoArgumentSchema, twoArgumentFieldDefinition,
      NormalForm.objectTypeNameBool,
      NormalForm.leafTypeNameBool, TypeRef.isCompositeBool, TypeRef.namedType,
      Schema.getPossibleTypes, Schema.lookupType, Schema.lookupField,
      Schema.allTypes, Schema.builtinScalarDefinitions, TypeDefinition.name,
      TypeDefinition.fields?, BuiltinScalar.name, List.find?] <;> rfl
  have hrightCompute : computeOperationShape twoArgumentSchema
      reorderedSelectionsRight = .ok reorderedSelectionsRightShape := by
    simp [computeOperationShape, NormalForm.completeNormalizeOperation,
      NormalForm.operationBoolVars, NormalForm.selectionSetBooleanVariables,
      NormalForm.selectionBooleanVariables, NormalForm.directivesBooleanVariables,
      NormalForm.dedupBoolVars, NormalForm.completeNormalizeRootSelectionSet,
      NormalForm.allBoolCases, NormalForm.normalizeSelectionSet.eq_1,
      NormalForm.normalizeSelectionSet.eq_2,
      NormalForm.withoutFieldSelectionsWithResponseName,
      NormalForm.fieldSelectionsWithResponseNameInScope,
      NormalForm.mergeSelectionSets, NormalForm.normalizedField,
      NormalForm.filterSelectionSetBoolCase, NormalForm.wrapWithBoolCase,
      NormalForm.directivesAllowIn, Operation.rootType, OperationType.rootType,
      decodeCompleteOperationShape, decodeCompleteRoot,
      foldGroundSelectionSet.eq_1, foldGroundSelectionSet.eq_2,
      singletonDefinitionShape, mergeResponseShapes,
      reorderedSelectionsRight, reorderedSelectionsRightShape,
      twoLookupOperation, leafOperationShape, leafShapePosition,
      reorderedArguments, twoArgumentSchema, twoArgumentFieldDefinition,
      NormalForm.objectTypeNameBool,
      NormalForm.leafTypeNameBool, TypeRef.isCompositeBool, TypeRef.namedType,
      Schema.getPossibleTypes, Schema.lookupType, Schema.lookupField,
      Schema.allTypes, Schema.builtinScalarDefinitions, TypeDefinition.name,
      TypeDefinition.fields?, BuiltinScalar.name, List.find?] <;> rfl
  refine ⟨hleft, hright, by decide,
    accepted_of_concrete_shapes _ _ _ _ hleftCompute hrightCompute
      (by decide) ?_⟩
  set_option maxHeartbeats 0 in
    decide

/-- Reversing independent Boolean directives reverses source support order but
preserves every complete-case response footprint, so the valid pair is accepted. -/
theorem booleanDirectiveOrderAccepted
    : Validation.operationDefinitionValid twoArgumentSchema booleanDirectivesLeft
      ∧ Validation.operationDefinitionValid twoArgumentSchema booleanDirectivesRight
      ∧ Algorithms.selectionSetEqBool
          booleanDirectivesLeft.selectionSet booleanDirectivesRight.selectionSet
        = false
      ∧ NormalForm.operationBoolVars booleanDirectivesLeft = ["x", "y"]
      ∧ NormalForm.operationBoolVars booleanDirectivesRight = ["y", "x"]
      ∧ ∃ proof basis,
          decideOperationEquivalence twoArgumentSchema
            booleanDirectivesLeft booleanDirectivesRight
          = CertifiedVerdict.accepted proof basis := by
  have hleft := booleanDirectivesLeftValid
  have hright := booleanDirectivesRightValid
  have hleftCompute : computeOperationShape twoArgumentSchema
      booleanDirectivesLeft = .ok booleanDirectivesLeftShape := by
    simp [computeOperationShape, NormalForm.completeNormalizeOperation,
      NormalForm.operationBoolVars, NormalForm.selectionSetBooleanVariables,
      NormalForm.selectionBooleanVariables, NormalForm.directivesBooleanVariables,
      NormalForm.directiveBooleanVariables,
      NormalForm.inputValueBooleanVariables,
      NormalForm.dedupBoolVars, NormalForm.boolVariableMem,
      NormalForm.completeNormalizeRootSelectionSet,
      NormalForm.allBoolCases, NormalForm.normalizeSelectionSet.eq_1,
      NormalForm.normalizeSelectionSet.eq_2,
      NormalForm.withoutFieldSelectionsWithResponseName,
      NormalForm.fieldSelectionsWithResponseNameInScope,
      NormalForm.mergeSelectionSets, NormalForm.normalizedField,
      NormalForm.filterSelectionSetBoolCase, NormalForm.wrapWithBoolCase,
      NormalForm.directivesAllowIn, NormalForm.directiveAllowsIn,
      NormalForm.inputValueBoolIn?, NormalForm.BoolCase.lookup?,
      NormalForm.directiveForBit, Operation.rootType, OperationType.rootType,
      decodeCompleteOperationShape, decodeCompleteRoot,
      decodeRootBranches, decodeCompleteStem, decodeStemDirective,
      clauseFromCompleteStem, firstOutsideSupport?, firstDuplicate?,
      firstMissingStemVariable?, Clause.canonical,
      Clause.sortLiterals, Clause.insertLiteralSorted, Clause.validBool,
      Clause.completeMintermBool, namesStrictlyIncreasing,
      foldGroundSelectionSet.eq_1, foldGroundSelectionSet.eq_2,
      singletonDefinitionShape, mergeResponseShapes,
      Bind.bind, Except.bind,
      booleanDirectivesLeft, booleanDirectivesLeftShape,
      singleLookupOperation, booleanVariableDefinitions,
      NormalForm.booleanVariableDefinition, leafOperationShape,
      leafShapePosition, storedArguments, twoArgumentSchema,
      twoArgumentFieldDefinition,
      NormalForm.objectTypeNameBool, NormalForm.leafTypeNameBool,
      TypeRef.isCompositeBool, TypeRef.namedType, Schema.getPossibleTypes,
      Schema.lookupType, Schema.lookupField, Schema.allTypes,
      Schema.builtinScalarDefinitions, TypeDefinition.name,
      TypeDefinition.fields?, BuiltinScalar.name, List.find?] <;> rfl
  have hrightCompute : computeOperationShape twoArgumentSchema
      booleanDirectivesRight = .ok booleanDirectivesRightShape := by
    simp [computeOperationShape, NormalForm.completeNormalizeOperation,
      NormalForm.operationBoolVars, NormalForm.selectionSetBooleanVariables,
      NormalForm.selectionBooleanVariables, NormalForm.directivesBooleanVariables,
      NormalForm.directiveBooleanVariables,
      NormalForm.inputValueBooleanVariables,
      NormalForm.dedupBoolVars, NormalForm.boolVariableMem,
      NormalForm.completeNormalizeRootSelectionSet,
      NormalForm.allBoolCases, NormalForm.normalizeSelectionSet.eq_1,
      NormalForm.normalizeSelectionSet.eq_2,
      NormalForm.withoutFieldSelectionsWithResponseName,
      NormalForm.fieldSelectionsWithResponseNameInScope,
      NormalForm.mergeSelectionSets, NormalForm.normalizedField,
      NormalForm.filterSelectionSetBoolCase, NormalForm.wrapWithBoolCase,
      NormalForm.directivesAllowIn, NormalForm.directiveAllowsIn,
      NormalForm.inputValueBoolIn?, NormalForm.BoolCase.lookup?,
      NormalForm.directiveForBit, Operation.rootType, OperationType.rootType,
      decodeCompleteOperationShape, decodeCompleteRoot,
      decodeRootBranches, decodeCompleteStem, decodeStemDirective,
      clauseFromCompleteStem, firstOutsideSupport?, firstDuplicate?,
      firstMissingStemVariable?, Clause.canonical,
      Clause.sortLiterals, Clause.insertLiteralSorted, Clause.validBool,
      Clause.completeMintermBool, namesStrictlyIncreasing,
      foldGroundSelectionSet.eq_1, foldGroundSelectionSet.eq_2,
      singletonDefinitionShape, mergeResponseShapes,
      Bind.bind, Except.bind,
      booleanDirectivesRight, booleanDirectivesRightShape,
      singleLookupOperation, booleanVariableDefinitions,
      NormalForm.booleanVariableDefinition, leafOperationShape,
      leafShapePosition, storedArguments, twoArgumentSchema,
      twoArgumentFieldDefinition,
      NormalForm.objectTypeNameBool, NormalForm.leafTypeNameBool,
      TypeRef.isCompositeBool, TypeRef.namedType, Schema.getPossibleTypes,
      Schema.lookupType, Schema.lookupField, Schema.allTypes,
      Schema.builtinScalarDefinitions, TypeDefinition.name,
      TypeDefinition.fields?, BuiltinScalar.name, List.find?] <;> rfl
  refine ⟨hleft, hright, by decide, by decide, by decide,
    accepted_of_concrete_shapes _ _ _ _ hleftCompute hrightCompute
      (by decide) ?_⟩
  set_option maxHeartbeats 0 in
    decide

/-- Opposite complete minterms leave exactly the `beta`, then `alpha` branches
under `x, y` support and the `alpha`, then `beta` branches under `y, x`
support. The decoded branch positions are literal reverses, and the comparator
accepts the valid pair. -/
theorem twoSurvivingBooleanBranchOrderAccepted
    : Validation.operationDefinitionValid twoArgumentSchema
        twoBranchBooleanPermutationLeft
      ∧ Validation.operationDefinitionValid twoArgumentSchema
          twoBranchBooleanPermutationRight
      ∧ Algorithms.selectionSetEqBool
          twoBranchBooleanPermutationLeft.selectionSet
          twoBranchBooleanPermutationRight.selectionSet
        = false
      ∧ NormalForm.operationBoolVars twoBranchBooleanPermutationLeft = ["x", "y"]
      ∧ NormalForm.operationBoolVars twoBranchBooleanPermutationRight = ["y", "x"]
      ∧ (NormalForm.completeNormalizeOperation twoArgumentSchema
            twoBranchBooleanPermutationLeft).selectionSet
          = twoBranchBooleanPermutationLeftBranches
      ∧ (NormalForm.completeNormalizeOperation twoArgumentSchema
            twoBranchBooleanPermutationRight).selectionSet
          = twoBranchBooleanPermutationRightBranches
      ∧ (NormalForm.completeNormalizeOperation twoArgumentSchema
            twoBranchBooleanPermutationLeft).selectionSet.length = 2
      ∧ (NormalForm.completeNormalizeOperation twoArgumentSchema
            twoBranchBooleanPermutationRight).selectionSet.length = 2
      ∧ computeOperationShape twoArgumentSchema twoBranchBooleanPermutationLeft
          = .ok twoBranchBooleanPermutationLeftShape
      ∧ computeOperationShape twoArgumentSchema twoBranchBooleanPermutationRight
          = .ok twoBranchBooleanPermutationRightShape
      ∧ twoBranchBooleanPermutationLeftShape.root.positions.map
          ResponsePosition.responseName = ["beta", "alpha"]
      ∧ twoBranchBooleanPermutationRightShape.root.positions.map
          ResponsePosition.responseName = ["alpha", "beta"]
      ∧ twoBranchBooleanPermutationLeftShape.root.positions.reverse
          = twoBranchBooleanPermutationRightShape.root.positions
      ∧ ∃ proof basis,
          decideOperationEquivalence twoArgumentSchema
            twoBranchBooleanPermutationLeft twoBranchBooleanPermutationRight
          = CertifiedVerdict.accepted proof basis := by
  refine ⟨twoBranchBooleanPermutationLeftValid,
    twoBranchBooleanPermutationRightValid, by decide,
    twoBranchBooleanPermutationLeftSupport,
    twoBranchBooleanPermutationRightSupport,
    twoBranchBooleanPermutationLeftNormalized,
    twoBranchBooleanPermutationRightNormalized,
    by
      simpa [twoBranchBooleanPermutationLeftBranches] using
        congrArg List.length twoBranchBooleanPermutationLeftNormalized,
    by
      simpa [twoBranchBooleanPermutationRightBranches] using
        congrArg List.length twoBranchBooleanPermutationRightNormalized,
    computeTwoBranchBooleanPermutationLeftShape,
    computeTwoBranchBooleanPermutationRightShape, by rfl, by rfl, by rfl,
    accepted_of_concrete_shapes _ _ _ _
      computeTwoBranchBooleanPermutationLeftShape
      computeTwoBranchBooleanPermutationRightShape (by decide) ?_⟩
  set_option maxHeartbeats 0 in
    decide

/-- An alias change is rejected with the exact first uncovered path and is
semantically distinct under the full uniqueness premises. -/
theorem aliasChangeRejectedWithExactPayload
    : Validation.operationDefinitionValid twoArgumentSchema aliasedLeft
      ∧ Validation.operationDefinitionValid twoArgumentSchema aliasedRight
      ∧ (∃ proof witness,
          decideOperationEquivalence twoArgumentSchema aliasedLeft aliasedRight
            = CertifiedVerdict.rejected proof witness
          ∧ witness.strictCounterexample
            = .footprint
                (.leftNotSubsetRight
                  (.uncovered
                    { assignmentIndex := 0, pathIndex := 0 }
                    { assignment := [], path := expectedPath "lookup" storedArguments }
                    [expectedPath "renamed" storedArguments])))
      ∧ ¬ NormalForm.operationsSemanticallyEquivalent
            twoArgumentSchema aliasedLeft aliasedRight := by
  have harguments : Validation.argumentsValid twoArgumentSchema
      twoArgumentFieldDefinition.arguments [] storedArguments := by
    simpa [storedArguments] using orderedArgumentsValid [] "one" "two"
  have hleft : Validation.operationDefinitionValid twoArgumentSchema aliasedLeft :=
    singleLookupOperationValid "AliasedLeft" "lookup" storedArguments harguments
  have hright : Validation.operationDefinitionValid twoArgumentSchema aliasedRight :=
    singleLookupOperationValid "AliasedRight" "renamed" storedArguments harguments
  have hleftCompute : computeOperationShape twoArgumentSchema aliasedLeft =
      .ok aliasedLeftShape := by
    simpa [aliasedLeft, aliasedLeftShape] using
      computeSingleLookupOperationShape
        "AliasedLeft" "lookup" storedArguments
  have hrightCompute : computeOperationShape twoArgumentSchema aliasedRight =
      .ok aliasedRightShape := by
    simpa [aliasedRight, aliasedRightShape] using
      computeSingleLookupOperationShape
        "AliasedRight" "renamed" storedArguments
  rcases aliasStrictRejected with ⟨strictProof, hstrict⟩
  rcases decideOperationEquivalence_rejected_of_computed
      hleftCompute hrightCompute hstrict with
    ⟨operationProof, operationWitness, hoperation, hpayload⟩
  have hexact : ∃ proof witness,
      decideOperationEquivalence twoArgumentSchema aliasedLeft aliasedRight =
        CertifiedVerdict.rejected proof witness
      ∧ witness.strictCounterexample =
        .footprint (.leftNotSubsetRight (.uncovered
          { assignmentIndex := 0, pathIndex := 0 }
          { assignment := [], path := expectedPath "lookup" storedArguments }
          [expectedPath "renamed" storedArguments])) :=
    ⟨operationProof, operationWitness, hoperation,
      by simpa [aliasStrictCounterexample] using hpayload⟩
  refine ⟨hleft, hright, hexact, ?_⟩
  apply decideOperationEquivalence_rejected_not_semanticallyEquivalent
    ⟨operationProof, operationWitness, hoperation⟩
    twoArgumentSchemaWellFormed hleft hright
    (singleLookupFieldsValidInPossibleTypes _ _ _ harguments)
    (singleLookupFieldsValidInPossibleTypes _ _ _ harguments)
    (singleLookupBoolTypeConditionFeasible _ _ _)
    (singleLookupBoolTypeConditionFeasible _ _ _)
    (singleLookupSupportEquivalent _ _ _ _ _ _)

/-- An argument-value change is rejected with the exact required and available
paths and is semantically distinct under the full uniqueness premises. -/
theorem argumentValueChangeRejectedWithExactPayload
    : Validation.operationDefinitionValid twoArgumentSchema storedArgumentOperation
      ∧ Validation.operationDefinitionValid twoArgumentSchema changedArgumentOperation
      ∧ (∃ proof witness,
          decideOperationEquivalence twoArgumentSchema
              storedArgumentOperation changedArgumentOperation
            = CertifiedVerdict.rejected proof witness
          ∧ witness.strictCounterexample
            = .footprint
                (.leftNotSubsetRight
                  (.uncovered
                    { assignmentIndex := 0, pathIndex := 0 }
                    { assignment := [], path := expectedPath "lookup" storedArguments }
                    [expectedPath "lookup" changedArguments])))
      ∧ ¬ NormalForm.operationsSemanticallyEquivalent twoArgumentSchema
            storedArgumentOperation changedArgumentOperation := by
  have hstored : Validation.argumentsValid twoArgumentSchema
      twoArgumentFieldDefinition.arguments [] storedArguments := by
    simpa [storedArguments] using orderedArgumentsValid [] "one" "two"
  have hchanged : Validation.argumentsValid twoArgumentSchema
      twoArgumentFieldDefinition.arguments [] changedArguments := by
    simpa [changedArguments] using orderedArgumentsValid [] "one" "changed"
  have hleft : Validation.operationDefinitionValid twoArgumentSchema
      storedArgumentOperation :=
    singleLookupOperationValid
      "StoredArguments" "lookup" storedArguments hstored
  have hright : Validation.operationDefinitionValid twoArgumentSchema
      changedArgumentOperation :=
    singleLookupOperationValid
      "ChangedArguments" "lookup" changedArguments hchanged
  have hleftCompute : computeOperationShape twoArgumentSchema
      storedArgumentOperation = .ok storedArgumentShape := by
    simpa [storedArgumentOperation, storedArgumentShape] using
      computeSingleLookupOperationShape
        "StoredArguments" "lookup" storedArguments
  have hrightCompute : computeOperationShape twoArgumentSchema
      changedArgumentOperation = .ok changedArgumentShape := by
    simpa [changedArgumentOperation, changedArgumentShape] using
      computeSingleLookupOperationShape
        "ChangedArguments" "lookup" changedArguments
  rcases argumentStrictRejected with ⟨strictProof, hstrict⟩
  rcases decideOperationEquivalence_rejected_of_computed
      hleftCompute hrightCompute hstrict with
    ⟨operationProof, operationWitness, hoperation, hpayload⟩
  have hexact : ∃ proof witness,
      decideOperationEquivalence twoArgumentSchema
          storedArgumentOperation changedArgumentOperation =
        CertifiedVerdict.rejected proof witness
      ∧ witness.strictCounterexample =
        .footprint (.leftNotSubsetRight (.uncovered
          { assignmentIndex := 0, pathIndex := 0 }
          { assignment := [], path := expectedPath "lookup" storedArguments }
          [expectedPath "lookup" changedArguments])) :=
    ⟨operationProof, operationWitness, hoperation,
      by simpa [argumentStrictCounterexample] using hpayload⟩
  refine ⟨hleft, hright, hexact, ?_⟩
  apply decideOperationEquivalence_rejected_not_semanticallyEquivalent
    ⟨operationProof, operationWitness, hoperation⟩
    twoArgumentSchemaWellFormed hleft hright
    (singleLookupFieldsValidInPossibleTypes _ _ _ hstored)
    (singleLookupFieldsValidInPossibleTypes _ _ _ hchanged)
    (singleLookupBoolTypeConditionFeasible _ _ _)
    (singleLookupBoolTypeConditionFeasible _ _ _)
    (singleLookupSupportEquivalent _ _ _ _ _ _)

end OperationComparison
end ResponseShape
end Tests
end GraphQL
