import GraphQL.Theories.NormalForm
import Proofs.GraphQL.Theories.QueryInclusionSemantics.ArgumentCoercibility
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.ArgumentCoercibility

/-! Regression for input-coercion fuel under nested singleton-list coercion.

For `type Query { f(a: [[[Int]]]): String }`, the operation `{ f(a: 1) }` is valid
in every possible type. The old syntax-only budget was 3, although the three list
wrappers and scalar need 4 steps. The revised budget supplies coercible environments
for this operation, including after complete normalization.
-/

namespace GraphQL.Tests.ArgumentCoercibility

private def nestedType : TypeRef := .list (.list (.list (.named "Int")))
private def arg : InputValueDefinition := { name := "a", inputType := nestedType }

private def field : FieldDefinition :=
  { name := "f", outputType := .named "String", arguments := [arg] }

private def query : ObjectType := { name := "Query", fields := [field] }
private def schema : Schema := { queryType := "Query", types := [.object query] }
private def args : List Argument := [{ name := "a", value := .int 1 }]
private def op : Operation := { selectionSet := [.field "f" "f" args [] []] }

private theorem inputInt : (TypeRef.named "Int").isInputType schema :=
  ⟨.builtinScalar .int, rfl, trivial⟩

private theorem outputString : (TypeRef.named "String").isOutputType schema :=
  ⟨.builtinScalar .string, rfl, trivial⟩

private theorem leafString : schema.isLeafType "String" :=
  ⟨.builtinScalar .string, rfl, trivial⟩

private theorem intLiteralValid
    : Validation.ValueIsCorrectTypeAtLocation schema [] (.int 1) nestedType none := by
  have hbase : Validation.ValueIsCorrectTypeAtLocation schema []
      (.int 1) (.named "Int") none := by
    refine .namedNonInputObject _ _ _ inputInt ?_ ?_ ?_ ⟨.int 1, rfl⟩ rfl
    all_goals simp
  have hwrap (inner : TypeRef) (hinput : inner.isInputType schema)
      (h : Validation.ValueIsCorrectTypeAtLocation schema [] (.int 1) inner none) :
      Validation.ValueIsCorrectTypeAtLocation schema [] (.int 1) (.list inner) none := by
    refine .singletonListItem _ _ _ hinput ?_ ?_ ?_ ?_ h
    all_goals simp
  exact hwrap _ inputInt (hwrap _ inputInt (hwrap _ inputInt hbase))

private theorem fieldValid
    : Validation.selectionValid schema [] "Query" (.field "f" "f" args [] []) := by
  unfold Validation.selectionValid
  constructor
  · simp [Validation.directivesValid]
  refine ⟨field, rfl, ?_, ?_⟩
  · constructor
    · simp [args]
    constructor
    · intro argument hmem
      have heq : argument = { name := "a", value := .int 1 } := by simpa [args] using hmem
      subst argument
      exact ⟨arg, rfl, intLiteralValid⟩
    · intro definition hmem hrequired
      have heq : definition = arg := by simpa [field] using hmem
      subst definition
      exact False.elim hrequired
  · unfold Validation.fieldSelectionSetValid
    dsimp only
    exact ⟨outputString, Or.inl ⟨leafString, rfl⟩⟩

private theorem fieldsValid
    : NormalForm.operationFieldsValidInPossibleTypes schema op := by
  refine ⟨⟨fieldValid, ?_⟩, trivial⟩
  change ∀ objectType, objectType ∈ schema.getPossibleTypes "String" -> True
  intros
  trivial

theorem nestedListLiteralArgumentsCoerce (values : Execution.VariableValues)
    : Execution.coerceArgumentValues schema values [arg] args
      = .success [{ name := "a", value := .list [.list [.list [.int 1]]] }] := by
  cbv

private theorem possibleTypes (typeName : Name)
    : schema.getPossibleTypes typeName
      = if typeName = "Query" then ["Query"] else [] := by
  by_cases hQ : typeName = "Query"
  · subst typeName; rfl
  by_cases hInt : typeName = "Int"
  · subst typeName; rfl
  by_cases hFloat : typeName = "Float"
  · subst typeName; rfl
  by_cases hString : typeName = "String"
  · subst typeName; rfl
  by_cases hBool : typeName = "Boolean"
  · subst typeName; rfl
  by_cases hID : typeName = "ID"
  · subst typeName; rfl
  have hbInt := beq_eq_false_iff_ne.mpr (Ne.symm hInt)
  have hbFloat := beq_eq_false_iff_ne.mpr (Ne.symm hFloat)
  have hbString := beq_eq_false_iff_ne.mpr (Ne.symm hString)
  have hbBool := beq_eq_false_iff_ne.mpr (Ne.symm hBool)
  have hbID := beq_eq_false_iff_ne.mpr (Ne.symm hID)
  have hbQ := beq_eq_false_iff_ne.mpr (Ne.symm hQ)
  simp [Schema.getPossibleTypes, Schema.lookupType, Schema.allTypes,
    Schema.builtinScalarDefinitions, List.find?, TypeDefinition.name, BuiltinScalar.name,
    query, schema, hbInt, hbFloat, hbString, hbBool, hbID, hbQ, hQ]

private theorem lookupQuery (fieldName : Name)
    : schema.lookupField "Query" fieldName
      = if fieldName = "f" then some field else none := by
  by_cases h : fieldName = "f"
  · subst fieldName; rfl
  · have hb := beq_eq_false_iff_ne.mpr (Ne.symm h)
    unfold Schema.lookupField
    rw [show schema.lookupType "Query" = some (.object query) from rfl]
    simp [TypeDefinition.fields?, query, field, List.find?, hb, h]

private theorem wellFormed : SchemaWellFormedness.schemaWellFormed schema := by
  constructor
  · change (["Int", "Float", "String", "Boolean", "ID", "Query"] : List Name).Nodup
    decide
  constructor
  · exact ⟨query, rfl⟩
  constructor
  · intro typeDefinition hmem
    have heq : typeDefinition = .object query := by simpa [schema] using hmem
    subst typeDefinition
    constructor
    · refine ⟨by simp [SchemaWellFormedness.listNonempty, query],
        by simp [SchemaWellFormedness.namesAreUnique, query], ?_⟩
      intro fieldDefinition hmem
      have heq : fieldDefinition = field := by simpa [query] using hmem
      subst fieldDefinition
      refine ⟨outputString, by simp [SchemaWellFormedness.namesAreUnique, field], ?_⟩
      intro definition hmem
      have heq : definition = arg := by simpa [field] using hmem
      subst definition
      exact ⟨inputInt, trivial⟩
    · exact ⟨by simp [SchemaWellFormedness.namesAreUnique, query], by simp [query]⟩
  constructor
  · exact ⟨rfl, rfl⟩
  constructor
  · intro typeName objectTypeName hmem
    rw [possibleTypes] at hmem
    split at hmem
    · have heq : objectTypeName = "Query" := by simpa using hmem
      subst objectTypeName
      exact ⟨query, rfl⟩
    · cases hmem
  constructor
  · intro typeName
    rw [possibleTypes]
    split <;> simp
  · intro parentType objectTypeName fieldName expected hpossible hlookup
    rw [possibleTypes] at hpossible
    split at hpossible
    next heq =>
      subst parentType
      have heq : objectTypeName = "Query" := by simpa using hpossible
      subst objectTypeName
      rw [lookupQuery] at hlookup
      split at hlookup
      next heq =>
        subst fieldName
        have heq : expected = field := Option.some.inj hlookup.symm
        subst expected
        refine ⟨field, rfl, ?_, ?_⟩
        · constructor
          · exact Or.inl ⟨leafString, leafString, rfl⟩
          · simp [SchemaWellFormedness.argumentDefinitionsImplement,
              Schema.lookupArgumentDefinition, field, arg]
        · exact ⟨outputString, outputString, by intro _; rfl⟩
      next => cases hlookup
    next => cases hpossible

private def scopedField : FieldMerge.ScopedField :=
  {
    parentType := "Query",
    responseName := "f",
    fieldName := "f",
    arguments := args,
    outputType := .named "String",
    selectionSet := []
  }

private theorem valid : Validation.operationDefinitionValid schema op := by
  refine ⟨rfl, ⟨.object query, rfl, trivial⟩, ?_, by decide, ?_, ?_, ?_⟩
  · simp [Validation.variableDefinitionsValid, op]
  · unfold Validation.selectionSetValid
    intro selection hmem
    have heq : selection = .field "f" "f" args [] [] := by simpa [op] using hmem
    subst selection
    exact fieldValid
  · refine FieldMerge.FieldsInSetCanMerge.intro _ _ ?_
    dsimp
    intro left hleft right hright _
    have hcollect : FieldMerge.collectFields schema (op.rootType schema) op.selectionSet =
        [scopedField] := by
      have hlookup : schema.lookupField "Query" "f" = some field := by rfl
      change FieldMerge.collectFields schema "Query" [.field "f" "f" args [] []] = [scopedField]
      simp [FieldMerge.collectFields, hlookup, scopedField, field]
    rw [hcollect] at hleft hright
    simp only [List.mem_singleton] at hleft hright
    subst left
    subst right
    refine FieldMerge.FieldsForNameCanMerge.intro _ _ ?_ ?_ ?_
    · exact ⟨outputString, outputString, by intro _; rfl⟩
    · intro _
      constructor
      · rfl
      · change Argument.argumentsEquivalent args args
        constructor <;> intro argument hmem
        all_goals
          refine ⟨argument, hmem, ?_⟩
          have heq : argument = { name := "a", value := .int 1 } := by
            simpa [args] using hmem
          subst argument
          change "a" = "a" ∧ (1 : Int) = 1
          exact ⟨rfl, rfl⟩
    · intro _ objectType
      refine FieldMerge.FieldsInSetCanMerge.intro objectType [] ?_
      dsimp
      intro left hleft
      simp [FieldMerge.collectFields] at hleft
  · simp [Validation.operationVariablesUsed, op]

private theorem comparisonCoercible
    : ∃ values, operationArgumentsCoercible schema values op := by
  obtain ⟨values, _, hcoercible, _⟩ :=
    QueryInclusionSemantics.exists_coercibleValues_for_comparisonCase
    wellFormed valid valid
    (ExecutionReadiness.operationCoercibleInPossibleTypes_of_fieldsValidInPossibleTypes
      wellFormed fieldsValid)
    (ExecutionReadiness.operationCoercibleInPossibleTypes_of_fieldsValidInPossibleTypes
      wellFormed fieldsValid)
    (by constructor <;> intro definition hmem <;> cases hmem)
    [] (by intro name hmem; cases hmem)
  exact ⟨values, hcoercible⟩

private theorem normalized : NormalForm.completeNormalizeOperation schema op = op := by
  cbv

private theorem jointlyCoercible
    : NormalForm.completeBoolCasesJointlyCoercible schema op op := by
  have hnormal : NormalForm.completeNormalOperation schema op := by
    simpa only [normalized]
      using NormalForm.CompleteNormalization.completeNormalizeOperation_normal schema op
        wellFormed valid
  apply NormalForm.CompleteNormalization.completeBoolCasesJointlyCoercible_of_completeNormal
    wellFormed valid valid hnormal hnormal
  constructor <;> intro definition hmem <;> cases hmem

private theorem feasible : NormalForm.operationBoolTypeConditionFeasible schema op := by
  intro selection hmem
  have heq : selection = .field "f" "f" args [] [] := by simpa [op] using hmem
  subst selection
  unfold NormalForm.selectionBoolTypeConditionFeasible
  refine ⟨by decide, ?_, Or.inl rfl⟩
  exact ⟨"Query", by decide⟩

-- The formerly failing example has witnesses for both coercibility helpers;
-- complete normality supplies the normal-form witness without a separate field-validity premise.
theorem nestedListArgumentsAdmitJointCoercibility
    : ∃ (schema : Schema) (operation : Operation),
        SchemaWellFormedness.schemaWellFormed schema
        ∧ Validation.operationDefinitionValid schema operation
        ∧ NormalForm.operationFieldsValidInPossibleTypes schema operation
        ∧ NormalForm.operationBoolTypeConditionFeasible schema operation
        ∧ NormalForm.completeBoolCasesJointlyCoercible schema
            (NormalForm.completeNormalizeOperation schema operation)
            (NormalForm.completeNormalizeOperation schema operation)
        ∧ ∃ values, operationArgumentsCoercible schema values operation := by
  refine ⟨schema, op, wellFormed, valid, fieldsValid, feasible, ?_, comparisonCoercible⟩
  simpa only [normalized] using jointlyCoercible

-- A wrapped nullable recursive field can consume the same type-wrapper budget
-- repeatedly along a finite supplied value or a finite schema default.
private def recursiveInput : Nat -> ConstInputValue
  | 0 => .object []
  | n + 1 => .object [("next", recursiveInput n)]

private def coercedRecursiveInput : Nat -> ConstInputValue
  | 0 => .object []
  | n + 1 => .object [("next", .list [.list [.list [coercedRecursiveInput n]]])]

private def recursiveSchema : Schema :=
  {
    queryType := "Query",
    types :=
      [
        .inputObject
          {
            name := "Chain",
            inputFields :=
              [{ name := "next", inputType := .list (.list (.list (.named "Chain"))) }]
          },
        .inputObject
          {
            name := "Holder",
            inputFields :=
              [{
                name := "value"
                inputType := .named "Chain"
                defaultValue := some (recursiveInput 8)
              }]
          }
      ]
  }

theorem recursiveWrappedLiteralCoerces
    : Execution.coerceInputValue recursiveSchema [] (.named "Chain")
        (recursiveInput 8).toInputValue
      = .success (coercedRecursiveInput 8) := by
  cbv

theorem recursiveWrappedVariableCoerces
    : Execution.coerceInputValue recursiveSchema [("chain", recursiveInput 8)]
        (.named "Chain") (.variable "chain")
      = .success (coercedRecursiveInput 8) := by
  cbv

theorem recursiveWrappedDefaultCoerces
    : Execution.coerceInputValue recursiveSchema [] (.named "Holder") (.object [])
      = .success (.object [("value", coercedRecursiveInput 8)]) := by
  cbv

end GraphQL.Tests.ArgumentCoercibility
