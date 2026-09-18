import Proofs.GraphQL.Execution.InputCoercionSupport
import Proofs.GraphQL.Execution.InputValues
import Proofs.GraphQL.Validation.ConstantInputs

namespace GraphQL.Execution

theorem coerceInputValueBounded_success_of_valid_of_defaults
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (definitions : List VariableDefinition) (values : VariableValues)
    (hvalues : variablesHaveNonNullValues schema definitions values)
    (reserve width : Nat)
    (hwidthFields
      : ∀ name inputObject definition,
          schema.lookupInputObject name = some inputObject
          -> definition ∈ inputObject.inputFields
          -> inputTypeCoercionDepth definition.inputType ≤ width)
    (hdefaults
      : ∀ name inputObject definition defaultValue,
          schema.lookupInputObject name = some inputObject
          -> definition ∈ inputObject.inputFields
          -> definition.defaultValue = some defaultValue
          -> ∀ fuel,
              reserve ≤ fuel
              -> ∃ coerced,
                  coerceInputValueBounded schema values fuel definition.inputType
                    defaultValue.toInputValue
                  = .success coerced)
    : ∀ fuel inputType value locationDefault,
        Validation.ValueIsCorrectTypeAtLocation schema definitions value inputType
          locationDefault
        -> inputTypeCoercionDepth inputType ≤ width
        -> inputCoercionBudget reserve width values inputType value ≤ fuel
        -> ∃ coerced,
            coerceInputValueBounded schema values fuel inputType value
            = .success coerced := by
  intro fuel
  induction fuel with
  | zero =>
      intro inputType value locationDefault _ _ hbudget
      have hpositive := inputTypeCoercionDepth_pos inputType
      unfold inputCoercionBudget at hbudget
      omega
  | succ fuel ih =>
      intro inputType value locationDefault hvalid hwidth hbudget
      cases hvalid with
      | «variable» name inputType locationDefault definition _ hlookup husage =>
          have hmem : definition ∈ definitions := List.mem_of_find?_eq_some hlookup
          obtain ⟨value, hvalue, hnonnull, hcorrect⟩ := hvalues definition hmem
          have hname : definition.name = name := by
            simpa using List.find?_some hlookup
          rw [hname] at hvalue
          have htyped := Validation.constInputValue_correctType_of_variableUsageAllowed
            hcorrect hnonnull husage
          have hsource := Validation.constInputValue_valid_toInputValue schema definitions
            locationDefault htyped
          have hsize : inputCoercionSyntaxSize values value.toInputValue + 1 ≤
              inputCoercionSyntaxSize values (.variable name) := by
            simp [inputCoercionSyntaxSize, referencedVariableValuesCoercionFuel, hvalue,
              referencedVariableValuesCoercionFuel_const, inputValueCoercionFuel]
          have hchild := inputCoercionBudget_child reserve width values
            (parentType := inputType) hsize hwidth
          obtain ⟨coerced, hcoerced⟩ :=
            ih inputType value.toInputValue locationDefault hsource hwidth (by omega)
          exact ⟨coerced, by simp [coerceInputValueBounded, hvalue, hcoerced]⟩
      | nullNamed name _ _ =>
          exact ⟨.null, by simp [coerceInputValueBounded]⟩
      | nullList inner _ _ =>
          exact ⟨.null, by simp [coerceInputValueBounded]⟩
      | nonNull value inner _ _ hnotNull hnotVariable hinner =>
          have hwidthInner : inputTypeCoercionDepth inner ≤ width := by
            simp only [inputTypeCoercionDepth] at hwidth; omega
          have hbudgetInner
              : inputCoercionBudget reserve width values inner value ≤ fuel := by
            simp only [inputCoercionBudget, inputTypeCoercionDepth] at hbudget ⊢; omega
          obtain ⟨coerced, hcoerced⟩ :=
            ih inner value none hinner hwidthInner hbudgetInner
          exact ⟨
            coerced,
            by rw [coerceInputValueBounded_nonNull
              schema values fuel inner value hnotNull hnotVariable, hcoerced]
          ⟩
      | list items inner _ _ hitems =>
          have hwidthInner : inputTypeCoercionDepth inner ≤ width := by
            simp only [inputTypeCoercionDepth] at hwidth; omega
          have hcoerceItems : ∀ item, item ∈ items -> ∃ coerced,
              coerceInputValueBounded schema values fuel inner item = .success coerced := by
            intro item hmem
            have hchild := inputCoercionBudget_child reserve width values
              (parentType := .list inner) (inputCoercionSyntaxSize_mem_list values hmem) hwidthInner
            exact ih inner item none (hitems item hmem) hwidthInner (by omega)
          obtain ⟨coerced, hcoerced⟩ :=
            coerceInputValueListBounded_success_of_items hcoerceItems
          exact ⟨.list coerced, by simp [coerceInputValueBounded, hcoerced]⟩
      | objectNamed fields name _ inputObject _ hlookup hfields =>
          have hobjectWell
              : SchemaWellFormedness.inputObjectTypeWellFormed schema inputObject :=
            hschema.2.2.1 (.inputObject inputObject)
              (SchemaWellFormedness.lookupInputObject_mem hlookup)
          cases hfields with
          | intro _ _ _ hknown htyped hrequired _ =>
              have hknownBool := inputObjectFieldsKnownBool_of_known hknown
              have hfieldCoercion : ∀ definition, definition ∈ inputObject.inputFields ->
                  coerceInputObjectFieldValueBounded schema values fuel definition fields ≠ .error := by
                intro definition hdefinition
                cases hsupplied : lookupInputObjectFieldValue? fields definition.name with
                | some value =>
                    have hmem := lookupInputObjectFieldValue_mem hsupplied
                    have hlookupDef :=
                      SchemaWellFormedness.inputValueDefinitions_lookupArgument_of_mem
                        hobjectWell.2.1 hdefinition
                    have hsource :=
                      htyped definition.name value definition hmem hlookupDef
                    have hfieldWidth :=
                      hwidthFields name inputObject definition hlookup hdefinition
                    have hchild := inputCoercionBudget_child reserve width values
                      (parentType := .named name) (inputCoercionSyntaxSize_mem_object values hmem) hfieldWidth
                    obtain ⟨coerced, hcoerced⟩ :=
                      ih definition.inputType value definition.defaultValue
                        hsource hfieldWidth (by omega)
                    simp [coerceInputObjectFieldValueBounded, hsupplied, hcoerced]
                | none =>
                    cases hdefault : definition.defaultValue with
                    | some defaultValue =>
                        have hreserve : reserve ≤ fuel := by
                          simp only [inputCoercionBudget, inputTypeCoercionDepth] at hbudget; omega
                        obtain ⟨coerced, hcoerced⟩ :=
                          hdefaults name inputObject definition defaultValue
                            hlookup hdefinition hdefault fuel hreserve
                        simp [coerceInputObjectFieldValueBounded, hsupplied, hdefault,
                          hcoerced]
                    | none =>
                        have hnullable : definition.inputType.isNonNull = false := by
                          cases htype : definition.inputType with
                          | named _ => rfl
                          | list _ => rfl
                          | nonNull inner =>
                              have hreq : definition.isRequired := by
                                simp [InputValueDefinition.isRequired, htype, hdefault]
                              have hpresent := hrequired definition hdefinition hreq
                              rw [← lookupInputObjectFieldValue_eq_validation, hsupplied]
                                at hpresent
                              cases hpresent
                        simp [coerceInputObjectFieldValueBounded, hsupplied, hdefault,
                          hnullable]
              obtain ⟨coerced, hcoerced⟩ :=
                coerceInputObjectFieldsBounded_success_of_fields hfieldCoercion
              exact ⟨
                .object coerced,
                by simp [coerceInputValueBounded, hlookup, hknownBool, hcoerced]
              ⟩
      | objectAsListItem fields inner _ _ hitem =>
          cases hitem with
          | intro _ _ hinner =>
              have hwidthInner : inputTypeCoercionDepth inner ≤ width := by
                simp only [inputTypeCoercionDepth] at hwidth; omega
              have hbudgetInner
                  : inputCoercionBudget reserve width values inner (.object fields)
                    ≤ fuel := by
                simp only [inputCoercionBudget, inputTypeCoercionDepth] at hbudget ⊢; omega
              obtain ⟨coerced, hcoerced⟩ :=
                ih inner (.object fields) none hinner hwidthInner hbudgetInner
              exact ⟨.list [coerced], by simp [coerceInputValueBounded, hcoerced]⟩
      | singletonListItem value inner _ _ hnotList _ hnotNull hnotVariable hinner =>
          have hwidthInner : inputTypeCoercionDepth inner ≤ width := by
            simp only [inputTypeCoercionDepth] at hwidth; omega
          have hbudgetInner
              : inputCoercionBudget reserve width values inner value ≤ fuel := by
            simp only [inputCoercionBudget, inputTypeCoercionDepth] at hbudget ⊢; omega
          obtain ⟨coerced, hcoerced⟩ :=
            ih inner value none hinner hwidthInner hbudgetInner
          refine ⟨.list [coerced], ?_⟩
          rw [coerceInputValueBounded_singleton schema values fuel inner value
            hnotNull hnotVariable hnotList, hcoerced]
      | namedNonInputObject value name _ _ hnotObject hnotNull hnotVariable hconst hlookup
        =>
          obtain ⟨coerced, heq⟩ := hconst
          have hconverted : ConstInputValue.ofInputValue? value = some coerced :=
            heq ▸ ofInputValue_toInputValue coerced
          refine ⟨coerced, ?_⟩
          cases value <;> simp_all [coerceInputValueBounded]

theorem inputValueDefinition_depth_le {definitions : List InputValueDefinition}
    {definition : InputValueDefinition} (hmem : definition ∈ definitions)
    : inputTypeCoercionDepth definition.inputType
      ≤ inputValueDefinitionsCoercionDepth definitions := by
  induction definitions with
  | nil => cases hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

theorem inputObjectField_depth_le_schema {schema : Schema} {name : Name}
    {inputObject : InputObjectType} {definition : InputValueDefinition}
    (hlookup : schema.lookupInputObject name = some inputObject)
    (hmem : definition ∈ inputObject.inputFields)
    : inputTypeCoercionDepth definition.inputType ≤ schemaInputCoercionDepth schema := by
  have hobject := SchemaWellFormedness.lookupInputObject_mem hlookup
  have hfield := inputValueDefinition_depth_le hmem
  unfold schemaInputCoercionDepth
  generalize schema.types = types at hobject ⊢
  induction types with
  | nil => cases hobject
  | cons head rest ih =>
      rcases List.mem_cons.mp hobject with heq | hmem
      · subst head
        exact Nat.le_trans hfield (Nat.le_max_left _ _)
      · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

-- The remaining schema-only obligation: every input-object field default succeeds
-- within the part of the budget reserved for schema defaults.
def schemaInputDefaultsCoercible (schema : Schema) : Prop :=
  ∀ name inputObject definition defaultValue,
    schema.lookupInputObject name = some inputObject
    -> definition ∈ inputObject.inputFields
    -> definition.defaultValue = some defaultValue
    -> ∀ values fuel,
        schemaInputCoercionFuel schema * schemaInputCoercionDepth schema ≤ fuel
        -> ∃ coerced,
            coerceInputValueBounded schema values fuel definition.inputType
              defaultValue.toInputValue
            = .success coerced

theorem coerceInputValue_success_of_valid_of_defaults
    {schema : Schema} (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hdefaults : schemaInputDefaultsCoercible schema)
    {definitions : List VariableDefinition} {values : VariableValues}
    (hvalues : variablesHaveNonNullValues schema definitions values)
    {inputType : TypeRef} {value : InputValue} {locationDefault : Option ConstInputValue}
    (hvalid
      : Validation.ValueIsCorrectTypeAtLocation schema definitions value inputType
          locationDefault)
    : ∃ coerced, coerceInputValue schema values inputType value = .success coerced := by
  let width := max (inputTypeCoercionDepth inputType) (schemaInputCoercionDepth schema)
  let reserve := schemaInputCoercionFuel schema * width
  have hwidthFields : ∀ name inputObject definition,
      schema.lookupInputObject name = some inputObject ->
      definition ∈ inputObject.inputFields -> inputTypeCoercionDepth definition.inputType ≤ width := by
    intro name object definition hlookup hmem
    exact Nat.le_trans (inputObjectField_depth_le_schema hlookup hmem) (Nat.le_max_right _ _)
  have hdefaultFuel : schemaInputCoercionFuel schema * schemaInputCoercionDepth schema ≤ reserve :=
    Nat.mul_le_mul_left _ (Nat.le_max_right _ _)
  apply coerceInputValueBounded_success_of_valid_of_defaults schema hschema definitions
    values hvalues reserve width hwidthFields
    (fun name object definition defaultValue hlookup hmem hdefault fuel hfuel =>
      hdefaults name object definition defaultValue hlookup hmem hdefault values fuel
        (Nat.le_trans hdefaultFuel hfuel))
    _ inputType value locationDefault hvalid (Nat.le_max_left _ _)
  have hpositive := inputCoercionSyntaxSize_pos values value
  have hsplit : inputCoercionSyntaxSize values value =
      (inputCoercionSyntaxSize values value - 1) + 1 := by omega
  have hmul := congrArg (fun n => n * width) hsplit
  simp only [Nat.add_mul, Nat.one_mul] at hmul
  have hwidth : inputTypeCoercionDepth inputType ≤ width := Nat.le_max_left _ _
  unfold coerceInputValueFuel
  rw [Nat.add_assoc]
  change reserve + (inputCoercionSyntaxSize values value - 1) * width
    + inputTypeCoercionDepth inputType ≤ (schemaInputCoercionFuel schema
      + inputCoercionSyntaxSize values value) * width
  rw [Nat.add_mul]
  change reserve + _ + _ ≤ reserve + _
  omega

end GraphQL.Execution
