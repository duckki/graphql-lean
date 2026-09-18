import Proofs.GraphQL.Execution.InputDefaultBudget

namespace GraphQL.Execution
open SchemaWellFormedness

private theorem constSize_mem_list {values : List ConstInputValue}
    {value : ConstInputValue} (hmem : value ∈ values)
    : constInputValueSize value + 1 ≤ constInputValueSize (.list values) := by
  simp only [constInputValueSize]
  suffices constInputValueSize value ≤ constInputValueListSize values by omega
  induction values with
  | nil => cases hmem
  | cons head rest ih =>
      simp only [constInputValueListSize]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · omega
      · have := ih hmem; omega

private theorem constSize_mem_object {fields : List (Name × ConstInputValue)}
    {name : Name} {value : ConstInputValue} (hmem : (name, value) ∈ fields)
    : constInputValueSize value + 1 ≤ constInputValueSize (.object fields) := by
  simp only [constInputValueSize]
  suffices constInputValueSize value ≤ constInputValueFieldSize fields by omega
  induction fields with
  | nil => cases hmem
  | cons head rest ih =>
      rcases head with ⟨headName, headValue⟩
      simp only [constInputValueFieldSize]
      rcases List.mem_cons.mp hmem with heq | hmem
      · cases heq; omega
      · have := ih hmem; omega

private theorem constField_lookup_mem {fields : List (Name × ConstInputValue)}
    {name : Name} {value : ConstInputValue}
    (hlookup : Schema.getConstInputObjectField? fields name = some value)
    : (name, value) ∈ fields := by
  induction fields with
  | nil => cases hlookup
  | cons head rest ih =>
      rcases head with ⟨headName, headValue⟩
      simp only [Schema.getConstInputObjectField?] at hlookup
      split at hlookup
      · rename_i heq; subst headName; cases Option.some.inj hlookup; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hlookup)

private theorem constField_lookup_map (fields : List (Name × ConstInputValue))
    (name : Name)
    : lookupInputObjectFieldValue? (ConstInputValue.objectFieldsToInputFields fields) name
      = (Schema.getConstInputObjectField? fields name).map
          ConstInputValue.toInputValue := by
  rw [lookupInputObjectFieldValue_eq_validation, Validation.objectFieldsToInputFields_eq_map]
  exact Validation.inputObjectField_map fields name

-- The cycle checker follows value nodes; the execution budget also covers type wrappers.
theorem coerceConstInputValueBounded_success_of_no_default_cycle
    (schema : Schema) (hschema : schemaWellFormed schema) (values : VariableValues)
    (width : Nat)
    (hwidthFields
      : ∀ name inputObject definition,
          schema.lookupInputObject name = some inputObject
          -> definition ∈ inputObject.inputFields
          -> inputTypeCoercionDepth definition.inputType ≤ width)
    : ∀ fuel inputType value visited scanFuel,
        Schema.ConstInputValueIsCorrectType schema value inputType
        -> (∀ inputObject,
              schema.lookupInputObject inputType.namedType = some inputObject
              -> remainingDefaultFuel schema visited + constInputValueSize value
                    ≤ scanFuel
                  ∧ inputObjectDefaultValueHasCycleWithFuel schema scanFuel inputObject
                      value visited
                    = false)
        -> inputTypeCoercionDepth inputType ≤ width
        -> constInputCoercionBudget schema visited width inputType value ≤ fuel
        -> ∃ coerced,
            coerceInputValueBounded schema values fuel inputType value.toInputValue
            = .success coerced := by
  intro fuel
  induction fuel with
  | zero =>
      intro inputType value visited scanFuel _ _ _ hbudget
      have := inputTypeCoercionDepth_pos inputType
      unfold constInputCoercionBudget at hbudget
      omega
  | succ fuel ih =>
      intro inputType value visited scanFuel hvalid hscan hwidth hbudget
      cases hvalid with
      | nullNamed name _ =>
          exact ⟨.null, by simp [ConstInputValue.toInputValue, coerceInputValueBounded]⟩
      | nullList inner _ =>
          exact ⟨.null, by simp [ConstInputValue.toInputValue, coerceInputValueBounded]⟩
      | nonNull value inner _ hnotNull hinner =>
          have hwidthInner : inputTypeCoercionDepth inner ≤ width := by
            simp only [inputTypeCoercionDepth] at hwidth; omega
          have hbudgetInner
              : constInputCoercionBudget schema visited width inner value ≤ fuel := by
            change (defaultReserve schema visited inner + constInputValueSize value - 1) * width
              + (inputTypeCoercionDepth inner + 1) ≤ fuel + 1 at hbudget
            unfold constInputCoercionBudget
            omega
          obtain ⟨coerced, hcoerced⟩ :=
            ih inner value visited scanFuel hinner hscan hwidthInner hbudgetInner
          exact ⟨
            coerced,
            by
              rw [coerceInputValueBounded_nonNull schema values fuel inner value.toInputValue
                (Validation.toInputValue_ne_null hnotNull) (Validation.toInputValue_ne_variable value), hcoerced]
          ⟩
      | list items inner _ hitems =>
          have hwidthInner : inputTypeCoercionDepth inner ≤ width := by
            simp only [inputTypeCoercionDepth] at hwidth; omega
          have hcoerceItems
              : ∀ item,
                  item ∈ ConstInputValue.valuesToInputValues items
                  -> ∃ coerced,
                      coerceInputValueBounded schema values fuel inner item
                      = .success coerced := by
            intro item hmem
            rw [Validation.valuesToInputValues_eq_map] at hmem
            obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmem
            have hsize := constSize_mem_list hsource
            have hchild := constInputCoercionBudget_child schema width
              (visited := visited) (childVisited := visited) (parentType := .list inner)
              (childType := inner) (parent := .list items) (child := source) (by
                change defaultReserve schema visited inner + _ + 1 ≤
                  defaultReserve schema visited inner + _
                omega) hwidthInner
            have hchildScan
                : ∀ inputObject,
                    schema.lookupInputObject inner.namedType = some inputObject
                    -> remainingDefaultFuel schema visited + constInputValueSize source
                          ≤ scanFuel - 1
                        ∧ inputObjectDefaultValueHasCycleWithFuel schema (scanFuel - 1)
                            inputObject source visited
                          = false := by
              intro inputObject hlookup
              obtain ⟨hsizeScan, hcycle⟩ := hscan inputObject hlookup
              cases scanFuel with
              | zero =>
                  have := constInputValueSize_pos (.list items); omega
              | succ scanFuel =>
                  constructor
                  · omega
                  · simpa using List.any_eq_false.mp hcycle source hsource
            exact ih inner source visited (scanFuel - 1) (hitems source hsource)
              hchildScan hwidthInner (by omega)
          obtain ⟨coerced, hcoerced⟩ :=
            coerceInputValueListBounded_success_of_items hcoerceItems
          exact ⟨
            .list coerced,
            by simp [ConstInputValue.toInputValue, coerceInputValueBounded, hcoerced]
          ⟩
      | objectNamed fields name inputObject _ hlookup hfields =>
          have hobjectWell : inputObjectTypeWellFormed schema inputObject :=
            hschema.2.2.1 (.inputObject inputObject) (lookupInputObject_mem hlookup)
          obtain ⟨hscanSize, hcycle⟩ := hscan inputObject hlookup
          have hparentSize := constInputValueSize_pos (.object fields)
          cases scanFuel with
          | zero => omega
          | succ scanFuel =>
              simp only [inputObjectDefaultValueHasCycleWithFuel] at hcycle
              cases hfields with
              | intro _ _ _ hknown htyped hrequired _ =>
                  have hknownBool
                      : inputObjectFieldsKnownBool inputObject.inputFields
                          (ConstInputValue.objectFieldsToInputFields fields)
                        = true := by
                    apply inputObjectFieldsKnownBool_of_known
                    intro fieldName value hmem
                    rw [Validation.objectFieldsToInputFields_eq_map] at hmem
                    obtain ⟨⟨sourceName, sourceValue⟩, hsource, heq⟩ :=
                      List.mem_map.mp hmem
                    cases heq
                    exact hknown sourceName sourceValue hsource
                  have hfieldCoercion
                      : ∀ definition,
                          definition ∈ inputObject.inputFields
                          -> coerceInputObjectFieldValueBounded schema values fuel
                                definition
                                (ConstInputValue.objectFieldsToInputFields fields)
                              ≠ .error := by
                    intro definition hdefinition
                    have hfieldCycle := List.any_eq_false.mp hcycle definition hdefinition
                    have hfieldWidth :=
                      hwidthFields name inputObject definition hlookup hdefinition
                    cases hsupplied
                          : Schema.getConstInputObjectField? fields definition.name with
                    | some source =>
                        have hmem := constField_lookup_mem hsupplied
                        have hlookupDef :=
                          inputValueDefinitions_lookupArgument_of_mem hobjectWell.2.1
                            hdefinition
                        have hsource :=
                          htyped definition.name source definition hmem hlookupDef
                        have hsize := constSize_mem_object hmem
                        have hreserve
                            : defaultReserve schema visited definition.inputType
                              ≤ remainingDefaultFuel schema visited := by
                          unfold defaultReserve; split <;> omega
                        have hchild :=
                          constInputCoercionBudget_child schema width (visited := visited)
                            (childVisited := visited) (parentType := .named name)
                            (childType := definition.inputType) (parent := .object fields)
                            (child := source)
                            (by
                              simp only [defaultReserve, TypeRef.namedType, hlookup, Option.isSome_some,
                                ↓reduceIte]; change defaultReserve schema visited definition.inputType + _ + 1 ≤ _
                              omega)
                            hfieldWidth
                        obtain ⟨coerced, hcoerced⟩ :=
                          ih definition.inputType source visited scanFuel hsource
                            (by intro childObject hchildLookup
                                constructor
                                · omega
                                · simpa [hchildLookup, hsupplied] using hfieldCycle)
                            hfieldWidth
                            (by omega)
                        simp [coerceInputObjectFieldValueBounded, constField_lookup_map, hsupplied, hcoerced]
                    | none =>
                        cases hdefault : definition.defaultValue with
                        | none =>
                            have hnullable : definition.inputType.isNonNull = false := by
                              cases htype : definition.inputType with
                              | named _ => rfl
                              | list _ => rfl
                              | nonNull inner =>
                                  have hreq : definition.isRequired := by
                                    simp [InputValueDefinition.isRequired, htype,
                                      hdefault]
                                  have hpresent := hrequired definition hdefinition hreq
                                  simp [hsupplied] at hpresent
                            simp [coerceInputObjectFieldValueBounded,
                              constField_lookup_map, hsupplied, hdefault, hnullable]
                        | some defaultValue =>
                            have hvalidDefault
                                : Schema.ConstInputValueIsCorrectType schema defaultValue
                                    definition.inputType := by
                              have hwell := (hobjectWell.2.2 definition hdefinition).2
                              simpa [hdefault, ConstInputValue.isCorrectType, Schema.constInputValueIsCorrectType] using hwell
                            have hentry := inputDefaultEntries_mem hlookup hdefinition
                            cases hchildLookup
                                  : schema.lookupInputObject
                                      definition.inputType.namedType with
                            | none =>
                                have hweight :=
                                  remainingDefaultFuel_leaf (visited := visited) hentry
                                    hchildLookup
                                have hsize
                                    : constInputValueSize defaultValue
                                      ≤ remainingDefaultFuel schema visited := by
                                  simpa [inputValueDefinitionCoercionFuel, hdefault,
                                    constInputValueSize_eq_fuel]
                                    using hweight
                                have hchild := constInputCoercionBudget_child schema width
                                  (visited := visited) (childVisited := visited) (parentType := .named name)
                                  (childType := definition.inputType) (parent := .object fields) (child := defaultValue)
                                  (by simp only [defaultReserve, TypeRef.namedType, hlookup, hchildLookup,
                                        Option.isSome_some, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
                                      omega) hfieldWidth
                                obtain ⟨coerced, hcoerced⟩ :=
                                  ih definition.inputType defaultValue visited 0
                                    hvalidDefault
                                    (by
                                      intro childObject himpossible; simp [hchildLookup] at himpossible)
                                    hfieldWidth
                                    (by omega)
                                simp [coerceInputObjectFieldValueBounded, constField_lookup_map, hsupplied,
                                  hdefault, hcoerced]
                            | some childObject =>
                                let coordinate := (inputObject.name, definition.name)
                                have hnotmem : coordinate ∉ visited := by
                                  intro hmem
                                  simp [hchildLookup, hsupplied, hdefault, coordinate, hmem] at hfieldCycle
                                have hremove := remainingDefaultFuel_remove hentry hnotmem
                                  (by simp [hchildLookup])
                                have hsize
                                    : remainingDefaultFuel schema (coordinate :: visited)
                                        + constInputValueSize defaultValue
                                      ≤ remainingDefaultFuel schema visited := by
                                  simpa [inputValueDefinitionCoercionFuel, hdefault,
                                    constInputValueSize_eq_fuel]
                                    using hremove
                                have hchild := constInputCoercionBudget_child schema width
                                  (visited := visited) (childVisited := coordinate :: visited) (parentType := .named name)
                                  (childType := definition.inputType) (parent := .object fields) (child := defaultValue)
                                  (by simp only [defaultReserve, TypeRef.namedType, hlookup, hchildLookup,
                                        Option.isSome_some, ↓reduceIte]
                                      omega) hfieldWidth
                                obtain ⟨coerced, hcoerced⟩ :=
                                  ih definition.inputType defaultValue
                                    (coordinate :: visited)
                                    scanFuel hvalidDefault
                                    (by
                                      intro candidate hcandidate
                                      rw [hchildLookup] at hcandidate
                                      cases Option.some.inj hcandidate
                                      constructor
                                      · omega
                                      · change (inputObject.name, definition.name) ∉ visited at hnotmem
                                        simpa [hchildLookup, hsupplied, hdefault, hnotmem, coordinate] using hfieldCycle)
                                    hfieldWidth
                                    (by omega)
                                simp [coerceInputObjectFieldValueBounded, constField_lookup_map, hsupplied,
                                  hdefault, hcoerced]
                  obtain ⟨coerced, hcoerced⟩ :=
                    coerceInputObjectFieldsBounded_success_of_fields hfieldCoercion
                  exact ⟨
                    .object coerced,
                    by
                      simp [ConstInputValue.toInputValue, coerceInputValueBounded, hlookup, hknownBool, hcoerced]
                  ⟩
      | objectAsListItem fields inner _ hitem =>
          cases hitem with
          | intro _ _ hinner =>
              have hwidthInner : inputTypeCoercionDepth inner ≤ width := by
                simp only [inputTypeCoercionDepth] at hwidth; omega
              have hbudgetInner
                  : constInputCoercionBudget schema visited width inner (.object fields)
                    ≤ fuel := by
                change (defaultReserve schema visited inner + constInputValueSize (.object fields) - 1) * width
                  + (inputTypeCoercionDepth inner + 1) ≤ fuel + 1 at hbudget
                unfold constInputCoercionBudget
                omega
              obtain ⟨coerced, hcoerced⟩ :=
                ih inner (.object fields) visited scanFuel hinner hscan
                  hwidthInner hbudgetInner
              simp only [ConstInputValue.toInputValue] at hcoerced
              exact ⟨
                .list [coerced],
                by
                  simp [ConstInputValue.toInputValue, coerceInputValueBounded, hcoerced]
              ⟩
      | singletonListItem value inner _ hnotList _ hnotNull hinner =>
          have hwidthInner : inputTypeCoercionDepth inner ≤ width := by
            simp only [inputTypeCoercionDepth] at hwidth; omega
          have hbudgetInner
              : constInputCoercionBudget schema visited width inner value ≤ fuel := by
            change (defaultReserve schema visited inner + constInputValueSize value - 1) * width
              + (inputTypeCoercionDepth inner + 1) ≤ fuel + 1 at hbudget
            unfold constInputCoercionBudget
            omega
          obtain ⟨coerced, hcoerced⟩ :=
            ih inner value visited scanFuel hinner hscan hwidthInner hbudgetInner
          refine ⟨.list [coerced], ?_⟩
          rw [
            coerceInputValueBounded_singleton schema values fuel inner value.toInputValue
              (Validation.toInputValue_ne_null
                hnotNull) (Validation.toInputValue_ne_variable value)
              (Validation.toInputValue_ne_list hnotList), hcoerced]
      | namedNonInputObject value name _ hnotObject hnotNull hlookup =>
          refine ⟨value, ?_⟩
          have hconverted := ofInputValue_toInputValue value
          cases value <;> simp_all [ConstInputValue.toInputValue, coerceInputValueBounded]

theorem schemaWellFormed_schemaInputDefaultsCoercible
    {schema : Schema} (hschema : schemaWellFormed schema)
    : schemaInputDefaultsCoercible schema := by
  intro name inputObject definition defaultValue hlookup hmem hdefault values fuel hfuel
  have hobjectWell : inputObjectTypeWellFormed schema inputObject :=
    hschema.2.2.1 (.inputObject inputObject) (lookupInputObject_mem hlookup)
  have hvalid : Schema.ConstInputValueIsCorrectType schema defaultValue definition.inputType := by
    have hwell := (hobjectWell.2.2 definition hmem).2
    simpa [hdefault, ConstInputValue.isCorrectType, Schema.constInputValueIsCorrectType] using hwell
  have hentry := inputDefaultEntries_mem hlookup hmem
  have htotal := remainingDefaultFuel_nil_le_coercion schema
  have htotalScan := remainingDefaultFuel_nil_lt_expansion schema
  have htotalFuel : remainingDefaultFuel schema [] ≤ schemaInputCoercionFuel schema := by
    unfold schemaInputCoercionFuel; omega
  have hready : ∃ visited scanFuel,
      defaultReserve schema visited definition.inputType + constInputValueSize defaultValue
        ≤ schemaInputCoercionFuel schema ∧
      ∀ childObject, schema.lookupInputObject definition.inputType.namedType = some childObject ->
        remainingDefaultFuel schema visited + constInputValueSize defaultValue ≤ scanFuel ∧
        inputObjectDefaultValueHasCycleWithFuel schema scanFuel childObject defaultValue visited = false := by
    cases hchild : schema.lookupInputObject definition.inputType.namedType with
    | none =>
        have hleaf := remainingDefaultFuel_leaf (visited := []) hentry hchild
        have hsize : constInputValueSize defaultValue ≤ remainingDefaultFuel schema [] := by
          simpa [inputValueDefinitionCoercionFuel, hdefault, constInputValueSize_eq_fuel]
            using hleaf
        refine ⟨[], 0, ?_, ?_⟩
        · simp only [defaultReserve, hchild, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            Nat.zero_add]
          omega
        · intro childObject himpossible; cases himpossible
    | some childObject =>
        have hacyclic := hschema.2.2.2.1.2
        unfold inputDefaultExpansionAcyclic inputDefaultExpansionAcyclicBool at hacyclic
        have hinputMember
            : inputObject
              ∈ schema.types.filterMap
                  (fun type =>
                    match type with
                    | .inputObject object => some object
                    | _ => none) :=
          List.mem_filterMap.mpr
            ⟨.inputObject inputObject, lookupInputObject_mem hlookup, rfl⟩
        have hcycle : inputObjectDefaultValueHasCycle schema inputObject = false := by
          simpa using List.all_eq_true.mp hacyclic inputObject hinputMember
        unfold inputObjectDefaultValueHasCycle at hcycle
        cases hexp : inputObjectDefaultExpansionFuel schema with
        | zero => omega
        | succ scanFuel =>
            rw [hexp] at hcycle
            simp only [inputObjectDefaultValueHasCycleWithFuel] at hcycle
            have hfield := List.any_eq_false.mp hcycle definition hmem
            let coordinate := (inputObject.name, definition.name)
            have hremove := remainingDefaultFuel_remove (visited := []) hentry (by simp)
              (by simp [hchild])
            have hsize
                : remainingDefaultFuel schema [coordinate]
                    + constInputValueSize defaultValue
                  ≤ remainingDefaultFuel schema [] := by
              simpa [inputValueDefinitionCoercionFuel, hdefault,
                constInputValueSize_eq_fuel]
                using hremove
            refine ⟨[coordinate], scanFuel, ?_, ?_⟩
            · simp only [defaultReserve, hchild, Option.isSome_some, ↓reduceIte]
              omega
            · intro candidate hcandidate
              cases Option.some.inj hcandidate
              constructor
              · omega
              · simpa [hchild, Schema.getConstInputObjectField?, hdefault, coordinate] using hfield
  obtain ⟨visited, scanFuel, hsize, hscan⟩ := hready
  have hwidth := inputObjectField_depth_le_schema hlookup hmem
  apply coerceConstInputValueBounded_success_of_no_default_cycle schema hschema values
    (schemaInputCoercionDepth schema)
    (fun _ _ _ hlookup hmem => inputObjectField_depth_le_schema hlookup hmem)
    fuel definition.inputType defaultValue visited scanFuel hvalid hscan hwidth
  have hpos := constInputValueSize_pos defaultValue
  have hsplit : defaultReserve schema visited definition.inputType + constInputValueSize defaultValue =
      (defaultReserve schema visited definition.inputType + constInputValueSize defaultValue - 1) + 1 := by
    omega
  have hmul := Nat.mul_le_mul_right (schemaInputCoercionDepth schema) hsize
  rw [hsplit, Nat.add_mul, Nat.one_mul] at hmul
  unfold constInputCoercionBudget
  omega

theorem coerceInputValue_success_of_valid
    {schema : Schema} (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {definitions : List VariableDefinition} {values : VariableValues}
    (hvalues : variablesHaveNonNullValues schema definitions values)
    {inputType : TypeRef} {value : InputValue} {locationDefault : Option ConstInputValue}
    (hvalid
      : Validation.ValueIsCorrectTypeAtLocation schema definitions value inputType
          locationDefault)
    : ∃ coerced, coerceInputValue schema values inputType value = .success coerced :=
  coerceInputValue_success_of_valid_of_defaults hschema
    (schemaWellFormed_schemaInputDefaultsCoercible hschema) hvalues hvalid

end GraphQL.Execution
