import Proofs.GraphQL.Execution.InputCoercionValidity

namespace GraphQL.Execution
open SchemaWellFormedness

-- Each coordinate contributes its default's syntax until that default is expanded.
-- Scalar defaults remain available because they cannot participate in a cycle.
def inputDefaultEntries (schema : Schema) : List ((Name × Name) × InputValueDefinition) :=
  schema.types.flatMap
    fun type =>
      match type with
      | .inputObject object =>
          object.inputFields.map fun field => ((object.name, field.name), field)
      | _ => []

def remainingDefaultWeight (schema : Schema) (visited : List (Name × Name))
    (entry : (Name × Name) × InputValueDefinition)
    : Nat :=
  if entry.1 ∈ visited
      ∧ (schema.lookupInputObject entry.2.inputType.namedType).isSome = true then
    0
  else
    inputValueDefinitionCoercionFuel entry.2

def remainingDefaultFuel (schema : Schema) (visited : List (Name × Name)) : Nat :=
  ((inputDefaultEntries schema).map (remainingDefaultWeight schema visited)).sum

theorem remainingDefaultWeight_cons_le (schema : Schema) (visited : List (Name × Name))
    (coordinate : Name × Name) (entry : (Name × Name) × InputValueDefinition)
    : remainingDefaultWeight schema (coordinate :: visited) entry
      ≤ remainingDefaultWeight schema visited entry := by
  simp only [remainingDefaultWeight, List.mem_cons]
  split <;> split <;> simp_all <;> omega

theorem remainingDefaultFuel_cons_le (schema : Schema) (visited : List (Name × Name))
    (coordinate : Name × Name)
    : remainingDefaultFuel schema (coordinate :: visited)
      ≤ remainingDefaultFuel schema visited := by
  unfold remainingDefaultFuel
  induction inputDefaultEntries schema with
  | nil => simp
  | cons head rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have := remainingDefaultWeight_cons_le schema visited coordinate head
      omega

theorem inputDefaultEntries_mem {schema : Schema} {name : Name} {object : InputObjectType}
    {field : InputValueDefinition} (hlookup : schema.lookupInputObject name = some object)
    (hmem : field ∈ object.inputFields)
    : ((object.name, field.name), field) ∈ inputDefaultEntries schema := by
  apply List.mem_flatMap.mpr
  exact ⟨.inputObject object, lookupInputObject_mem hlookup,
    List.mem_map.mpr ⟨field, hmem, rfl⟩⟩

theorem remainingDefaultFuel_remove {schema : Schema} {visited : List (Name × Name)}
    {coordinate : Name × Name} {field : InputValueDefinition}
    (hmem : (coordinate, field) ∈ inputDefaultEntries schema)
    (hnotmem : coordinate ∉ visited)
    (hobject : (schema.lookupInputObject field.inputType.namedType).isSome = true)
    : remainingDefaultFuel schema (coordinate :: visited)
        + inputValueDefinitionCoercionFuel field
      ≤ remainingDefaultFuel schema visited := by
  unfold remainingDefaultFuel
  generalize inputDefaultEntries schema = entries at hmem ⊢
  induction entries with
  | nil => cases hmem
  | cons head rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · have hrest
            : (rest.map (remainingDefaultWeight schema (coordinate :: visited))).sum
              ≤ (rest.map (remainingDefaultWeight schema visited)).sum := by
          clear ih hmem
          induction rest with
          | nil => simp
          | cons head rest ih =>
              simp only [List.map_cons, List.sum_cons]
              have := remainingDefaultWeight_cons_le schema visited coordinate head
              omega
        simp [remainingDefaultWeight, hnotmem, hobject]
        omega
      · have hhead := remainingDefaultWeight_cons_le schema visited coordinate head
        have hrest := ih hmem
        omega

theorem remainingDefaultFuel_leaf {schema : Schema} {visited : List (Name × Name)}
    {coordinate : Name × Name} {field : InputValueDefinition}
    (hmem : (coordinate, field) ∈ inputDefaultEntries schema)
    (hobject : schema.lookupInputObject field.inputType.namedType = none)
    : inputValueDefinitionCoercionFuel field ≤ remainingDefaultFuel schema visited := by
  have hweight : remainingDefaultWeight schema visited (coordinate, field) =
      inputValueDefinitionCoercionFuel field := by simp [remainingDefaultWeight, hobject]
  rw [← hweight]
  unfold remainingDefaultFuel
  generalize inputDefaultEntries schema = entries at hmem ⊢
  induction entries with
  | nil => cases hmem
  | cons head rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · omega
      · have := ih hmem; omega

mutual
  theorem constInputValueSize_eq_fuel (value : ConstInputValue)
      : constInputValueSize value = inputValueCoercionFuel value.toInputValue := by
    cases value <;> simp [constInputValueSize, ConstInputValue.toInputValue,
      inputValueCoercionFuel, constInputValueListSize_eq_fuel, constInputValueFieldSize_eq_fuel,
      Nat.add_comm]

  theorem constInputValueListSize_eq_fuel (values : List ConstInputValue)
      : constInputValueListSize values
        = inputValuesCoercionFuel (ConstInputValue.valuesToInputValues values) := by
    cases values <;> simp [constInputValueListSize, ConstInputValue.valuesToInputValues,
      inputValuesCoercionFuel, constInputValueSize_eq_fuel, constInputValueListSize_eq_fuel]

  theorem constInputValueFieldSize_eq_fuel (fields : List (Name × ConstInputValue))
      : constInputValueFieldSize fields
        = inputObjectFieldsCoercionFuel
            (ConstInputValue.objectFieldsToInputFields fields) := by
    cases fields with
    | nil => rfl
    | cons head rest =>
        cases head
        simp [constInputValueFieldSize, ConstInputValue.objectFieldsToInputFields,
          inputObjectFieldsCoercionFuel, constInputValueSize_eq_fuel, constInputValueFieldSize_eq_fuel]
end

theorem constInputValueSize_pos (value : ConstInputValue)
    : 0 < constInputValueSize value := by
  cases value <;> simp [constInputValueSize] <;> omega

theorem remainingDefaultFuel_nil_le_coercion (schema : Schema)
    : remainingDefaultFuel schema [] ≤ typeDefinitionsInputCoercionFuel schema.types := by
  unfold remainingDefaultFuel inputDefaultEntries
  simp only [show remainingDefaultWeight schema [] =
      (fun entry => inputValueDefinitionCoercionFuel entry.2) from by
    funext entry; simp [remainingDefaultWeight]]
  induction schema.types with
  | nil => simp [typeDefinitionsInputCoercionFuel]
  | cons head rest ih =>
      cases head <;> simp only [List.flatMap_cons, List.map_append, List.sum_append,
        typeDefinitionsInputCoercionFuel, typeDefinitionInputCoercionFuel,
        List.nil_append] <;> try omega
      case inputObject object =>
        have heq
            : ((object.inputFields.map
                  fun field => ((object.name, field.name), field)).map
                fun entry => inputValueDefinitionCoercionFuel entry.2).sum
              = inputValueDefinitionsCoercionFuel object.inputFields := by
          induction object.inputFields with
          | nil => rfl
          | cons head rest ih =>
              simpa only [List.map_cons, List.sum_cons, inputValueDefinitionsCoercionFuel]
                using congrArg (fun n => inputValueDefinitionCoercionFuel head + n) ih
        rw [heq]
        omega

theorem remainingDefaultFuel_nil_lt_expansion (schema : Schema)
    : remainingDefaultFuel schema [] < inputObjectDefaultExpansionFuel schema := by
  unfold remainingDefaultFuel inputDefaultEntries inputObjectDefaultExpansionFuel
  simp only [show remainingDefaultWeight schema [] =
      (fun entry => inputValueDefinitionCoercionFuel entry.2) from by
    funext entry; simp [remainingDefaultWeight]]
  induction schema.types with
  | nil => simp
  | cons head rest ih =>
      cases head <;> simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.foldr_cons, List.nil_append] <;> try exact ih
      case inputObject object =>

        induction object.inputFields with
        | nil => simpa using ih
        | cons head rest ihFields =>
            simp only [List.map_cons, List.sum_cons, List.foldr_cons]
            cases hdefault : head.defaultValue <;>
              simp only [inputValueDefinitionCoercionFuel, hdefault, constInputValueSize_eq_fuel] at * <;> omega

def defaultReserve (schema : Schema) (visited : List (Name × Name)) (inputType : TypeRef)
    : Nat :=
  if (schema.lookupInputObject inputType.namedType).isSome then
    remainingDefaultFuel schema visited
  else
    0

def constInputCoercionBudget (schema : Schema) (visited : List (Name × Name))
    (width : Nat) (inputType : TypeRef) (value : ConstInputValue)
    : Nat :=
  (defaultReserve schema visited inputType + constInputValueSize value - 1) * width
  + inputTypeCoercionDepth inputType

theorem constInputCoercionBudget_child (schema : Schema) (width : Nat)
    {visited childVisited : List (Name × Name)} {parentType childType : TypeRef}
    {parent child : ConstInputValue}
    (hsize
      : defaultReserve schema childVisited childType + constInputValueSize child + 1
        ≤ defaultReserve schema visited parentType + constInputValueSize parent)
    (hwidth : inputTypeCoercionDepth childType ≤ width)
    : constInputCoercionBudget schema childVisited width childType child + 1
      ≤ constInputCoercionBudget schema visited width parentType parent := by
  have hpos := constInputValueSize_pos child
  have hparent := inputTypeCoercionDepth_pos parentType
  have hle : defaultReserve schema childVisited childType + constInputValueSize child ≤
      defaultReserve schema visited parentType + constInputValueSize parent - 1 := by omega
  have hmul := Nat.mul_le_mul_right width hle
  have hsplit : defaultReserve schema childVisited childType + constInputValueSize child =
      (defaultReserve schema childVisited childType + constInputValueSize child - 1) + 1 := by omega
  rw [hsplit, Nat.add_mul, Nat.one_mul] at hmul
  unfold constInputCoercionBudget
  omega

end GraphQL.Execution
