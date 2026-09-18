import GraphQL.Validation

/-! Constant defaults satisfy executable-value validation without variable references. -/

namespace GraphQL.Validation

theorem inputObjectField_map (fields : List (Name × ConstInputValue)) (name : Name)
    : getInputObjectField? (fields.map (fun entry => (entry.1, entry.2.toInputValue)))
        name
      = (Schema.getConstInputObjectField? fields name).map
          ConstInputValue.toInputValue := by
  induction fields with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨fieldName, value⟩
      simp only [List.map_cons, getInputObjectField?, Schema.getConstInputObjectField?]
      split <;> simp_all

theorem nonNull_toInputValue {value : ConstInputValue} (h : value.nonNull)
    : inputValueNonNull value.toInputValue := by
  cases value <;> simp_all [ConstInputValue.nonNull, ConstInputValue.toInputValue,
    inputValueNonNull]

theorem valuesToInputValues_eq_map (values : List ConstInputValue)
    : ConstInputValue.valuesToInputValues values
      = values.map ConstInputValue.toInputValue := by
  induction values <;> simp_all [ConstInputValue.valuesToInputValues]

theorem objectFieldsToInputFields_eq_map (fields : List (Name × ConstInputValue))
    : ConstInputValue.objectFieldsToInputFields fields
      = fields.map (fun entry => (entry.1, entry.2.toInputValue)) := by
  induction fields with
  | nil => rfl
  | cons head rest ih =>
      cases head
      simp [ConstInputValue.objectFieldsToInputFields, ih]

theorem toInputValue_ne_null {value : ConstInputValue} (h : value ≠ .null)
    : value.toInputValue ≠ .null := by
  cases value <;> simp_all [ConstInputValue.toInputValue]

theorem toInputValue_ne_variable (value : ConstInputValue) (name : Name)
    : value.toInputValue ≠ .variable name := by
  cases value <;> simp [ConstInputValue.toInputValue]

theorem toInputValue_ne_list {value : ConstInputValue}
    (h : ∀ values, value ≠ .list values) (values : List InputValue)
    : value.toInputValue ≠ .list values := by
  cases value <;> simp_all [ConstInputValue.toInputValue]

theorem toInputValue_ne_object {value : ConstInputValue}
    (h : ∀ fields, value ≠ .object fields) (fields : List (Name × InputValue))
    : value.toInputValue ≠ .object fields := by
  cases value <;> simp_all [ConstInputValue.toInputValue]

theorem constInputValue_valid_toInputValue (schema : Schema)
    (definitions : List VariableDefinition) (locationDefault : Option ConstInputValue)
    {value : ConstInputValue} {inputType : TypeRef}
    (h : Schema.ConstInputValueIsCorrectType schema value inputType)
    : ValueIsCorrectTypeAtLocation schema definitions value.toInputValue inputType
        locationDefault := by
  revert locationDefault
  refine Schema.ConstInputValueIsCorrectType.rec
    (motive_1 :=
      fun value inputType _ =>
        ∀ locationDefault,
          ValueIsCorrectTypeAtLocation schema definitions value.toInputValue inputType
            locationDefault)
    (motive_2 :=
      fun fieldDefinitions fields _ =>
        InputObjectFieldsValid schema definitions
          fieldDefinitions (fields.map fun entry => (entry.1, entry.2.toInputValue)))
    (motive_3 :=
      fun fields inputType _ =>
        InputObjectAsListItemValid schema definitions
          (fields.map fun entry => (entry.1, entry.2.toInputValue)) inputType)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro name hinput locationDefault
    exact .nullNamed _ _ hinput
  · intro inner hinput locationDefault
    exact .nullList _ _ hinput
  · intro value inner hinput hnotNull _ ih locationDefault
    exact .nonNull _ _ _ hinput (toInputValue_ne_null hnotNull)
      (toInputValue_ne_variable value) (ih none)
  · intro values inner hinput _ ih locationDefault
    refine .list _ _ _ hinput ?_
    intro item hitem
    rw [valuesToInputValues_eq_map] at hitem
    obtain ⟨value, hmem, rfl⟩ := List.mem_map.mp hitem
    exact ih value hmem none
  · intro fields name object hinput hlookup _ ih locationDefault
    apply ValueIsCorrectTypeAtLocation.objectNamed _ _ _ object hinput hlookup
    simpa only [objectFieldsToInputFields_eq_map] using ih
  · intro fields inner hinput _ ih locationDefault
    apply ValueIsCorrectTypeAtLocation.objectAsListItem _ _ _ hinput
    simpa only [objectFieldsToInputFields_eq_map] using ih
  · intro value inner hinput hnotList hnotObject hnotNull _ ih locationDefault
    exact .singletonListItem _ _ _ hinput (toInputValue_ne_list hnotList)
      (toInputValue_ne_object hnotObject) (toInputValue_ne_null hnotNull)
      (toInputValue_ne_variable value) (ih none)
  · intro value name hinput hnotObject hnotNull hlookup locationDefault
    exact .namedNonInputObject _ _ _ hinput (toInputValue_ne_object hnotObject)
      (toInputValue_ne_null hnotNull) (toInputValue_ne_variable value) ⟨value, rfl⟩ hlookup
  · intro fieldDefinitions fields hnodup hknown _ hrequired hnonnull ih
    refine .intro _ _ ?_ ?_ ?_ ?_ ?_
    · simpa [List.map_map, Function.comp_def] using hnodup
    · intro name value hmem
      obtain ⟨⟨sourceName, sourceValue⟩, hsource, heq⟩ := List.mem_map.mp hmem
      cases heq
      exact hknown sourceName sourceValue hsource
    · intro name value definition hmem hlookup
      obtain ⟨⟨sourceName, sourceValue⟩, hsource, heq⟩ := List.mem_map.mp hmem
      cases heq
      exact ih sourceName sourceValue definition hsource hlookup definition.defaultValue
    · intro definition hmem hreq
      rw [inputObjectField_map]
      simpa using hrequired definition hmem hreq
    · intro definition value hmem hreq hlookup
      rw [inputObjectField_map] at hlookup
      cases hsource : Schema.getConstInputObjectField? fields definition.name with
      | none => simp [hsource] at hlookup
      | some source =>
          have heq : value = source.toInputValue := by simpa [hsource] using hlookup.symm
          subst value
          exact nonNull_toInputValue (hnonnull definition source hmem hreq hsource)
  · intro fields inputType _ ih
    apply InputObjectAsListItemValid.intro
    simpa only [ConstInputValue.toInputValue, objectFieldsToInputFields_eq_map] using ih none

end GraphQL.Validation
