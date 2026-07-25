import GraphQL.NormalForm
import GraphQL.SchemaWellFormedness.PossibleTypes
import GraphQL.Validation.SelectionValidity

/-!
Lookup-validity facts shared by NormalForm proof families.
-/

namespace GraphQL

namespace NormalForm

mutual
  def selectionLookupValid (schema : Schema) (parentType : Name) : Selection -> Prop
    | .field _responseName fieldName _arguments _directives _selectionSet =>
        ∃ fieldDefinition, schema.lookupField parentType fieldName = some fieldDefinition
    | .inlineFragment none _directives selectionSet =>
        selectionSetLookupValid schema parentType selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        selectionSetLookupValid schema typeCondition selectionSet

  def selectionSetLookupValid (schema : Schema)
      (parentType : Name) (selectionSet : List Selection)
      : Prop :=
    ∀ selection,
      selection ∈ selectionSet -> selectionLookupValid schema parentType selection
end

theorem selectionSetLookupValid_nil (schema : Schema) (parentType : Name)
    : selectionSetLookupValid schema parentType [] := by
  simp [selectionSetLookupValid]

theorem selectionSetLookupValid_append
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    : selectionSetLookupValid schema parentType left
      -> selectionSetLookupValid schema parentType right
      -> selectionSetLookupValid schema parentType (left ++ right) := by
  intro hleft hright
  unfold selectionSetLookupValid at hleft hright ⊢
  intro selection hselection
  rcases List.mem_append.mp hselection with hselection | hselection
  · exact hleft selection hselection
  · exact hright selection hselection

theorem selectionSetLookupValid_append_left
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    : selectionSetLookupValid schema parentType (left ++ right)
      -> selectionSetLookupValid schema parentType left := by
  intro hvalid
  unfold selectionSetLookupValid at hvalid ⊢
  intro selection hselection
  exact hvalid selection (List.mem_append.mpr (Or.inl hselection))

theorem selectionSetLookupValid_append_right
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    : selectionSetLookupValid schema parentType (left ++ right)
      -> selectionSetLookupValid schema parentType right := by
  intro hvalid
  unfold selectionSetLookupValid at hvalid ⊢
  intro selection hselection
  exact hvalid selection (List.mem_append.mpr (Or.inr hselection))

theorem selectionSetLookupValid_tail
    {schema : Schema} {parentType : Name}
    {selection : Selection} {selectionSet : List Selection}
    : selectionSetLookupValid schema parentType (selection :: selectionSet)
      -> selectionSetLookupValid schema parentType selectionSet := by
  intro hvalid
  unfold selectionSetLookupValid at hvalid ⊢
  intro candidate hcandidate
  exact hvalid candidate (List.mem_cons_of_mem selection hcandidate)

theorem selectionSetLookupValid_head
    {schema : Schema} {parentType : Name}
    {selection : Selection} {selectionSet : List Selection}
    : selectionSetLookupValid schema parentType (selection :: selectionSet)
      -> selectionLookupValid schema parentType selection := by
  intro hvalid
  unfold selectionSetLookupValid at hvalid
  exact hvalid selection (by simp)

theorem selectionSetLookupValid_withoutFieldSelectionsWithResponseName_core
    (schema : Schema) (responseName : Name)
    : ∀ parentType selectionSet,
        selectionSetLookupValid schema parentType selectionSet
        -> selectionSetLookupValid schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
  | _parentType, [], _hvalid => by
      simp [withoutFieldSelectionsWithResponseName, selectionSetLookupValid]
  | parentType, selection :: rest, hvalid => by
      have hhead :
          selectionLookupValid schema parentType selection := by
        unfold selectionSetLookupValid at hvalid
        exact hvalid selection (by simp)
      have htail :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hvalid
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldSelectionsWithResponseName, hname]
            simpa [selectionSetLookupValid] using
              selectionSetLookupValid_withoutFieldSelectionsWithResponseName_core
                schema responseName parentType rest htail
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldSelectionsWithResponseName, hfalse,
              selectionSetLookupValid]
            constructor
            · exact hhead
            · simpa [selectionSetLookupValid] using
                selectionSetLookupValid_withoutFieldSelectionsWithResponseName_core
                  schema responseName parentType rest htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [withoutFieldSelectionsWithResponseName,
                selectionSetLookupValid, selectionLookupValid]
              constructor
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldSelectionsWithResponseName_core
                    schema responseName parentType selectionSet
                    (by simpa [selectionLookupValid] using hhead)
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldSelectionsWithResponseName_core
                    schema responseName parentType rest htail
          | some typeCondition =>
              simp [withoutFieldSelectionsWithResponseName,
                selectionSetLookupValid, selectionLookupValid]
              constructor
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldSelectionsWithResponseName_core
                    schema responseName typeCondition selectionSet
                    (by simpa [selectionLookupValid] using hhead)
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldSelectionsWithResponseName_core
                    schema responseName parentType rest htail

mutual
  theorem selectionLookupValid_of_selectionValid
      {schema : Schema} {variableDefinitions : List VariableDefinition}
      {parentType : Name}
      : ∀ selection,
          Validation.selectionValid schema variableDefinitions parentType selection
          -> selectionLookupValid schema parentType selection
    | .field _responseName fieldName _arguments _directives _selectionSet,
        hvalid => by
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
        simpa [selectionLookupValid] using ⟨fieldDefinition, hlookup⟩
    | .inlineFragment none _directives selectionSet, hvalid => by
        simpa [selectionLookupValid] using
          selectionSetLookupValid_of_selectionSetValid selectionSet
            (Validation.selectionValid_inlineFragment_none_selectionSetValid
              hvalid)
    | .inlineFragment (some typeCondition) _directives selectionSet, hvalid => by
        simpa [selectionLookupValid] using
          selectionSetLookupValid_of_selectionSetValid selectionSet
            (Validation.selectionValid_inlineFragment_some_selectionSetValid
              hvalid)

  theorem selectionSetLookupValid_of_selectionSetValid
      {schema : Schema} {variableDefinitions : List VariableDefinition}
      {parentType : Name}
      : ∀ selectionSet,
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetLookupValid schema parentType selectionSet
    | [], _hvalid => by
        exact selectionSetLookupValid_nil schema parentType
    | selection :: rest, hvalid => by
        have hhead :
            Validation.selectionValid schema variableDefinitions parentType
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        have htail :
            Validation.selectionSetValid schema variableDefinitions parentType
              rest :=
          Validation.selectionSetValid_tail hvalid
        simp [selectionSetLookupValid]
        constructor
        · exact selectionLookupValid_of_selectionValid selection hhead
        · simpa [selectionSetLookupValid] using
            selectionSetLookupValid_of_selectionSetValid rest htail
end

mutual
  theorem selectionLookupValid_of_selectionValid_possibleObject
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (parentType objectType : Name)
      : SchemaWellFormedness.schemaWellFormed schema
        -> objectType ∈ schema.getPossibleTypes parentType
        -> ∀ selection,
            Validation.selectionValid schema variableDefinitions parentType selection
            -> selectionLookupValid schema objectType selection
    | hschema, hpossible,
      .field _responseName fieldName _arguments _directives _selectionSet,
      hvalid => by
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
        simp [selectionLookupValid]
        exact
          SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_exists
            hschema hpossible hlookup
    | hschema, hpossible,
      .inlineFragment none _directives selectionSet, hvalid => by
        simpa [selectionLookupValid] using
          selectionSetLookupValid_of_selectionSetValid_possibleObject
            schema variableDefinitions parentType objectType hschema
            hpossible selectionSet
            (Validation.selectionValid_inlineFragment_none_selectionSetValid
              hvalid)
    | _hschema, _hpossible,
      .inlineFragment (some _typeCondition) _directives selectionSet,
      hvalid => by
        simpa [selectionLookupValid] using
          selectionSetLookupValid_of_selectionSetValid selectionSet
            (Validation.selectionValid_inlineFragment_some_selectionSetValid
              hvalid)

  theorem selectionSetLookupValid_of_selectionSetValid_possibleObject
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (parentType objectType : Name)
      : SchemaWellFormedness.schemaWellFormed schema
        -> objectType ∈ schema.getPossibleTypes parentType
        -> ∀ selectionSet,
            Validation.selectionSetValid schema variableDefinitions parentType
              selectionSet
            -> selectionSetLookupValid schema objectType selectionSet
    | _hschema, _hpossible, [], _hvalid => by
        exact selectionSetLookupValid_nil schema objectType
    | hschema, hpossible, selection :: rest, hvalid => by
        have hhead :
            Validation.selectionValid schema variableDefinitions parentType
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        have htail :
            Validation.selectionSetValid schema variableDefinitions parentType
              rest :=
          Validation.selectionSetValid_tail hvalid
        simp [selectionSetLookupValid]
        constructor
        · exact selectionLookupValid_of_selectionValid_possibleObject schema
            variableDefinitions parentType objectType hschema hpossible
            selection hhead
        · simpa [selectionSetLookupValid] using
            selectionSetLookupValid_of_selectionSetValid_possibleObject
              schema variableDefinitions parentType objectType hschema
              hpossible rest htail
end

end NormalForm

end GraphQL
