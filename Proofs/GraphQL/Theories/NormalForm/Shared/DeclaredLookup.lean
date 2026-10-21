import Proofs.GraphQL.Theories.NormalForm.Shared.LookupValidity
import Proofs.GraphQL.Theories.NormalForm.Shared.RuntimeTypes

/-! Recursive declared-scope lookup evidence, allowing empty filtered selections. -/

namespace GraphQL.NormalForm

mutual
  def selectionDeclaredLookupReady (schema : Schema) (parentType : Name)
      : Selection -> Prop
    | .field _ fieldName _ _ children =>
        ∃ definition,
          schema.lookupField parentType fieldName = some definition
          ∧ selectionSetDeclaredLookupReady schema definition.outputType.namedType
              children
    | .inlineFragment none _ children =>
        selectionSetDeclaredLookupReady schema parentType children
    | .inlineFragment (some condition) _ children =>
        selectionSetDeclaredLookupReady schema condition children

  def selectionSetDeclaredLookupReady (schema : Schema) (parentType : Name)
      (selectionSet : List Selection)
      : Prop :=
    ∀ selection,
      selection ∈ selectionSet -> selectionDeclaredLookupReady schema parentType selection
end

theorem selectionSetDeclaredLookupReady_append {schema : Schema} {parentType : Name}
    {left right : List Selection}
    (hleft : selectionSetDeclaredLookupReady schema parentType left)
    (hright : selectionSetDeclaredLookupReady schema parentType right)
    : selectionSetDeclaredLookupReady schema parentType (left ++ right) := by
  unfold selectionSetDeclaredLookupReady at hleft hright ⊢
  intro selection hselection
  exact (List.mem_append.mp hselection).elim (hleft selection) (hright selection)

mutual
  theorem selectionDeclaredLookupReady_of_valid (schema : Schema)
      (definitions : List VariableDefinition) (parentType : Name)
      : ∀ selection,
          Validation.selectionValid schema definitions parentType selection
          -> selectionDeclaredLookupReady schema parentType selection
    | .field responseName fieldName arguments directives children, hvalid => by
        simp only [selectionDeclaredLookupReady]
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨definition, hlookup, _, hchildren⟩
        refine ⟨definition, hlookup, ?_⟩
        unfold Validation.fieldSelectionSetValid at hchildren
        rcases hchildren.2 with ⟨_, rfl⟩ | ⟨_, _, hchildren⟩
        · simp [selectionSetDeclaredLookupReady]
        · exact selectionSetDeclaredLookupReady_of_valid schema definitions
            definition.outputType.namedType children hchildren
    | .inlineFragment none directives children, hvalid => by
        simp only [selectionDeclaredLookupReady]
        exact selectionSetDeclaredLookupReady_of_valid schema definitions parentType children
          (Validation.selectionValid_inlineFragment_none_selectionSetValid hvalid)
    | .inlineFragment (some condition) directives children, hvalid => by
        simp only [selectionDeclaredLookupReady]
        exact selectionSetDeclaredLookupReady_of_valid schema definitions condition children
          (Validation.selectionValid_inlineFragment_some_selectionSetValid hvalid)

  theorem selectionSetDeclaredLookupReady_of_valid (schema : Schema)
      (definitions : List VariableDefinition) (parentType : Name)
      : ∀ selectionSet,
          Validation.selectionSetValid schema definitions parentType selectionSet
          -> selectionSetDeclaredLookupReady schema parentType selectionSet
    | [], _ => by simp [selectionSetDeclaredLookupReady]
    | selection :: rest, hvalid => by
        have hhead := (by
          unfold Validation.selectionSetValid at hvalid
          exact hvalid selection (by simp))
        have htail := Validation.selectionSetValid_tail hvalid
        unfold selectionSetDeclaredLookupReady
        intro candidate hcandidate
        rcases List.mem_cons.mp hcandidate with heq | hcandidate
        · rw [heq]
          exact selectionDeclaredLookupReady_of_valid schema definitions parentType selection hhead
        · have hrest := selectionSetDeclaredLookupReady_of_valid schema definitions parentType rest htail
          unfold selectionSetDeclaredLookupReady at hrest
          exact hrest candidate hcandidate
end

theorem collectFields_declaredLookupReady (schema : Schema)
    : ∀ parentType selectionSet source,
        selectionSetDeclaredLookupReady schema parentType selectionSet
        -> source ∈ FieldMerge.collectFields schema parentType selectionSet
        -> ∃ definition,
            schema.lookupField source.parentType source.fieldName = some definition
            ∧ definition.outputType = source.outputType
            ∧ selectionSetDeclaredLookupReady schema source.outputType.namedType
                source.selectionSet
  | parentType, [], source, _, hsource => by simp [FieldMerge.collectFields] at hsource
  | parentType, selection :: rest, source, hready, hsource => by
      unfold selectionSetDeclaredLookupReady at hready
      have hhead := hready selection (by simp)
      have htail : selectionSetDeclaredLookupReady schema parentType rest := by
        unfold selectionSetDeclaredLookupReady
        exact fun candidate hcandidate => hready candidate (by simp [hcandidate])
      cases selection with
      | field responseName fieldName arguments directives children =>
          simp only [selectionDeclaredLookupReady] at hhead
          rcases hhead with ⟨definition, hlookup, hchildren⟩
          simp only [FieldMerge.collectFields, hlookup, List.singleton_append,
            List.mem_cons] at hsource
          rcases hsource with rfl | hsource
          · exact ⟨definition, hlookup, rfl, hchildren⟩
          · exact collectFields_declaredLookupReady schema parentType rest source htail hsource
      | inlineFragment condition directives children =>
          cases condition with
          | none =>
              simp only [selectionDeclaredLookupReady] at hhead
              simp only [FieldMerge.collectFields] at hsource
              rcases List.mem_append.mp hsource with hsource | hsource
              · exact collectFields_declaredLookupReady schema parentType children source hhead hsource
              · exact collectFields_declaredLookupReady schema parentType rest source htail hsource
          | some condition =>
              simp only [selectionDeclaredLookupReady] at hhead
              simp only [FieldMerge.collectFields] at hsource
              rcases List.mem_append.mp hsource with hsource | hsource
              · exact collectFields_declaredLookupReady schema condition children source hhead hsource
              · exact collectFields_declaredLookupReady schema parentType rest source htail hsource

theorem runtimeFields_declaredSource (schema : Schema)
    (runtimeType : Name) (hobject : schema.objectType runtimeType)
    : ∀ parentType selectionSet responseName fieldName arguments directives children,
        schema.typeIncludesObjectBool parentType runtimeType = true
        -> selectionSetDeclaredLookupReady schema parentType selectionSet
        -> Selection.field responseName fieldName arguments directives children
            ∈ fieldSelectionsWithResponseNameInScope schema runtimeType responseName
                selectionSet
        -> ∃ source,
            source ∈ FieldMerge.collectFields schema parentType selectionSet
            ∧ schema.typeIncludesObjectBool source.parentType runtimeType = true
            ∧ source.responseName = responseName
            ∧ source.fieldName = fieldName
            ∧ source.arguments = arguments
            ∧ source.selectionSet = children
  | parentType, [], responseName, fieldName, arguments, directives, children,
      _, _, hfield => by simp [fieldSelectionsWithResponseNameInScope] at hfield
  | parentType, selection :: rest, responseName, fieldName, arguments, directives, children,
      happlies, hready, hfield => by
      unfold selectionSetDeclaredLookupReady at hready
      have hhead := hready selection (by simp)
      have htail : selectionSetDeclaredLookupReady schema parentType rest := by
        unfold selectionSetDeclaredLookupReady
        exact fun candidate hcandidate => hready candidate (by simp [hcandidate])
      have hrestSource (hfield : Selection.field responseName fieldName arguments directives children
          ∈ fieldSelectionsWithResponseNameInScope schema runtimeType responseName rest) :=
        runtimeFields_declaredSource schema runtimeType hobject parentType rest responseName
          fieldName arguments directives children happlies htail hfield
      cases selection with
      | field name selectedName selectedArguments selectedDirectives selectedChildren =>
          simp only [selectionDeclaredLookupReady] at hhead
          rcases hhead with ⟨definition, hlookup, _⟩
          simp only [fieldSelectionsWithResponseNameInScope] at hfield
          split at hfield
          · rcases List.mem_cons.mp hfield with heq | hfield
            · cases heq
              let source : FieldMerge.ScopedField := {
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                outputType := definition.outputType
                selectionSet := children
              }
              exact ⟨source,
                by simp [source, FieldMerge.collectFields, hlookup], happlies,
                rfl, rfl, rfl, rfl⟩
            · rcases hrestSource hfield with ⟨source, hsource, hrest⟩
              exact ⟨source, by simp [FieldMerge.collectFields, hlookup, hsource], hrest⟩
          · rcases hrestSource hfield with ⟨source, hsource, hrest⟩
            exact ⟨source, by simp [FieldMerge.collectFields, hlookup, hsource], hrest⟩
      | inlineFragment condition selectedDirectives selectedChildren =>
          cases condition with
          | none =>
              simp only [selectionDeclaredLookupReady] at hhead
              simp only [fieldSelectionsWithResponseNameInScope] at hfield
              simp only [FieldMerge.collectFields]
              rcases List.mem_append.mp hfield with hfield | hfield
              · rcases runtimeFields_declaredSource schema runtimeType hobject parentType
                  selectedChildren responseName fieldName arguments directives children happlies
                  hhead hfield with ⟨source, hsource, hrest⟩
                exact ⟨source, List.mem_append_left _ hsource, hrest⟩
              · rcases hrestSource hfield with ⟨source, hsource, hrest⟩
                exact ⟨source, List.mem_append_right _ hsource, hrest⟩
          | some condition =>
              simp only [selectionDeclaredLookupReady] at hhead
              simp only [fieldSelectionsWithResponseNameInScope] at hfield
              simp only [FieldMerge.collectFields]
              split at hfield
              · rename_i hoverlap
                rcases List.mem_append.mp hfield with hfield | hfield
                · rcases runtimeFields_declaredSource schema runtimeType hobject condition
                    selectedChildren responseName fieldName arguments directives children
                    (typeIncludesObjectBool_of_object_typesOverlapBool schema hobject hoverlap)
                    hhead hfield with ⟨source, hsource, hrest⟩
                  exact ⟨source, List.mem_append_left _ hsource, hrest⟩
                · rcases hrestSource hfield with ⟨source, hsource, hrest⟩
                  exact ⟨source, List.mem_append_right _ hsource, hrest⟩
              · rcases hrestSource hfield with ⟨source, hsource, hrest⟩
                exact ⟨source, List.mem_append_right _ hsource, hrest⟩

end GraphQL.NormalForm
