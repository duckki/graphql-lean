import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedSelectedPathAbstractSeparation

/-!
Object-output response paths and response-name absence separation.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem
    pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_objectChild_of_observableResponsePath
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection} {fieldDefinition : FieldDefinition}
    {childPath : List Name}
    : NormalSelectionSetObservableResponsePath schema
        fieldDefinition.outputType.namedType childSelectionSet childPath
      -> Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType childSelectionSet
      -> selectionSetNormal schema fieldDefinition.outputType.namedType childSelectionSet
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> ∃ childRuntimeType childSpine,
          schema.typeIncludesObjectBool
              fieldDefinition.outputType.namedType childRuntimeType
            = true
          ∧ ∀ currentSelectionSet,
              PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
                parentType parentType currentSelectionSet selectionSet
                ({
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    childRuntime := some childRuntimeType
                  }
                  :: childSpine) := by
  intro hchildPath hchildValid hchildNormal hobject hmem hlookup hcomposite
  rcases
      pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_observableResponsePath_valid_normal
        hchildPath hchildValid hchildNormal with
    ⟨childRuntimeType, childSpine, hchildInclude, hchildObservable⟩
  exact ⟨
    childRuntimeType,
    childSpine,
    hchildInclude,
    fun currentSelectionSet =>
      PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime.objectChild
        hobject hmem hlookup hcomposite
        (hchildObservable
          (fieldPairPathLocalNextSelectionSet schema parentType
            childRuntimeType fieldName arguments currentSelectionSet))
  ⟩

theorem
    pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_objectChild_of_valid_normal_observableResponsePath
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection} {fieldDefinition : FieldDefinition}
    {childPath : List Name}
    : NormalSelectionSetObservableResponsePath schema
        fieldDefinition.outputType.namedType childSelectionSet childPath
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> ∃ childRuntimeType childSpine,
          schema.typeIncludesObjectBool
              fieldDefinition.outputType.namedType childRuntimeType
            = true
          ∧ ∀ currentSelectionSet,
              PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
                parentType parentType currentSelectionSet selectionSet
                ({
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    childRuntime := some childRuntimeType
                  }
                  :: childSpine) := by
  intro hchildPath hvalid hnormal hobject hmem hlookup hcomposite
  rcases selectionSetValid_field_lookup_leaf_or_composite_child hvalid
      hmem with
    ⟨candidateDefinition, hcandidateLookup, hkind⟩
  have hcandidateEq : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidateDefinition
  rcases hkind with hleaf | hcompositeKind
  · rw [hcomposite] at hleaf
    simp at hleaf
  · have hchildNormal :
        selectionSetNormal schema fieldDefinition.outputType.namedType
          childSelectionSet :=
      selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
    exact
      pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_objectChild_of_observableResponsePath
        hchildPath hcompositeKind.2.2 hchildNormal hobject hmem
        hlookup hcomposite

theorem field_mem_of_object_normalSelectionSetObservableResponsePath_cons
    {schema : Schema} {parentType responseName : Name}
    {selectionSet : List Selection}
    {pathTail : List Name}
    : objectTypeNameBool schema parentType = true
      -> NormalSelectionSetObservableResponsePath schema parentType selectionSet
          (responseName :: pathTail)
      -> ∃ fieldName arguments directives childSelectionSet fieldDefinition,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ selectionSet
          ∧ schema.lookupField parentType fieldName = some fieldDefinition := by
  intro hobject hpath
  cases hpath with
  | objectLeaf hobjectPath hmem hlookup _hleaf =>
      exact ⟨_, _, _, _, _, hmem, hlookup⟩
  | objectChild hobjectPath hmem hlookup _hcomposite _hchild =>
      exact ⟨_, _, _, _, _, hmem, hlookup⟩
  | abstractInlineFragment hnonObject _hmem _hchild =>
      rw [hobject] at hnonObject
      simp at hnonObject

theorem field_components_eq_of_object_observablePath_responseName_mem
    {schema : Schema} {parentType responseName : Name}
    {selectionSet : List Selection}
    {pathTail : List Name}
    {fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> NormalSelectionSetObservableResponsePath schema parentType selectionSet
          (responseName :: pathTail)
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> ∃ pathFieldName pathArguments pathDirectives pathChildSelectionSet
            pathFieldDefinition,
          Selection.field responseName pathFieldName pathArguments
              pathDirectives pathChildSelectionSet
            ∈ selectionSet
          ∧ schema.lookupField parentType pathFieldName = some pathFieldDefinition
          ∧ pathFieldName = fieldName
          ∧ pathArguments = arguments
          ∧ pathDirectives = directives
          ∧ pathChildSelectionSet = childSelectionSet := by
  intro hnormal hobject hpath hmem
  rcases field_mem_of_object_normalSelectionSetObservableResponsePath_cons
      hobject hpath with
    ⟨pathFieldName, pathArguments, pathDirectives,
      pathChildSelectionSet, pathFieldDefinition, hpathMem,
      hpathLookup⟩
  rcases
      field_components_eq_of_selectionSetNormal_responseName_mem
        hnormal hpathMem hmem with
    ⟨hfieldName, harguments, hdirectives, hchild⟩
  exact ⟨
    pathFieldName,
    pathArguments,
    pathDirectives,
    pathChildSelectionSet,
    pathFieldDefinition,
    hpathMem,
    hpathLookup,
    hfieldName,
    harguments,
    hdirectives,
    hchild
  ⟩

theorem field_path_cases_of_object_observablePath_responseName_mem
    {schema : Schema} {parentType responseName : Name}
    {selectionSet : List Selection}
    {pathTail : List Name}
    {fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> NormalSelectionSetObservableResponsePath schema parentType selectionSet
          (responseName :: pathTail)
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> (pathTail = []
            ∧ ∃ fieldDefinition,
                schema.lookupField parentType fieldName = some fieldDefinition
                ∧ (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                    schema
                  = false)
          ∨ ∃ fieldDefinition,
              schema.lookupField parentType fieldName = some fieldDefinition
              ∧ (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
              ∧ NormalSelectionSetObservableResponsePath schema
                  fieldDefinition.outputType.namedType childSelectionSet
                  pathTail := by
  intro hnormal hobject hpath hmem
  cases hpath with
  | objectLeaf hpathObject hpathMem hlookup hleaf =>
      rcases
          field_components_eq_of_selectionSetNormal_responseName_mem
            hnormal hpathMem hmem with
        ⟨hfieldName, harguments, hdirectives, hchild⟩
      subst fieldName
      subst arguments
      subst directives
      subst childSelectionSet
      exact Or.inl ⟨rfl, ⟨_, hlookup, hleaf⟩⟩
  | objectChild hpathObject hpathMem hlookup hcomposite hchildPath =>
      rcases
          field_components_eq_of_selectionSetNormal_responseName_mem
            hnormal hpathMem hmem with
        ⟨hfieldName, harguments, hdirectives, hchild⟩
      subst fieldName
      subst arguments
      subst directives
      subst childSelectionSet
      exact Or.inr ⟨_, hlookup, hcomposite, hchildPath⟩
  | abstractInlineFragment hnonObject _hmem _hchildPath =>
      rw [hobject] at hnonObject
      simp at hnonObject

theorem normalSelectionSetObservableResponsePath_of_valid_normal_object_field_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> ∃ pathTail,
          NormalSelectionSetObservableResponsePath schema parentType
            selectionSet (responseName :: pathTail) := by
  intro hvalid hnormal hobject hmem hlookup
  by_cases hleaf :
      (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
        schema = false
  · exact ⟨
      [],
      NormalSelectionSetObservableResponsePath.objectLeaf hobject hmem hlookup hleaf
    ⟩
  · have hcomposite :
        (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
          schema = true := by
      cases h :
          (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
            schema <;>
        simp [h] at hleaf ⊢
    rcases
        normalSelectionSetObservableResponsePath_of_valid_normal_composite_field_mem
          hvalid hnormal hmem hlookup hcomposite with
      ⟨childPath, hchildPath⟩
    exact ⟨
      childPath,
      NormalSelectionSetObservableResponsePath.objectChild hobject hmem
        hlookup hcomposite hchildPath
    ⟩

theorem normalSelectionSetObservableResponsePath_exists_of_valid_normal_object_nonempty
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> selectionSet ≠ []
      -> ∃ responsePath,
          NormalSelectionSetObservableResponsePath schema parentType
            selectionSet responsePath := by
  intro hvalid hnormal hobject hnonempty
  rcases
      selectionSetNormal_field_mem_of_object_nonempty hnormal hobject
        hnonempty with
    ⟨responseName, fieldName, arguments, directives, childSelectionSet,
      hmem⟩
  rcases selectionSetValid_field_lookup_of_mem hvalid hmem with
    ⟨fieldDefinition, hlookup, _harguments, _hfieldValid⟩
  rcases
      normalSelectionSetObservableResponsePath_of_valid_normal_object_field_mem
        hvalid hnormal hobject hmem hlookup with
    ⟨pathTail, hpath⟩
  exact ⟨responseName :: pathTail, hpath⟩

theorem normalSelectionSetObservableResponsePath_ne_nil
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetObservableResponsePath schema parentType selectionSet responsePath
      -> responsePath ≠ [] := by
  intro hpath
  induction hpath with
  | objectLeaf =>
      simp
  | objectChild =>
      simp
  | abstractInlineFragment _ _ _ ih =>
      exact ih

inductive NormalSelectionSetObjectOutputObservableResponsePath (schema : Schema)
    : Name -> List Selection -> List Name -> Prop where
  | objectLeaf
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> NormalSelectionSetObjectOutputObservableResponsePath schema parentType
          selectionSet [responseName]
  | objectChild
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> NormalSelectionSetObjectOutputObservableResponsePath schema
          fieldDefinition.outputType.namedType childSelectionSet childPath
      -> NormalSelectionSetObjectOutputObservableResponsePath schema parentType
          selectionSet (responseName :: childPath)

inductive SelectionSetCompositeFieldsObjectOutputClosed (schema : Schema)
    : Name -> List Selection -> Prop where
  | mk {parentType : Name} {selectionSet : List Selection}
    : (∀ {responseName fieldName : Name}
          {arguments : List Argument}
          {directives : List DirectiveApplication}
          {childSelectionSet : List Selection}
          {fieldDefinition : FieldDefinition},
        Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
        -> schema.lookupField parentType fieldName = some fieldDefinition
        -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
            = true
        -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true)
      -> (∀ {responseName fieldName : Name}
            {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection}
            {fieldDefinition : FieldDefinition},
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> schema.lookupField parentType fieldName = some fieldDefinition
            -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
            -> SelectionSetCompositeFieldsObjectOutputClosed schema
                fieldDefinition.outputType.namedType childSelectionSet)
      -> SelectionSetCompositeFieldsObjectOutputClosed schema parentType selectionSet

theorem SelectionSetCompositeFieldsObjectOutputClosed.object_output
    {schema : Schema} {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : SelectionSetCompositeFieldsObjectOutputClosed schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true := by
  intro hclosed hmem hlookup hcomposite
  cases hclosed with
  | mk hobject _hchild =>
      exact hobject hmem hlookup hcomposite

theorem SelectionSetCompositeFieldsObjectOutputClosed.child
    {schema : Schema} {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : SelectionSetCompositeFieldsObjectOutputClosed schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> SelectionSetCompositeFieldsObjectOutputClosed schema
          fieldDefinition.outputType.namedType childSelectionSet := by
  intro hclosed hmem hlookup hcomposite
  cases hclosed with
  | mk _hobject hchild =>
      exact hchild hmem hlookup hcomposite

theorem NormalSelectionSetObjectOutputObservableResponsePath.to_observable
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetObjectOutputObservableResponsePath schema parentType
        selectionSet responsePath
      -> NormalSelectionSetObservableResponsePath schema parentType selectionSet
          responsePath := by
  intro hpath
  induction hpath with
  | objectLeaf hobject hmem hlookup hleaf =>
      exact
        NormalSelectionSetObservableResponsePath.objectLeaf hobject hmem
          hlookup hleaf
  | objectChild hobject hmem hlookup hcomposite _hobjectOutput
      _hchild ih =>
      exact
        NormalSelectionSetObservableResponsePath.objectChild hobject hmem
          hlookup hcomposite ih

theorem normalSelectionSetObjectOutputObservableResponsePath_ne_nil
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetObjectOutputObservableResponsePath schema parentType
        selectionSet responsePath
      -> responsePath ≠ [] := by
  intro hpath
  exact normalSelectionSetObservableResponsePath_ne_nil hpath.to_observable

inductive NormalSelectionSetObjectOutputSameFieldResponsePath (schema : Schema)
    : Name -> List Selection -> List Selection -> List Name -> Prop where
  | leaf
    {parentType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> NormalSelectionSetObjectOutputSameFieldResponsePath schema
          parentType left right [responseName]
  | child
    {parentType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {fieldDefinition : FieldDefinition}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> NormalSelectionSetObjectOutputSameFieldResponsePath schema
          fieldDefinition.outputType.namedType leftChildSelectionSet
          rightChildSelectionSet childPath
      -> NormalSelectionSetObjectOutputSameFieldResponsePath schema
          parentType left right (responseName :: childPath)

inductive NormalSelectionSetObjectOutputSameFieldSpinePath (schema : Schema)
    : Name -> List Selection -> List Selection -> List Name
      -> List NormalSelectionSetObservableFieldStep
      -> List NormalSelectionSetObservableFieldStep -> Prop where
  | leaf
    {parentType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> NormalSelectionSetObjectOutputSameFieldSpinePath schema
          parentType left right [responseName]
          [{
            responseName := responseName,
            fieldName := fieldName,
            arguments := leftArguments,
            childRuntime := none
          }]
          [{
            responseName := responseName,
            fieldName := fieldName,
            arguments := rightArguments,
            childRuntime := none
          }]
  | child
    {parentType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {fieldDefinition : FieldDefinition}
    {childPath : List Name}
    {leftChildSpine rightChildSpine : List NormalSelectionSetObservableFieldStep}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> NormalSelectionSetObjectOutputSameFieldSpinePath schema
          fieldDefinition.outputType.namedType leftChildSelectionSet
          rightChildSelectionSet childPath leftChildSpine rightChildSpine
      -> NormalSelectionSetObjectOutputSameFieldSpinePath schema
          parentType left right (responseName :: childPath)
          ({
              responseName := responseName,
              fieldName := fieldName,
              arguments := leftArguments,
              childRuntime := some fieldDefinition.outputType.namedType
            }
            :: leftChildSpine)
          ({
              responseName := responseName,
              fieldName := fieldName,
              arguments := rightArguments,
              childRuntime := some fieldDefinition.outputType.namedType
            }
            :: rightChildSpine)

theorem normalSelectionSetObjectOutputSameFieldSpinePath_exists_of_responsePath
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetObjectOutputSameFieldResponsePath schema parentType
        left right responsePath
      -> ∃ leftSpine rightSpine,
          NormalSelectionSetObjectOutputSameFieldSpinePath schema parentType
            left right responsePath leftSpine rightSpine := by
  intro hpath
  induction hpath with
  | leaf hobject hleftMem hrightMem hlookup hleaf =>
      exact ⟨
        _,
        _,
        NormalSelectionSetObjectOutputSameFieldSpinePath.leaf hobject
          hleftMem hrightMem hlookup hleaf
      ⟩
  | child hobject hleftMem hrightMem hlookup hcomposite hobjectOutput
      _hchild ih =>
      rcases ih with ⟨leftChildSpine, rightChildSpine, hchildSpine⟩
      exact ⟨
        _,
        _,
        NormalSelectionSetObjectOutputSameFieldSpinePath.child hobject
          hleftMem hrightMem hlookup hcomposite hobjectOutput
          hchildSpine
      ⟩

theorem field_mem_of_object_normalSelectionSetObjectOutputObservableResponsePath_cons
    {schema : Schema} {parentType responseName : Name}
    {selectionSet : List Selection}
    {pathTail : List Name}
    : objectTypeNameBool schema parentType = true
      -> NormalSelectionSetObjectOutputObservableResponsePath schema parentType
          selectionSet (responseName :: pathTail)
      -> ∃ fieldName arguments directives childSelectionSet fieldDefinition,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ selectionSet
          ∧ schema.lookupField parentType fieldName = some fieldDefinition := by
  intro hobject hpath
  cases hpath with
  | objectLeaf hobjectPath hmem hlookup _hleaf =>
      exact ⟨_, _, _, _, _, hmem, hlookup⟩
  | objectChild hobjectPath hmem hlookup _hcomposite _hobjectOutput
      _hchild =>
      exact ⟨_, _, _, _, _, hmem, hlookup⟩

theorem field_path_cases_of_object_objectOutputObservablePath_responseName_mem
    {schema : Schema} {parentType responseName : Name}
    {selectionSet : List Selection}
    {pathTail : List Name}
    {fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> NormalSelectionSetObjectOutputObservableResponsePath schema parentType
          selectionSet (responseName :: pathTail)
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> (pathTail = []
            ∧ ∃ fieldDefinition,
                schema.lookupField parentType fieldName = some fieldDefinition
                ∧ (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                    schema
                  = false)
          ∨ ∃ fieldDefinition,
              schema.lookupField parentType fieldName = some fieldDefinition
              ∧ (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = true
              ∧ NormalSelectionSetObjectOutputObservableResponsePath schema
                  fieldDefinition.outputType.namedType childSelectionSet
                  pathTail := by
  intro hnormal hobject hpath hmem
  cases hpath with
  | objectLeaf hpathObject hpathMem hlookup hleaf =>
      rcases
          field_components_eq_of_selectionSetNormal_responseName_mem
            hnormal hpathMem hmem with
        ⟨hfieldName, harguments, hdirectives, hchild⟩
      subst fieldName
      subst arguments
      subst directives
      subst childSelectionSet
      exact Or.inl ⟨rfl, ⟨_, hlookup, hleaf⟩⟩
  | objectChild hpathObject hpathMem hlookup hcomposite hobjectOutput
      hchildPath =>
      rcases
          field_components_eq_of_selectionSetNormal_responseName_mem
            hnormal hpathMem hmem with
        ⟨hfieldName, harguments, hdirectives, hchild⟩
      subst fieldName
      subst arguments
      subst directives
      subst childSelectionSet
      exact
        Or.inr
          ⟨_, hlookup, hcomposite, hobjectOutput, hchildPath⟩

theorem
    pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_objectOutputObservableResponsePath_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition} {parentType : Name}
    {selectionSet : List Selection} {responsePath : List Name}
    : NormalSelectionSetObjectOutputObservableResponsePath schema parentType
        selectionSet responsePath
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> ∃ fieldSpine,
          ∀ currentSelectionSet,
            PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
              parentType parentType currentSelectionSet selectionSet
              fieldSpine := by
  intro hpath
  induction hpath with
  | objectLeaf hobject hmem hlookup hleaf =>
      rename_i pathParentType responseName fieldName arguments directives
        childSelectionSet pathSelectionSet fieldDefinition
      intro _hvalid _hnormal
      exact ⟨
        [{
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          childRuntime := none
        }],
        fun currentSelectionSet =>
          PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime.objectLeaf
            hobject hmem hlookup hleaf
      ⟩
  | objectChild hobject hmem hlookup hcomposite hobjectOutput
      _hchild ih =>
      rename_i pathParentType responseName fieldName arguments directives
        childSelectionSet pathSelectionSet fieldDefinition childPath
      intro hvalid hnormal
      have hchildValid :
          Validation.selectionSetValid schema variableDefinitions
            fieldDefinition.outputType.namedType childSelectionSet :=
        selectionSetValid_object_field_child_of_mem_lookup hvalid hmem
          hlookup hobjectOutput
      have hchildNormal :
          selectionSetNormal schema fieldDefinition.outputType.namedType
            childSelectionSet :=
        selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
      rcases ih hchildValid hchildNormal with
        ⟨childSpine, hchildSpine⟩
      exact ⟨
        ({
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            childRuntime := some fieldDefinition.outputType.namedType
          }
          :: childSpine),
        fun currentSelectionSet =>
          PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime.objectChild
            hobject hmem hlookup hcomposite
            (hchildSpine
              (fieldPairPathLocalNextSelectionSet schema pathParentType
                fieldDefinition.outputType.namedType fieldName arguments
                currentSelectionSet))
      ⟩

theorem
    pathLocalSelectionSetObservableLeafAtRuntime_of_objectOutputObservableResponsePath_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition} {parentType : Name}
    {selectionSet currentSelectionSet : List Selection} {responsePath : List Name}
    : NormalSelectionSetObjectOutputObservableResponsePath schema parentType
        selectionSet responsePath
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> PathLocalSupportValidNormal schema parentType currentSelectionSet
      -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
      -> PathLocalSelectionSetObservableLeafAtRuntime schema parentType
          parentType currentSelectionSet selectionSet := by
  intro hpath
  induction hpath generalizing variableDefinitions currentSelectionSet with
  | objectLeaf hobject hmem hlookup hleaf =>
      intro _hvalid _hnormal _hsupport _hcontext
      exact
        PathLocalSelectionSetObservableLeafAtRuntime.objectLeaf hobject
          hmem hlookup hleaf
  | objectChild hobject hmem hlookup hcomposite hobjectOutput
      _hchild ih =>
      rename_i pathParentType responseName fieldName arguments directives
        childSelectionSet pathSelectionSet fieldDefinition childPath
      intro hvalid hnormal hsupport hcontext
      have hchildValid :
          Validation.selectionSetValid schema variableDefinitions
            fieldDefinition.outputType.namedType childSelectionSet :=
        selectionSetValid_object_field_child_of_mem_lookup hvalid hmem
          hlookup hobjectOutput
      have hchildNormal :
          selectionSetNormal schema fieldDefinition.outputType.namedType
            childSelectionSet :=
        selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
      have hchildSupport :
          PathLocalSupportValidNormal schema
            fieldDefinition.outputType.namedType
            (fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName arguments
              currentSelectionSet) :=
        hsupport.fieldPairPathLocalNextSelectionSet_of_object_output
          hobject hobjectOutput hlookup rfl
      have hallFields : selectionsAllFields childSelectionSet :=
        selectionSetNormal_allFields_of_object hchildNormal hobjectOutput
      have hpruned :
          runtimePrunedSelectionSet schema
              fieldDefinition.outputType.namedType childSelectionSet =
            childSelectionSet :=
        runtimePrunedSelectionSet_eq_self_of_allFields schema
          fieldDefinition.outputType.namedType hallFields
      have hchildContext :
          PathLocalSelectionSetCurrentContext childSelectionSet
            (fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName arguments
              currentSelectionSet) :=
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
          (schema := schema) (currentRuntimeType := pathParentType)
          (childRuntimeType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := arguments) (arguments := arguments)
          (directives := directives) (selectionSet := pathSelectionSet)
          (childSelectionSet := childSelectionSet)
          (currentSelectionSet := currentSelectionSet) hcontext hmem
          hpruned
      have hchildObservable :
          PathLocalSelectionSetObservableLeafAtRuntime schema
            fieldDefinition.outputType.namedType
            fieldDefinition.outputType.namedType
            (fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName arguments
              currentSelectionSet)
            childSelectionSet :=
        ih hchildValid hchildNormal hchildSupport hchildContext
      exact
        PathLocalSelectionSetObservableLeafAtRuntime.objectChild hobject
          hmem hlookup
          (by
            unfold Schema.isCompositeType
            unfold TypeRef.isCompositeBool TypeRef.namedType at hcomposite
            cases hlookupType :
                schema.lookupType fieldDefinition.outputType.namedType with
            | none =>
                simp [hlookupType] at hcomposite
            | some typeDefinition =>
                have htypeComposite :
                    TypeDefinition.isCompositeType typeDefinition := by
                  cases typeDefinition <;>
                    simp [hlookupType, TypeDefinition.isCompositeType] at hcomposite ⊢
                exact ⟨typeDefinition, rfl, htypeComposite⟩)
          (Or.inl ⟨hobjectOutput, rfl⟩) hchildObservable

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_objectOutputObservableResponsePath_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType currentSelectionSet (selectionSet : List Selection)
            {responsePath : List Name},
          NormalSelectionSetObjectOutputObservableResponsePath schema parentType
            selectionSet responsePath
          -> ∀ variableDefinitions fuel targetParent leftField rightField
                (leftArguments rightArguments : List Argument)
                (leftRuntime rightRuntime : Name),
              Validation.selectionSetValid schema variableDefinitions parentType
                selectionSet
              -> selectionSetDirectiveFree selectionSet
              -> selectionSetNormal schema parentType selectionSet
              -> objectTypeNameBool schema parentType = true
              -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
              -> PathLocalSupportValidNormal schema parentType currentSelectionSet
              -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
              -> ¬ Execution.ResponseValue.semanticEquivalent
                    (Execution.executeSelectionSetAsResponse schema
                      (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                        (fieldPairPathLocalProbeResolvers schema
                          leftInitialSelectionSet rightInitialSelectionSet
                          targetParent leftField rightField leftArguments
                          rightArguments leftRuntime rightRuntime)
                        targetParent leftField rightField leftArguments
                        rightArguments)
                      variableValues (fuel + 1) parentType
                      (projectionTargetResolverValue
                        (.object parentType
                          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                            currentSelectionSet)))
                      selectionSet).data
                    (Execution.executeSelectionSetAsResponse schema
                      (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                        (fieldPairPathLocalProbeResolvers schema
                          leftInitialSelectionSet rightInitialSelectionSet
                          targetParent leftField rightField leftArguments
                          rightArguments leftRuntime rightRuntime)
                        targetParent leftField rightField leftArguments
                        rightArguments)
                      variableValues (fuel + 1) parentType
                      (projectionTargetResolverValue
                        (.object parentType
                          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                            currentSelectionSet)))
                      selectionSet).data := by
  intro hschema parentType currentSelectionSet selectionSet responsePath
    hpath variableDefinitions fuel targetParent leftField rightField
    leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
    hnormal hobject hfuel hsupport hcontext
  have hobservable :
      PathLocalSelectionSetObservableLeafAtRuntime schema parentType
        parentType currentSelectionSet selectionSet :=
    pathLocalSelectionSetObservableLeafAtRuntime_of_objectOutputObservableResponsePath_valid_normal
      hpath hvalid hnormal hsupport hcontext
  exact
    responseData_not_semanticEquivalent_of_pathLocalProbe_observableLeafAtRuntime_valid_normal_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues hschema parentType parentType
      currentSelectionSet selectionSet hobservable variableDefinitions fuel
      targetParent leftField rightField leftArguments rightArguments
      leftRuntime rightRuntime hvalid hfree hnormal
      (typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject)
      hfuel hsupport (fun _hobject => hcontext)
      (fun hnonObject => by
        rw [hobject] at hnonObject
        simp at hnonObject)

theorem
    selectedFieldSpineRuntimeValid_exists_of_objectOutputObservableResponsePath_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition} {parentType : Name}
    {selectionSet : List Selection} {responsePath : List Name}
    : NormalSelectionSetObjectOutputObservableResponsePath schema parentType
        selectionSet responsePath
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> ∃ fieldSpine,
          SelectedFieldSpineRuntimeValid schema parentType parentType fieldSpine
          ∧ ∀ currentSelectionSet,
              PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
                parentType parentType currentSelectionSet selectionSet
                fieldSpine := by
  intro hpath hvalid hnormal
  rcases
      pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_objectOutputObservableResponsePath_valid_normal
        hpath hvalid hnormal with
    ⟨fieldSpine, hspine⟩
  exact ⟨
    fieldSpine,
    selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
      (hspine selectionSet),
    hspine
  ⟩

theorem field_leaf_of_object_normalSelectionSetObservableResponsePath_single
    {schema : Schema} {parentType responseName : Name}
    {selectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> NormalSelectionSetObservableResponsePath schema parentType selectionSet
          [responseName]
      -> ∃ fieldName arguments directives childSelectionSet fieldDefinition,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ selectionSet
          ∧ schema.lookupField parentType fieldName = some fieldDefinition
          ∧ (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
            = false := by
  intro hobject hpath
  cases hpath with
  | objectLeaf hobjectPath hmem hlookup hleaf =>
      exact ⟨_, _, _, _, _, hmem, hlookup, hleaf⟩
  | objectChild hobjectPath hmem hlookup hcomposite hchild =>
      have hchildNonempty :=
        normalSelectionSetObservableResponsePath_ne_nil hchild
      simp at hchildNonempty
  | abstractInlineFragment hnonObject _hmem _hchild =>
      rw [hobject] at hnonObject
      simp at hnonObject

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_responseName_absent
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField leftParentType
      rightParentType leftSourceRuntimeType rightSourceRuntimeType
      : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right : List Selection} {responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType
          leftSourceRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType
          rightSourceRuntimeType rightSpine
      -> PathLocalSupportValidNormal schema leftSourceRuntimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightSourceRuntimeType
          rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftMem hrightNoResponseName
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet leftSpine))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet rightSpine))
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1) leftSource responseName
              [{
                parentType := leftParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, leftSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
        (schema := schema)
        (variableDefinitions := leftVariableDefinitions)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := leftCurrentSelectionSet)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := leftSpine)
        (variableValues := variableValues) (fuel := fuel)
        (targetParent := targetParent) (leftField := leftField)
        (rightField := rightField) (parentType := leftParentType)
        (sourceRuntimeType := leftSourceRuntimeType)
        (leftArguments := leftArguments)
        (rightArguments := rightArguments) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (tag := FieldPairProbeTag.left)
        (selectionSet := left)
        hschema hleftValid hleftFree hleftNormal hleftObject hleftFuel
        hleftSpineValid hleftSupport hleftContext
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1) rightSource responseName
              [{
                parentType := rightParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, rightSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
        (schema := schema)
        (variableDefinitions := rightVariableDefinitions)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := rightCurrentSelectionSet)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := rightSpine)
        (variableValues := variableValues) (fuel := fuel)
        (targetParent := targetParent) (leftField := leftField)
        (rightField := rightField) (parentType := rightParentType)
        (sourceRuntimeType := rightSourceRuntimeType)
        (leftArguments := leftArguments)
        (rightArguments := rightArguments) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (tag := FieldPairProbeTag.right)
        (selectionSet := right)
        hschema hrightValid hrightFree hrightNormal hrightObject hrightFuel
        hrightSpineValid hrightSupport hrightContext
  simpa [resolvers, leftSource, rightSource] using
    SemanticSeparation.responseData_not_semanticEquivalent_of_left_responseName_diff_of_field_ok_sources_pair
      (schema := schema) (leftParentType := leftParentType)
      (rightParentType := rightParentType) (left := left) (right := right)
      (responseName := responseName) (fieldName := fieldName)
      (arguments := arguments) (directives := directives)
      (childSelectionSet := childSelectionSet)
      resolvers resolvers variableValues (fuel + 1) leftSource
      rightSource hleftObject hrightObject hleftNormal hrightNormal
      hleftFree hrightFree hleftMem hrightNoResponseName hleftFieldOk
      hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_responseName_absent_fuels
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftField rightField
      leftParentType rightParentType leftSourceRuntimeType
      rightSourceRuntimeType
      : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right : List Selection} {responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType
          leftSourceRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType
          rightSourceRuntimeType rightSpine
      -> PathLocalSupportValidNormal schema leftSourceRuntimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightSourceRuntimeType
          rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (leftFuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (rightFuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftMem hrightNoResponseName
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet leftSpine))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet rightSpine))
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (leftFuel + 1) leftSource responseName
              [{
                parentType := leftParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, leftSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
        (schema := schema)
        (variableDefinitions := leftVariableDefinitions)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := leftCurrentSelectionSet)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := leftSpine)
        (variableValues := variableValues) (fuel := leftFuel)
        (targetParent := targetParent) (leftField := leftField)
        (rightField := rightField) (parentType := leftParentType)
        (sourceRuntimeType := leftSourceRuntimeType)
        (leftArguments := leftArguments)
        (rightArguments := rightArguments) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (tag := FieldPairProbeTag.left)
        (selectionSet := left)
        hschema hleftValid hleftFree hleftNormal hleftObject hleftFuel
        hleftSpineValid hleftSupport hleftContext
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (rightFuel + 1) rightSource responseName
              [{
                parentType := rightParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, rightSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
        (schema := schema)
        (variableDefinitions := rightVariableDefinitions)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := rightCurrentSelectionSet)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := rightSpine)
        (variableValues := variableValues) (fuel := rightFuel)
        (targetParent := targetParent) (leftField := leftField)
        (rightField := rightField) (parentType := rightParentType)
        (sourceRuntimeType := rightSourceRuntimeType)
        (leftArguments := leftArguments)
        (rightArguments := rightArguments) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (tag := FieldPairProbeTag.right)
        (selectionSet := right)
        hschema hrightValid hrightFree hrightNormal hrightObject hrightFuel
        hrightSpineValid hrightSupport hrightContext
  simpa [resolvers, leftSource, rightSource] using
    SemanticSeparation.responseData_not_semanticEquivalent_of_left_responseName_diff_of_field_ok_sources_pair_fuels
      (schema := schema) (leftParentType := leftParentType)
      (rightParentType := rightParentType) (left := left) (right := right)
      (responseName := responseName) (fieldName := fieldName)
      (arguments := arguments) (directives := directives)
      (childSelectionSet := childSelectionSet)
      resolvers resolvers variableValues (leftFuel + 1)
      (rightFuel + 1) leftSource rightSource hleftObject hrightObject
      hleftNormal hrightNormal hleftFree hrightFree hleftMem
      hrightNoResponseName hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_responseName_absent
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField leftParentType
      rightParentType leftSourceRuntimeType rightSourceRuntimeType
      : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right : List Selection} {responseName : Name} {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType
          leftSourceRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType
          rightSourceRuntimeType rightSpine
      -> PathLocalSupportValidNormal schema leftSourceRuntimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightSourceRuntimeType
          rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema leftParentType left
          (responseName :: pathTail)
      -> responseName ∉ right.filterMap Selection.responseName?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hobservable hrightNoResponseName
  rcases
      field_mem_of_object_normalSelectionSetObservableResponsePath_cons
        hleftObject hobservable with
    ⟨fieldName, arguments, directives, childSelectionSet,
      _fieldDefinition, hleftMem, _hlookup⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_responseName_absent
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftField rightField leftParentType rightParentType
      leftSourceRuntimeType rightSourceRuntimeType leftArguments
      rightArguments leftRuntime rightRuntime hschema hleftValid hrightValid
      hleftFree hrightFree hleftNormal hrightNormal hleftObject
      hrightObject hleftFuel hrightFuel hleftSpineValid hrightSpineValid
      hleftSupport hrightSupport hleftContext hrightContext hleftMem
      hrightNoResponseName

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_responseName_absent_fuels
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftField rightField
      leftParentType rightParentType leftSourceRuntimeType
      rightSourceRuntimeType
      : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right : List Selection} {responseName : Name} {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType
          leftSourceRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType
          rightSourceRuntimeType rightSpine
      -> PathLocalSupportValidNormal schema leftSourceRuntimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightSourceRuntimeType
          rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema leftParentType left
          (responseName :: pathTail)
      -> responseName ∉ right.filterMap Selection.responseName?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (leftFuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (rightFuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hobservable hrightNoResponseName
  rcases
      field_mem_of_object_normalSelectionSetObservableResponsePath_cons
        hleftObject hobservable with
    ⟨fieldName, arguments, directives, childSelectionSet,
      _fieldDefinition, hleftMem, _hlookup⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_responseName_absent_fuels
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues leftFuel
      rightFuel targetParent leftField rightField leftParentType
      rightParentType leftSourceRuntimeType rightSourceRuntimeType
      leftArguments rightArguments leftRuntime rightRuntime hschema
      hleftValid hrightValid hleftFree hrightFree hleftNormal
      hrightNormal hleftObject hrightObject hleftFuel hrightFuel
      hleftSpineValid hrightSpineValid hleftSupport hrightSupport
      hleftContext hrightContext hleftMem hrightNoResponseName

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_right_responseName_absent
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField leftParentType
      rightParentType leftSourceRuntimeType rightSourceRuntimeType
      : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right : List Selection} {responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType
          leftSourceRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType
          rightSourceRuntimeType rightSpine
      -> PathLocalSupportValidNormal schema leftSourceRuntimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightSourceRuntimeType
          rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hrightMem hleftNoResponseName
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet leftSpine))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet rightSpine))
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1) leftSource responseName
              [{
                parentType := leftParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, leftSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
        (schema := schema)
        (variableDefinitions := leftVariableDefinitions)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := leftCurrentSelectionSet)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := leftSpine)
        (variableValues := variableValues) (fuel := fuel)
        (targetParent := targetParent) (leftField := leftField)
        (rightField := rightField) (parentType := leftParentType)
        (sourceRuntimeType := leftSourceRuntimeType)
        (leftArguments := leftArguments)
        (rightArguments := rightArguments) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (tag := FieldPairProbeTag.left)
        (selectionSet := left)
        hschema hleftValid hleftFree hleftNormal hleftObject hleftFuel
        hleftSpineValid hleftSupport hleftContext
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1) rightSource responseName
              [{
                parentType := rightParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, rightSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
        (schema := schema)
        (variableDefinitions := rightVariableDefinitions)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := rightCurrentSelectionSet)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := rightSpine)
        (variableValues := variableValues) (fuel := fuel)
        (targetParent := targetParent) (leftField := leftField)
        (rightField := rightField) (parentType := rightParentType)
        (sourceRuntimeType := rightSourceRuntimeType)
        (leftArguments := leftArguments)
        (rightArguments := rightArguments) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (tag := FieldPairProbeTag.right)
        (selectionSet := right)
        hschema hrightValid hrightFree hrightNormal hrightObject hrightFuel
        hrightSpineValid hrightSupport hrightContext
  simpa [resolvers, leftSource, rightSource] using
    SemanticSeparation.responseData_not_semanticEquivalent_of_right_responseName_diff_of_field_ok_sources_pair
      (schema := schema) (leftParentType := leftParentType)
      (rightParentType := rightParentType) (left := left) (right := right)
      (responseName := responseName) (fieldName := fieldName)
      (arguments := arguments) (directives := directives)
      (childSelectionSet := childSelectionSet)
      resolvers resolvers variableValues (fuel + 1) leftSource
      rightSource hleftObject hrightObject hleftNormal hrightNormal
      hleftFree hrightFree hrightMem hleftNoResponseName hleftFieldOk
      hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_right_responseName_absent_fuels
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftField rightField
      leftParentType rightParentType leftSourceRuntimeType
      rightSourceRuntimeType
      : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right : List Selection} {responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType
          leftSourceRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType
          rightSourceRuntimeType rightSpine
      -> PathLocalSupportValidNormal schema leftSourceRuntimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightSourceRuntimeType
          rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (leftFuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (rightFuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hrightMem hleftNoResponseName
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet leftSpine))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet rightSpine))
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (leftFuel + 1) leftSource responseName
              [{
                parentType := leftParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, leftSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
        (schema := schema)
        (variableDefinitions := leftVariableDefinitions)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := leftCurrentSelectionSet)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := leftSpine)
        (variableValues := variableValues) (fuel := leftFuel)
        (targetParent := targetParent) (leftField := leftField)
        (rightField := rightField) (parentType := leftParentType)
        (sourceRuntimeType := leftSourceRuntimeType)
        (leftArguments := leftArguments)
        (rightArguments := rightArguments) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (tag := FieldPairProbeTag.left)
        (selectionSet := left)
        hschema hleftValid hleftFree hleftNormal hleftObject hleftFuel
        hleftSpineValid hleftSupport hleftContext
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (rightFuel + 1) rightSource responseName
              [{
                parentType := rightParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, rightSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
        (schema := schema)
        (variableDefinitions := rightVariableDefinitions)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := rightCurrentSelectionSet)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := rightSpine)
        (variableValues := variableValues) (fuel := rightFuel)
        (targetParent := targetParent) (leftField := leftField)
        (rightField := rightField) (parentType := rightParentType)
        (sourceRuntimeType := rightSourceRuntimeType)
        (leftArguments := leftArguments)
        (rightArguments := rightArguments) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (tag := FieldPairProbeTag.right)
        (selectionSet := right)
        hschema hrightValid hrightFree hrightNormal hrightObject hrightFuel
        hrightSpineValid hrightSupport hrightContext
  simpa [resolvers, leftSource, rightSource] using
    SemanticSeparation.responseData_not_semanticEquivalent_of_right_responseName_diff_of_field_ok_sources_pair_fuels
      (schema := schema) (leftParentType := leftParentType)
      (rightParentType := rightParentType) (left := left) (right := right)
      (responseName := responseName) (fieldName := fieldName)
      (arguments := arguments) (directives := directives)
      (childSelectionSet := childSelectionSet)
      resolvers resolvers variableValues (leftFuel + 1)
      (rightFuel + 1) leftSource rightSource hleftObject hrightObject
      hleftNormal hrightNormal hleftFree hrightFree hrightMem
      hleftNoResponseName hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_right_observable_responseName_absent
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField leftParentType
      rightParentType leftSourceRuntimeType rightSourceRuntimeType
      : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right : List Selection} {responseName : Name} {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType
          leftSourceRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType
          rightSourceRuntimeType rightSpine
      -> PathLocalSupportValidNormal schema leftSourceRuntimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightSourceRuntimeType
          rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema rightParentType right
          (responseName :: pathTail)
      -> responseName ∉ left.filterMap Selection.responseName?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hobservable hleftNoResponseName
  rcases
      field_mem_of_object_normalSelectionSetObservableResponsePath_cons
        hrightObject hobservable with
    ⟨fieldName, arguments, directives, childSelectionSet,
      _fieldDefinition, hrightMem, _hlookup⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_right_responseName_absent
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftField rightField leftParentType rightParentType
      leftSourceRuntimeType rightSourceRuntimeType leftArguments
      rightArguments leftRuntime rightRuntime hschema hleftValid hrightValid
      hleftFree hrightFree hleftNormal hrightNormal hleftObject
      hrightObject hleftFuel hrightFuel hleftSpineValid hrightSpineValid
      hleftSupport hrightSupport hleftContext hrightContext hrightMem
      hleftNoResponseName

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_right_observable_responseName_absent_fuels
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftField rightField
      leftParentType rightParentType leftSourceRuntimeType
      rightSourceRuntimeType
      : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right : List Selection} {responseName : Name} {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType
          leftSourceRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType
          rightSourceRuntimeType rightSpine
      -> PathLocalSupportValidNormal schema leftSourceRuntimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightSourceRuntimeType
          rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema rightParentType right
          (responseName :: pathTail)
      -> responseName ∉ left.filterMap Selection.responseName?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (leftFuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (rightFuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hobservable hleftNoResponseName
  rcases
      field_mem_of_object_normalSelectionSetObservableResponsePath_cons
        hrightObject hobservable with
    ⟨fieldName, arguments, directives, childSelectionSet,
      _fieldDefinition, hrightMem, _hlookup⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_right_responseName_absent_fuels
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues leftFuel
      rightFuel targetParent leftField rightField leftParentType
      rightParentType leftSourceRuntimeType rightSourceRuntimeType
      leftArguments rightArguments leftRuntime rightRuntime hschema
      hleftValid hrightValid hleftFree hrightFree hleftNormal
      hrightNormal hleftObject hrightObject hleftFuel hrightFuel
      hleftSpineValid hrightSpineValid hleftSupport hrightSupport
      hleftContext hrightContext hrightMem hleftNoResponseName

theorem
    responseData_not_semanticEquivalent_existsSpine_of_fieldPairOrDeepSuccess_selectedPathProbe_left_objectOutputObservablePath_right_responseName_absent_valid_normal
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ fuel
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObjectOutputObservableResponsePath schema
          leftParentType left (responseName :: pathTail)
      -> responseName ∉ right.filterMap Selection.responseName?
      -> right ≠ []
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema leftParentType leftParentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema rightParentType
              rightParentType rightSpine
          ∧ ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (fuel + 1) leftParentType
                  (projectionTargetResolverValue
                    (.object leftParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftCurrentSelectionSet
                        leftSpine)))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (fuel + 1) rightParentType
                  (projectionTargetResolverValue
                    (.object rightParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightCurrentSelectionSet
                        rightSpine)))
                  right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSupport hrightSupport hleftContext hrightContext hleftPath
    hrightNoResponseName hrightNonempty
  rcases
      selectedFieldSpineRuntimeValid_exists_of_objectOutputObservableResponsePath_valid_normal
        hleftPath hleftValid hleftNormal with
    ⟨leftSpine, hleftSpineValid, _hleftObservableSpine⟩
  rcases
      selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
        hrightValid hrightNormal hrightObject hrightNonempty with
    ⟨rightSpine, hrightSpineValid, _hrightObservableSpine⟩
  refine ⟨leftSpine, rightSpine, hleftSpineValid, hrightSpineValid, ?_⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_responseName_absent
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hschema hleftValid
      hrightValid hleftFree hrightFree hleftNormal hrightNormal
      hleftObject hrightObject hleftFuel hrightFuel hleftSpineValid
      hrightSpineValid hleftSupport hrightSupport hleftContext
      hrightContext hleftPath.to_observable hrightNoResponseName

theorem
    responseData_not_semanticEquivalent_existsSpine_of_fieldPairOrDeepSuccess_selectedPathProbe_left_responseName_absent_right_objectOutputObservablePath_valid_normal
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ fuel
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> responseName ∉ left.filterMap Selection.responseName?
      -> NormalSelectionSetObjectOutputObservableResponsePath schema
          rightParentType right (responseName :: pathTail)
      -> left ≠ []
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema leftParentType leftParentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema rightParentType
              rightParentType rightSpine
          ∧ ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (fuel + 1) leftParentType
                  (projectionTargetResolverValue
                    (.object leftParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftCurrentSelectionSet
                        leftSpine)))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (fuel + 1) rightParentType
                  (projectionTargetResolverValue
                    (.object rightParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightCurrentSelectionSet
                        rightSpine)))
                  right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSupport hrightSupport hleftContext hrightContext
    hleftNoResponseName hrightPath hleftNonempty
  rcases
      selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
        hleftValid hleftNormal hleftObject hleftNonempty with
    ⟨leftSpine, hleftSpineValid, _hleftObservableSpine⟩
  rcases
      selectedFieldSpineRuntimeValid_exists_of_objectOutputObservableResponsePath_valid_normal
        hrightPath hrightValid hrightNormal with
    ⟨rightSpine, hrightSpineValid, _hrightObservableSpine⟩
  refine ⟨leftSpine, rightSpine, hleftSpineValid, hrightSpineValid, ?_⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_right_observable_responseName_absent
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hschema hleftValid
      hrightValid hleftFree hrightFree hleftNormal hrightNormal
      hleftObject hrightObject hleftFuel hrightFuel hleftSpineValid
      hrightSpineValid hleftSupport hrightSupport hleftContext
      hrightContext hrightPath.to_observable hleftNoResponseName

theorem
    responseData_not_semanticEquivalent_existsSpine_of_fieldPairOrDeepSuccess_selectedPathProbe_left_objectOutputObservablePath_right_responseName_absent_valid_normal_fuels
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObjectOutputObservableResponsePath schema
          leftParentType left (responseName :: pathTail)
      -> responseName ∉ right.filterMap Selection.responseName?
      -> right ≠ []
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema leftParentType leftParentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema rightParentType
              rightParentType rightSpine
          ∧ ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (leftFuel + 1) leftParentType
                  (projectionTargetResolverValue
                    (.object leftParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftCurrentSelectionSet
                        leftSpine)))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (rightFuel + 1) rightParentType
                  (projectionTargetResolverValue
                    (.object rightParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightCurrentSelectionSet
                        rightSpine)))
                  right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSupport hrightSupport hleftContext hrightContext hleftPath
    hrightNoResponseName hrightNonempty
  rcases
      selectedFieldSpineRuntimeValid_exists_of_objectOutputObservableResponsePath_valid_normal
        hleftPath hleftValid hleftNormal with
    ⟨leftSpine, hleftSpineValid, _hleftObservableSpine⟩
  rcases
      selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
        hrightValid hrightNormal hrightObject hrightNonempty with
    ⟨rightSpine, hrightSpineValid, _hrightObservableSpine⟩
  refine ⟨leftSpine, rightSpine, hleftSpineValid, hrightSpineValid, ?_⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_responseName_absent_fuels
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues leftFuel
      rightFuel targetParent leftProbeField rightProbeField
      leftParentType rightParentType leftParentType rightParentType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
      hrightNormal hleftObject hrightObject hleftFuel hrightFuel
      hleftSpineValid hrightSpineValid hleftSupport hrightSupport
      hleftContext hrightContext hleftPath.to_observable
      hrightNoResponseName

theorem
    responseData_not_semanticEquivalent_existsSpine_of_fieldPairOrDeepSuccess_selectedPathProbe_left_responseName_absent_right_objectOutputObservablePath_valid_normal_fuels
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> responseName ∉ left.filterMap Selection.responseName?
      -> NormalSelectionSetObjectOutputObservableResponsePath schema
          rightParentType right (responseName :: pathTail)
      -> left ≠ []
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema leftParentType leftParentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema rightParentType
              rightParentType rightSpine
          ∧ ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (leftFuel + 1) leftParentType
                  (projectionTargetResolverValue
                    (.object leftParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftCurrentSelectionSet
                        leftSpine)))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (rightFuel + 1) rightParentType
                  (projectionTargetResolverValue
                    (.object rightParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightCurrentSelectionSet
                        rightSpine)))
                  right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSupport hrightSupport hleftContext hrightContext
    hleftNoResponseName hrightPath hleftNonempty
  rcases
      selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
        hleftValid hleftNormal hleftObject hleftNonempty with
    ⟨leftSpine, hleftSpineValid, _hleftObservableSpine⟩
  rcases
      selectedFieldSpineRuntimeValid_exists_of_objectOutputObservableResponsePath_valid_normal
        hrightPath hrightValid hrightNormal with
    ⟨rightSpine, hrightSpineValid, _hrightObservableSpine⟩
  refine ⟨leftSpine, rightSpine, hleftSpineValid, hrightSpineValid, ?_⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_right_observable_responseName_absent_fuels
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues leftFuel
      rightFuel targetParent leftProbeField rightProbeField
      leftParentType rightParentType leftParentType rightParentType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
      hrightNormal hleftObject hrightObject hleftFuel hrightFuel
      hleftSpineValid hrightSpineValid hleftSupport hrightSupport
      hleftContext hrightContext hrightPath.to_observable
      hleftNoResponseName

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_observable_responseName_absent_valid_normal_runtimeSpine
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
      -> SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema parentType left
          (responseName :: pathTail)
      -> responseName ∉ right.filterMap Selection.responseName?
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues (fuel + 1)
          parentType parentType targetParent leftProbeField rightProbeField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
          left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSpineValid
    hrightSpineValid hleftSupport hrightSupport hleftContext
    hrightContext hleftObservable hrightNoResponseName
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size left + 1) parentType
        leftVariableDefinitions left fuel parentType targetParent
        leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        leftCurrentSelectionSet leftSpine (by omega) hleftFuel
        hleftValid hleftFree hleftNormal hleftSpineValid hleftSupport
        (fun _hobject => hleftContext)
        (fun hnonObject => by
          rw [hobject] at hnonObject
          simp at hnonObject) with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size right + 1) parentType
        rightVariableDefinitions right fuel parentType targetParent
        leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        rightCurrentSelectionSet rightSpine (by omega) hrightFuel
        hrightValid hrightFree hrightNormal hrightSpineValid hrightSupport
        (fun _hobject => hrightContext)
        (fun hnonObject => by
          rw [hobject] at hnonObject
          simp at hnonObject) with
    ⟨rightFields, rightErrors, hrightResponse⟩
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftProbeField
              rightProbeField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftProbeField rightProbeField targetLeftArguments
            targetRightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftCurrentSelectionSet leftSpine)))
          left).data
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftProbeField
              rightProbeField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftProbeField rightProbeField targetLeftArguments
            targetRightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet rightSpine)))
          right).data :=
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_responseName_absent
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField parentType parentType
      parentType parentType targetLeftArguments targetRightArguments
      leftRuntime rightRuntime hschema hleftValid hrightValid hleftFree
      hrightFree hleftNormal hrightNormal hobject hobject hleftFuel
      hrightFuel hleftSpineValid hrightSpineValid hleftSupport
      hrightSupport hleftContext hrightContext hleftObservable
      hrightNoResponseName
  refine ⟨
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
    leftFields,
    leftErrors,
    rightFields,
    rightErrors,
    hleftResponse,
    hrightResponse,
    ?_
  ⟩
  intro hobjects
  exact hdataNot (by simpa [hleftResponse, hrightResponse] using hobjects)

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_right_observable_responseName_absent_valid_normal_runtimeSpine
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
      -> SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema parentType right
          (responseName :: pathTail)
      -> responseName ∉ left.filterMap Selection.responseName?
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues (fuel + 1)
          parentType parentType targetParent leftProbeField rightProbeField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
          left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSpineValid
    hrightSpineValid hleftSupport hrightSupport hleftContext
    hrightContext hrightObservable hleftNoResponseName
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size left + 1) parentType
        leftVariableDefinitions left fuel parentType targetParent
        leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        leftCurrentSelectionSet leftSpine (by omega) hleftFuel
        hleftValid hleftFree hleftNormal hleftSpineValid hleftSupport
        (fun _hobject => hleftContext)
        (fun hnonObject => by
          rw [hobject] at hnonObject
          simp at hnonObject) with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size right + 1) parentType
        rightVariableDefinitions right fuel parentType targetParent
        leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        rightCurrentSelectionSet rightSpine (by omega) hrightFuel
        hrightValid hrightFree hrightNormal hrightSpineValid hrightSupport
        (fun _hobject => hrightContext)
        (fun hnonObject => by
          rw [hobject] at hnonObject
          simp at hnonObject) with
    ⟨rightFields, rightErrors, hrightResponse⟩
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftProbeField
              rightProbeField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftProbeField rightProbeField targetLeftArguments
            targetRightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftCurrentSelectionSet leftSpine)))
          left).data
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftProbeField
              rightProbeField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftProbeField rightProbeField targetLeftArguments
            targetRightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet rightSpine)))
          right).data :=
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_right_observable_responseName_absent
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField parentType parentType
      parentType parentType targetLeftArguments targetRightArguments
      leftRuntime rightRuntime hschema hleftValid hrightValid hleftFree
      hrightFree hleftNormal hrightNormal hobject hobject hleftFuel
      hrightFuel hleftSpineValid hrightSpineValid hleftSupport
      hrightSupport hleftContext hrightContext hrightObservable
      hleftNoResponseName
  refine ⟨
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
    leftFields,
    leftErrors,
    rightFields,
    rightErrors,
    hleftResponse,
    hrightResponse,
    ?_
  ⟩
  intro hobjects
  exact hdataNot (by simpa [hleftResponse, hrightResponse] using hobjects)

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_object_left_responseName_diff_valid_normal_self
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {childSelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> ∃ leftSpine rightSpine,
          SelectedPathTaggedSelectionSetsResponseDiffWitness schema
            rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
            leftInitialSpine rightInitialSpine variableValues (fuel + 1)
            parentType parentType targetParent leftProbeField rightProbeField
            targetLeftArguments targetRightArguments leftRuntime rightRuntime
            left right leftSpine rightSpine left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftMem
    hrightNoResponseName
  rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
    ⟨fieldDefinition, hlookup, _harguments, _hfieldValid⟩
  rcases
      normalSelectionSetObservableResponsePath_of_valid_normal_object_field_mem
        hleftValid hleftNormal hobject hleftMem hlookup with
    ⟨pathTail, hleftObservablePath⟩
  rcases
      pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_observableResponsePath_valid_normal
        hleftObservablePath hleftValid hleftNormal with
    ⟨runtimeType, spine, hinclude, hobservableSpine⟩
  have hruntimeEq : runtimeType = parentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hobject
      hinclude
  subst runtimeType
  have hspineValid :
      SelectedFieldSpineRuntimeValid schema parentType parentType spine :=
    selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
      (hobservableSpine left)
  refine ⟨spine, spine, ?_⟩
  exact
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_observable_responseName_absent_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      left right leftInitialSpine rightInitialSpine spine spine
      variableValues fuel targetParent leftProbeField rightProbeField
      parentType targetLeftArguments targetRightArguments leftRuntime
      rightRuntime hschema hleftValid hrightValid hleftFree hrightFree
      hleftNormal hrightNormal hobject hleftFuel hrightFuel hspineValid
      hspineValid
      (PathLocalSupportValidNormal.of_valid_normal_self hleftValid
        hleftFree hleftNormal)
      (PathLocalSupportValidNormal.of_valid_normal_self hrightValid
        hrightFree hrightNormal)
      PathLocalSelectionSetCurrentContext.self
      PathLocalSelectionSetCurrentContext.self hleftObservablePath
      hrightNoResponseName

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_object_right_responseName_diff_valid_normal_self
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {childSelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> ∃ leftSpine rightSpine,
          SelectedPathTaggedSelectionSetsResponseDiffWitness schema
            rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
            leftInitialSpine rightInitialSpine variableValues (fuel + 1)
            parentType parentType targetParent leftProbeField rightProbeField
            targetLeftArguments targetRightArguments leftRuntime rightRuntime
            left right leftSpine rightSpine left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hrightMem
    hleftNoResponseName
  rcases selectionSetValid_field_lookup_of_mem hrightValid hrightMem with
    ⟨fieldDefinition, hlookup, _harguments, _hfieldValid⟩
  rcases
      normalSelectionSetObservableResponsePath_of_valid_normal_object_field_mem
        hrightValid hrightNormal hobject hrightMem hlookup with
    ⟨pathTail, hrightObservablePath⟩
  rcases
      pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_observableResponsePath_valid_normal
        hrightObservablePath hrightValid hrightNormal with
    ⟨runtimeType, spine, hinclude, hobservableSpine⟩
  have hruntimeEq : runtimeType = parentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hobject
      hinclude
  subst runtimeType
  have hspineValid :
      SelectedFieldSpineRuntimeValid schema parentType parentType spine :=
    selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
      (hobservableSpine right)
  refine ⟨spine, spine, ?_⟩
  exact
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_right_observable_responseName_absent_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      left right leftInitialSpine rightInitialSpine spine spine
      variableValues fuel targetParent leftProbeField rightProbeField
      parentType targetLeftArguments targetRightArguments leftRuntime
      rightRuntime hschema hleftValid hrightValid hleftFree hrightFree
      hleftNormal hrightNormal hobject hleftFuel hrightFuel hspineValid
      hspineValid
      (PathLocalSupportValidNormal.of_valid_normal_self hleftValid
        hleftFree hleftNormal)
      (PathLocalSupportValidNormal.of_valid_normal_self hrightValid
        hrightFree hrightNormal)
      PathLocalSelectionSetCurrentContext.self
      PathLocalSelectionSetCurrentContext.self hrightObservablePath
      hleftNoResponseName

end GroundTypeNormalization

end NormalForm

end GraphQL
