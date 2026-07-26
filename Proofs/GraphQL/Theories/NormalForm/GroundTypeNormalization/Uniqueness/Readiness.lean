import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Probes
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Validity

/-!
Readiness facts for deep-success uniqueness probes.

These lemmas bridge normal/valid selection-set structure to the stronger
execution readiness predicate used by semantic separation.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem typeRef_named_isCompositeBool_false_of_isLeafType
    {schema : Schema} {typeName : Name}
    : schema.isLeafType typeName
      -> (TypeRef.named typeName).isCompositeBool schema = false := by
  intro hleaf
  rcases hleaf with ⟨typeDefinition, hlookup, htypeLeaf⟩
  cases typeDefinition <;>
    simp [TypeDefinition.isLeafType] at htypeLeaf
  all_goals
    simp [TypeRef.isCompositeBool, TypeRef.namedType, hlookup]

theorem objectTypeNameBool_of_typeIncludesObjectBool
    {schema : Schema} {typeName runtimeType : Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.typeIncludesObjectBool typeName runtimeType = true
      -> objectTypeNameBool schema runtimeType = true := by
  intro hschema hinclude
  have hmem : runtimeType ∈ schema.getPossibleTypes typeName :=
    List.contains_iff_mem.mp hinclude
  exact objectTypeNameBool_eq_true_of_objectType schema
    (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
      typeName runtimeType hmem)

theorem leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem
    (schema : Schema) (parentType : Name)
    {selectionSet : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Selection.field responseName fieldName arguments directives childSelectionSet
        ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> leafProbeFuel fieldDefinition.outputType
          ≤ selectionSetDeepProbeFuel schema parentType selectionSet := by
  intro hmem hlookup
  have hdeep :=
    selectionSetDeepProbeFuel_field_mem schema parentType selectionSet
      responseName fieldName arguments directives childSelectionSet
      fieldDefinition hmem hlookup
  omega

theorem selectionSetDeepProbeFuel_le_append_left (schema : Schema) (parentType : Name)
    : ∀ left right,
        selectionSetDeepProbeFuel schema parentType left
        ≤ selectionSetDeepProbeFuel schema parentType (left ++ right)
  | [], right => by
      simpa [selectionSetDeepProbeFuel] using
        Nat.succ_le_of_lt
          (selectionSetDeepProbeFuel_pos schema parentType right)
  | Selection.field responseName fieldName arguments directives
      childSelectionSet :: rest, right => by
      cases hlookup : schema.lookupField parentType fieldName with
      | none =>
          simpa [selectionSetDeepProbeFuel, hlookup] using
            selectionSetDeepProbeFuel_le_append_left schema parentType rest
              right
      | some fieldDefinition =>
          have htail :=
            selectionSetDeepProbeFuel_le_append_left schema parentType rest
              right
          simp [selectionSetDeepProbeFuel, hlookup]
          omega
  | Selection.inlineFragment (some typeCondition) directives
      childSelectionSet :: rest, right => by
      have htail :=
        selectionSetDeepProbeFuel_le_append_left schema parentType rest right
      simp [selectionSetDeepProbeFuel]
      omega
  | Selection.inlineFragment none directives childSelectionSet :: rest,
      right => by
      have htail :=
        selectionSetDeepProbeFuel_le_append_left schema parentType rest right
      simp [selectionSetDeepProbeFuel]
      omega

theorem selectionSetDeepProbeFuel_le_append_right (schema : Schema) (parentType : Name)
    : ∀ left right,
        selectionSetDeepProbeFuel schema parentType right
        ≤ selectionSetDeepProbeFuel schema parentType (left ++ right)
  | [], right => by
      simp
  | Selection.field responseName fieldName arguments directives
      childSelectionSet :: rest, right => by
      cases hlookup : schema.lookupField parentType fieldName with
      | none =>
          simpa [selectionSetDeepProbeFuel, hlookup] using
            selectionSetDeepProbeFuel_le_append_right schema parentType rest
              right
      | some fieldDefinition =>
          have htail :=
            selectionSetDeepProbeFuel_le_append_right schema parentType rest
              right
          simp [selectionSetDeepProbeFuel, hlookup]
          omega
  | Selection.inlineFragment (some typeCondition) directives
      childSelectionSet :: rest, right => by
      have htail :=
        selectionSetDeepProbeFuel_le_append_right schema parentType rest right
      simp [selectionSetDeepProbeFuel]
      omega
  | Selection.inlineFragment none directives childSelectionSet :: rest,
      right => by
      have htail :=
        selectionSetDeepProbeFuel_le_append_right schema parentType rest right
      simp [selectionSetDeepProbeFuel]
      omega

theorem selectionSetDeepProbeFuel_le_flatten_member
    (schema : Schema) (parentType : Name)
    {members : List (List Selection)} {selectionSet : List Selection}
    : selectionSet ∈ members
      -> selectionSetDeepProbeFuel schema parentType selectionSet
          ≤ selectionSetDeepProbeFuel schema parentType (List.flatten members) := by
  intro hmem
  induction members with
  | nil =>
      simp at hmem
  | cons head rest ih =>
      simp at hmem
      rcases hmem with hhead | htail
      · subst selectionSet
        exact
          selectionSetDeepProbeFuel_le_append_left schema parentType head
            (List.flatten rest)
      · exact
          Nat.le_trans (ih htail)
            (selectionSetDeepProbeFuel_le_append_right schema parentType head
              (List.flatten rest))

theorem selectionSetValid_field_lookup_leaf_or_composite_child
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> ∃ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
          ∧ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                  = false
                ∧ childSelectionSet = []
              ∨ schema.isCompositeType fieldDefinition.outputType.namedType
                ∧ childSelectionSet ≠ []
                ∧ Validation.selectionSetValid schema variableDefinitions
                    fieldDefinition.outputType.namedType childSelectionSet) := by
  intro hvalid hmem
  rcases selectionSetValid_field_lookup_of_mem hvalid hmem with
    ⟨fieldDefinition, hlookup, _harguments, hfieldValid⟩
  refine ⟨fieldDefinition, hlookup, ?_⟩
  simp [Validation.fieldSelectionSetValid] at hfieldValid
  rcases hfieldValid with ⟨_houtput, hleaf | hcomposite⟩
  · exact Or.inl
      ⟨typeRef_named_isCompositeBool_false_of_isLeafType hleaf.1,
        hleaf.2⟩
  · exact Or.inr ⟨hcomposite.1, hcomposite.2.1, hcomposite.2.2⟩

theorem selectionSetValid_field_child_of_mem_lookup
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> childSelectionSet ≠ []
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType childSelectionSet := by
  intro hvalid hmem hnonempty hlookup
  rcases selectionSetValid_field_child_of_mem hvalid hmem hnonempty with
    ⟨candidateDefinition, hcandidateLookup, _hcomposite, hchildValid⟩
  have hdefinition : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidateDefinition
  exact hchildValid

theorem selectionSetValid_object_field_child_of_mem_lookup
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType childSelectionSet := by
  intro hvalid hmem hlookup hobject
  rcases selectionSetValid_field_lookup_of_mem hvalid hmem with
    ⟨candidateDefinition, hcandidateLookup, _harguments, hfieldValid⟩
  have hdefinition : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidateDefinition
  have hcomposite :
      schema.isCompositeType fieldDefinition.outputType.namedType :=
    objectType_isCompositeType
      (objectType_of_objectTypeNameBool_eq_true schema hobject)
  exact
    (fieldSelectionSetValid_child_of_composite hfieldValid hcomposite).2

theorem selectionSetNormal_field_child_of_mem_lookup
    {schema : Schema} {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> selectionSetNormal schema fieldDefinition.outputType.namedType
          childSelectionSet := by
  intro hnormal hmem hlookup
  rcases selectionSetNormal_field_child_of_mem_with_returnType hnormal hmem
    with ⟨returnType, hreturnType, hchildNormal⟩
  have hnamed :
      fieldDefinition.outputType.namedType = returnType :=
    fieldDefinition_namedType_eq_of_fieldReturnType? hlookup hreturnType
  simpa [hnamed] using hchildNormal

theorem firstInlineFragmentTypeCondition?_some_of_valid_normal_abstract_field_mem_lookup
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = false
      -> ∃ runtimeType,
          firstInlineFragmentTypeCondition? childSelectionSet = some runtimeType
          ∧ schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
            = true := by
  intro hvalid hnormal hmem hlookup hcomposite hnonObject
  have hchildNonempty : childSelectionSet ≠ [] := by
    rcases selectionSetValid_field_lookup_leaf_or_composite_child hvalid hmem
      with ⟨candidateDefinition, hcandidateLookup, hkind⟩
    have hdefinition : candidateDefinition = fieldDefinition := by
      rw [hlookup] at hcandidateLookup
      exact Option.some.inj hcandidateLookup.symm
    subst candidateDefinition
    rcases hkind with hleaf | hcompositeChild
    · have hleafComposite := hleaf.1
      rw [hcomposite] at hleafComposite
      simp at hleafComposite
    · exact hcompositeChild.2.1
  have hchildNormal :
      selectionSetNormal schema fieldDefinition.outputType.namedType
        childSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
  cases childSelectionSet with
  | nil =>
      exact False.elim (hchildNonempty rfl)
  | cons child rest =>
      have hall :
          selectionsAllInlineFragments (child :: rest) :=
        selectionSetNormal_allInlineFragments_of_abstract hchildNormal
          hnonObject
      have hchildInline : Selection.isInlineFragment child :=
        hall child (by simp)
      cases child with
      | field responseName fieldName arguments directives childSelectionSet =>
          simp [Selection.isInlineFragment] at hchildInline
      | inlineFragment typeCondition directives inlineChildSelectionSet =>
          cases typeCondition with
          | none =>
              have hselectionGround :
                  selectionGroundTyped schema
                    fieldDefinition.outputType.namedType
                    (Selection.inlineFragment none directives
                      inlineChildSelectionSet) := by
                have hground := hchildNormal.1
                unfold selectionSetGroundTyped at hground
                exact hground.2
                  (Selection.inlineFragment none directives
                    inlineChildSelectionSet)
                  (by simp)
              simp [selectionGroundTyped] at hselectionGround
          | some typeCondition =>
              have hinlineMem :
                  Selection.inlineFragment (some typeCondition) directives
                    inlineChildSelectionSet ∈
                    Selection.inlineFragment (some typeCondition) directives
                      inlineChildSelectionSet :: rest := by
                simp
              rcases selectionSetNormal_inlineFragment_child_of_mem
                  hchildNormal hinlineMem with
                ⟨htypeObject, _hbodyNormal⟩
              have hchildValid :
                  Validation.selectionSetValid schema variableDefinitions
                    fieldDefinition.outputType.namedType
                    (Selection.inlineFragment (some typeCondition) directives
                      inlineChildSelectionSet :: rest) :=
                selectionSetValid_field_child_of_mem_lookup hvalid hmem
                  (by simp) hlookup
              have hoverlap :
                  schema.typesOverlap fieldDefinition.outputType.namedType
                    typeCondition :=
                selectionSetValid_inlineFragment_some_typesOverlap_of_mem
                  hchildValid hinlineMem
              have hreturnIncludes :
                  schema.typeIncludesObjectBool
                    fieldDefinition.outputType.namedType typeCondition = true :=
                typeIncludesObjectBool_of_typesOverlap_object schema hoverlap
                  htypeObject
              exact
                ⟨typeCondition,
                  by simp [firstInlineFragmentTypeCondition?],
                  hreturnIncludes⟩

theorem abstractRuntimeForFieldDeep?_some_of_valid_normal_abstract_mem_lookup
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = false
      -> ∃ runtimeType,
          abstractRuntimeForFieldDeep? schema parentType fieldName parentType selectionSet
            = some runtimeType
          ∧ schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
            = true := by
  intro hvalid hnormal hmem hlookup hcomposite hnonObject
  induction selectionSet with
  | nil =>
      simp at hmem
  | cons head tail ih =>
      cases head with
      | field headResponseName headFieldName headArguments headDirectives
          headChildSelectionSet =>
          cases hmatch : headFieldName == fieldName
          · rcases List.mem_cons.mp hmem with hhead | htail
            · cases hhead
              simp at hmatch
            · rcases ih (Validation.selectionSetValid_tail hvalid)
                (selectionSetNormal_tail hnormal) htail with
                ⟨runtimeType, hruntime, hinclude⟩
              exact
                ⟨runtimeType,
                  by
                    simp [abstractRuntimeForFieldDeep?, hmatch, hruntime],
                  hinclude⟩
          · have hheadFieldName : headFieldName = fieldName := by
              simpa using hmatch
            have hheadLookup :
                schema.lookupField parentType headFieldName =
                  some fieldDefinition := by
              simpa [hheadFieldName] using hlookup
            have hheadMem :
                Selection.field headResponseName headFieldName headArguments
                  headDirectives headChildSelectionSet ∈
                  Selection.field headResponseName headFieldName headArguments
                    headDirectives headChildSelectionSet :: tail := by
              simp
            rcases
                firstInlineFragmentTypeCondition?_some_of_valid_normal_abstract_field_mem_lookup
                  hvalid hnormal hheadMem hheadLookup hcomposite
                  hnonObject with
              ⟨runtimeType, hruntime, hinclude⟩
            exact
              ⟨runtimeType,
                by
                  simp [abstractRuntimeForFieldDeep?, hmatch, hruntime],
                hinclude⟩
      | inlineFragment typeCondition headDirectives headChildSelectionSet =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
          · rcases ih (Validation.selectionSetValid_tail hvalid)
              (selectionSetNormal_tail hnormal) htail with
              ⟨runtimeType, hruntime, hinclude⟩
            exact
              ⟨runtimeType,
                by
                  cases typeCondition <;>
                    simp [abstractRuntimeForFieldDeep?, hruntime],
                hinclude⟩

theorem abstractRuntimeForFieldHeadDeep?_some_of_valid_normal_abstract_mem_lookup
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = false
      -> ∃ runtimeType,
          abstractRuntimeForFieldHeadDeep? schema parentType fieldName
              arguments parentType selectionSet
            = some runtimeType
          ∧ schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
            = true := by
  intro hvalid hnormal hmem hlookup hcomposite hnonObject
  induction selectionSet with
  | nil =>
      simp at hmem
  | cons head tail ih =>
      cases head with
      | field headResponseName headFieldName headArguments headDirectives
          headChildSelectionSet =>
          by_cases hmatch :
              parentType = parentType
                ∧ headFieldName = fieldName
                ∧ Argument.argumentsEquivalent headArguments arguments
          · cases hfirst :
                firstInlineFragmentTypeCondition? headChildSelectionSet with
            | some runtimeType =>
                have hheadLookup :
                    schema.lookupField parentType headFieldName =
                      some fieldDefinition := by
                  simpa [hmatch.2.1] using hlookup
                have hheadMem :
                    Selection.field headResponseName headFieldName
                      headArguments headDirectives headChildSelectionSet ∈
                      Selection.field headResponseName headFieldName
                        headArguments headDirectives headChildSelectionSet ::
                        tail := by
                  simp
                rcases
                    firstInlineFragmentTypeCondition?_some_of_valid_normal_abstract_field_mem_lookup
                      hvalid hnormal hheadMem hheadLookup hcomposite
                      hnonObject with
                  ⟨candidateRuntimeType, hcandidateRuntime,
                    hcandidateInclude⟩
                have hcandidateEq :
                    candidateRuntimeType = runtimeType := by
                  rw [hfirst] at hcandidateRuntime
                  exact (Option.some.inj hcandidateRuntime).symm
                exact
                  ⟨runtimeType,
                    by
                      simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                        hfirst],
                    by simpa [hcandidateEq] using hcandidateInclude⟩
            | none =>
                have hheadLookup :
                    schema.lookupField parentType headFieldName =
                      some fieldDefinition := by
                  simpa [hmatch.2.1] using hlookup
                have hheadMem :
                    Selection.field headResponseName headFieldName
                      headArguments headDirectives headChildSelectionSet ∈
                      Selection.field headResponseName headFieldName
                        headArguments headDirectives headChildSelectionSet ::
                        tail := by
                  simp
                rcases
                    firstInlineFragmentTypeCondition?_some_of_valid_normal_abstract_field_mem_lookup
                      hvalid hnormal hheadMem hheadLookup hcomposite
                      hnonObject with
                  ⟨runtimeType, hruntime, _hinclude⟩
                rw [hfirst] at hruntime
                cases hruntime
          · rcases List.mem_cons.mp hmem with hhead | htail
            · cases hhead
              have hargs :
                  Argument.argumentsEquivalent arguments arguments :=
                argumentsEquivalent_refl arguments
              exact False.elim (hmatch ⟨rfl, rfl, hargs⟩)
            · rcases ih (Validation.selectionSetValid_tail hvalid)
                (selectionSetNormal_tail hnormal) htail with
                ⟨runtimeType, hruntime, hinclude⟩
              have hmatchReduced :
                  ¬ (headFieldName = fieldName
                    ∧ Argument.argumentsEquivalent headArguments arguments) := by
                intro h
                exact hmatch ⟨rfl, h.1, h.2⟩
              exact
                ⟨runtimeType,
                  by
                    simp [abstractRuntimeForFieldHeadDeep?, hmatchReduced,
                      hruntime],
                  hinclude⟩
      | inlineFragment typeCondition headDirectives headChildSelectionSet =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
          · rcases ih (Validation.selectionSetValid_tail hvalid)
              (selectionSetNormal_tail hnormal) htail with
              ⟨runtimeType, hruntime, hinclude⟩
            exact
              ⟨runtimeType,
                by
                  cases typeCondition <;>
                    simp [abstractRuntimeForFieldHeadDeep?, hruntime],
                hinclude⟩

theorem abstractRuntimeForFieldDeep?_some_include_of_valid_normal_size
    (schema : Schema)
    {variableDefinitions : List VariableDefinition}
    {targetParent targetField : Name}
    {targetFieldDefinition : FieldDefinition}
    : schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> ∀ n currentParent (selectionSet : List Selection) runtimeType,
          SelectionSet.size selectionSet < n
          -> Validation.selectionSetValid schema variableDefinitions currentParent
              selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema currentParent selectionSet
          -> abstractRuntimeForFieldDeep? schema targetParent targetField
                currentParent selectionSet
              = some runtimeType
          -> schema.typeIncludesObjectBool
                targetFieldDefinition.outputType.namedType runtimeType
              = true := by
  intro htargetLookup htargetComposite htargetNonObject n
  induction n with
  | zero =>
      intro currentParent selectionSet runtimeType hsize _hvalid _hfree
        _hnormal _hruntime
      omega
  | succ n ih =>
      intro currentParent selectionSet runtimeType hsize hvalid hfree hnormal
        hruntime
      cases selectionSet with
      | nil =>
          simp [abstractRuntimeForFieldDeep?] at hruntime
      | cons head rest =>
          cases head with
          | field responseName fieldName arguments directives
              childSelectionSet =>
              have hheadMem :
                  Selection.field responseName fieldName arguments directives
                      childSelectionSet ∈
                    Selection.field responseName fieldName arguments
                      directives childSelectionSet :: rest := by
                simp
              cases hmatch :
                  (currentParent == targetParent
                    && fieldName == targetField)
              · cases hrest :
                    abstractRuntimeForFieldDeep? schema targetParent
                      targetField currentParent rest with
                | none =>
                    cases hlookup :
                        schema.lookupField currentParent fieldName with
                    | none =>
                        simp [abstractRuntimeForFieldDeep?, hmatch, hrest,
                          hlookup] at hruntime
                    | some fieldDefinition =>
                        cases hchild : childSelectionSet with
                        | nil =>
                            simp [abstractRuntimeForFieldDeep?, hmatch,
                              hrest, hlookup, hchild] at hruntime
                        | cons childHead childTail =>
                            have hchildRuntime :
                                abstractRuntimeForFieldDeep? schema
                                  targetParent targetField
                                  fieldDefinition.outputType.namedType
                                  (childHead :: childTail)
                                =
                                  some runtimeType := by
                              simpa [abstractRuntimeForFieldDeep?, hmatch,
                                hrest, hlookup, hchild] using hruntime
                            have hchildValid :
                                Validation.selectionSetValid schema
                                  variableDefinitions
                                  fieldDefinition.outputType.namedType
                                  (childHead :: childTail) :=
                              have hheadMemChild :
                                  Selection.field responseName fieldName
                                      arguments directives
                                      (childHead :: childTail) ∈
                                    Selection.field responseName fieldName
                                      arguments directives
                                      childSelectionSet :: rest := by
                                simp [hchild]
                              selectionSetValid_field_child_of_mem_lookup
                                hvalid hheadMemChild (by simp) hlookup
                            have hchildFree :
                                selectionSetDirectiveFree
                                  (childHead :: childTail) := by
                              simpa [hchild] using
                                selectionSetDirectiveFree_field_child_of_mem
                                  hfree hheadMem
                            have hchildNormal :
                                selectionSetNormal schema
                                  fieldDefinition.outputType.namedType
                                  (childHead :: childTail) := by
                              simpa [hchild] using
                                selectionSetNormal_field_child_of_mem_lookup
                                  hnormal hheadMem hlookup
                            have hchildSize :
                                SelectionSet.size (childHead :: childTail) <
                                  n := by
                              have hlt :
                                  SelectionSet.size (childHead :: childTail)
                                    <
                                  SelectionSet.size
                                    (Selection.field responseName fieldName
                                      arguments directives
                                      (childHead :: childTail) :: rest) := by
                                simp [SelectionSet.size, Selection.size]
                                omega
                              simp [hchild] at hsize
                              omega
                            exact
                              ih fieldDefinition.outputType.namedType
                                (childHead :: childTail) runtimeType
                                hchildSize hchildValid hchildFree
                                hchildNormal hchildRuntime
                | some restRuntime =>
                    have hrestRuntime :
                        restRuntime = runtimeType := by
                      simpa [abstractRuntimeForFieldDeep?, hmatch, hrest]
                        using hruntime
                    subst runtimeType
                    have hrestSize : SelectionSet.size rest < n := by
                      simp [SelectionSet.size, Selection.size] at hsize
                      omega
                    exact
                      ih currentParent rest restRuntime hrestSize
                        (Validation.selectionSetValid_tail hvalid)
                        (selectionSetDirectiveFree_tail hfree)
                        (selectionSetNormal_tail hnormal) hrest
              · cases hfirst :
                    firstInlineFragmentTypeCondition? childSelectionSet with
                | some headRuntime =>
                    have hparts :
                        currentParent = targetParent
                          ∧ fieldName = targetField := by
                      simpa using hmatch
                    have hheadLookup :
                        schema.lookupField currentParent fieldName =
                          some targetFieldDefinition := by
                      simpa [hparts.1, hparts.2] using htargetLookup
                    rcases
                        firstInlineFragmentTypeCondition?_some_of_valid_normal_abstract_field_mem_lookup
                          hvalid hnormal hheadMem hheadLookup
                          htargetComposite htargetNonObject with
                      ⟨candidateRuntime, hcandidateRuntime,
                        hcandidateInclude⟩
                    have hcandidateEq : candidateRuntime = headRuntime := by
                      rw [hfirst] at hcandidateRuntime
                      exact (Option.some.inj hcandidateRuntime).symm
                    have hruntimeEq : headRuntime = runtimeType := by
                      simpa [abstractRuntimeForFieldDeep?, hmatch, hfirst]
                        using hruntime
                    subst candidateRuntime
                    subst runtimeType
                    exact hcandidateInclude
                | none =>
                    cases hrest :
                        abstractRuntimeForFieldDeep? schema targetParent
                          targetField currentParent rest with
                    | none =>
                        cases hlookup :
                            schema.lookupField currentParent fieldName with
                        | none =>
                            simp [abstractRuntimeForFieldDeep?, hmatch,
                              hfirst, hrest, hlookup] at hruntime
                        | some fieldDefinition =>
                            cases hchild : childSelectionSet with
                            | nil =>
                                simp [abstractRuntimeForFieldDeep?, hmatch,
                                  hrest, hlookup, hchild,
                                  firstInlineFragmentTypeCondition?] at hruntime
                            | cons childHead childTail =>
                                have hfirstChild :
                                    firstInlineFragmentTypeCondition?
                                        (childHead :: childTail) =
                                      none := by
                                  simpa [hchild] using hfirst
                                have hchildRuntime :
                                    abstractRuntimeForFieldDeep? schema
                                      targetParent targetField
                                      fieldDefinition.outputType.namedType
                                      (childHead :: childTail)
                                    =
                                      some runtimeType := by
                                  simpa [abstractRuntimeForFieldDeep?, hmatch,
                                    hfirstChild, hrest, hlookup, hchild] using
                                    hruntime
                                have hchildValid :
                                    Validation.selectionSetValid schema
                                      variableDefinitions
                                      fieldDefinition.outputType.namedType
                                      (childHead :: childTail) :=
                                  have hheadMemChild :
                                      Selection.field responseName fieldName
                                          arguments directives
                                          (childHead :: childTail) ∈
                                        Selection.field responseName fieldName
                                          arguments directives
                                          childSelectionSet :: rest := by
                                    simp [hchild]
                                  selectionSetValid_field_child_of_mem_lookup
                                    hvalid hheadMemChild (by simp) hlookup
                                have hchildFree :
                                    selectionSetDirectiveFree
                                      (childHead :: childTail) := by
                                  simpa [hchild] using
                                    selectionSetDirectiveFree_field_child_of_mem
                                      hfree hheadMem
                                have hchildNormal :
                                    selectionSetNormal schema
                                      fieldDefinition.outputType.namedType
                                      (childHead :: childTail) := by
                                  simpa [hchild] using
                                    selectionSetNormal_field_child_of_mem_lookup
                                      hnormal hheadMem hlookup
                                have hchildSize :
                                    SelectionSet.size
                                        (childHead :: childTail) < n := by
                                  have hlt :
                                      SelectionSet.size
                                          (childHead :: childTail)
                                        <
                                      SelectionSet.size
                                        (Selection.field responseName fieldName
                                          arguments directives
                                          (childHead :: childTail) ::
                                          rest) := by
                                    simp [SelectionSet.size, Selection.size]
                                    omega
                                  simp [hchild] at hsize
                                  omega
                                exact
                                  ih fieldDefinition.outputType.namedType
                                    (childHead :: childTail) runtimeType
                                    hchildSize hchildValid hchildFree
                                    hchildNormal hchildRuntime
                    | some restRuntime =>
                        have hrestRuntime :
                            restRuntime = runtimeType := by
                          simpa [abstractRuntimeForFieldDeep?, hmatch,
                            hfirst, hrest] using hruntime
                        subst runtimeType
                        have hrestSize : SelectionSet.size rest < n := by
                          simp [SelectionSet.size, Selection.size] at hsize
                          omega
                        exact
                          ih currentParent rest restRuntime hrestSize
                            (Validation.selectionSetValid_tail hvalid)
                            (selectionSetDirectiveFree_tail hfree)
                            (selectionSetNormal_tail hnormal) hrest
          | inlineFragment typeCondition directives childSelectionSet =>
              cases typeCondition with
              | none =>
                  have hheadMem :
                      Selection.inlineFragment none directives
                          childSelectionSet ∈
                        Selection.inlineFragment none directives
                          childSelectionSet :: rest := by
                    simp
                  have hground :
                      selectionGroundTyped schema currentParent
                        (Selection.inlineFragment none directives
                          childSelectionSet) := by
                    have hsetGround :
                        selectionSetGroundTyped schema currentParent
                          (Selection.inlineFragment none directives
                            childSelectionSet :: rest) :=
                      hnormal.1
                    unfold selectionSetGroundTyped at hsetGround
                    exact hsetGround.2 _ hheadMem
                  simp [selectionGroundTyped] at hground
              | some typeCondition =>
                  have hheadMem :
                      Selection.inlineFragment (some typeCondition) directives
                          childSelectionSet ∈
                        Selection.inlineFragment (some typeCondition)
                          directives childSelectionSet :: rest := by
                    simp
                  cases hrest :
                      abstractRuntimeForFieldDeep? schema targetParent
                        targetField currentParent rest with
                  | some restRuntime =>
                      have hrestRuntime :
                          restRuntime = runtimeType := by
                        simpa [abstractRuntimeForFieldDeep?, hrest] using
                          hruntime
                      subst runtimeType
                      have hrestSize : SelectionSet.size rest < n := by
                        simp [SelectionSet.size, Selection.size] at hsize
                        omega
                      exact
                        ih currentParent rest restRuntime hrestSize
                          (Validation.selectionSetValid_tail hvalid)
                          (selectionSetDirectiveFree_tail hfree)
                          (selectionSetNormal_tail hnormal) hrest
                  | none =>
                      cases hchild : childSelectionSet with
                      | nil =>
                          simp [abstractRuntimeForFieldDeep?, hrest, hchild]
                            at hruntime
                      | cons childHead childTail =>
                          have hchildRuntime :
                              abstractRuntimeForFieldDeep? schema
                                targetParent targetField typeCondition
                                (childHead :: childTail)
                              =
                                some runtimeType := by
                            simpa [abstractRuntimeForFieldDeep?, hrest,
                              hchild] using hruntime
                          have hchildValid :
                              Validation.selectionSetValid schema
                                variableDefinitions typeCondition
                                (childHead :: childTail) := by
                            simpa [hchild] using
                              selectionSetValid_inlineFragment_some_child_of_mem
                                hvalid hheadMem
                          have hchildFree :
                              selectionSetDirectiveFree
                                (childHead :: childTail) := by
                            simpa [hchild] using
                              selectionSetDirectiveFree_inlineFragment_child_of_mem
                                hfree hheadMem
                          have hchildNormal :
                              selectionSetNormal schema typeCondition
                                (childHead :: childTail) := by
                            simpa [hchild] using
                              (selectionSetNormal_inlineFragment_child_of_mem
                                hnormal hheadMem).2
                          have hchildSize :
                              SelectionSet.size (childHead :: childTail) <
                                n := by
                            have hlt :
                                SelectionSet.size (childHead :: childTail)
                                  <
                                SelectionSet.size
                                  (Selection.inlineFragment
                                    (some typeCondition) directives
                                    (childHead :: childTail) :: rest) := by
                              simp [SelectionSet.size, Selection.size]
                              omega
                            simp [hchild] at hsize
                            omega
                          exact
                            ih typeCondition (childHead :: childTail)
                              runtimeType hchildSize hchildValid hchildFree
                              hchildNormal hchildRuntime

theorem abstractRuntimeForFieldDeep?_some_include_of_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {currentParent targetParent targetField runtimeType : Name}
    {selectionSet : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions currentParent selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema currentParent selectionSet
      -> schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldDeep? schema targetParent targetField currentParent
            selectionSet
          = some runtimeType
      -> schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType runtimeType
          = true := by
  intro hvalid hfree hnormal htargetLookup htargetComposite htargetNonObject
    hruntime
  exact
    abstractRuntimeForFieldDeep?_some_include_of_valid_normal_size schema
      htargetLookup htargetComposite htargetNonObject
      (SelectionSet.size selectionSet + 1) currentParent selectionSet
      runtimeType (by omega) hvalid hfree hnormal hruntime

theorem abstractRuntimeForFieldHeadDeep?_some_include_of_valid_normal_size
    (schema : Schema)
    {variableDefinitions : List VariableDefinition}
    {targetParent targetField : Name}
    {targetArguments : List Argument}
    {targetFieldDefinition : FieldDefinition}
    : schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> ∀ n currentParent (selectionSet : List Selection) runtimeType,
          SelectionSet.size selectionSet < n
          -> Validation.selectionSetValid schema variableDefinitions currentParent
              selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema currentParent selectionSet
          -> abstractRuntimeForFieldHeadDeep? schema targetParent targetField
                targetArguments currentParent selectionSet
              = some runtimeType
          -> schema.typeIncludesObjectBool
                targetFieldDefinition.outputType.namedType runtimeType
              = true := by
  intro htargetLookup htargetComposite htargetNonObject n
  induction n with
  | zero =>
      intro currentParent selectionSet runtimeType hsize _hvalid _hfree
        _hnormal _hruntime
      omega
  | succ n ih =>
      intro currentParent selectionSet runtimeType hsize hvalid hfree hnormal
        hruntime
      cases selectionSet with
      | nil =>
          simp [abstractRuntimeForFieldHeadDeep?] at hruntime
      | cons head rest =>
          cases head with
          | field responseName fieldName arguments directives
              childSelectionSet =>
              have hheadMem :
                  Selection.field responseName fieldName arguments directives
                      childSelectionSet ∈
                    Selection.field responseName fieldName arguments
                      directives childSelectionSet :: rest := by
                simp
              by_cases hmatch :
                  currentParent = targetParent
                    ∧ fieldName = targetField
                    ∧ Argument.argumentsEquivalent arguments targetArguments
              · cases hfirst :
                    firstInlineFragmentTypeCondition? childSelectionSet with
                | some headRuntime =>
                    have hheadLookup :
                        schema.lookupField currentParent fieldName =
                          some targetFieldDefinition := by
                      simpa [hmatch.1, hmatch.2.1] using htargetLookup
                    rcases
                        firstInlineFragmentTypeCondition?_some_of_valid_normal_abstract_field_mem_lookup
                          hvalid hnormal hheadMem hheadLookup
                          htargetComposite htargetNonObject with
                      ⟨candidateRuntime, hcandidateRuntime,
                        hcandidateInclude⟩
                    have hcandidateEq : candidateRuntime = headRuntime := by
                      rw [hfirst] at hcandidateRuntime
                      exact (Option.some.inj hcandidateRuntime).symm
                    have hruntimeEq : headRuntime = runtimeType := by
                      simpa [abstractRuntimeForFieldHeadDeep?, hmatch,
                        hfirst] using hruntime
                    subst candidateRuntime
                    subst runtimeType
                    exact hcandidateInclude
                | none =>
                    have hheadLookup :
                        schema.lookupField currentParent fieldName =
                          some targetFieldDefinition := by
                      simpa [hmatch.1, hmatch.2.1] using htargetLookup
                    cases hrest :
                        abstractRuntimeForFieldHeadDeep? schema targetParent
                          targetField targetArguments currentParent rest with
                    | some restRuntime =>
                        have hrestTarget :
                            abstractRuntimeForFieldHeadDeep? schema
                              targetParent targetField targetArguments
                              targetParent rest =
                              some restRuntime := by
                          simpa [hmatch.1] using hrest
                        have hrestRuntime :
                            restRuntime = runtimeType := by
                          simpa [abstractRuntimeForFieldHeadDeep?, hmatch,
                            hfirst, hrestTarget] using hruntime
                        subst runtimeType
                        have hrestSize : SelectionSet.size rest < n := by
                          simp [SelectionSet.size, Selection.size] at hsize
                          omega
                        exact
                          ih currentParent rest restRuntime hrestSize
                            (Validation.selectionSetValid_tail hvalid)
                            (selectionSetDirectiveFree_tail hfree)
                            (selectionSetNormal_tail hnormal) hrest
                    | none =>
                        have hrestTarget :
                            abstractRuntimeForFieldHeadDeep? schema
                              targetParent targetField targetArguments
                              targetParent rest =
                              none := by
                          simpa [hmatch.1] using hrest
                        cases hchild : childSelectionSet with
                        | nil =>
                            simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                              hrestTarget, htargetLookup, hchild,
                              firstInlineFragmentTypeCondition?]
                              at hruntime
                        | cons childHead childTail =>
                            have hfirstChild :
                                firstInlineFragmentTypeCondition?
                                    (childHead :: childTail) =
                                  none := by
                              simpa [hchild] using hfirst
                            have hchildRuntime :
                                abstractRuntimeForFieldHeadDeep? schema
                                  targetParent targetField targetArguments
                                  targetFieldDefinition.outputType.namedType
                                  (childHead :: childTail)
                                =
                                  some runtimeType := by
                              simpa [abstractRuntimeForFieldHeadDeep?,
                                hmatch, hfirstChild, hrestTarget,
                                htargetLookup,
                                hchild] using hruntime
                            have hchildValid :
                                Validation.selectionSetValid schema
                                  variableDefinitions
                                  targetFieldDefinition.outputType.namedType
                                  (childHead :: childTail) :=
                              have hheadMemChild :
                                  Selection.field responseName fieldName
                                      arguments directives
                                      (childHead :: childTail) ∈
                                    Selection.field responseName fieldName
                                      arguments directives childSelectionSet ::
                                      rest := by
                                simp [hchild]
                              selectionSetValid_field_child_of_mem_lookup
                                hvalid hheadMemChild (by simp) hheadLookup
                            have hchildFree :
                                selectionSetDirectiveFree
                                  (childHead :: childTail) := by
                              simpa [hchild] using
                                selectionSetDirectiveFree_field_child_of_mem
                                  hfree hheadMem
                            have hchildNormal :
                                selectionSetNormal schema
                                  targetFieldDefinition.outputType.namedType
                                  (childHead :: childTail) := by
                              simpa [hchild] using
                                selectionSetNormal_field_child_of_mem_lookup
                                  hnormal hheadMem hheadLookup
                            have hchildSize :
                                SelectionSet.size (childHead :: childTail) <
                                  n := by
                              have hlt :
                                  SelectionSet.size (childHead :: childTail)
                                    <
                                  SelectionSet.size
                                    (Selection.field responseName fieldName
                                      arguments directives
                                      (childHead :: childTail) :: rest) := by
                                simp [SelectionSet.size, Selection.size]
                                omega
                              simp [hchild] at hsize
                              omega
                            exact
                              ih targetFieldDefinition.outputType.namedType
                                (childHead :: childTail) runtimeType
                                hchildSize hchildValid hchildFree
                                hchildNormal hchildRuntime
              · cases hrest :
                    abstractRuntimeForFieldHeadDeep? schema targetParent
                      targetField targetArguments currentParent rest with
                | some restRuntime =>
                    have hrestRuntime :
                        restRuntime = runtimeType := by
                      simpa [abstractRuntimeForFieldHeadDeep?, hmatch, hrest]
                        using hruntime
                    subst runtimeType
                    have hrestSize : SelectionSet.size rest < n := by
                      simp [SelectionSet.size, Selection.size] at hsize
                      omega
                    exact
                      ih currentParent rest restRuntime hrestSize
                        (Validation.selectionSetValid_tail hvalid)
                        (selectionSetDirectiveFree_tail hfree)
                        (selectionSetNormal_tail hnormal) hrest
                | none =>
                    cases hlookup :
                        schema.lookupField currentParent fieldName with
                    | none =>
                        simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                          hrest, hlookup] at hruntime
                    | some fieldDefinition =>
                        cases hchild : childSelectionSet with
                        | nil =>
                            simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                              hrest, hlookup, hchild] at hruntime
                        | cons childHead childTail =>
                            have hchildRuntime :
                                abstractRuntimeForFieldHeadDeep? schema
                                  targetParent targetField targetArguments
                                  fieldDefinition.outputType.namedType
                                  (childHead :: childTail)
                                =
                                  some runtimeType := by
                              simpa [abstractRuntimeForFieldHeadDeep?,
                                hmatch, hrest, hlookup, hchild] using
                                hruntime
                            have hchildValid :
                                Validation.selectionSetValid schema
                                  variableDefinitions
                                  fieldDefinition.outputType.namedType
                                  (childHead :: childTail) :=
                              have hheadMemChild :
                                  Selection.field responseName fieldName
                                      arguments directives
                                      (childHead :: childTail) ∈
                                    Selection.field responseName fieldName
                                      arguments directives childSelectionSet ::
                                      rest := by
                                simp [hchild]
                              selectionSetValid_field_child_of_mem_lookup
                                hvalid hheadMemChild (by simp) hlookup
                            have hchildFree :
                                selectionSetDirectiveFree
                                  (childHead :: childTail) := by
                              simpa [hchild] using
                                selectionSetDirectiveFree_field_child_of_mem
                                  hfree hheadMem
                            have hchildNormal :
                                selectionSetNormal schema
                                  fieldDefinition.outputType.namedType
                                  (childHead :: childTail) := by
                              simpa [hchild] using
                                selectionSetNormal_field_child_of_mem_lookup
                                  hnormal hheadMem hlookup
                            have hchildSize :
                                SelectionSet.size (childHead :: childTail) <
                                  n := by
                              have hlt :
                                  SelectionSet.size (childHead :: childTail)
                                    <
                                  SelectionSet.size
                                    (Selection.field responseName fieldName
                                      arguments directives
                                      (childHead :: childTail) :: rest) := by
                                simp [SelectionSet.size, Selection.size]
                                omega
                              simp [hchild] at hsize
                              omega
                            exact
                              ih fieldDefinition.outputType.namedType
                                (childHead :: childTail) runtimeType
                                hchildSize hchildValid hchildFree
                                hchildNormal hchildRuntime
          | inlineFragment typeCondition directives childSelectionSet =>
              cases typeCondition with
              | none =>
                  have hheadMem :
                      Selection.inlineFragment none directives
                          childSelectionSet ∈
                        Selection.inlineFragment none directives
                          childSelectionSet :: rest := by
                    simp
                  have hground :
                      selectionGroundTyped schema currentParent
                        (Selection.inlineFragment none directives
                          childSelectionSet) := by
                    have hsetGround :
                        selectionSetGroundTyped schema currentParent
                          (Selection.inlineFragment none directives
                            childSelectionSet :: rest) :=
                      hnormal.1
                    unfold selectionSetGroundTyped at hsetGround
                    exact hsetGround.2 _ hheadMem
                  simp [selectionGroundTyped] at hground
              | some typeCondition =>
                  have hheadMem :
                      Selection.inlineFragment (some typeCondition) directives
                          childSelectionSet ∈
                        Selection.inlineFragment (some typeCondition)
                          directives childSelectionSet :: rest := by
                    simp
                  cases hrest :
                      abstractRuntimeForFieldHeadDeep? schema targetParent
                        targetField targetArguments currentParent rest with
                  | some restRuntime =>
                      have hrestRuntime :
                          restRuntime = runtimeType := by
                        simpa [abstractRuntimeForFieldHeadDeep?, hrest] using
                          hruntime
                      subst runtimeType
                      have hrestSize : SelectionSet.size rest < n := by
                        simp [SelectionSet.size, Selection.size] at hsize
                        omega
                      exact
                        ih currentParent rest restRuntime hrestSize
                          (Validation.selectionSetValid_tail hvalid)
                          (selectionSetDirectiveFree_tail hfree)
                          (selectionSetNormal_tail hnormal) hrest
                  | none =>
                      cases hchild : childSelectionSet with
                      | nil =>
                          simp [abstractRuntimeForFieldHeadDeep?, hrest,
                            hchild] at hruntime
                      | cons childHead childTail =>
                          have hchildRuntime :
                              abstractRuntimeForFieldHeadDeep? schema
                                targetParent targetField targetArguments
                                typeCondition (childHead :: childTail)
                              =
                                some runtimeType := by
                            simpa [abstractRuntimeForFieldHeadDeep?, hrest,
                              hchild] using hruntime
                          have hchildValid :
                              Validation.selectionSetValid schema
                                variableDefinitions typeCondition
                                (childHead :: childTail) := by
                            simpa [hchild] using
                              selectionSetValid_inlineFragment_some_child_of_mem
                                hvalid hheadMem
                          have hchildFree :
                              selectionSetDirectiveFree
                                (childHead :: childTail) := by
                            simpa [hchild] using
                              selectionSetDirectiveFree_inlineFragment_child_of_mem
                                hfree hheadMem
                          have hchildNormal :
                              selectionSetNormal schema typeCondition
                                (childHead :: childTail) := by
                            simpa [hchild] using
                              (selectionSetNormal_inlineFragment_child_of_mem
                                hnormal hheadMem).2
                          have hchildSize :
                              SelectionSet.size (childHead :: childTail) <
                                n := by
                            have hlt :
                                SelectionSet.size (childHead :: childTail)
                                  <
                                SelectionSet.size
                                  (Selection.inlineFragment
                                    (some typeCondition) directives
                                    (childHead :: childTail) :: rest) := by
                              simp [SelectionSet.size, Selection.size]
                              omega
                            simp [hchild] at hsize
                            omega
                          exact
                            ih typeCondition (childHead :: childTail)
                              runtimeType hchildSize hchildValid hchildFree
                              hchildNormal hchildRuntime

theorem abstractRuntimeForFieldHeadDeep?_some_include_of_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {currentParent targetParent targetField runtimeType : Name}
    {targetArguments : List Argument}
    {selectionSet : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions currentParent selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema currentParent selectionSet
      -> schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments currentParent selectionSet
          = some runtimeType
      -> schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType runtimeType
          = true := by
  intro hvalid hfree hnormal htargetLookup htargetComposite htargetNonObject
    hruntime
  exact
    abstractRuntimeForFieldHeadDeep?_some_include_of_valid_normal_size schema
      htargetLookup htargetComposite htargetNonObject
      (SelectionSet.size selectionSet + 1) currentParent selectionSet
      runtimeType (by omega) hvalid hfree hnormal hruntime

theorem abstractRuntimeForFieldDeep?_object_field_child_promote_some_of_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition targetFieldDefinition : FieldDefinition}
    {targetParent targetField targetRuntimeType : Name}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldDeep? schema targetParent targetField
            fieldDefinition.outputType.namedType childSelectionSet
          = some targetRuntimeType
      -> ∃ runtimeType,
          abstractRuntimeForFieldDeep? schema targetParent targetField
              parentType selectionSet
            = some runtimeType
          ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType runtimeType
            = true := by
  intro hvalid hfree hnormal hmem hlookup htargetLookup htargetComposite
    htargetNonObject hchildRuntime
  have hsome :
      ∃ runtimeType,
        abstractRuntimeForFieldDeep? schema targetParent targetField
          parentType selectionSet = some runtimeType := by
    induction selectionSet with
    | nil =>
        simp at hmem
    | cons head rest ih =>
        cases head with
        | field headResponseName headFieldName headArguments headDirectives
            headChildSelectionSet =>
            rcases List.mem_cons.mp hmem with hhead | htail
            · cases hhead
              cases hcurrent :
                  (if parentType == targetParent && fieldName == targetField
                    then firstInlineFragmentTypeCondition? childSelectionSet
                    else none) with
              | some currentRuntimeType =>
                  have hcurrent' :
                      (if parentType = targetParent ∧ fieldName = targetField
                        then firstInlineFragmentTypeCondition? childSelectionSet
                        else none) = some currentRuntimeType := by
                    simpa using hcurrent
                  exact
                    ⟨currentRuntimeType, by
                      simp [abstractRuntimeForFieldDeep?, hcurrent']⟩
              | none =>
                  have hcurrent' :
                      (if parentType = targetParent ∧ fieldName = targetField
                        then firstInlineFragmentTypeCondition? childSelectionSet
                        else none) = none := by
                    simpa using hcurrent
                  cases hrest :
                      abstractRuntimeForFieldDeep? schema targetParent
                        targetField parentType rest with
                  | some restRuntimeType =>
                      exact
                        ⟨restRuntimeType, by
                          simp [abstractRuntimeForFieldDeep?, hcurrent',
                            hrest]⟩
                  | none =>
                      exact
                        ⟨targetRuntimeType, by
                          simp [abstractRuntimeForFieldDeep?, hcurrent',
                            hrest, hlookup, hchildRuntime]⟩
            · rcases ih (Validation.selectionSetValid_tail hvalid)
                (selectionSetDirectiveFree_tail hfree)
                (selectionSetNormal_tail hnormal) htail with
                ⟨tailRuntimeType, htailRuntime⟩
              cases hcurrent :
                  (if parentType == targetParent && headFieldName == targetField
                    then
                      firstInlineFragmentTypeCondition? headChildSelectionSet
                    else none) with
              | some currentRuntimeType =>
                  have hcurrent' :
                      (if parentType = targetParent
                        ∧ headFieldName = targetField then
                        firstInlineFragmentTypeCondition? headChildSelectionSet
                      else none) = some currentRuntimeType := by
                    simpa using hcurrent
                  exact
                    ⟨currentRuntimeType, by
                      simp [abstractRuntimeForFieldDeep?, hcurrent']⟩
              | none =>
                  have hcurrent' :
                      (if parentType = targetParent
                        ∧ headFieldName = targetField then
                        firstInlineFragmentTypeCondition? headChildSelectionSet
                      else none) = none := by
                    simpa using hcurrent
                  exact
                    ⟨tailRuntimeType, by
                      simp [abstractRuntimeForFieldDeep?, hcurrent',
                        htailRuntime]⟩
        | inlineFragment typeCondition headDirectives headChildSelectionSet =>
            rcases List.mem_cons.mp hmem with hhead | htail
            · cases hhead
            · rcases ih (Validation.selectionSetValid_tail hvalid)
                (selectionSetDirectiveFree_tail hfree)
                (selectionSetNormal_tail hnormal) htail with
                ⟨tailRuntimeType, htailRuntime⟩
              exact
                ⟨tailRuntimeType, by
                  cases typeCondition <;>
                    simp [abstractRuntimeForFieldDeep?, htailRuntime]⟩
  rcases hsome with ⟨runtimeType, hruntime⟩
  exact
    ⟨runtimeType, hruntime,
      abstractRuntimeForFieldDeep?_some_include_of_valid_normal hvalid hfree
        hnormal htargetLookup htargetComposite htargetNonObject hruntime⟩

theorem abstractRuntimeForFieldDeep?_inlineFragment_child_promote_some_of_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {targetFieldDefinition : FieldDefinition}
    {targetParent targetField targetRuntimeType : Name}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldDeep? schema targetParent targetField
            typeCondition childSelectionSet
          = some targetRuntimeType
      -> ∃ runtimeType,
          abstractRuntimeForFieldDeep? schema targetParent targetField
              parentType selectionSet
            = some runtimeType
          ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType runtimeType
            = true := by
  intro hvalid hfree hnormal hmem htargetLookup htargetComposite
    htargetNonObject hchildRuntime
  have hsome :
      ∃ runtimeType,
        abstractRuntimeForFieldDeep? schema targetParent targetField
          parentType selectionSet = some runtimeType := by
    induction selectionSet with
    | nil =>
        simp at hmem
    | cons head rest ih =>
        cases head with
        | field responseName fieldName arguments fieldDirectives
            fieldChildSelectionSet =>
            rcases List.mem_cons.mp hmem with hhead | htail
            · cases hhead
            · rcases ih (Validation.selectionSetValid_tail hvalid)
                (selectionSetDirectiveFree_tail hfree)
                (selectionSetNormal_tail hnormal) htail with
                ⟨tailRuntimeType, htailRuntime⟩
              cases hcurrent :
                  (if parentType == targetParent && fieldName == targetField
                    then
                      firstInlineFragmentTypeCondition? fieldChildSelectionSet
                    else none) with
              | some currentRuntimeType =>
                  have hcurrent' :
                      (if parentType = targetParent ∧ fieldName = targetField
                        then
                          firstInlineFragmentTypeCondition?
                            fieldChildSelectionSet
                        else none) = some currentRuntimeType := by
                    simpa using hcurrent
                  exact
                    ⟨currentRuntimeType, by
                      simp [abstractRuntimeForFieldDeep?, hcurrent']⟩
              | none =>
                  have hcurrent' :
                      (if parentType = targetParent ∧ fieldName = targetField
                        then
                          firstInlineFragmentTypeCondition?
                            fieldChildSelectionSet
                        else none) = none := by
                    simpa using hcurrent
                  exact
                    ⟨tailRuntimeType, by
                      simp [abstractRuntimeForFieldDeep?, hcurrent',
                        htailRuntime]⟩
        | inlineFragment headTypeCondition headDirectives
            headChildSelectionSet =>
            rcases List.mem_cons.mp hmem with hhead | htail
            · cases hhead
              cases hrest :
                  abstractRuntimeForFieldDeep? schema targetParent
                    targetField parentType rest with
              | some restRuntimeType =>
                  exact
                    ⟨restRuntimeType, by
                      simp [abstractRuntimeForFieldDeep?, hrest]⟩
              | none =>
                  exact
                    ⟨targetRuntimeType, by
                      simp [abstractRuntimeForFieldDeep?, hrest,
                        hchildRuntime]⟩
            · rcases ih (Validation.selectionSetValid_tail hvalid)
                (selectionSetDirectiveFree_tail hfree)
                (selectionSetNormal_tail hnormal) htail with
                ⟨tailRuntimeType, htailRuntime⟩
              exact
                ⟨tailRuntimeType, by
                  cases headTypeCondition <;>
                    simp [abstractRuntimeForFieldDeep?, htailRuntime]⟩
  rcases hsome with ⟨runtimeType, hruntime⟩
  exact
    ⟨runtimeType, hruntime,
      abstractRuntimeForFieldDeep?_some_include_of_valid_normal hvalid hfree
        hnormal htargetLookup htargetComposite htargetNonObject hruntime⟩

theorem abstractRuntimeForFieldHeadDeep?_object_field_child_promote_some_of_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments targetArguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    {targetParent targetField targetRuntimeType : Name}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments fieldDefinition.outputType.namedType childSelectionSet
          = some targetRuntimeType
      -> ∃ runtimeType,
          abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments parentType selectionSet
          = some runtimeType := by
  intro hvalid hfree hnormal hmem hlookup hchildRuntime
  induction selectionSet with
  | nil =>
      simp at hmem
  | cons head rest ih =>
      cases head with
      | field headResponseName headFieldName headArguments headDirectives
          headChildSelectionSet =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
            by_cases hmatch :
                parentType = targetParent
                  ∧ fieldName = targetField
                  ∧ Argument.argumentsEquivalent arguments
                    targetArguments
            · cases hcurrent :
                  firstInlineFragmentTypeCondition? childSelectionSet with
              | some currentRuntimeType =>
                  exact
                    ⟨currentRuntimeType, by
                      simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                        hcurrent]⟩
              | none =>
                  have hlookupTarget :
                      schema.lookupField targetParent targetField =
                        some fieldDefinition := by
                    simpa [← hmatch.1, ← hmatch.2.1] using hlookup
                  cases hrest :
                      abstractRuntimeForFieldHeadDeep? schema targetParent
                        targetField targetArguments targetParent rest with
                  | some restRuntimeType =>
                      exact
                        ⟨restRuntimeType, by
                          simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                            hcurrent, hrest]⟩
                  | none =>
                      exact
                        ⟨targetRuntimeType, by
                          simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                            hcurrent, hrest, hlookupTarget,
                            hchildRuntime]⟩
            · cases hrest :
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField targetArguments parentType rest with
              | some restRuntimeType =>
                  exact
                    ⟨restRuntimeType, by
                      simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                        hrest]⟩
              | none =>
                  exact
                    ⟨targetRuntimeType, by
                      simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                        hrest, hlookup, hchildRuntime]⟩
          · rcases ih (Validation.selectionSetValid_tail hvalid)
              (selectionSetDirectiveFree_tail hfree)
              (selectionSetNormal_tail hnormal) htail with
              ⟨tailRuntimeType, htailRuntime⟩
            by_cases hmatch :
                parentType = targetParent
                  ∧ headFieldName = targetField
                  ∧ Argument.argumentsEquivalent headArguments
                    targetArguments
            · cases hcurrent :
                  firstInlineFragmentTypeCondition? headChildSelectionSet with
              | some currentRuntimeType =>
                  exact
                    ⟨currentRuntimeType, by
                      simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                        hcurrent]⟩
              | none =>
                  have htailRuntimeTarget :
                      abstractRuntimeForFieldHeadDeep? schema targetParent
                        targetField targetArguments targetParent rest =
                        some tailRuntimeType := by
                    simpa [← hmatch.1] using htailRuntime
                  exact
                    ⟨tailRuntimeType, by
                      simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                        hcurrent, htailRuntimeTarget]⟩
            · exact
                ⟨tailRuntimeType, by
                  simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                    htailRuntime]⟩
      | inlineFragment typeCondition headDirectives headChildSelectionSet =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
          · rcases ih (Validation.selectionSetValid_tail hvalid)
              (selectionSetDirectiveFree_tail hfree)
              (selectionSetNormal_tail hnormal) htail with
              ⟨tailRuntimeType, htailRuntime⟩
            exact
              ⟨tailRuntimeType, by
                cases typeCondition <;>
                  simp [abstractRuntimeForFieldHeadDeep?, htailRuntime]⟩

theorem abstractRuntimeForFieldHeadDeep?_inlineFragment_child_promote_some_of_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType typeCondition : Name} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection} {targetArguments : List Argument}
    {targetParent targetField targetRuntimeType : Name}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments typeCondition childSelectionSet
          = some targetRuntimeType
      -> ∃ runtimeType,
          abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments parentType selectionSet
          = some runtimeType := by
  intro hvalid hfree hnormal hmem hchildRuntime
  induction selectionSet with
  | nil =>
      simp at hmem
  | cons head rest ih =>
      cases head with
      | field responseName fieldName arguments fieldDirectives
          fieldChildSelectionSet =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
          · rcases ih (Validation.selectionSetValid_tail hvalid)
              (selectionSetDirectiveFree_tail hfree)
              (selectionSetNormal_tail hnormal) htail with
              ⟨tailRuntimeType, htailRuntime⟩
            by_cases hmatch :
                parentType = targetParent
                  ∧ fieldName = targetField
                  ∧ Argument.argumentsEquivalent arguments
                    targetArguments
            · cases hcurrent :
                  firstInlineFragmentTypeCondition? fieldChildSelectionSet with
              | some currentRuntimeType =>
                  exact
                    ⟨currentRuntimeType, by
                      simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                        hcurrent]⟩
              | none =>
                  have htailRuntimeTarget :
                      abstractRuntimeForFieldHeadDeep? schema targetParent
                        targetField targetArguments targetParent rest =
                        some tailRuntimeType := by
                    simpa [← hmatch.1] using htailRuntime
                  exact
                    ⟨tailRuntimeType, by
                      simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                        hcurrent, htailRuntimeTarget]⟩
            · exact
                ⟨tailRuntimeType, by
                  simp [abstractRuntimeForFieldHeadDeep?, hmatch,
                    htailRuntime]⟩
      | inlineFragment headTypeCondition headDirectives
          headChildSelectionSet =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
            cases hrest :
                abstractRuntimeForFieldHeadDeep? schema targetParent
                  targetField targetArguments parentType rest with
            | some restRuntimeType =>
                exact
                  ⟨restRuntimeType, by
                    simp [abstractRuntimeForFieldHeadDeep?, hrest]⟩
            | none =>
                exact
                  ⟨targetRuntimeType, by
                    simp [abstractRuntimeForFieldHeadDeep?, hrest,
                      hchildRuntime]⟩
          · rcases ih (Validation.selectionSetValid_tail hvalid)
              (selectionSetDirectiveFree_tail hfree)
              (selectionSetNormal_tail hnormal) htail with
              ⟨tailRuntimeType, htailRuntime⟩
            exact
              ⟨tailRuntimeType, by
                cases headTypeCondition <;>
                  simp [abstractRuntimeForFieldHeadDeep?, htailRuntime]⟩

theorem selectionSetDirectiveFree_append_left {left right : List Selection}
    : selectionSetDirectiveFree (left ++ right) -> selectionSetDirectiveFree left := by
  induction left with
  | nil =>
      intro _hfree
      exact selectionSetDirectiveFree_nil
  | cons selection rest ih =>
      intro hfree
      exact
        ⟨selectionSetDirectiveFree_head hfree,
          ih (selectionSetDirectiveFree_tail hfree)⟩

theorem selectionSetDirectiveFree_append_right {left right : List Selection}
    : selectionSetDirectiveFree (left ++ right) -> selectionSetDirectiveFree right := by
  induction left with
  | nil =>
      intro hfree
      simpa using hfree
  | cons selection rest ih =>
      intro hfree
      exact ih (selectionSetDirectiveFree_tail hfree)

theorem selectionSetGroundTyped_append_left
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : selectionSetGroundTyped schema parentType (left ++ right)
      -> selectionSetGroundTyped schema parentType left := by
  intro hground
  unfold selectionSetGroundTyped at hground ⊢
  constructor
  · cases hobject : objectTypeNameBool schema parentType
    · simp [hobject] at hground ⊢
      intro selection hselection
      exact hground.1 selection (List.mem_append_left right hselection)
    · simp [hobject] at hground ⊢
      intro selection hselection
      exact hground.1 selection (List.mem_append_left right hselection)
  · intro selection hselection
    exact hground.2 selection (List.mem_append_left right hselection)

theorem selectionSetGroundTyped_append_right
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : selectionSetGroundTyped schema parentType (left ++ right)
      -> selectionSetGroundTyped schema parentType right := by
  intro hground
  unfold selectionSetGroundTyped at hground ⊢
  constructor
  · cases hobject : objectTypeNameBool schema parentType
    · simp [hobject] at hground ⊢
      intro selection hselection
      exact hground.1 selection (List.mem_append_right left hselection)
    · simp [hobject] at hground ⊢
      intro selection hselection
      exact hground.1 selection (List.mem_append_right left hselection)
  · intro selection hselection
    exact hground.2 selection (List.mem_append_right left hselection)

theorem responseNamesNodup_append_left {left right : List Selection}
    : responseNamesNodup (left ++ right) -> responseNamesNodup left := by
  intro hnodup
  unfold responseNamesNodup at hnodup ⊢
  have hnames :
      (left.filterMap Selection.responseName? ++
        right.filterMap Selection.responseName?).Nodup := by
    simpa [List.filterMap_append] using hnodup
  exact (List.nodup_append.mp hnames).1

theorem responseNamesNodup_append_right {left right : List Selection}
    : responseNamesNodup (left ++ right) -> responseNamesNodup right := by
  intro hnodup
  unfold responseNamesNodup at hnodup ⊢
  have hnames :
      (left.filterMap Selection.responseName? ++
        right.filterMap Selection.responseName?).Nodup := by
    simpa [List.filterMap_append] using hnodup
  exact (List.nodup_append.mp hnames).2.1

theorem inlineFragmentTypeConditionsNodup_append_left {left right : List Selection}
    : inlineFragmentTypeConditionsNodup (left ++ right)
      -> inlineFragmentTypeConditionsNodup left := by
  intro hnodup
  unfold inlineFragmentTypeConditionsNodup at hnodup ⊢
  have hconditions :
      (left.filterMap inlineFragmentTypeCondition? ++
        right.filterMap inlineFragmentTypeCondition?).Nodup := by
    simpa [List.filterMap_append] using hnodup
  exact (List.nodup_append.mp hconditions).1

theorem inlineFragmentTypeConditionsNodup_append_right {left right : List Selection}
    : inlineFragmentTypeConditionsNodup (left ++ right)
      -> inlineFragmentTypeConditionsNodup right := by
  intro hnodup
  unfold inlineFragmentTypeConditionsNodup at hnodup ⊢
  have hconditions :
      (left.filterMap inlineFragmentTypeCondition? ++
        right.filterMap inlineFragmentTypeCondition?).Nodup := by
    simpa [List.filterMap_append] using hnodup
  exact (List.nodup_append.mp hconditions).2.1

theorem selectionSetNonRedundant_append_left {left right : List Selection}
    : selectionSetNonRedundant (left ++ right) -> selectionSetNonRedundant left := by
  intro hnonRedundant
  unfold selectionSetNonRedundant at hnonRedundant ⊢
  exact
    ⟨responseNamesNodup_append_left hnonRedundant.1,
      inlineFragmentTypeConditionsNodup_append_left hnonRedundant.2.1,
      by
        intro selection hselection
        exact hnonRedundant.2.2 selection
          (List.mem_append_left right hselection)⟩

theorem selectionSetNonRedundant_append_right {left right : List Selection}
    : selectionSetNonRedundant (left ++ right) -> selectionSetNonRedundant right := by
  intro hnonRedundant
  unfold selectionSetNonRedundant at hnonRedundant ⊢
  exact
    ⟨responseNamesNodup_append_right hnonRedundant.1,
      inlineFragmentTypeConditionsNodup_append_right hnonRedundant.2.1,
      by
        intro selection hselection
        exact hnonRedundant.2.2 selection
          (List.mem_append_right left hselection)⟩

theorem selectionSetNormal_append_left
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : selectionSetNormal schema parentType (left ++ right)
      -> selectionSetNormal schema parentType left := by
  intro hnormal
  exact
    ⟨selectionSetGroundTyped_append_left hnormal.1,
      selectionSetNonRedundant_append_left hnormal.2⟩

theorem selectionSetNormal_append_right
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : selectionSetNormal schema parentType (left ++ right)
      -> selectionSetNormal schema parentType right := by
  intro hnormal
  exact
    ⟨selectionSetGroundTyped_append_right hnormal.1,
      selectionSetNonRedundant_append_right hnormal.2⟩

theorem selectionSetNormal_inlineFragment_some_of_nonObject_mem
    {schema : Schema} {parentType : Name}
    {selectionSet : List Selection} {selection : Selection}
    : selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = false
      -> selection ∈ selectionSet
      -> ∃ typeCondition directives childSelectionSet,
          selection
          = Selection.inlineFragment (some typeCondition) directives
              childSelectionSet := by
  intro hnormal habstract hmem
  have hall :
      selectionsAllInlineFragments selectionSet :=
    selectionSetNormal_allInlineFragments_of_abstract hnormal habstract
  have hinline : Selection.isInlineFragment selection :=
    hall selection hmem
  cases selection with
  | field responseName fieldName arguments directives childSelectionSet =>
      simp [Selection.isInlineFragment] at hinline
  | inlineFragment typeCondition directives childSelectionSet =>
      cases typeCondition with
      | none =>
          have hselectionGround :
              selectionGroundTyped schema parentType
                (Selection.inlineFragment none directives childSelectionSet) :=
            by
              have hground := hnormal.1
              unfold selectionSetGroundTyped at hground
              exact hground.2
                (Selection.inlineFragment none directives childSelectionSet)
                hmem
          simp [selectionGroundTyped] at hselectionGround
      | some typeCondition =>
          exact ⟨typeCondition, directives, childSelectionSet, rfl⟩

theorem doesFragmentTypeApplyBool_object_condition_other_false
    {ObjectRef : Type} (schema : Schema)
    {parentType runtimeType typeCondition : Name} (ref : ObjectRef)
    : objectTypeNameBool schema typeCondition = true
      -> typeCondition ≠ runtimeType
      -> Execution.doesFragmentTypeApplyBool schema parentType
            (.object runtimeType ref) typeCondition
          = false := by
  intro hobject hne
  have hinclude :
      schema.typeIncludesObjectBool typeCondition runtimeType = false := by
    cases h :
        schema.typeIncludesObjectBool typeCondition runtimeType
    · rfl
    · have heq :
          runtimeType = typeCondition :=
        typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
          hobject h
      exact False.elim (hne heq.symm)
  simp [Execution.doesFragmentTypeApplyBool, Execution.runtimeObjectType?,
    hinclude]

theorem collectFields_other_object_inlineFragments_eq_nil_at_runtime_parent
    {ObjectRef : Type} (schema : Schema)
    (variableValues : Execution.VariableValues)
    {executionParentType runtimeType : Name} (ref : ObjectRef)
    {selectionSet : List Selection}
    : selectionSetDirectiveFree selectionSet
      -> (∀ selection,
            selection ∈ selectionSet
            -> ∃ typeCondition childSelectionSet,
                selection
                  = Selection.inlineFragment (some typeCondition) [] childSelectionSet
                ∧ objectTypeNameBool schema typeCondition = true
                ∧ typeCondition ≠ runtimeType)
      -> Execution.collectFields schema variableValues executionParentType
            (.object runtimeType ref) selectionSet
          = [] := by
  intro hfree hother
  induction selectionSet with
  | nil =>
      rfl
  | cons selection rest ih =>
      rcases hother selection (by simp) with
        ⟨typeCondition, childSelectionSet, hselection,
          htypeConditionObject, hne⟩
      subst selection
      have hskip :
          Execution.doesFragmentTypeApplyBool schema executionParentType
            (.object runtimeType ref) typeCondition = false :=
        doesFragmentTypeApplyBool_object_condition_other_false schema
          (parentType := executionParentType) (runtimeType := runtimeType)
          (typeCondition := typeCondition) ref htypeConditionObject hne
      have hheadEq :
          Execution.collectFields schema variableValues executionParentType
            (.object runtimeType ref)
            (Selection.inlineFragment (some typeCondition) []
              childSelectionSet :: rest)
          =
          Execution.collectFields schema variableValues executionParentType
            (.object runtimeType ref) rest :=
        collectFields_inlineFragment_some_directiveFree_skip_eq schema
          variableValues executionParentType typeCondition
          (.object runtimeType ref) childSelectionSet rest hskip
      rw [hheadEq]
      exact ih (selectionSetDirectiveFree_tail hfree)
        (by
          intro selection hselectionMem
          exact hother selection (List.mem_cons_of_mem
            (Selection.inlineFragment (some typeCondition) []
              childSelectionSet) hselectionMem))

theorem collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
    {ObjectRef : Type} (schema : Schema)
    (variableValues : Execution.VariableValues)
    {normalParentType executionParentType runtimeType : Name}
    (ref : ObjectRef)
    {selectionSet : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema normalParentType selectionSet
      -> runtimeType ∉ selectionSet.filterMap inlineFragmentTypeCondition?
      -> Execution.collectFields schema variableValues executionParentType
            (.object runtimeType ref) selectionSet
          = [] := by
  intro hnonObject hfree hnormal hnotMem
  induction selectionSet with
  | nil =>
      rfl
  | cons selection rest ih =>
      rcases selectionSetNormal_inlineFragment_some_of_nonObject_mem
          hnormal hnonObject (by simp : selection ∈ selection :: rest) with
        ⟨headTypeCondition, headDirectives, headChildSelectionSet,
          hselection⟩
      subst selection
      have hheadDirectives : headDirectives = [] :=
        (selectionSetDirectiveFree_head hfree).1
      subst headDirectives
      have hheadMem :
          Selection.inlineFragment (some headTypeCondition) []
            headChildSelectionSet ∈
            Selection.inlineFragment (some headTypeCondition) []
              headChildSelectionSet :: rest := by
        simp
      rcases selectionSetNormal_inlineFragment_child_of_mem hnormal
          hheadMem with
        ⟨hheadObject, _hincludes, _hheadChildNormal⟩
      have hheadObjectBool :
          objectTypeNameBool schema headTypeCondition = true :=
        objectTypeNameBool_eq_true_of_objectType_forNormality schema
          hheadObject
      have hheadNe : headTypeCondition ≠ runtimeType := by
        intro heq
        subst headTypeCondition
        exact hnotMem (by simp [inlineFragmentTypeCondition?])
      have hrestNotMem :
          runtimeType ∉ rest.filterMap inlineFragmentTypeCondition? := by
        intro hmem
        exact hnotMem (by simp [inlineFragmentTypeCondition?, hmem])
      have hskip :
          Execution.doesFragmentTypeApplyBool schema executionParentType
            (.object runtimeType ref) headTypeCondition = false :=
        doesFragmentTypeApplyBool_object_condition_other_false schema
          (parentType := executionParentType) (runtimeType := runtimeType)
          (typeCondition := headTypeCondition) ref hheadObjectBool hheadNe
      have hheadEq :
          Execution.collectFields schema variableValues executionParentType
            (.object runtimeType ref)
            (Selection.inlineFragment (some headTypeCondition) []
              headChildSelectionSet :: rest)
          =
          Execution.collectFields schema variableValues executionParentType
            (.object runtimeType ref) rest :=
        collectFields_inlineFragment_some_directiveFree_skip_eq schema
          variableValues executionParentType headTypeCondition
          (.object runtimeType ref) headChildSelectionSet rest hskip
      rw [hheadEq]
      exact ih (selectionSetDirectiveFree_tail hfree)
        (selectionSetNormal_tail hnormal) hrestNotMem

theorem executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    {normalParentType runtimeType : Name} (ref : ObjectRef)
    {pref childSelectionSet suffix : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree
          (pref
            ++ Selection.inlineFragment (some runtimeType) [] childSelectionSet :: suffix)
      -> selectionSetNormal schema normalParentType
          (pref
            ++ Selection.inlineFragment (some runtimeType) [] childSelectionSet :: suffix)
      -> Execution.executeSelectionSet schema resolvers variableValues
            fuel runtimeType (.object runtimeType ref)
            (pref
              ++ Selection.inlineFragment (some runtimeType) [] childSelectionSet
                  :: suffix)
          = Execution.executeSelectionSet schema resolvers variableValues
              fuel runtimeType (.object runtimeType ref)
              [Selection.inlineFragment (some runtimeType) [] childSelectionSet] := by
  intro hnonObject hruntimeObject hfree hnormal
  let matched :=
    Selection.inlineFragment (some runtimeType) [] childSelectionSet
  have hprefFree : selectionSetDirectiveFree pref :=
    selectionSetDirectiveFree_append_left hfree
  have htailFree :
      selectionSetDirectiveFree (matched :: suffix) :=
    selectionSetDirectiveFree_append_right (left := pref) hfree
  have hsuffixFree : selectionSetDirectiveFree suffix :=
    selectionSetDirectiveFree_tail htailFree
  have hnodup :
      inlineFragmentTypeConditionsNodup (pref ++ matched :: suffix) :=
    selectionSetNormal_inlineFragmentTypeConditionsNodup hnormal
  have hnotOther :
      runtimeType ∉ (pref ++ suffix).filterMap inlineFragmentTypeCondition? :=
    inlineFragmentTypeCondition_not_mem_remove_middle_inlineFragment
      (pref := pref) (suffix := suffix) (typeCondition := runtimeType)
      (directives := []) (childSelectionSet := childSelectionSet)
      hnodup
  have hother :
      ∀ selection, selection ∈ pref ++ suffix ->
        ∃ typeCondition childSelectionSet,
          selection =
            Selection.inlineFragment (some typeCondition) []
              childSelectionSet
            ∧ objectTypeNameBool schema typeCondition = true
            ∧ typeCondition ≠ runtimeType := by
    intro selection hselectionMem
    have hselectionOriginal :
        selection ∈ pref ++ matched :: suffix := by
      rcases List.mem_append.mp hselectionMem with hpref | hsuffix
      · exact List.mem_append_left _ hpref
      · exact List.mem_append_right _
          (List.mem_cons_of_mem matched hsuffix)
    rcases selectionSetNormal_inlineFragment_some_of_nonObject_mem
        hnormal hnonObject hselectionOriginal with
      ⟨typeCondition, directives, nestedSelectionSet, hselection⟩
    subst selection
    have hselectionMemOriginal :
        Selection.inlineFragment (some typeCondition) directives
          nestedSelectionSet ∈ pref ++ matched :: suffix :=
      hselectionOriginal
    have hdirectives : directives = [] :=
      selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
        hfree hselectionMemOriginal
    subst directives
    have hinlineMem :
        Selection.inlineFragment (some typeCondition) []
          nestedSelectionSet ∈ pref ++ matched :: suffix :=
      hselectionMemOriginal
    rcases selectionSetNormal_inlineFragment_child_of_mem hnormal
        hinlineMem with
      ⟨htypeConditionObject, _hincludes, _hchildNormal⟩
    have htypeConditionObjectBool :
        objectTypeNameBool schema typeCondition = true :=
      objectTypeNameBool_eq_true_of_objectType_forNormality schema
        htypeConditionObject
    have hne : typeCondition ≠ runtimeType := by
      intro heq
      subst typeCondition
      exact hnotOther (by
        exact List.mem_filterMap.mpr
          ⟨Selection.inlineFragment (some runtimeType) []
              nestedSelectionSet, hselectionMem, by
            simp [inlineFragmentTypeCondition?]⟩)
    exact
      ⟨typeCondition, nestedSelectionSet, rfl,
        htypeConditionObjectBool, hne⟩
  have hprefCollect :
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType ref) pref = [] :=
    collectFields_other_object_inlineFragments_eq_nil_at_runtime_parent
      schema variableValues (executionParentType := runtimeType)
      (runtimeType := runtimeType) ref hprefFree
      (by
        intro selection hselectionMem
        exact hother selection (List.mem_append_left suffix hselectionMem))
  have hsuffixCollect :
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType ref) suffix = [] :=
    collectFields_other_object_inlineFragments_eq_nil_at_runtime_parent
      schema variableValues (executionParentType := runtimeType)
      (runtimeType := runtimeType) ref hsuffixFree
      (by
        intro selection hselectionMem
        exact hother selection (List.mem_append_right pref hselectionMem))
  have happly :
      Execution.doesFragmentTypeApplyBool schema runtimeType
        (.object runtimeType ref) runtimeType = true :=
    doesFragmentTypeApplyBool_object_self schema (ref := ref) hruntimeObject
  have hfullCollect :
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType ref)
        (pref ++ Selection.inlineFragment (some runtimeType) []
          childSelectionSet :: suffix)
      =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType ref)
        [Selection.inlineFragment (some runtimeType) []
          childSelectionSet] := by
    rw [collectFields_append schema variableValues runtimeType
      (.object runtimeType ref) pref
      (Selection.inlineFragment (some runtimeType) [] childSelectionSet
        :: suffix)]
    rw [hprefCollect]
    rw [mergeExecutableGroups_nil_left_collectFields_eq schema variableValues
      runtimeType (.object runtimeType ref)
      (Selection.inlineFragment (some runtimeType) [] childSelectionSet
        :: suffix)]
    rw [collectFields_inlineFragment_some_directiveFree_apply schema
      variableValues runtimeType runtimeType (.object runtimeType ref)
      childSelectionSet suffix happly]
    rw [hsuffixCollect]
    rw [Execution.mergeExecutableGroups_nil_right]
    rw [collectFields_inlineFragment_some_directiveFree_apply schema
      variableValues runtimeType runtimeType (.object runtimeType ref)
      childSelectionSet [] happly]
    simp [Execution.collectFields, Execution.mergeExecutableGroups]
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    hfullCollect]

theorem executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_object_runtime_source
    {ObjectRef : Type} (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    {normalParentType runtimeType : Name} (ref : ObjectRef)
    {pref childSelectionSet suffix : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree
          (pref
            ++ Selection.inlineFragment (some runtimeType) [] childSelectionSet :: suffix)
      -> selectionSetNormal schema normalParentType
          (pref
            ++ Selection.inlineFragment (some runtimeType) [] childSelectionSet :: suffix)
      -> Execution.executeSelectionSet schema resolvers variableValues
            fuel normalParentType (.object runtimeType ref)
            (pref
              ++ Selection.inlineFragment (some runtimeType) [] childSelectionSet
                  :: suffix)
          = Execution.executeSelectionSet schema resolvers variableValues
              fuel normalParentType (.object runtimeType ref)
              [Selection.inlineFragment (some runtimeType) [] childSelectionSet] := by
  intro hnonObject hruntimeObject hfree hnormal
  let matched :=
    Selection.inlineFragment (some runtimeType) [] childSelectionSet
  have hprefFree : selectionSetDirectiveFree pref :=
    selectionSetDirectiveFree_append_left hfree
  have htailFree :
      selectionSetDirectiveFree (matched :: suffix) :=
    selectionSetDirectiveFree_append_right (left := pref) hfree
  have hsuffixFree : selectionSetDirectiveFree suffix :=
    selectionSetDirectiveFree_tail htailFree
  have hnodup :
      inlineFragmentTypeConditionsNodup (pref ++ matched :: suffix) :=
    selectionSetNormal_inlineFragmentTypeConditionsNodup hnormal
  have hnotOther :
      runtimeType ∉ (pref ++ suffix).filterMap inlineFragmentTypeCondition? :=
    inlineFragmentTypeCondition_not_mem_remove_middle_inlineFragment
      (pref := pref) (suffix := suffix) (typeCondition := runtimeType)
      (directives := []) (childSelectionSet := childSelectionSet)
      hnodup
  have hother :
      ∀ selection, selection ∈ pref ++ suffix ->
        ∃ typeCondition childSelectionSet,
          selection =
            Selection.inlineFragment (some typeCondition) []
              childSelectionSet
            ∧ objectTypeNameBool schema typeCondition = true
            ∧ typeCondition ≠ runtimeType := by
    intro selection hselectionMem
    have hselectionOriginal :
        selection ∈ pref ++ matched :: suffix := by
      rcases List.mem_append.mp hselectionMem with hpref | hsuffix
      · exact List.mem_append_left _ hpref
      · exact List.mem_append_right _
          (List.mem_cons_of_mem matched hsuffix)
    rcases selectionSetNormal_inlineFragment_some_of_nonObject_mem
        hnormal hnonObject hselectionOriginal with
      ⟨typeCondition, directives, nestedSelectionSet, hselection⟩
    subst selection
    have hselectionMemOriginal :
        Selection.inlineFragment (some typeCondition) directives
          nestedSelectionSet ∈ pref ++ matched :: suffix :=
      hselectionOriginal
    have hdirectives : directives = [] :=
      selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
        hfree hselectionMemOriginal
    subst directives
    have hinlineMem :
        Selection.inlineFragment (some typeCondition) []
          nestedSelectionSet ∈ pref ++ matched :: suffix :=
      hselectionMemOriginal
    rcases selectionSetNormal_inlineFragment_child_of_mem hnormal
        hinlineMem with
      ⟨htypeConditionObject, _hincludes, _hchildNormal⟩
    have htypeConditionObjectBool :
        objectTypeNameBool schema typeCondition = true :=
      objectTypeNameBool_eq_true_of_objectType_forNormality schema
        htypeConditionObject
    have hne : typeCondition ≠ runtimeType := by
      intro heq
      subst typeCondition
      exact hnotOther (by
        exact List.mem_filterMap.mpr
          ⟨Selection.inlineFragment (some runtimeType) []
              nestedSelectionSet, hselectionMem, by
            simp [inlineFragmentTypeCondition?]⟩)
    exact
      ⟨typeCondition, nestedSelectionSet, rfl,
        htypeConditionObjectBool, hne⟩
  have hprefCollect :
      Execution.collectFields schema variableValues normalParentType
        (.object runtimeType ref) pref = [] :=
    collectFields_other_object_inlineFragments_eq_nil_at_runtime_parent
      schema variableValues (executionParentType := normalParentType)
      (runtimeType := runtimeType) ref hprefFree
      (by
        intro selection hselectionMem
        exact hother selection (List.mem_append_left suffix hselectionMem))
  have hsuffixCollect :
      Execution.collectFields schema variableValues normalParentType
        (.object runtimeType ref) suffix = [] :=
    collectFields_other_object_inlineFragments_eq_nil_at_runtime_parent
      schema variableValues (executionParentType := normalParentType)
      (runtimeType := runtimeType) ref hsuffixFree
      (by
        intro selection hselectionMem
        exact hother selection (List.mem_append_right pref hselectionMem))
  have happly :
      Execution.doesFragmentTypeApplyBool schema normalParentType
        (.object runtimeType ref) runtimeType = true := by
    simp [Execution.doesFragmentTypeApplyBool,
      Execution.runtimeObjectType?,
      typeIncludesObjectBool_self_of_objectTypeNameBool schema
        hruntimeObject]
  have hfullCollect :
      Execution.collectFields schema variableValues normalParentType
        (.object runtimeType ref)
        (pref ++ Selection.inlineFragment (some runtimeType) []
          childSelectionSet :: suffix)
      =
      Execution.collectFields schema variableValues normalParentType
        (.object runtimeType ref)
        [Selection.inlineFragment (some runtimeType) []
          childSelectionSet] := by
    rw [collectFields_append schema variableValues normalParentType
      (.object runtimeType ref) pref
      (Selection.inlineFragment (some runtimeType) [] childSelectionSet
        :: suffix)]
    rw [hprefCollect]
    rw [mergeExecutableGroups_nil_left_collectFields_eq schema variableValues
      normalParentType (.object runtimeType ref)
      (Selection.inlineFragment (some runtimeType) [] childSelectionSet
        :: suffix)]
    rw [collectFields_inlineFragment_some_directiveFree_apply schema
      variableValues normalParentType runtimeType (.object runtimeType ref)
      childSelectionSet suffix happly]
    rw [hsuffixCollect]
    rw [Execution.mergeExecutableGroups_nil_right]
    rw [collectFields_inlineFragment_some_directiveFree_apply schema
      variableValues normalParentType runtimeType (.object runtimeType ref)
      childSelectionSet [] happly]
    simp [Execution.collectFields, Execution.mergeExecutableGroups]
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    hfullCollect]

theorem executeSelectionSet_deepSelectionSetSuccessWithRef_abstract_of_inlineFragment_body_deepFieldReady
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues) (fuel : Nat)
    {normalParentType runtimeType : Name} {selectionSet : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema normalParentType selectionSet
      -> (∀ typeCondition bodySelectionSet,
            Selection.inlineFragment (some typeCondition) [] bodySelectionSet
              ∈ selectionSet
            -> ∀ bodyResponseName bodyFieldName bodyArguments bodyDirectives
                  bodyChildSelectionSet,
                Selection.field bodyResponseName bodyFieldName bodyArguments
                    bodyDirectives bodyChildSelectionSet
                  ∈ bodySelectionSet
                -> ∃ bodyFieldDefinition,
                    schema.lookupField typeCondition bodyFieldName
                      = some bodyFieldDefinition
                    ∧ leafProbeFuel bodyFieldDefinition.outputType ≤ fuel
                    ∧ deepFieldSelectionSetExecutionReadyWithRef schema
                        rootSelectionSet objectRef variableValues
                        (fuel - leafProbeFuel bodyFieldDefinition.outputType)
                        typeCondition bodyResponseName bodyFieldName bodyArguments
                        bodyChildSelectionSet bodyFieldDefinition)
      -> ∃ responseFields errors,
          Execution.executeSelectionSet schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef)
            variableValues (fuel + 1) runtimeType (.object runtimeType objectRef)
            selectionSet
          = .ok (responseFields, errors) := by
  intro hnonObject hruntimeObject hfree hnormal hbodyReady
  by_cases hruntimeMem :
      runtimeType ∈ selectionSet.filterMap inlineFragmentTypeCondition?
  · rcases List.mem_filterMap.mp hruntimeMem with
      ⟨selection, hselectionMem, hselectionRuntime⟩
    cases selection with
    | field responseName fieldName arguments directives childSelectionSet =>
        simp [inlineFragmentTypeCondition?] at hselectionRuntime
    | inlineFragment maybeTypeCondition directives bodySelectionSet =>
        cases maybeTypeCondition with
        | none =>
            simp [inlineFragmentTypeCondition?] at hselectionRuntime
        | some typeCondition =>
            simp [inlineFragmentTypeCondition?] at hselectionRuntime
            subst typeCondition
            have hdirectives : directives = [] :=
              selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
                hfree hselectionMem
            subst directives
            rcases List.mem_iff_append.mp hselectionMem with
              ⟨pref, suffix, hselectionSet⟩
            subst selectionSet
            have hinlineMem :
                Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet ∈
                  pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix := by
              exact List.mem_append_right _ (by simp)
            have hbodyFree : selectionSetDirectiveFree bodySelectionSet :=
              selectionSetDirectiveFree_inlineFragment_child_of_mem hfree
                hinlineMem
            have hbodyNormal :
                selectionSetNormal schema runtimeType bodySelectionSet :=
              (selectionSetNormal_inlineFragment_child_of_mem hnormal
                hinlineMem).2
            have hsource :
                ∃ runtimeType' ref',
                  (Execution.ResolverValue.object runtimeType objectRef :
                    Execution.ResolverValue ObjectRef)
                    =
                      Execution.ResolverValue.object runtimeType' ref'
                    ∧ schema.typeIncludesObjectBool runtimeType
                      runtimeType' = true := by
              exact
                ⟨runtimeType, objectRef, rfl,
                  typeIncludesObjectBool_self_of_objectTypeNameBool schema
                    hruntimeObject⟩
            rcases
                executeSelectionSet_deepSelectionSetSuccessWithRef_deepFieldReady
                  schema rootSelectionSet objectRef variableValues fuel
                  runtimeType (.object runtimeType objectRef)
                  bodySelectionSet hbodyFree hbodyNormal hruntimeObject
                  hsource
                  (by
                    intro bodyResponseName bodyFieldName bodyArguments
                      bodyDirectives bodyChildSelectionSet hfieldMem
                    exact
                      hbodyReady runtimeType bodySelectionSet hinlineMem
                        bodyResponseName bodyFieldName bodyArguments
                        bodyDirectives bodyChildSelectionSet hfieldMem) with
              ⟨bodyFields, bodyErrors, hbodyExecute, _hbodyNames⟩
            have hmiddle :
                Execution.executeSelectionSet schema
                  (deepSelectionSetSuccessResolversWithRef schema
                    rootSelectionSet objectRef)
                  variableValues (fuel + 1) runtimeType
                  (.object runtimeType objectRef)
                  (pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix)
                =
                Execution.executeSelectionSet schema
                  (deepSelectionSetSuccessResolversWithRef schema
                    rootSelectionSet objectRef)
                  variableValues (fuel + 1) runtimeType
                  (.object runtimeType objectRef)
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet] :=
              executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
                schema
                (deepSelectionSetSuccessResolversWithRef schema
                  rootSelectionSet objectRef)
                variableValues (fuel + 1) objectRef hnonObject
                hruntimeObject hfree hnormal
            have happly :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                  (.object runtimeType objectRef) runtimeType = true :=
              doesFragmentTypeApplyBool_object_self schema
                (ref := objectRef) hruntimeObject
            have hflatten :
                Execution.executeSelectionSet schema
                  (deepSelectionSetSuccessResolversWithRef schema
                    rootSelectionSet objectRef)
                  variableValues (fuel + 1) runtimeType
                  (.object runtimeType objectRef)
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet]
                =
                Execution.executeSelectionSet schema
                  (deepSelectionSetSuccessResolversWithRef schema
                    rootSelectionSet objectRef)
                  variableValues (fuel + 1) runtimeType
                  (.object runtimeType objectRef) bodySelectionSet := by
              simpa using
                executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
                  schema
                  (deepSelectionSetSuccessResolversWithRef schema
                    rootSelectionSet objectRef)
                  variableValues (fuel + 1) runtimeType runtimeType
                  (.object runtimeType objectRef) bodySelectionSet [] happly
            refine ⟨bodyFields, bodyErrors, ?_⟩
            calc
              Execution.executeSelectionSet schema
                  (deepSelectionSetSuccessResolversWithRef schema
                    rootSelectionSet objectRef)
                  variableValues (fuel + 1) runtimeType
                  (.object runtimeType objectRef)
                  (pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix)
                  =
                Execution.executeSelectionSet schema
                  (deepSelectionSetSuccessResolversWithRef schema
                    rootSelectionSet objectRef)
                  variableValues (fuel + 1) runtimeType
                  (.object runtimeType objectRef)
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet] := hmiddle
              _ =
                Execution.executeSelectionSet schema
                  (deepSelectionSetSuccessResolversWithRef schema
                    rootSelectionSet objectRef)
                  variableValues (fuel + 1) runtimeType
                  (.object runtimeType objectRef) bodySelectionSet := hflatten
              _ = .ok (bodyFields, bodyErrors) := hbodyExecute
  · have hcollect :
        Execution.collectFields schema variableValues runtimeType
          (.object runtimeType objectRef) selectionSet = [] :=
      collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
        schema variableValues (normalParentType := normalParentType)
        (executionParentType := runtimeType) (runtimeType := runtimeType)
        objectRef hnonObject hfree hnormal hruntimeMem
    refine ⟨[], 0, ?_⟩
    simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      hcollect, Execution.executeCollectedFields]

theorem deepFieldSelectionSetReadyWithRef_of_valid_normal_object_promoted_fuel_ge_size
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ n parentType variableDefinitions (selectionSet : List Selection) fuel,
          SelectionSet.size selectionSet < n
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> Validation.selectionSetValid schema variableDefinitions parentType
              selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> (∀ targetParent targetField targetRuntimeType targetFieldDefinition,
                schema.lookupField targetParent targetField = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema targetParent targetField
                      parentType selectionSet
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema targetParent targetField
                        targetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> ∀ responseName fieldName arguments directives childSelectionSet,
              Selection.field responseName fieldName arguments directives
                  childSelectionSet
                ∈ selectionSet
              -> ∃ fieldDefinition,
                  schema.lookupField parentType fieldName = some fieldDefinition
                  ∧ leafProbeFuel fieldDefinition.outputType ≤ fuel
                  ∧ deepFieldSelectionSetExecutionReadyWithRef schema
                      rootSelectionSet objectRef variableValues
                      (fuel - leafProbeFuel fieldDefinition.outputType)
                      parentType responseName fieldName arguments childSelectionSet
                      fieldDefinition := by
  intro hschema n
  induction n with
  | zero =>
      intro parentType variableDefinitions selectionSet fuel hsize _hfuel
        _hvalid _hfree _hnormal _hobject _hpromote responseName fieldName
        arguments directives childSelectionSet _hmem
      omega
  | succ n ih =>
      intro parentType variableDefinitions selectionSet fuel hsize hfuel
        hvalid hfree hnormal hobject hpromote responseName fieldName
        arguments directives childSelectionSet hmem
      rcases selectionSetValid_field_lookup_of_mem hvalid hmem with
        ⟨fieldDefinition, hlookup, _harguments, _hfieldSelectionValid⟩
      have hleafFuel :
          leafProbeFuel fieldDefinition.outputType ≤ fuel := by
        have hlocal :=
          leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
            parentType (selectionSet := selectionSet)
            (responseName := responseName) (fieldName := fieldName)
            (arguments := arguments) (directives := directives)
            (childSelectionSet := childSelectionSet)
            (fieldDefinition := fieldDefinition) hmem hlookup
        omega
      have hfieldDeepFuel :
          leafProbeFuel fieldDefinition.outputType
            + selectionSetDeepProbeFuel schema
              fieldDefinition.outputType.namedType childSelectionSet
            + 1 ≤ fuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_field_mem schema parentType
            selectionSet responseName fieldName arguments directives
            childSelectionSet fieldDefinition hmem hlookup
        omega
      refine ⟨fieldDefinition, hlookup, hleafFuel, ?_⟩
      by_cases hreturnObject :
          objectTypeNameBool schema fieldDefinition.outputType.namedType =
            true
      · have hchildValid :
            Validation.selectionSetValid schema variableDefinitions
              fieldDefinition.outputType.namedType childSelectionSet :=
          selectionSetValid_object_field_child_of_mem_lookup hvalid hmem
            hlookup hreturnObject
        have hchildFree : selectionSetDirectiveFree childSelectionSet :=
          selectionSetDirectiveFree_field_child_of_mem hfree hmem
        have hchildNormal :
            selectionSetNormal schema fieldDefinition.outputType.namedType
              childSelectionSet :=
          selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
        let childFuel := fuel - leafProbeFuel fieldDefinition.outputType - 1
        have hchildSize :
            SelectionSet.size childSelectionSet < n := by
          have hlt :=
            selectionSet_size_field_child_lt_of_mem
              (responseName := responseName) (fieldName := fieldName)
              (arguments := arguments) (directives := directives)
              (childSelectionSet := childSelectionSet)
              (selectionSet := selectionSet) hmem
          omega
        have hchildFuel :
            selectionSetDeepProbeFuel schema
                fieldDefinition.outputType.namedType childSelectionSet
              ≤ childFuel := by
          dsimp [childFuel]
          omega
        have hchildPromote :
            ∀ targetParent targetField targetRuntimeType targetFieldDefinition,
              schema.lookupField targetParent targetField =
                some targetFieldDefinition ->
              (TypeRef.named
                  targetFieldDefinition.outputType.namedType).isCompositeBool
                schema = true ->
              objectTypeNameBool schema
                  targetFieldDefinition.outputType.namedType = false ->
              abstractRuntimeForFieldDeep? schema targetParent targetField
                fieldDefinition.outputType.namedType childSelectionSet =
                  some targetRuntimeType ->
                ∃ runtimeType,
                  abstractRuntimeForFieldDeep? schema targetParent targetField
                    targetParent rootSelectionSet = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                      targetFieldDefinition.outputType.namedType runtimeType =
                      true := by
          intro targetParent targetField targetRuntimeType targetFieldDefinition
            htargetLookup htargetComposite htargetNonObject hlocalRuntime
          rcases
              abstractRuntimeForFieldDeep?_object_field_child_promote_some_of_valid_normal
                hvalid hfree hnormal hmem hlookup htargetLookup
                htargetComposite htargetNonObject hlocalRuntime with
            ⟨parentRuntimeType, hparentRuntime, _hparentInclude⟩
          exact
            hpromote targetParent targetField parentRuntimeType
              targetFieldDefinition htargetLookup htargetComposite
              htargetNonObject hparentRuntime
        have hchildReady :
            ∀ childResponseName childFieldName childArguments childDirectives
                grandChildSelectionSet,
              Selection.field childResponseName childFieldName childArguments
                childDirectives grandChildSelectionSet ∈ childSelectionSet ->
              ∃ childFieldDefinition,
                schema.lookupField fieldDefinition.outputType.namedType
                    childFieldName = some childFieldDefinition
                  ∧ leafProbeFuel childFieldDefinition.outputType ≤ childFuel
                  ∧ deepFieldSelectionSetExecutionReadyWithRef schema
                    rootSelectionSet objectRef variableValues
                    (childFuel -
                      leafProbeFuel childFieldDefinition.outputType)
                    fieldDefinition.outputType.namedType childResponseName
                    childFieldName childArguments grandChildSelectionSet
                    childFieldDefinition := by
          intro childResponseName childFieldName childArguments
            childDirectives grandChildSelectionSet hchildMem
          exact
            ih fieldDefinition.outputType.namedType variableDefinitions
              childSelectionSet childFuel hchildSize hchildFuel hchildValid
              hchildFree hchildNormal hreturnObject hchildPromote
              childResponseName childFieldName childArguments childDirectives
              grandChildSelectionSet hchildMem
        have hfieldReady :=
          deepFieldSelectionSetExecutionReadyWithRef_object_of_child_deepFieldReady
            schema rootSelectionSet objectRef variableValues childFuel
            parentType responseName fieldName arguments childSelectionSet
            fieldDefinition hreturnObject hchildFree hchildNormal hchildReady
        have hchildFuelEq :
            childFuel + 1 =
              fuel - leafProbeFuel fieldDefinition.outputType := by
          dsimp [childFuel]
          omega
        simpa [hchildFuelEq] using hfieldReady
      · have hreturnNonObject :
            objectTypeNameBool schema fieldDefinition.outputType.namedType =
              false := by
          cases h :
              objectTypeNameBool schema
                fieldDefinition.outputType.namedType <;>
            simp [h] at hreturnObject ⊢
        by_cases hreturnLeaf :
            (TypeRef.named
                fieldDefinition.outputType.namedType).isCompositeBool
              schema = false
        · exact
            deepFieldSelectionSetExecutionReadyWithRef_leaf schema
              rootSelectionSet objectRef variableValues
              (fuel - leafProbeFuel fieldDefinition.outputType) parentType
              responseName fieldName arguments childSelectionSet
              fieldDefinition hreturnLeaf
        · have hreturnComposite :
              (TypeRef.named
                  fieldDefinition.outputType.namedType).isCompositeBool
                schema = true := by
            cases h :
                (TypeRef.named
                    fieldDefinition.outputType.namedType).isCompositeBool
                  schema <;>
              simp [h] at hreturnLeaf ⊢
          rcases
              abstractRuntimeForFieldDeep?_some_of_valid_normal_abstract_mem_lookup
                hvalid hnormal hmem hlookup hreturnComposite
                hreturnNonObject with
            ⟨localRuntimeType, hlocalRuntime, _hlocalInclude⟩
          rcases
              hpromote parentType fieldName localRuntimeType fieldDefinition
                hlookup hreturnComposite hreturnNonObject hlocalRuntime with
            ⟨runtimeType, hruntime, hinclude⟩
          have hruntimeObject :
              objectTypeNameBool schema runtimeType = true :=
            objectTypeNameBool_of_typeIncludesObjectBool hschema hinclude
          have hchildNonempty : childSelectionSet ≠ [] := by
            rcases
                selectionSetValid_field_lookup_leaf_or_composite_child
                  hvalid hmem with
              ⟨candidateDefinition, hcandidateLookup, hkind⟩
            have hdefinitionEq : candidateDefinition = fieldDefinition := by
              rw [hlookup] at hcandidateLookup
              exact (Option.some.inj hcandidateLookup).symm
            subst candidateDefinition
            rcases hkind with hleaf | hcomposite
            · have hleafComposite := hleaf.1
              rw [hreturnComposite] at hleafComposite
              simp at hleafComposite
            · exact hcomposite.2.1
          have hchildValid :
              Validation.selectionSetValid schema variableDefinitions
                fieldDefinition.outputType.namedType childSelectionSet :=
            selectionSetValid_field_child_of_mem_lookup hvalid hmem
              hchildNonempty hlookup
          have hchildFree : selectionSetDirectiveFree childSelectionSet :=
            selectionSetDirectiveFree_field_child_of_mem hfree hmem
          have hchildNormal :
              selectionSetNormal schema fieldDefinition.outputType.namedType
                childSelectionSet :=
            selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
          let childFuel := fuel - leafProbeFuel fieldDefinition.outputType - 1
          have hchildFuelEq :
              childFuel + 1 =
                fuel - leafProbeFuel fieldDefinition.outputType := by
            dsimp [childFuel]
            omega
          have hbodyReady :
              ∀ typeCondition bodySelectionSet,
                Selection.inlineFragment (some typeCondition) []
                    bodySelectionSet ∈ childSelectionSet ->
                ∀ bodyResponseName bodyFieldName bodyArguments bodyDirectives
                    bodyChildSelectionSet,
                  Selection.field bodyResponseName bodyFieldName
                      bodyArguments bodyDirectives bodyChildSelectionSet ∈
                    bodySelectionSet ->
                  ∃ bodyFieldDefinition,
                    schema.lookupField typeCondition bodyFieldName =
                        some bodyFieldDefinition
                      ∧ leafProbeFuel bodyFieldDefinition.outputType
                        ≤ childFuel
                      ∧ deepFieldSelectionSetExecutionReadyWithRef schema
                        rootSelectionSet objectRef variableValues
                        (childFuel -
                          leafProbeFuel bodyFieldDefinition.outputType)
                        typeCondition bodyResponseName bodyFieldName
                        bodyArguments bodyChildSelectionSet
                        bodyFieldDefinition := by
            intro typeCondition bodySelectionSet hinlineMem
              bodyResponseName bodyFieldName bodyArguments bodyDirectives
              bodyChildSelectionSet hfieldMem
            have hbodyValid :
                Validation.selectionSetValid schema variableDefinitions
                  typeCondition bodySelectionSet :=
              selectionSetValid_inlineFragment_some_child_of_mem hchildValid
                hinlineMem
            have hbodyFree : selectionSetDirectiveFree bodySelectionSet :=
              selectionSetDirectiveFree_inlineFragment_child_of_mem
                hchildFree hinlineMem
            rcases selectionSetNormal_inlineFragment_child_of_mem
                hchildNormal hinlineMem with
              ⟨htypeObject, hbodyNormal⟩
            have hbodyObject :
                objectTypeNameBool schema typeCondition = true :=
              objectTypeNameBool_eq_true_of_objectType_forNormality schema
                htypeObject
            have hbodySize :
                SelectionSet.size bodySelectionSet < n := by
              have hchildLt :=
                selectionSet_size_field_child_lt_of_mem
                  (responseName := responseName) (fieldName := fieldName)
                  (arguments := arguments) (directives := directives)
                  (childSelectionSet := childSelectionSet)
                  (selectionSet := selectionSet) hmem
              have hbodyLt :=
                selectionSet_size_inlineFragment_child_lt_of_mem
                  (typeCondition := some typeCondition)
                  (directives := ([] : List DirectiveApplication))
                  (childSelectionSet := bodySelectionSet)
                  (selectionSet := childSelectionSet) hinlineMem
              omega
            have hbodyFuel :
                selectionSetDeepProbeFuel schema typeCondition
                    bodySelectionSet
                  ≤ childFuel := by
              have hinlineFuel :=
                selectionSetDeepProbeFuel_inlineFragment_some_mem schema
                  fieldDefinition.outputType.namedType childSelectionSet
                  typeCondition ([] : List DirectiveApplication)
                  bodySelectionSet hinlineMem
              dsimp [childFuel]
              omega
            have hbodyPromote :
                ∀ targetParent targetField targetRuntimeType
                    targetFieldDefinition,
                  schema.lookupField targetParent targetField =
                    some targetFieldDefinition ->
                  (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                    schema = true ->
                  objectTypeNameBool schema
                      targetFieldDefinition.outputType.namedType = false ->
                  abstractRuntimeForFieldDeep? schema targetParent
                    targetField typeCondition bodySelectionSet =
                      some targetRuntimeType ->
                    ∃ runtimeType,
                      abstractRuntimeForFieldDeep? schema targetParent
                        targetField targetParent rootSelectionSet =
                        some runtimeType
                        ∧ schema.typeIncludesObjectBool
                          targetFieldDefinition.outputType.namedType
                          runtimeType = true := by
              intro targetParent targetField targetRuntimeType
                targetFieldDefinition htargetLookup htargetComposite
                htargetNonObject hbodyLocalRuntime
              rcases
                  abstractRuntimeForFieldDeep?_inlineFragment_child_promote_some_of_valid_normal
                    hchildValid hchildFree hchildNormal hinlineMem
                    htargetLookup htargetComposite htargetNonObject
                    hbodyLocalRuntime with
                ⟨childRuntimeType, hchildRuntime, _hchildInclude⟩
              rcases
                  abstractRuntimeForFieldDeep?_object_field_child_promote_some_of_valid_normal
                    hvalid hfree hnormal hmem hlookup htargetLookup
                    htargetComposite htargetNonObject hchildRuntime with
                ⟨parentRuntimeType, hparentRuntime, _hparentInclude⟩
              exact
                hpromote targetParent targetField parentRuntimeType
                  targetFieldDefinition htargetLookup htargetComposite
                  htargetNonObject hparentRuntime
            exact
              ih typeCondition variableDefinitions bodySelectionSet
                childFuel hbodySize hbodyFuel hbodyValid hbodyFree
                hbodyNormal hbodyObject hbodyPromote bodyResponseName
                bodyFieldName bodyArguments bodyDirectives
                bodyChildSelectionSet hfieldMem
          rcases
              executeSelectionSet_deepSelectionSetSuccessWithRef_abstract_of_inlineFragment_body_deepFieldReady
                schema rootSelectionSet objectRef variableValues childFuel
                (normalParentType :=
                  fieldDefinition.outputType.namedType)
                (runtimeType := runtimeType) hreturnNonObject
                hruntimeObject hchildFree hchildNormal hbodyReady with
            ⟨responseFields, errors, hexecute⟩
          have hfieldReady :=
            deepFieldSelectionSetExecutionReadyWithRef_abstract_of_execute
              schema rootSelectionSet objectRef variableValues
              (childFuel + 1) parentType responseName fieldName runtimeType
              arguments childSelectionSet fieldDefinition responseFields
              errors hreturnComposite hreturnNonObject hruntime hinclude
              hexecute
          simpa [hchildFuelEq] using hfieldReady

theorem deepFieldSelectionSetReadyWithRef_of_valid_normal_object_promoted_deepProbeFuel
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection),
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> (∀ targetParent targetField targetRuntimeType targetFieldDefinition,
                schema.lookupField targetParent targetField = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema targetParent targetField
                      parentType selectionSet
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema targetParent targetField
                        targetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> ∀ responseName fieldName arguments directives childSelectionSet,
              Selection.field responseName fieldName arguments directives
                  childSelectionSet
                ∈ selectionSet
              -> ∃ fieldDefinition,
                  schema.lookupField parentType fieldName = some fieldDefinition
                  ∧ leafProbeFuel fieldDefinition.outputType
                    ≤ selectionSetDeepProbeFuel schema parentType selectionSet
                  ∧ deepFieldSelectionSetExecutionReadyWithRef schema
                      rootSelectionSet objectRef variableValues
                      (selectionSetDeepProbeFuel schema parentType selectionSet
                        - leafProbeFuel fieldDefinition.outputType)
                      parentType responseName fieldName arguments childSelectionSet
                      fieldDefinition := by
  intro hschema parentType variableDefinitions selectionSet hvalid hfree
    hnormal hobject hpromote responseName fieldName arguments directives
    childSelectionSet hmem
  exact
    deepFieldSelectionSetReadyWithRef_of_valid_normal_object_promoted_fuel_ge_size
      schema rootSelectionSet objectRef variableValues hschema
      (SelectionSet.size selectionSet + 1) parentType variableDefinitions
      selectionSet (selectionSetDeepProbeFuel schema parentType selectionSet)
      (by omega) (by omega) hvalid hfree hnormal hobject hpromote
      responseName fieldName arguments directives childSelectionSet hmem

theorem executeSelectionSetAsResponse_deepSelectionSetSuccessWithRef_valid_normal_object_promoted_fuel_ge
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            fuel (source : Execution.ResolverValue ObjectRef),
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> (∃ runtimeType ref,
                source = Execution.ResolverValue.object runtimeType ref
                ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
          -> (∀ targetParent targetField targetRuntimeType targetFieldDefinition,
                schema.lookupField targetParent targetField = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema targetParent targetField
                      parentType selectionSet
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema targetParent targetField
                        targetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> ∃ responseFields errors,
              Execution.executeSelectionSetAsResponse schema
                (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                  objectRef)
                variableValues (fuel + 1) parentType source selectionSet
              = ({
                    data := Execution.ResponseValue.object responseFields,
                    errors := errors
                  }
                  : Execution.Response) := by
  intro hschema parentType variableDefinitions selectionSet fuel source
    hvalid hfree hnormal hobject hsource hpromote hfuel
  have hready :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
          childSelectionSet ∈ selectionSet ->
          ∃ fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
              ∧ leafProbeFuel fieldDefinition.outputType ≤ fuel
              ∧ deepFieldSelectionSetExecutionReadyWithRef schema
                rootSelectionSet objectRef variableValues
                (fuel - leafProbeFuel fieldDefinition.outputType)
                parentType responseName fieldName arguments childSelectionSet
                fieldDefinition := by
    intro responseName fieldName arguments directives childSelectionSet hmem
    exact
      deepFieldSelectionSetReadyWithRef_of_valid_normal_object_promoted_fuel_ge_size
        schema rootSelectionSet objectRef variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType variableDefinitions
        selectionSet fuel (by omega) hfuel hvalid hfree hnormal hobject
        hpromote responseName fieldName arguments directives childSelectionSet
        hmem
  rcases
      executeSelectionSet_deepSelectionSetSuccessWithRef_deepFieldReady
        schema rootSelectionSet objectRef variableValues fuel parentType
        source selectionSet hfree hnormal hobject hsource hready with
    ⟨responseFields, errors, hexecute, _hkeys⟩
  exact
    ⟨responseFields, errors, by
      simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
        hexecute]⟩

end GroundTypeNormalization

end NormalForm

end GraphQL
