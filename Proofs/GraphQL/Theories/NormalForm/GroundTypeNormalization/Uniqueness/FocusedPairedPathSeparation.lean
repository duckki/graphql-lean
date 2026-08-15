import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedPairedPath
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedSelectedPathSeparation

/-!
Semantic separation along heterogeneous paired paths.

The fixed-spine invariant below keeps runtime selection separate from execution
support.  A paired path first chooses concrete runtimes and field spines; the
invariant then works for every path-local support containing the current pair
of selection sets.  This ordering is important for abstract return types,
where the selected runtime determines the child support.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

def NormalSelectionSetPairedPathDataDiffAt
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    (leftFuel rightFuel : Nat)
    (leftParentType rightParentType leftRuntimeType rightRuntimeType
      targetParent leftProbeField rightProbeField
      : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (leftSpine rightSpine : List NormalSelectionSetObservableFieldStep)
    (left right : List Selection)
    : Prop :=
  ∀ leftCurrentSelectionSet rightCurrentSelectionSet,
    PathLocalSupportValidNormal schema leftRuntimeType leftCurrentSelectionSet
    -> PathLocalSupportValidNormal schema rightRuntimeType rightCurrentSelectionSet
    -> SelectedPathSelectionSetContextReady schema leftParentType
        leftRuntimeType leftCurrentSelectionSet left
    -> SelectedPathSelectionSetContextReady schema rightParentType
        rightRuntimeType rightCurrentSelectionSet right
    -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
        rightInitialSpine variableValues leftFuel rightFuel leftParentType
        rightParentType leftRuntimeType rightRuntimeType targetParent
        leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime
        leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
        left right

def NormalSelectionSetPairedPathDataDiff
    (schema : Schema)
    (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (leftFuel rightFuel : Nat)
    (leftParentType rightParentType targetParent leftProbeField rightProbeField : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (left right : List Selection)
    : Prop :=
  ∃ leftRuntimeType rightRuntimeType leftSpine rightSpine,
    SelectedFieldSpineRuntimeValid schema leftParentType leftRuntimeType leftSpine
    ∧ SelectedFieldSpineRuntimeValid schema rightParentType rightRuntimeType rightSpine
    ∧ ∀ leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine leftRuntime rightRuntime,
        NormalSelectionSetPairedPathDataDiffAt schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftProbeField rightProbeField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime leftSpine rightSpine
          left right

theorem selectedPathCompositeFieldChildSource_eq_of_selected_next
    {schema : Schema} {parentType fieldName : Name}
    {arguments : List Argument} {currentSelectionSet : List Selection}
    {spine selectedSpine childSpine : List NormalSelectionSetObservableFieldStep}
    {fieldDefinition : FieldDefinition}
    {selectedRuntime childRuntime : Name}
    : selectedObservableFieldSpineNext? fieldName arguments spine
        = some (some selectedRuntime, selectedSpine)
      -> (objectTypeNameBool schema fieldDefinition.outputType.namedType = true
          -> selectedRuntime = fieldDefinition.outputType.namedType)
      -> SelectedPathCompositeFieldChildSource schema parentType fieldName
          arguments currentSelectionSet spine fieldDefinition childRuntime
          childSpine
      -> childRuntime = selectedRuntime ∧ childSpine = selectedSpine := by
  intro hselected hselectedObjectOutput hsource
  rcases hsource with hsource | hsource
  · rcases hsource with ⟨hnext, _hruntimeCase⟩
    rw [hselected] at hnext
    have hpair :
        (some selectedRuntime, selectedSpine) =
          (some childRuntime, childSpine) :=
      Option.some.inj hnext
    have hruntime : some selectedRuntime = some childRuntime :=
      congrArg Prod.fst hpair
    have hspine : selectedSpine = childSpine :=
      congrArg Prod.snd hpair
    exact ⟨(Option.some.inj hruntime).symm, hspine.symm⟩
  rcases hsource with hobjectOutput | habstractFallback
  · rcases hobjectOutput with
      ⟨hobjectOutput, hchildRuntime, hchildSpine⟩
    have hselectedRuntime := hselectedObjectOutput hobjectOutput
    subst childRuntime
    subst selectedRuntime
    have htail :
        selectedObservableFieldSpineTailForRuntime
            fieldDefinition.outputType.namedType fieldName arguments spine =
          selectedSpine := by
      simp [selectedObservableFieldSpineTailForRuntime, hselected]
    exact ⟨rfl, hchildSpine.trans htail⟩
  · rcases habstractFallback with
      ⟨_hcomposite, _hnonObject, hnone, _hruntime, _hchildSpine⟩
    rw [hselected] at hnone
    simp at hnone

theorem selectedPathCompositeFieldChildSource_cons
    {schema : Schema} {parentType responseName fieldName : Name}
    {arguments : List Argument} {currentSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition} {childRuntime : Name}
    {childSpine : List NormalSelectionSetObservableFieldStep}
    : (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema = true
      -> SelectedFieldSpineRuntimeValid schema
          fieldDefinition.outputType.namedType childRuntime childSpine
      -> SelectedPathCompositeFieldChildSource schema parentType fieldName
          arguments currentSelectionSet
          ({
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              childRuntime := some childRuntime
            }
            :: childSpine)
          fieldDefinition childRuntime childSpine := by
  intro hcomposite hchildSpineValid
  refine Or.inl
    ⟨selectedObservableFieldSpineNext?_cons_self _ _, ?_⟩
  by_cases hobjectOutput :
      objectTypeNameBool schema fieldDefinition.outputType.namedType = true
  · exact Or.inl
      ⟨hobjectOutput,
        typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
          hobjectOutput
          (selectedFieldSpineRuntimeValid_typeIncludes
            hchildSpineValid)⟩
  · have hnonObject :
        objectTypeNameBool schema fieldDefinition.outputType.namedType =
          false := by
      cases h : objectTypeNameBool schema
          fieldDefinition.outputType.namedType <;>
        simp [h] at hobjectOutput ⊢
    exact Or.inr ⟨hcomposite, hnonObject⟩

theorem selectionSet_nonempty_of_valid_field_mem_lookup_compositeBool
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> childSelectionSet ≠ [] := by
  intro hvalid hmem hlookup hcomposite
  rcases selectionSetValid_field_lookup_leaf_or_composite_child hvalid hmem
      with
    ⟨candidateDefinition, hcandidateLookup, hkind⟩
  have hcandidateEq : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidateDefinition
  rcases hkind with hleaf | hcompositeKind
  · rw [hcomposite] at hleaf
    simp at hleaf
  · exact hcompositeKind.2.1

theorem normalSelectionSetPairedPathDataDiffAt_of_left_abstract
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftRuntimeType rightRuntimeType
      : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    {left right leftChildSelectionSet : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    : objectTypeNameBool schema leftParentType = false
      -> selectionSetDirectiveFree left
      -> selectionSetNormal schema leftParentType left
      -> Selection.inlineFragment (some typeCondition) directives leftChildSelectionSet
          ∈ left
      -> schema.typeIncludesObjectBool leftParentType typeCondition = true
      -> SelectedFieldSpineRuntimeValid schema typeCondition leftRuntimeType leftSpine
      -> NormalSelectionSetPairedPathDataDiffAt schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel typeCondition
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftProbeField rightProbeField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime leftSpine rightSpine
          leftChildSelectionSet right
      -> NormalSelectionSetPairedPathDataDiffAt schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftProbeField rightProbeField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime leftSpine rightSpine
          left right := by
  intro hleftNonObject hleftFree hleftNormal hleftMem hparentInclude
    hleftSpineValid hchildDiff
  rcases selectionSetNormal_inlineFragment_child_of_mem hleftNormal
      hleftMem with
    ⟨htypeObject, _hchildNormal⟩
  have htypeObjectBool :
      objectTypeNameBool schema typeCondition = true :=
    objectTypeNameBool_eq_true_of_objectType_forNormality schema
      htypeObject
  have hleftRuntimeEq : leftRuntimeType = typeCondition :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
      htypeObjectBool
      (selectedFieldSpineRuntimeValid_typeIncludes hleftSpineValid)
  subst leftRuntimeType
  have hdirectives : directives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hleftFree hleftMem
  subst directives
  intro leftCurrentSelectionSet rightCurrentSelectionSet hleftSupport
    hrightSupport hleftContext hrightContext
  have hleftChildContext :
      SelectedPathSelectionSetContextReady schema typeCondition
        typeCondition leftCurrentSelectionSet leftChildSelectionSet :=
    selectedPathSelectionSetContextReady_of_object_context
      htypeObjectBool
      (hleftContext.2 hleftNonObject hleftMem)
  exact
    selectedPathSelectionSetsResponseDataDiff_of_left_abstract_inlineFragment_body
      hleftNonObject htypeObjectBool hparentInclude hleftFree hleftNormal
      hleftMem
      (hchildDiff leftCurrentSelectionSet rightCurrentSelectionSet
        hleftSupport hrightSupport hleftChildContext hrightContext)

theorem normalSelectionSetPairedPathDataDiffAt_of_right_abstract
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftRuntimeType rightRuntimeType
      : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    {left right rightChildSelectionSet : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    : objectTypeNameBool schema rightParentType = false
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema rightParentType right
      -> Selection.inlineFragment (some typeCondition) directives rightChildSelectionSet
          ∈ right
      -> schema.typeIncludesObjectBool rightParentType typeCondition = true
      -> SelectedFieldSpineRuntimeValid schema typeCondition rightRuntimeType rightSpine
      -> NormalSelectionSetPairedPathDataDiffAt schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          typeCondition leftRuntimeType rightRuntimeType targetParent
          leftProbeField rightProbeField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime leftSpine rightSpine left
          rightChildSelectionSet
      -> NormalSelectionSetPairedPathDataDiffAt schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftProbeField rightProbeField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime leftSpine rightSpine
          left right := by
  intro hrightNonObject hrightFree hrightNormal hrightMem hparentInclude
    hrightSpineValid hchildDiff
  rcases selectionSetNormal_inlineFragment_child_of_mem hrightNormal
      hrightMem with
    ⟨htypeObject, _hchildNormal⟩
  have htypeObjectBool :
      objectTypeNameBool schema typeCondition = true :=
    objectTypeNameBool_eq_true_of_objectType_forNormality schema
      htypeObject
  have hrightRuntimeEq : rightRuntimeType = typeCondition :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
      htypeObjectBool
      (selectedFieldSpineRuntimeValid_typeIncludes hrightSpineValid)
  subst rightRuntimeType
  have hdirectives : directives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hrightFree hrightMem
  subst directives
  intro leftCurrentSelectionSet rightCurrentSelectionSet hleftSupport
    hrightSupport hleftContext hrightContext
  have hrightChildContext :
      SelectedPathSelectionSetContextReady schema typeCondition
        typeCondition rightCurrentSelectionSet rightChildSelectionSet :=
    selectedPathSelectionSetContextReady_of_object_context
      htypeObjectBool
      (hrightContext.2 hrightNonObject hrightMem)
  exact
    selectedPathSelectionSetsResponseDataDiff_of_right_abstract_inlineFragment_body
      hrightNonObject htypeObjectBool hparentInclude hrightFree
      hrightNormal hrightMem
      (hchildDiff leftCurrentSelectionSet rightCurrentSelectionSet
        hleftSupport hrightSupport hleftContext hrightChildContext)

theorem normalSelectionSetPairedPathDataDiffAt_of_object_composite_pair
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine leftChildSpine rightChildSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftChildRuntime rightChildRuntime
      : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> Validation.selectionSetValid schema leftVariableDefinitions
          leftFieldDefinition.outputType.namedType leftChildSelectionSet
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightFieldDefinition.outputType.namedType rightChildSelectionSet
      -> selectionSetDirectiveFree leftChildSelectionSet
      -> selectionSetDirectiveFree rightChildSelectionSet
      -> selectionSetNormal schema leftFieldDefinition.outputType.namedType
          leftChildSelectionSet
      -> selectionSetNormal schema rightFieldDefinition.outputType.namedType
          rightChildSelectionSet
      -> SelectedFieldSpineRuntimeValid schema
          leftFieldDefinition.outputType.namedType leftChildRuntime
          leftChildSpine
      -> SelectedFieldSpineRuntimeValid schema
          rightFieldDefinition.outputType.namedType rightChildRuntime
          rightChildSpine
      -> NormalSelectionSetPairedPathDataDiffAt schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues
          (leftFuel - leafProbeFuel leftFieldDefinition.outputType - 1)
          (rightFuel - leafProbeFuel rightFieldDefinition.outputType - 1)
          leftFieldDefinition.outputType.namedType
          rightFieldDefinition.outputType.namedType leftChildRuntime
          rightChildRuntime targetParent leftProbeField rightProbeField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftChildSpine rightChildSpine leftChildSelectionSet
          rightChildSelectionSet
      -> NormalSelectionSetPairedPathDataDiffAt schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftParentType rightParentType targetParent
          leftProbeField rightProbeField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime
          ({
              responseName := responseName,
              fieldName := leftFieldName,
              arguments := leftArguments,
              childRuntime := some leftChildRuntime
            }
            :: leftChildSpine)
          ({
              responseName := responseName,
              fieldName := rightFieldName,
              arguments := rightArguments,
              childRuntime := some rightChildRuntime
            }
            :: rightChildSpine)
          left right := by
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftMem
    hrightMem hleftLookup hrightLookup hleftComposite hrightComposite
    hleftChildValid hrightChildValid hleftChildFree hrightChildFree
    hleftChildNormal hrightChildNormal hleftChildSpineValid
    hrightChildSpineValid hchildDiff leftCurrentSelectionSet
    rightCurrentSelectionSet hleftSupport hrightSupport hleftContext
    hrightContext
  let leftStep : NormalSelectionSetObservableFieldStep :=
    { responseName := responseName, fieldName := leftFieldName,
      arguments := leftArguments, childRuntime := some leftChildRuntime }
  let rightStep : NormalSelectionSetObservableFieldStep :=
    { responseName := responseName, fieldName := rightFieldName,
      arguments := rightArguments, childRuntime := some rightChildRuntime }
  let leftSpine := leftStep :: leftChildSpine
  let rightSpine := rightStep :: rightChildSpine
  have hleftChildObject :=
    selectedFieldSpineRuntimeValid_runtime_object hleftChildSpineValid
  have hrightChildObject :=
    selectedFieldSpineRuntimeValid_runtime_object hrightChildSpineValid
  have hleftChildInclude :=
    selectedFieldSpineRuntimeValid_typeIncludes hleftChildSpineValid
  have hrightChildInclude :=
    selectedFieldSpineRuntimeValid_typeIncludes hrightChildSpineValid
  have hleftSpineValid :
      SelectedFieldSpineRuntimeValid schema leftParentType leftParentType
        leftSpine :=
    SelectedFieldSpineRuntimeValid.objectChild hleftObject hleftLookup
      hleftComposite hleftChildSpineValid
  have hrightSpineValid :
      SelectedFieldSpineRuntimeValid schema rightParentType rightParentType
        rightSpine :=
    SelectedFieldSpineRuntimeValid.objectChild hrightObject hrightLookup
      hrightComposite hrightChildSpineValid
  have hleftNext :
      selectedObservableFieldSpineNext? leftFieldName leftArguments
          leftSpine =
        some (some leftChildRuntime, leftChildSpine) := by
    dsimp [leftSpine, leftStep]
    exact selectedObservableFieldSpineNext?_cons_self _ _
  have hrightNext :
      selectedObservableFieldSpineNext? rightFieldName rightArguments
          rightSpine =
        some (some rightChildRuntime, rightChildSpine) := by
    dsimp [rightSpine, rightStep]
    exact selectedObservableFieldSpineNext?_cons_self _ _
  have hleftSelectedObjectOutput :
      objectTypeNameBool schema
          leftFieldDefinition.outputType.namedType = true ->
        leftChildRuntime = leftFieldDefinition.outputType.namedType := by
    intro hobjectOutput
    exact
      typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
        hobjectOutput hleftChildInclude
  have hrightSelectedObjectOutput :
      objectTypeNameBool schema
          rightFieldDefinition.outputType.namedType = true ->
        rightChildRuntime = rightFieldDefinition.outputType.namedType := by
    intro hobjectOutput
    exact
      typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
        hobjectOutput hrightChildInclude
  have hleftChildSource :
      SelectedPathCompositeFieldChildSource schema leftParentType
        leftFieldName leftArguments leftCurrentSelectionSet leftSpine
        leftFieldDefinition leftChildRuntime leftChildSpine := by
    refine Or.inl ⟨hleftNext, ?_⟩
    by_cases hobjectOutput :
        objectTypeNameBool schema
          leftFieldDefinition.outputType.namedType = true
    · exact Or.inl ⟨hobjectOutput,
        hleftSelectedObjectOutput hobjectOutput⟩
    · have hnonObject :
          objectTypeNameBool schema
              leftFieldDefinition.outputType.namedType = false := by
        cases h : objectTypeNameBool schema
            leftFieldDefinition.outputType.namedType <;>
          simp [h] at hobjectOutput ⊢
      exact Or.inr ⟨hleftComposite, hnonObject⟩
  have hrightChildSource :
      SelectedPathCompositeFieldChildSource schema rightParentType
        rightFieldName rightArguments rightCurrentSelectionSet rightSpine
        rightFieldDefinition rightChildRuntime rightChildSpine := by
    refine Or.inl ⟨hrightNext, ?_⟩
    by_cases hobjectOutput :
        objectTypeNameBool schema
          rightFieldDefinition.outputType.namedType = true
    · exact Or.inl ⟨hobjectOutput,
        hrightSelectedObjectOutput hobjectOutput⟩
    · have hnonObject :
          objectTypeNameBool schema
              rightFieldDefinition.outputType.namedType = false := by
        cases h : objectTypeNameBool schema
            rightFieldDefinition.outputType.namedType <;>
          simp [h] at hobjectOutput ⊢
      exact Or.inr ⟨hrightComposite, hnonObject⟩
  have hleftChildSupport :
      PathLocalSupportValidNormal schema leftChildRuntime
        (fieldPairPathLocalNextSelectionSet schema leftParentType
          leftChildRuntime leftFieldName leftArguments
          leftCurrentSelectionSet) :=
    pathLocalSupportValidNormal_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
      hleftSupport hleftObject hleftChildObject hleftLookup
      hleftChildSource hleftChildInclude
  have hrightChildSupport :
      PathLocalSupportValidNormal schema rightChildRuntime
        (fieldPairPathLocalNextSelectionSet schema rightParentType
          rightChildRuntime rightFieldName rightArguments
          rightCurrentSelectionSet) :=
    pathLocalSupportValidNormal_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
      hrightSupport hrightObject hrightChildObject hrightLookup
      hrightChildSource hrightChildInclude
  have hleftChildContext :
      SelectedPathSelectionSetContextReady schema
        leftFieldDefinition.outputType.namedType leftChildRuntime
        (fieldPairPathLocalNextSelectionSet schema leftParentType
          leftChildRuntime leftFieldName leftArguments
          leftCurrentSelectionSet)
        leftChildSelectionSet :=
    selectedPathSelectionSetContextReady_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
      (hleftContext.1 hleftObject) hleftMem hleftLookup
      hleftChildNormal hleftChildSource hleftChildObject
  have hrightChildContext :
      SelectedPathSelectionSetContextReady schema
        rightFieldDefinition.outputType.namedType rightChildRuntime
        (fieldPairPathLocalNextSelectionSet schema rightParentType
          rightChildRuntime rightFieldName rightArguments
          rightCurrentSelectionSet)
        rightChildSelectionSet :=
    selectedPathSelectionSetContextReady_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
      (hrightContext.1 hrightObject) hrightMem hrightLookup
      hrightChildNormal hrightChildSource hrightChildObject
  have hleftChildFuelEq :
      (leftFuel - leafProbeFuel leftFieldDefinition.outputType - 1) + 1 =
        leftFuel - leafProbeFuel leftFieldDefinition.outputType := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema leftParentType left
        responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet leftFieldDefinition hleftMem hleftLookup
    omega
  have hrightChildFuelEq :
      (rightFuel - leafProbeFuel rightFieldDefinition.outputType - 1) + 1 =
        rightFuel - leafProbeFuel rightFieldDefinition.outputType := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema rightParentType right
        responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet rightFieldDefinition hrightMem hrightLookup
    omega
  have hchildDataDiff :=
    hchildDiff
      (fieldPairPathLocalNextSelectionSet schema leftParentType
        leftChildRuntime leftFieldName leftArguments
        leftCurrentSelectionSet)
      (fieldPairPathLocalNextSelectionSet schema rightParentType
        rightChildRuntime rightFieldName rightArguments
        rightCurrentSelectionSet)
      hleftChildSupport hrightChildSupport hleftChildContext
      hrightChildContext
  rcases hchildDataDiff with
    ⟨_hleftInclude, _hrightInclude, _hleftSpineValid,
      _hrightSpineValid, hchildDataNot⟩
  have hleftReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet
        leftCurrentSelectionSet leftInitialSpine rightInitialSpine
        leftSpine variableValues leftFuel targetParent leftProbeField
        rightProbeField leftParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        left :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues hschema leftParentType leftVariableDefinitions left
      leftFuel leftParentType targetParent leftProbeField rightProbeField
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      FieldPairProbeTag.left leftCurrentSelectionSet leftSpine hleftFuel
      hleftValid hleftCoercion hleftFree hleftNormal hleftObject hleftSpineValid
      hleftSupport (hleftContext.1 hleftObject)
  have hrightReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet
        rightCurrentSelectionSet leftInitialSpine rightInitialSpine
        rightSpine variableValues rightFuel targetParent leftProbeField
        rightProbeField rightParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        right :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues hschema rightParentType rightVariableDefinitions right
      rightFuel rightParentType targetParent leftProbeField rightProbeField
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      FieldPairProbeTag.right rightCurrentSelectionSet rightSpine hrightFuel
      hrightValid hrightCoercion hrightFree hrightNormal hrightObject hrightSpineValid
      hrightSupport (hrightContext.1 hrightObject)
  refine
    selectedPathSelectionSetsResponseDataDiff_of_dataNot
      (typeIncludesObjectBool_self_of_objectTypeNameBool schema hleftObject)
      (typeIncludesObjectBool_self_of_objectTypeNameBool schema hrightObject)
      hleftSpineValid hrightSpineValid ?_
  apply
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_child_field_pair_of_field_children_fuels
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet leftInitialSpine rightInitialSpine
      leftSpine rightSpine variableValues leftFuel rightFuel targetParent
      leftProbeField rightProbeField leftParentType rightParentType
      leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem hrightMem
      hleftLookup hrightLookup hleftComposite hrightComposite
  · intro candidateLeftRuntime candidateLeftSpine candidateRightRuntime
      candidateRightSpine hcandidateLeftSource hcandidateRightSource
      _hcandidateLeftInclude _hcandidateRightInclude
    rcases
        selectedPathCompositeFieldChildSource_eq_of_selected_next
          hleftNext hleftSelectedObjectOutput hcandidateLeftSource with
      ⟨hcandidateLeftRuntime, hcandidateLeftSpine⟩
    rcases
        selectedPathCompositeFieldChildSource_eq_of_selected_next
          hrightNext hrightSelectedObjectOutput hcandidateRightSource with
      ⟨hcandidateRightRuntime, hcandidateRightSpine⟩
    subst candidateLeftRuntime
    subst candidateLeftSpine
    subst candidateRightRuntime
    subst candidateRightSpine
    simpa only [hleftChildFuelEq, hrightChildFuelEq] using hchildDataNot
  · exact hleftReady
  · exact hrightReady

theorem normalSelectionSetPairedPathDataDiffAt_of_object_left_responseName
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftRuntimeType rightRuntimeType
      : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType leftRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType rightRuntimeType rightSpine
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> NormalSelectionSetPairedPathDataDiffAt schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftProbeField rightProbeField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime leftSpine rightSpine
          left right := by
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftMem hrightMissing
    leftCurrentSelectionSet rightCurrentSelectionSet hleftSupport
    hrightSupport hleftContext hrightContext
  have hleftRuntimeEq : leftRuntimeType = leftParentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hleftObject
      (selectedFieldSpineRuntimeValid_typeIncludes hleftSpineValid)
  have hrightRuntimeEq : rightRuntimeType = rightParentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hrightObject
      (selectedFieldSpineRuntimeValid_typeIncludes hrightSpineValid)
  subst leftRuntimeType
  subst rightRuntimeType
  exact
    selectedPathSelectionSetsResponseDataDiff_of_dataNot
      (selectedFieldSpineRuntimeValid_typeIncludes hleftSpineValid)
      (selectedFieldSpineRuntimeValid_typeIncludes hrightSpineValid)
      hleftSpineValid hrightSpineValid
      (responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_responseName_absent_fuels
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet leftInitialSpine rightInitialSpine
        leftSpine rightSpine variableValues leftFuel rightFuel targetParent
        leftProbeField rightProbeField leftParentType rightParentType
        leftParentType rightParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime hschema hleftValid
        hrightValid hleftCoercion hrightCoercion hleftFree hrightFree
        hleftNormal hrightNormal
        hleftObject hrightObject hleftFuel hrightFuel hleftSpineValid
        hrightSpineValid hleftSupport hrightSupport
        (hleftContext.1 hleftObject) (hrightContext.1 hrightObject)
        hleftMem hrightMissing)

theorem normalSelectionSetPairedPathDataDiffAt_of_object_leaf_pair
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftRuntimeType rightRuntimeType
      : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType leftRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType rightRuntimeType rightSpine
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> NormalSelectionSetPairedPathDataDiffAt schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftProbeField rightProbeField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime leftSpine rightSpine
          left right := by
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftMem hrightMem hleftLookup
    hrightLookup hleftLeaf hrightLeaf leftCurrentSelectionSet
    rightCurrentSelectionSet hleftSupport hrightSupport hleftContext
    hrightContext
  have hleftRuntimeEq : leftRuntimeType = leftParentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hleftObject
      (selectedFieldSpineRuntimeValid_typeIncludes hleftSpineValid)
  have hrightRuntimeEq : rightRuntimeType = rightParentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hrightObject
      (selectedFieldSpineRuntimeValid_typeIncludes hrightSpineValid)
  subst leftRuntimeType
  subst rightRuntimeType
  exact
    selectedPathSelectionSetsResponseDataDiff_of_dataNot
      (selectedFieldSpineRuntimeValid_typeIncludes hleftSpineValid)
      (selectedFieldSpineRuntimeValid_typeIncludes hrightSpineValid)
      hleftSpineValid hrightSpineValid
      (responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_leaf_field_pair_of_valid_normal_runtimeSpine_fuels
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet leftInitialSpine rightInitialSpine
        leftSpine rightSpine variableValues leftFuel rightFuel targetParent
        leftProbeField rightProbeField leftParentType rightParentType
        leftParentType rightParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime hschema hleftValid
        hrightValid hleftCoercion hrightCoercion hleftFree hrightFree
        hleftNormal hrightNormal
        hleftObject hrightObject hleftFuel hrightFuel hleftSpineValid
        hrightSpineValid hleftSupport hrightSupport
        (hleftContext.1 hleftObject) (hrightContext.1 hrightObject)
        hleftMem hrightMem hleftLookup hrightLookup hleftLeaf hrightLeaf)

theorem normalSelectionSetPairedPathDataDiffAt_of_object_composite_left_leaf
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftRuntimeType rightRuntimeType
      : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType leftRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType rightRuntimeType rightSpine
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> NormalSelectionSetPairedPathDataDiffAt schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftProbeField rightProbeField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime leftSpine rightSpine
          left right := by
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftMem hrightMem hleftLookup
    hrightLookup hleftComposite hrightLeaf leftCurrentSelectionSet
    rightCurrentSelectionSet hleftSupport hrightSupport hleftContext
    hrightContext
  have hleftRuntimeEq : leftRuntimeType = leftParentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hleftObject
      (selectedFieldSpineRuntimeValid_typeIncludes hleftSpineValid)
  have hrightRuntimeEq : rightRuntimeType = rightParentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hrightObject
      (selectedFieldSpineRuntimeValid_typeIncludes hrightSpineValid)
  subst leftRuntimeType
  subst rightRuntimeType
  exact
    selectedPathSelectionSetsResponseDataDiff_of_dataNot
      (selectedFieldSpineRuntimeValid_typeIncludes hleftSpineValid)
      (selectedFieldSpineRuntimeValid_typeIncludes hrightSpineValid)
      hleftSpineValid hrightSpineValid
      (responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_composite_right_leaf_field_pair_of_valid_normal_runtimeSpine_fuels
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet leftInitialSpine rightInitialSpine
        leftSpine rightSpine variableValues leftFuel rightFuel targetParent
        leftProbeField rightProbeField leftParentType rightParentType
        leftParentType rightParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime hschema hleftValid
        hrightValid hleftCoercion hrightCoercion hleftFree hrightFree
        hleftNormal hrightNormal
        hleftObject hrightObject hleftFuel hrightFuel hleftSpineValid
        hrightSpineValid hleftSupport hrightSupport
        (hleftContext.1 hleftObject) (hrightContext.1 hrightObject)
        hleftMem hrightMem hleftLookup hrightLookup hleftComposite
        hrightLeaf)

theorem normalSelectionSetPairedPathDataDiffAt_of_object_leaf_composite_right
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftRuntimeType rightRuntimeType
      : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType leftRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType rightRuntimeType rightSpine
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> NormalSelectionSetPairedPathDataDiffAt schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftProbeField rightProbeField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime leftSpine rightSpine
          left right := by
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftMem hrightMem hleftLookup
    hrightLookup hleftLeaf hrightComposite leftCurrentSelectionSet
    rightCurrentSelectionSet hleftSupport hrightSupport hleftContext
    hrightContext
  have hleftRuntimeEq : leftRuntimeType = leftParentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hleftObject
      (selectedFieldSpineRuntimeValid_typeIncludes hleftSpineValid)
  have hrightRuntimeEq : rightRuntimeType = rightParentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hrightObject
      (selectedFieldSpineRuntimeValid_typeIncludes hrightSpineValid)
  subst leftRuntimeType
  subst rightRuntimeType
  exact
    selectedPathSelectionSetsResponseDataDiff_of_dataNot
      (selectedFieldSpineRuntimeValid_typeIncludes hleftSpineValid)
      (selectedFieldSpineRuntimeValid_typeIncludes hrightSpineValid)
      hleftSpineValid hrightSpineValid
      (responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_composite_field_pair_of_valid_normal_runtimeSpine_fuels
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet leftInitialSpine rightInitialSpine
        leftSpine rightSpine variableValues leftFuel rightFuel targetParent
        leftProbeField rightProbeField leftParentType rightParentType
        leftParentType rightParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime hschema hleftValid
        hrightValid hleftCoercion hrightCoercion hleftFree hrightFree
        hleftNormal hrightNormal
        hleftObject hrightObject hleftFuel hrightFuel hleftSpineValid
        hrightSpineValid hleftSupport hrightSupport
        (hleftContext.1 hleftObject) (hrightContext.1 hrightObject)
        hleftMem hrightMem hleftLookup hrightLookup hleftLeaf
        hrightComposite)

theorem normalSelectionSetPairedPathDataDiff_of_valid_normal
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    {leftParentType rightParentType : Name}
    {left right : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
          leftParentType left
      -> selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> left ≠ []
      -> right ≠ []
      -> NormalSelectionSetPairedPath schema leftParentType rightParentType left right
      -> NormalSelectionSetPairedPathDataDiff schema rootSelectionSet
          variableValues leftFuel rightFuel leftParentType rightParentType
          targetParent leftProbeField rightProbeField
          targetLeftArguments targetRightArguments left right := by
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftFuel hrightFuel hleftNonempty hrightNonempty hpath
  induction hpath generalizing leftVariableDefinitions
      rightVariableDefinitions leftFuel rightFuel with
  | @objectLeftResponseName pathLeftParentType pathRightParentType
      responseName fieldName arguments directives childSelectionSet pathLeft
      pathRight hleftObject hrightObject hleftMem hrightMissing =>
      rcases
          selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
            hleftValid hleftNormal hleftObject hleftNonempty with
        ⟨leftSpine, hleftSpineValid, _hleftObservable⟩
      rcases
          selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
            hrightValid hrightNormal hrightObject hrightNonempty with
        ⟨rightSpine, hrightSpineValid, _hrightObservable⟩
      refine ⟨
        pathLeftParentType,
        pathRightParentType,
        leftSpine,
        rightSpine,
        hleftSpineValid,
        hrightSpineValid,
        ?_
      ⟩
      intro leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine leftRuntime rightRuntime
      exact
        normalSelectionSetPairedPathDataDiffAt_of_object_left_responseName
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          leftSpine rightSpine variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField pathLeftParentType
          pathRightParentType pathLeftParentType pathRightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          hschema hleftValid hrightValid
          (hleftCoercion pathLeftParentType
            (typeIncludesObjectBool_self_of_objectTypeNameBool schema
              hleftObject))
          (hrightCoercion pathRightParentType
            (typeIncludesObjectBool_self_of_objectTypeNameBool schema
              hrightObject))
          hleftFree hrightFree hleftNormal
          hrightNormal hleftObject hrightObject hleftFuel hrightFuel
          hleftSpineValid hrightSpineValid hleftMem hrightMissing
  | @objectLeafPair pathLeftParentType pathRightParentType responseName
      leftFieldName rightFieldName leftArguments rightArguments
      leftDirectives rightDirectives leftChildSelectionSet
      rightChildSelectionSet pathLeft pathRight leftFieldDefinition
      rightFieldDefinition hleftObject hrightObject hleftMem hrightMem
      hleftLookup hrightLookup hleftLeaf hrightLeaf =>
      rcases
          selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
            hleftValid hleftNormal hleftObject hleftNonempty with
        ⟨leftSpine, hleftSpineValid, _hleftObservable⟩
      rcases
          selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
            hrightValid hrightNormal hrightObject hrightNonempty with
        ⟨rightSpine, hrightSpineValid, _hrightObservable⟩
      refine ⟨
        pathLeftParentType,
        pathRightParentType,
        leftSpine,
        rightSpine,
        hleftSpineValid,
        hrightSpineValid,
        ?_
      ⟩
      intro leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine leftRuntime rightRuntime
      exact
        normalSelectionSetPairedPathDataDiffAt_of_object_leaf_pair
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          leftSpine rightSpine variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField pathLeftParentType
          pathRightParentType pathLeftParentType pathRightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          hschema hleftValid hrightValid
          (hleftCoercion pathLeftParentType
            (typeIncludesObjectBool_self_of_objectTypeNameBool schema
              hleftObject))
          (hrightCoercion pathRightParentType
            (typeIncludesObjectBool_self_of_objectTypeNameBool schema
              hrightObject))
          hleftFree hrightFree hleftNormal
          hrightNormal hleftObject hrightObject hleftFuel hrightFuel
          hleftSpineValid hrightSpineValid hleftMem hrightMem hleftLookup
          hrightLookup hleftLeaf hrightLeaf
  | @objectCompositeLeftLeaf pathLeftParentType pathRightParentType
      responseName leftFieldName rightFieldName leftArguments rightArguments
      leftDirectives rightDirectives leftChildSelectionSet
      rightChildSelectionSet pathLeft pathRight leftFieldDefinition
      rightFieldDefinition hleftObject hrightObject hleftMem hrightMem
      hleftLookup hrightLookup hleftComposite hrightLeaf =>
      rcases
          selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
            hleftValid hleftNormal hleftObject hleftNonempty with
        ⟨leftSpine, hleftSpineValid, _hleftObservable⟩
      rcases
          selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
            hrightValid hrightNormal hrightObject hrightNonempty with
        ⟨rightSpine, hrightSpineValid, _hrightObservable⟩
      refine ⟨
        pathLeftParentType,
        pathRightParentType,
        leftSpine,
        rightSpine,
        hleftSpineValid,
        hrightSpineValid,
        ?_
      ⟩
      intro leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine leftRuntime rightRuntime
      exact
        normalSelectionSetPairedPathDataDiffAt_of_object_composite_left_leaf
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          leftSpine rightSpine variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField pathLeftParentType
          pathRightParentType pathLeftParentType pathRightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          hschema hleftValid hrightValid
          (hleftCoercion pathLeftParentType
            (typeIncludesObjectBool_self_of_objectTypeNameBool schema
              hleftObject))
          (hrightCoercion pathRightParentType
            (typeIncludesObjectBool_self_of_objectTypeNameBool schema
              hrightObject))
          hleftFree hrightFree hleftNormal
          hrightNormal hleftObject hrightObject hleftFuel hrightFuel
          hleftSpineValid hrightSpineValid hleftMem hrightMem hleftLookup
          hrightLookup hleftComposite hrightLeaf
  | @objectLeafCompositeRight pathLeftParentType pathRightParentType
      responseName leftFieldName rightFieldName leftArguments rightArguments
      leftDirectives rightDirectives leftChildSelectionSet
      rightChildSelectionSet pathLeft pathRight leftFieldDefinition
      rightFieldDefinition hleftObject hrightObject hleftMem hrightMem
      hleftLookup hrightLookup hleftLeaf hrightComposite =>
      rcases
          selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
            hleftValid hleftNormal hleftObject hleftNonempty with
        ⟨leftSpine, hleftSpineValid, _hleftObservable⟩
      rcases
          selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
            hrightValid hrightNormal hrightObject hrightNonempty with
        ⟨rightSpine, hrightSpineValid, _hrightObservable⟩
      refine ⟨
        pathLeftParentType,
        pathRightParentType,
        leftSpine,
        rightSpine,
        hleftSpineValid,
        hrightSpineValid,
        ?_
      ⟩
      intro leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine leftRuntime rightRuntime
      exact
        normalSelectionSetPairedPathDataDiffAt_of_object_leaf_composite_right
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          leftSpine rightSpine variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField pathLeftParentType
          pathRightParentType pathLeftParentType pathRightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          hschema hleftValid hrightValid
          (hleftCoercion pathLeftParentType
            (typeIncludesObjectBool_self_of_objectTypeNameBool schema
              hleftObject))
          (hrightCoercion pathRightParentType
            (typeIncludesObjectBool_self_of_objectTypeNameBool schema
              hrightObject))
          hleftFree hrightFree hleftNormal
          hrightNormal hleftObject hrightObject hleftFuel hrightFuel
          hleftSpineValid hrightSpineValid hleftMem hrightMem hleftLookup
          hrightLookup hleftLeaf hrightComposite
  | @objectCompositePair pathLeftParentType pathRightParentType responseName
      leftFieldName rightFieldName leftArguments rightArguments
      leftDirectives rightDirectives leftChildSelectionSet
      rightChildSelectionSet pathLeft pathRight leftFieldDefinition
      rightFieldDefinition hleftObject hrightObject hleftMem hrightMem
      hleftLookup hrightLookup hleftComposite hrightComposite _hchildPath ih =>
      let leftChildFuel :=
        leftFuel - leafProbeFuel leftFieldDefinition.outputType - 1
      let rightChildFuel :=
        rightFuel - leafProbeFuel rightFieldDefinition.outputType - 1
      have hleftChildNonempty : leftChildSelectionSet ≠ [] :=
        selectionSet_nonempty_of_valid_field_mem_lookup_compositeBool
          hleftValid hleftMem hleftLookup hleftComposite
      have hrightChildNonempty : rightChildSelectionSet ≠ [] :=
        selectionSet_nonempty_of_valid_field_mem_lookup_compositeBool
          hrightValid hrightMem hrightLookup hrightComposite
      have hleftChildValid :=
        selectionSetValid_field_child_of_mem_lookup hleftValid hleftMem
          hleftChildNonempty hleftLookup
      have hrightChildValid :=
        selectionSetValid_field_child_of_mem_lookup hrightValid hrightMem
          hrightChildNonempty hrightLookup
      have hleftChildFree :=
        selectionSetDirectiveFree_field_child_of_mem hleftFree hleftMem
      have hrightChildFree :=
        selectionSetDirectiveFree_field_child_of_mem hrightFree hrightMem
      have hleftChildNormal :=
        selectionSetNormal_field_child_of_mem_lookup hleftNormal hleftMem
          hleftLookup
      have hrightChildNormal :=
        selectionSetNormal_field_child_of_mem_lookup hrightNormal hrightMem
          hrightLookup
      have hleftChildFuel :
          selectionSetDeepProbeFuel schema
              leftFieldDefinition.outputType.namedType
              leftChildSelectionSet ≤ leftChildFuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_field_mem schema pathLeftParentType
            pathLeft responseName leftFieldName leftArguments
            leftDirectives leftChildSelectionSet leftFieldDefinition
            hleftMem hleftLookup
        dsimp [leftChildFuel]
        omega
      have hrightChildFuel :
          selectionSetDeepProbeFuel schema
              rightFieldDefinition.outputType.namedType
              rightChildSelectionSet ≤ rightChildFuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_field_mem schema pathRightParentType
            pathRight responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet rightFieldDefinition
            hrightMem hrightLookup
        dsimp [rightChildFuel]
        omega
      rcases
          ih (leftVariableDefinitions := leftVariableDefinitions)
            (rightVariableDefinitions := rightVariableDefinitions)
            (leftFuel := leftChildFuel) (rightFuel := rightChildFuel)
            hleftChildValid hrightChildValid
            (selectionSetArgumentsCoercible_field_children_of_directiveFree
              (hleftCoercion pathLeftParentType
                (typeIncludesObjectBool_self_of_objectTypeNameBool schema
                  hleftObject))
              hleftFree hleftMem hleftLookup)
            (selectionSetArgumentsCoercible_field_children_of_directiveFree
              (hrightCoercion pathRightParentType
                (typeIncludesObjectBool_self_of_objectTypeNameBool schema
                  hrightObject))
              hrightFree hrightMem hrightLookup)
            hleftChildFree
            hrightChildFree hleftChildNormal hrightChildNormal
            hleftChildFuel hrightChildFuel hleftChildNonempty
            hrightChildNonempty with
        ⟨leftChildRuntime, rightChildRuntime, leftChildSpine,
          rightChildSpine, hleftChildSpineValid,
          hrightChildSpineValid, hchildDataDiff⟩
      let leftSpine : List NormalSelectionSetObservableFieldStep :=
        { responseName := responseName, fieldName := leftFieldName,
          arguments := leftArguments,
          childRuntime := some leftChildRuntime } :: leftChildSpine
      let rightSpine : List NormalSelectionSetObservableFieldStep :=
        { responseName := responseName, fieldName := rightFieldName,
          arguments := rightArguments,
          childRuntime := some rightChildRuntime } :: rightChildSpine
      have hleftSpineValid :
          SelectedFieldSpineRuntimeValid schema pathLeftParentType
            pathLeftParentType leftSpine :=
        SelectedFieldSpineRuntimeValid.objectChild hleftObject hleftLookup
          hleftComposite hleftChildSpineValid
      have hrightSpineValid :
          SelectedFieldSpineRuntimeValid schema pathRightParentType
            pathRightParentType rightSpine :=
        SelectedFieldSpineRuntimeValid.objectChild hrightObject
          hrightLookup hrightComposite hrightChildSpineValid
      refine ⟨
        pathLeftParentType,
        pathRightParentType,
        leftSpine,
        rightSpine,
        hleftSpineValid,
        hrightSpineValid,
        ?_
      ⟩
      intro leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine leftRuntime rightRuntime
      simpa [leftSpine, rightSpine, leftChildFuel, rightChildFuel] using
        normalSelectionSetPairedPathDataDiffAt_of_object_composite_pair
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          leftChildSpine rightChildSpine variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField pathLeftParentType
          pathRightParentType leftChildRuntime rightChildRuntime
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          hschema hleftValid hrightValid
          (hleftCoercion pathLeftParentType
            (typeIncludesObjectBool_self_of_objectTypeNameBool schema
              hleftObject))
          (hrightCoercion pathRightParentType
            (typeIncludesObjectBool_self_of_objectTypeNameBool schema
              hrightObject))
          hleftFree hrightFree hleftNormal
          hrightNormal hleftObject hrightObject hleftFuel hrightFuel
          hleftMem hrightMem hleftLookup hrightLookup hleftComposite
          hrightComposite hleftChildValid hrightChildValid hleftChildFree
          hrightChildFree hleftChildNormal hrightChildNormal
          hleftChildSpineValid hrightChildSpineValid
          (hchildDataDiff leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            leftRuntime rightRuntime)
  | @leftAbstract pathLeftParentType pathRightParentType typeCondition
      directives leftChildSelectionSet pathLeft pathRight hleftNonObject
      hleftMem _hchildPath ih =>
      have hleftChildValid :=
        selectionSetValid_inlineFragment_some_child_of_mem hleftValid
          hleftMem
      have hleftChildFree :=
        selectionSetDirectiveFree_inlineFragment_child_of_mem hleftFree
          hleftMem
      rcases
          selectionSetNormal_inlineFragment_child_of_mem hleftNormal
            hleftMem with
        ⟨htypeObject, hleftChildNormal⟩
      have hoverlap : schema.typesOverlap pathLeftParentType typeCondition :=
        selectionSetValid_inlineFragment_some_typesOverlap_of_mem hleftValid
          hleftMem
      have hinclude :
          schema.typeIncludesObjectBool pathLeftParentType typeCondition =
            true :=
        typeIncludesObjectBool_of_typesOverlap_object schema hoverlap
          htypeObject
      have hleftChildNonempty : leftChildSelectionSet ≠ [] :=
        selectionSetValid_inlineFragment_some_child_nonempty_of_mem hleftValid
          hleftMem
      have htypeObjectBool :
          objectTypeNameBool schema typeCondition = true :=
        objectTypeNameBool_eq_true_of_objectType_forNormality schema
          htypeObject
      have hleftChildFuel :
          selectionSetDeepProbeFuel schema typeCondition
              leftChildSelectionSet ≤ leftFuel :=
        Nat.le_trans
          (selectionSetDeepProbeFuel_inlineFragment_some_mem schema
            pathLeftParentType pathLeft typeCondition directives
            leftChildSelectionSet hleftMem)
          hleftFuel
      rcases
          ih (leftVariableDefinitions := leftVariableDefinitions)
            (rightVariableDefinitions := rightVariableDefinitions)
            (leftFuel := leftFuel) (rightFuel := rightFuel)
            hleftChildValid hrightValid
            (selectionSetArgumentsCoercibleInPossibleTypes_of_object
              htypeObjectBool
              (selectionSetArgumentsCoercible_inlineFragment_child_of_directiveFree
                (hleftCoercion typeCondition hinclude) hleftFree hleftMem
                (typeIncludesObjectBool_self_of_objectTypeNameBool schema
                  htypeObjectBool)))
            hrightCoercion
            hleftChildFree hrightFree
            hleftChildNormal hrightNormal hleftChildFuel hrightFuel
            hleftChildNonempty hrightNonempty with
        ⟨leftChildRuntime, rightChildRuntime, leftSpine, rightSpine,
          hleftChildSpineValid, hrightSpineValid, hchildDataDiff⟩
      have hleftChildRuntimeEq : leftChildRuntime = typeCondition :=
        typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
          htypeObjectBool
          (selectedFieldSpineRuntimeValid_typeIncludes
            hleftChildSpineValid)
      subst leftChildRuntime
      have hleftSpineValid :
          SelectedFieldSpineRuntimeValid schema pathLeftParentType
            typeCondition leftSpine :=
        SelectedFieldSpineRuntimeValid.abstractRuntime hleftNonObject
          (selectedFieldSpineRuntimeValid_runtime_object
            hleftChildSpineValid)
          hinclude hleftChildSpineValid
      refine ⟨
        typeCondition,
        rightChildRuntime,
        leftSpine,
        rightSpine,
        hleftSpineValid,
        hrightSpineValid,
        ?_
      ⟩
      intro leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine leftRuntime rightRuntime
      exact
        normalSelectionSetPairedPathDataDiffAt_of_left_abstract schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine leftSpine rightSpine
          variableValues leftFuel rightFuel targetParent leftProbeField
          rightProbeField pathLeftParentType pathRightParentType
          typeCondition rightChildRuntime targetLeftArguments
          targetRightArguments
          leftRuntime rightRuntime hleftNonObject hleftFree hleftNormal
          hleftMem hinclude hleftChildSpineValid
          (hchildDataDiff leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            leftRuntime rightRuntime)
  | @rightAbstract pathLeftParentType pathRightParentType typeCondition
      directives rightChildSelectionSet pathLeft pathRight hrightNonObject
      hrightMem _hchildPath ih =>
      have hrightChildValid :=
        selectionSetValid_inlineFragment_some_child_of_mem hrightValid
          hrightMem
      have hrightChildFree :=
        selectionSetDirectiveFree_inlineFragment_child_of_mem hrightFree
          hrightMem
      rcases
          selectionSetNormal_inlineFragment_child_of_mem hrightNormal
            hrightMem with
        ⟨htypeObject, hrightChildNormal⟩
      have hoverlap : schema.typesOverlap pathRightParentType typeCondition :=
        selectionSetValid_inlineFragment_some_typesOverlap_of_mem hrightValid
          hrightMem
      have hinclude :
          schema.typeIncludesObjectBool pathRightParentType typeCondition =
            true :=
        typeIncludesObjectBool_of_typesOverlap_object schema hoverlap
          htypeObject
      have hrightChildNonempty : rightChildSelectionSet ≠ [] :=
        selectionSetValid_inlineFragment_some_child_nonempty_of_mem hrightValid
          hrightMem
      have htypeObjectBool :
          objectTypeNameBool schema typeCondition = true :=
        objectTypeNameBool_eq_true_of_objectType_forNormality schema
          htypeObject
      have hrightChildFuel :
          selectionSetDeepProbeFuel schema typeCondition
              rightChildSelectionSet ≤ rightFuel :=
        Nat.le_trans
          (selectionSetDeepProbeFuel_inlineFragment_some_mem schema
            pathRightParentType pathRight typeCondition directives
            rightChildSelectionSet hrightMem)
          hrightFuel
      rcases
          ih (leftVariableDefinitions := leftVariableDefinitions)
            (rightVariableDefinitions := rightVariableDefinitions)
            (leftFuel := leftFuel) (rightFuel := rightFuel)
            hleftValid hrightChildValid hleftCoercion
            (selectionSetArgumentsCoercibleInPossibleTypes_of_object
              htypeObjectBool
              (selectionSetArgumentsCoercible_inlineFragment_child_of_directiveFree
                (hrightCoercion typeCondition hinclude) hrightFree hrightMem
                (typeIncludesObjectBool_self_of_objectTypeNameBool schema
                  htypeObjectBool)))
            hleftFree hrightChildFree
            hleftNormal hrightChildNormal hleftFuel hrightChildFuel
            hleftNonempty hrightChildNonempty with
        ⟨leftChildRuntime, rightChildRuntime, leftSpine, rightSpine,
          hleftSpineValid, hrightChildSpineValid, hchildDataDiff⟩
      have hrightChildRuntimeEq : rightChildRuntime = typeCondition :=
        typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
          htypeObjectBool
          (selectedFieldSpineRuntimeValid_typeIncludes
            hrightChildSpineValid)
      subst rightChildRuntime
      have hrightSpineValid :
          SelectedFieldSpineRuntimeValid schema pathRightParentType
            typeCondition rightSpine :=
        SelectedFieldSpineRuntimeValid.abstractRuntime hrightNonObject
          (selectedFieldSpineRuntimeValid_runtime_object
            hrightChildSpineValid)
          hinclude hrightChildSpineValid
      refine ⟨
        leftChildRuntime,
        typeCondition,
        leftSpine,
        rightSpine,
        hleftSpineValid,
        hrightSpineValid,
        ?_
      ⟩
      intro leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine leftRuntime rightRuntime
      exact
        normalSelectionSetPairedPathDataDiffAt_of_right_abstract schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine leftSpine rightSpine
          variableValues leftFuel rightFuel targetParent leftProbeField
          rightProbeField pathLeftParentType pathRightParentType
          leftChildRuntime typeCondition targetLeftArguments
          targetRightArguments
          leftRuntime rightRuntime hrightNonObject hrightFree hrightNormal
          hrightMem hinclude hrightChildSpineValid
          (hchildDataDiff leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            leftRuntime rightRuntime)

end GroundTypeNormalization

end NormalForm

end GraphQL
