import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedSelectedPathFoundations

/-!
Abstract-inline-fragment execution, pruning, and response-data separation.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

def SelectedPathSelectionSetsResponseDataDiff
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    (leftFuel rightFuel : Nat)
    (leftParentType rightParentType leftRuntimeType rightRuntimeType
      targetParent leftField rightField
      : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (leftCurrentSelectionSet rightCurrentSelectionSet : List Selection)
    (leftSpine rightSpine : List NormalSelectionSetObservableFieldStep)
    (left right : List Selection)
    : Prop :=
  schema.typeIncludesObjectBool leftParentType leftRuntimeType = true
  ∧ schema.typeIncludesObjectBool rightParentType rightRuntimeType = true
  ∧ SelectedFieldSpineRuntimeValid schema leftParentType leftRuntimeType leftSpine
  ∧ SelectedFieldSpineRuntimeValid schema rightParentType rightRuntimeType rightSpine
  ∧ ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftField
              rightField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField targetLeftArguments
            targetRightArguments)
          variableValues (leftFuel + 1) leftRuntimeType
          (projectionTargetResolverValue
            (.object leftRuntimeType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftCurrentSelectionSet leftSpine)))
          left).data
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftField
              rightField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField targetLeftArguments
            targetRightArguments)
          variableValues (rightFuel + 1) rightRuntimeType
          (projectionTargetResolverValue
            (.object rightRuntimeType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet rightSpine)))
          right).data

def SelectedPathSelectionSetsResponseDataDiffRightPruned
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    (leftFuel _rightFuel : Nat)
    (leftParentType rightParentType leftRuntimeType rightRuntimeType
      targetParent leftField rightField
      : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (leftCurrentSelectionSet : List Selection)
    (leftSpine : List NormalSelectionSetObservableFieldStep)
    (left _right : List Selection)
    : Prop :=
  schema.typeIncludesObjectBool leftParentType leftRuntimeType = true
  ∧ schema.typeIncludesObjectBool rightParentType rightRuntimeType = true
  ∧ SelectedFieldSpineRuntimeValid schema leftParentType leftRuntimeType leftSpine
  ∧ ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftField
              rightField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField targetLeftArguments
            targetRightArguments)
          variableValues (leftFuel + 1) leftRuntimeType
          (projectionTargetResolverValue
            (.object leftRuntimeType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftCurrentSelectionSet leftSpine)))
          left).data
        (Execution.ResponseValue.object [])

def SelectedPathSelectionSetsResponseDataDiffLeftPruned
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    (_leftFuel rightFuel : Nat)
    (leftParentType rightParentType leftRuntimeType rightRuntimeType
      targetParent leftField rightField
      : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (rightCurrentSelectionSet : List Selection)
    (rightSpine : List NormalSelectionSetObservableFieldStep)
    (_left right : List Selection)
    : Prop :=
  schema.typeIncludesObjectBool leftParentType leftRuntimeType = true
  ∧ schema.typeIncludesObjectBool rightParentType rightRuntimeType = true
  ∧ SelectedFieldSpineRuntimeValid schema rightParentType rightRuntimeType rightSpine
  ∧ ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object [])
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftField
              rightField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField targetLeftArguments
            targetRightArguments)
          variableValues (rightFuel + 1) rightRuntimeType
          (projectionTargetResolverValue
            (.object rightRuntimeType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet rightSpine)))
          right).data

theorem selectedPathSelectionSetsResponseDataDiff_of_dataNot
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntimeType rightRuntimeType
      targetParent leftField rightField
      : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {leftSpine rightSpine : List NormalSelectionSetObservableFieldStep}
    {left right : List Selection}
    : schema.typeIncludesObjectBool leftParentType leftRuntimeType = true
      -> schema.typeIncludesObjectBool rightParentType rightRuntimeType = true
      -> SelectedFieldSpineRuntimeValid schema leftParentType leftRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType rightRuntimeType rightSpine
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField targetLeftArguments
                targetRightArguments)
              variableValues (leftFuel + 1) leftRuntimeType
              (projectionTargetResolverValue
                (.object leftRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField targetLeftArguments
                targetRightArguments)
              variableValues (rightFuel + 1) rightRuntimeType
              (projectionTargetResolverValue
                (.object rightRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data
      -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftField rightField targetLeftArguments targetRightArguments
          leftRuntime rightRuntime leftCurrentSelectionSet
          rightCurrentSelectionSet leftSpine rightSpine left right := by
  intro hleftInclude hrightInclude hleftSpineValid hrightSpineValid
    hdataNot
  exact ⟨hleftInclude, hrightInclude, hleftSpineValid, hrightSpineValid, hdataNot⟩

theorem selectedPathSelectionSetsResponseDataDiffRightPruned_of_dataNot
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntimeType rightRuntimeType
      targetParent leftField rightField
      : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet : List Selection}
    {leftSpine : List NormalSelectionSetObservableFieldStep}
    {left right : List Selection}
    : schema.typeIncludesObjectBool leftParentType leftRuntimeType = true
      -> schema.typeIncludesObjectBool rightParentType rightRuntimeType = true
      -> SelectedFieldSpineRuntimeValid schema leftParentType leftRuntimeType leftSpine
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField targetLeftArguments
                targetRightArguments)
              variableValues (leftFuel + 1) leftRuntimeType
              (projectionTargetResolverValue
                (.object leftRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.ResponseValue.object [])
      -> SelectedPathSelectionSetsResponseDataDiffRightPruned schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues leftFuel
          rightFuel leftParentType rightParentType leftRuntimeType
          rightRuntimeType targetParent leftField rightField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet leftSpine left right := by
  intro hleftInclude hrightInclude hleftSpineValid hdataNot
  exact ⟨hleftInclude, hrightInclude, hleftSpineValid, hdataNot⟩

theorem selectedPathSelectionSetsResponseDataDiffLeftPruned_of_dataNot
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntimeType rightRuntimeType
      targetParent leftField rightField
      : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {rightCurrentSelectionSet : List Selection}
    {rightSpine : List NormalSelectionSetObservableFieldStep}
    {left right : List Selection}
    : schema.typeIncludesObjectBool leftParentType leftRuntimeType = true
      -> schema.typeIncludesObjectBool rightParentType rightRuntimeType = true
      -> SelectedFieldSpineRuntimeValid schema rightParentType rightRuntimeType rightSpine
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object [])
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField targetLeftArguments
                targetRightArguments)
              variableValues (rightFuel + 1) rightRuntimeType
              (projectionTargetResolverValue
                (.object rightRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data
      -> SelectedPathSelectionSetsResponseDataDiffLeftPruned schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues leftFuel
          rightFuel leftParentType rightParentType leftRuntimeType
          rightRuntimeType targetParent leftField rightField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          rightCurrentSelectionSet rightSpine left right := by
  intro hleftInclude hrightInclude hrightSpineValid hdataNot
  exact ⟨hleftInclude, hrightInclude, hrightSpineValid, hdataNot⟩

theorem selectedPathSelectionSetsResponseDataDiff_of_taggedWitness_sameFuel
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {fuel : Nat}
    {normalParentType runtimeType targetParent leftField rightField : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {left right : List Selection}
    : SelectedFieldSpineRuntimeValid schema normalParentType runtimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema normalParentType runtimeType rightSpine
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues (fuel + 1)
          normalParentType runtimeType targetParent leftField rightField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
          left right
      -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues fuel fuel normalParentType
          normalParentType runtimeType runtimeType targetParent leftField
          rightField targetLeftArguments targetRightArguments leftRuntime
          rightRuntime leftCurrentSelectionSet rightCurrentSelectionSet
          leftSpine rightSpine left right := by
  intro hleftSpineValid hrightSpineValid hwitness
  rcases hwitness with
    ⟨hinclude, leftFields, leftErrors, rightFields, rightErrors,
      hleftResponse, hrightResponse, hdataNot⟩
  exact
    selectedPathSelectionSetsResponseDataDiff_of_dataNot
      hinclude hinclude hleftSpineValid hrightSpineValid
      (by
        intro hsemantic
        exact hdataNot
          (by simpa [hleftResponse, hrightResponse] using hsemantic))

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_inlineFragment_body_eq
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) {selectionSet bodySelectionSet : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema normalParentType selectionSet
      -> Selection.inlineFragment (some runtimeType) [] bodySelectionSet ∈ selectionSet
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
            selectionSet
          = Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
              bodySelectionSet := by
  intro hnonObject hruntimeObject hfree hnormal hmem
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let source :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine))
  rcases List.mem_iff_append.mp hmem with
    ⟨pref, suffix, hselectionSet⟩
  subst selectionSet
  have hmiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType source
        (pref ++ Selection.inlineFragment (some runtimeType) []
          bodySelectionSet :: suffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType source
        [Selection.inlineFragment (some runtimeType) []
          bodySelectionSet] := by
    dsimp [source]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
        schema resolvers variableValues (fuel + 1)
        (ProjectionResolverRef.target
          (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
            spine))
        hnonObject hruntimeObject hfree hnormal
  have happly :
      Execution.doesFragmentTypeApplyBool schema runtimeType source
        runtimeType = true := by
    dsimp [source]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      (doesFragmentTypeApplyBool_object_self schema
        (ref :=
          ProjectionResolverRef.target
            (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
              spine))
        hruntimeObject)
  have hflatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType source
        [Selection.inlineFragment (some runtimeType) [] bodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType source bodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        source bodySelectionSet [] happly
  simp [Execution.executeSelectionSetAsResponse, resolvers, source, hmiddle, hflatten]

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_abstract_sameTypeCondition_bodyWitness
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues} {fuel : Nat}
    {normalParentType runtimeType targetParent leftField rightField : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {left right leftBodySelectionSet rightBodySelectionSet : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> schema.typeIncludesObjectBool normalParentType runtimeType = true
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> Selection.inlineFragment (some runtimeType) [] leftBodySelectionSet ∈ left
      -> Selection.inlineFragment (some runtimeType) [] rightBodySelectionSet ∈ right
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues (fuel + 1)
          runtimeType runtimeType targetParent leftField rightField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
          leftBodySelectionSet rightBodySelectionSet
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues (fuel + 1)
          normalParentType runtimeType targetParent leftField rightField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
          left right := by
  intro hnonObject hruntimeObject hinclude hleftFree hrightFree
    hleftNormal hrightNormal hleftMem hrightMem hbodyWitness
  rcases hbodyWitness with
    ⟨_hbodyInclude, leftFields, leftErrors, rightFields, rightErrors,
      hleftBodyResponse, hrightBodyResponse, hnot⟩
  have hleftEq :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_inlineFragment_body_eq
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine variableValues fuel targetParent
      leftField rightField normalParentType runtimeType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      FieldPairProbeTag.left hnonObject hruntimeObject hleftFree
      hleftNormal hleftMem
  have hrightEq :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_inlineFragment_body_eq
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine rightSpine variableValues fuel targetParent
      leftField rightField normalParentType runtimeType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      FieldPairProbeTag.right hnonObject hruntimeObject hrightFree
      hrightNormal hrightMem
  exact ⟨
    hinclude,
    leftFields,
    leftErrors,
    rightFields,
    rightErrors,
    by simpa [hleftEq] using hleftBodyResponse,
    by simpa [hrightEq] using hrightBodyResponse,
    hnot
  ⟩

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_missing_runtime_eq_empty
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) {selectionSet : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema normalParentType selectionSet
      -> runtimeType ∉ selectionSet.filterMap inlineFragmentTypeCondition?
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
            selectionSet
          = ({ data := Execution.ResponseValue.object [], errors := 0 }
              : Execution.Response) := by
  intro hnonObject hfree hnormal hruntimeMissing
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let source :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine))
  have hcollect :
      Execution.collectFields schema variableValues runtimeType source
        selectionSet = [] := by
    dsimp [source]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
        schema variableValues (normalParentType := normalParentType)
        (executionParentType := runtimeType) (runtimeType := runtimeType)
        (ProjectionResolverRef.target
          (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
            spine))
        hnonObject hfree hnormal hruntimeMissing
  have hcollectObject :
      Execution.collectFields schema variableValues runtimeType
        (Execution.ResolverValue.object runtimeType
          (ProjectionResolverRef.target
            (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
              spine)))
        selectionSet = [] := by
    simpa [source, projectionTargetResolverValue, projectionResolverValue]
      using hcollect
  simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
    Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    projectionTargetResolverValue, projectionResolverValue,
    hcollectObject, Execution.executeCollectedFields]

theorem
    selectedPathTaggedSelectionSetsRightPrunedResponseDiffWitness_of_left_abstract_body_nonempty_right_missing
    {schema : Schema} {leftVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right leftBodySelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions
          runtimeType leftBodySelectionSet
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetDirectiveFree leftBodySelectionSet
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> selectionSetNormal schema runtimeType leftBodySelectionSet
      -> objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> schema.typeIncludesObjectBool normalParentType runtimeType = true
      -> Selection.inlineFragment (some runtimeType) [] leftBodySelectionSet ∈ left
      -> runtimeType ∉ right.filterMap inlineFragmentTypeCondition?
      -> selectionSetDeepProbeFuel schema runtimeType leftBodySelectionSet ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema runtimeType runtimeType leftSpine
      -> PathLocalSupportValidNormal schema runtimeType leftCurrentSelectionSet
      -> SelectedPathSelectionSetContextReady schema runtimeType runtimeType
          leftCurrentSelectionSet leftBodySelectionSet
      -> leftBodySelectionSet ≠ []
      -> SelectedPathTaggedSelectionSetsRightPrunedResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues (fuel + 1)
          normalParentType runtimeType targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
          rightSpine left right := by
  intro hschema hleftBodyValid hleftFree hrightFree hleftBodyFree
    hleftNormal hrightNormal hleftBodyNormal hnonObject hruntimeObject
    hinclude hleftMem hrightMissing hfuel hleftSpineValid hleftSupport
    hleftContextReady hleftBodyNonempty
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_contextReady_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size leftBodySelectionSet + 1)
        runtimeType leftVariableDefinitions leftBodySelectionSet fuel
        runtimeType targetParent leftField rightField leftArguments
        rightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        leftCurrentSelectionSet leftSpine (by omega) hfuel
        hleftBodyValid hleftBodyFree hleftBodyNormal hleftSpineValid
        hleftSupport hleftContextReady with
    ⟨leftFields, leftErrors, hleftBodyResponse⟩
  have hleftEq :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_inlineFragment_body_eq
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine variableValues fuel targetParent
      leftField rightField normalParentType runtimeType leftArguments
      rightArguments leftRuntime rightRuntime FieldPairProbeTag.left
      hnonObject hruntimeObject hleftFree hleftNormal hleftMem
  have hrightResponse :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_missing_runtime_eq_empty
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine rightSpine variableValues fuel targetParent
      leftField rightField normalParentType runtimeType leftArguments
      rightArguments leftRuntime rightRuntime FieldPairProbeTag.right
      hnonObject hrightFree hrightNormal hrightMissing
  have hleftResponse :
      Execution.executeSelectionSetAsResponse schema
        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
          (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            targetParent leftField rightField leftArguments rightArguments
            leftRuntime rightRuntime)
          targetParent leftField rightField leftArguments rightArguments)
        variableValues (fuel + 1) runtimeType
        (projectionTargetResolverValue
          (.object runtimeType
            (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
              leftCurrentSelectionSet leftSpine)))
        left =
        ({ data := Execution.ResponseValue.object leftFields,
           errors := leftErrors } : Execution.Response) := by
    rw [hleftEq]
    exact hleftBodyResponse
  have hbodyNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) runtimeType
          (projectionTargetResolverValue
            (.object runtimeType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftCurrentSelectionSet leftSpine)))
          leftBodySelectionSet).data
        (Execution.ResponseValue.object []) :=
    responseData_not_semanticEquivalent_empty_object_of_valid_normal_object_nonempty_response
      schema
      (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
        (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          targetParent leftField rightField leftArguments rightArguments
          leftRuntime rightRuntime)
        targetParent leftField rightField leftArguments rightArguments)
      variableValues (fuel + 1) runtimeType
      (projectionTargetResolverValue
        (.object runtimeType
          (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
            leftCurrentSelectionSet leftSpine)))
      hruntimeObject hleftBodyFree hleftBodyNormal hleftBodyNonempty
      hleftBodyResponse
  exact ⟨
    hinclude,
    leftFields,
    leftErrors,
    hleftResponse,
    hrightResponse,
    by
      intro hsemantic
      exact hbodyNot (by simpa [hleftBodyResponse] using hsemantic)
  ⟩

theorem
    selectedPathTaggedSelectionSetsLeftPrunedResponseDiffWitness_of_right_abstract_body_nonempty_left_missing
    {schema : Schema} {rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right rightBodySelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema rightVariableDefinitions
          runtimeType rightBodySelectionSet
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetDirectiveFree rightBodySelectionSet
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> selectionSetNormal schema runtimeType rightBodySelectionSet
      -> objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> schema.typeIncludesObjectBool normalParentType runtimeType = true
      -> Selection.inlineFragment (some runtimeType) [] rightBodySelectionSet ∈ right
      -> runtimeType ∉ left.filterMap inlineFragmentTypeCondition?
      -> selectionSetDeepProbeFuel schema runtimeType rightBodySelectionSet ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema runtimeType runtimeType rightSpine
      -> PathLocalSupportValidNormal schema runtimeType rightCurrentSelectionSet
      -> SelectedPathSelectionSetContextReady schema runtimeType runtimeType
          rightCurrentSelectionSet rightBodySelectionSet
      -> rightBodySelectionSet ≠ []
      -> SelectedPathTaggedSelectionSetsLeftPrunedResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues (fuel + 1)
          normalParentType runtimeType targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
          rightSpine left right := by
  intro hschema hrightBodyValid hleftFree hrightFree hrightBodyFree
    hleftNormal hrightNormal hrightBodyNormal hnonObject hruntimeObject
    hinclude hrightMem hleftMissing hfuel hrightSpineValid hrightSupport
    hrightContextReady hrightBodyNonempty
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_contextReady_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size rightBodySelectionSet + 1)
        runtimeType rightVariableDefinitions rightBodySelectionSet fuel
        runtimeType targetParent leftField rightField leftArguments
        rightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        rightCurrentSelectionSet rightSpine (by omega) hfuel
        hrightBodyValid hrightBodyFree hrightBodyNormal hrightSpineValid
        hrightSupport hrightContextReady with
    ⟨rightFields, rightErrors, hrightBodyResponse⟩
  have hleftResponse :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_missing_runtime_eq_empty
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine variableValues fuel targetParent
      leftField rightField normalParentType runtimeType leftArguments
      rightArguments leftRuntime rightRuntime FieldPairProbeTag.left
      hnonObject hleftFree hleftNormal hleftMissing
  have hrightEq :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_inlineFragment_body_eq
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine rightSpine variableValues fuel targetParent
      leftField rightField normalParentType runtimeType leftArguments
      rightArguments leftRuntime rightRuntime FieldPairProbeTag.right
      hnonObject hruntimeObject hrightFree hrightNormal hrightMem
  have hrightResponse :
      Execution.executeSelectionSetAsResponse schema
        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
          (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            targetParent leftField rightField leftArguments rightArguments
            leftRuntime rightRuntime)
          targetParent leftField rightField leftArguments rightArguments)
        variableValues (fuel + 1) runtimeType
        (projectionTargetResolverValue
          (.object runtimeType
            (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
              rightCurrentSelectionSet rightSpine)))
        right =
        ({ data := Execution.ResponseValue.object rightFields,
           errors := rightErrors } : Execution.Response) := by
    rw [hrightEq]
    exact hrightBodyResponse
  have hbodyNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object [])
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) runtimeType
          (projectionTargetResolverValue
            (.object runtimeType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet rightSpine)))
          rightBodySelectionSet).data :=
    responseData_empty_object_not_semanticEquivalent_of_valid_normal_object_nonempty_response
      schema
      (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
        (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          targetParent leftField rightField leftArguments rightArguments
          leftRuntime rightRuntime)
        targetParent leftField rightField leftArguments rightArguments)
      variableValues (fuel + 1) runtimeType
      (projectionTargetResolverValue
        (.object runtimeType
          (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
            rightCurrentSelectionSet rightSpine)))
      hruntimeObject hrightBodyFree hrightBodyNormal hrightBodyNonempty
      hrightBodyResponse
  exact ⟨
    hinclude,
    rightFields,
    rightErrors,
    hleftResponse,
    hrightResponse,
    by
      intro hsemantic
      exact hbodyNot (by simpa [hrightBodyResponse] using hsemantic)
  ⟩

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_abstract_inlineFragment_body_pair
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField leftParentType rightParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right leftBodySelectionSet rightBodySelectionSet : List Selection}
    : objectTypeNameBool schema leftParentType = false
      -> objectTypeNameBool schema rightParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> Selection.inlineFragment (some runtimeType) [] leftBodySelectionSet ∈ left
      -> Selection.inlineFragment (some runtimeType) [] rightBodySelectionSet ∈ right
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              leftBodySelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              rightBodySelectionSet).data
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data := by
  intro hleftNonObject hrightNonObject hruntimeObject hleftFree hrightFree
    hleftNormal hrightNormal hleftMem hrightMem hbodyNot hsemantic
  have hleftEq :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_inlineFragment_body_eq
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine variableValues fuel targetParent
      leftField rightField leftParentType runtimeType leftArguments
      rightArguments leftRuntime rightRuntime FieldPairProbeTag.left
      hleftNonObject hruntimeObject hleftFree hleftNormal hleftMem
  have hrightEq :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_inlineFragment_body_eq
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine rightSpine variableValues fuel targetParent
      leftField rightField rightParentType runtimeType leftArguments
      rightArguments leftRuntime rightRuntime FieldPairProbeTag.right
      hrightNonObject hruntimeObject hrightFree hrightNormal hrightMem
  exact hbodyNot (by simpa [hleftEq, hrightEq] using hsemantic)

theorem selectedPathSelectionSetsResponseDataDiff_of_right_abstract_inlineFragment_body
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntimeType rightRuntimeType
      targetParent leftField rightField
      : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {left right rightBodySelectionSet : List Selection}
    : objectTypeNameBool schema rightParentType = false
      -> objectTypeNameBool schema rightRuntimeType = true
      -> schema.typeIncludesObjectBool rightParentType rightRuntimeType = true
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema rightParentType right
      -> Selection.inlineFragment (some rightRuntimeType) [] rightBodySelectionSet ∈ right
      -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightRuntimeType leftRuntimeType rightRuntimeType targetParent
          leftField rightField targetLeftArguments targetRightArguments
          leftRuntime rightRuntime leftCurrentSelectionSet
          rightCurrentSelectionSet leftSpine rightSpine left
          rightBodySelectionSet
      -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftField rightField targetLeftArguments targetRightArguments
          leftRuntime rightRuntime leftCurrentSelectionSet
          rightCurrentSelectionSet leftSpine rightSpine left right := by
  intro hrightNonObject hrightRuntimeObject hrightInclude hrightFree
    hrightNormal hrightMem hbodyDiff
  rcases hbodyDiff with
    ⟨hleftInclude, _hrightBodyInclude, hleftSpineValid,
      hrightBodySpineValid, hbodyNot⟩
  have hrightSpineValid :
      SelectedFieldSpineRuntimeValid schema rightParentType
        rightRuntimeType rightSpine :=
    SelectedFieldSpineRuntimeValid.abstractRuntime hrightNonObject
      hrightRuntimeObject hrightInclude hrightBodySpineValid
  exact
    selectedPathSelectionSetsResponseDataDiff_of_dataNot
      hleftInclude hrightInclude hleftSpineValid hrightSpineValid
      (by
        intro hsemantic
        have hrightEq :=
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_inlineFragment_body_eq
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet rightCurrentSelectionSet
            leftInitialSpine rightInitialSpine rightSpine variableValues
            rightFuel targetParent leftField rightField rightParentType
            rightRuntimeType targetLeftArguments targetRightArguments
            leftRuntime rightRuntime FieldPairProbeTag.right
            hrightNonObject hrightRuntimeObject hrightFree hrightNormal
            hrightMem
        exact hbodyNot (by simpa [hrightEq] using hsemantic))

theorem selectedPathSelectionSetsResponseDataDiff_of_left_abstract_inlineFragment_body
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntimeType rightRuntimeType
      targetParent leftField rightField
      : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {left leftBodySelectionSet right : List Selection}
    : objectTypeNameBool schema leftParentType = false
      -> objectTypeNameBool schema leftRuntimeType = true
      -> schema.typeIncludesObjectBool leftParentType leftRuntimeType = true
      -> selectionSetDirectiveFree left
      -> selectionSetNormal schema leftParentType left
      -> Selection.inlineFragment (some leftRuntimeType) [] leftBodySelectionSet ∈ left
      -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftRuntimeType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftField rightField targetLeftArguments targetRightArguments
          leftRuntime rightRuntime leftCurrentSelectionSet
          rightCurrentSelectionSet leftSpine rightSpine leftBodySelectionSet
          right
      -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftField rightField targetLeftArguments targetRightArguments
          leftRuntime rightRuntime leftCurrentSelectionSet
          rightCurrentSelectionSet leftSpine rightSpine left right := by
  intro hleftNonObject hleftRuntimeObject hleftInclude hleftFree
    hleftNormal hleftMem hbodyDiff
  rcases hbodyDiff with
    ⟨_hleftBodyInclude, hrightInclude, hleftBodySpineValid,
      hrightSpineValid, hbodyNot⟩
  have hleftSpineValid :
      SelectedFieldSpineRuntimeValid schema leftParentType
        leftRuntimeType leftSpine :=
    SelectedFieldSpineRuntimeValid.abstractRuntime hleftNonObject
      hleftRuntimeObject hleftInclude hleftBodySpineValid
  exact
    selectedPathSelectionSetsResponseDataDiff_of_dataNot
      hleftInclude hrightInclude hleftSpineValid hrightSpineValid
      (by
        intro hsemantic
        have hleftEq :=
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_inlineFragment_body_eq
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet leftCurrentSelectionSet
            leftInitialSpine rightInitialSpine leftSpine variableValues
            leftFuel targetParent leftField rightField leftParentType
            leftRuntimeType targetLeftArguments targetRightArguments
            leftRuntime rightRuntime FieldPairProbeTag.left
            hleftNonObject hleftRuntimeObject hleftFree hleftNormal
            hleftMem
        exact hbodyNot (by simpa [hleftEq] using hsemantic))

theorem
    selectedPathSelectionSetsResponseDataDiff_of_observableResponsePath_valid_normal_pair_contextReady_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ normalParentType leftCurrentSelectionSet rightCurrentSelectionSet
            (selectionSet : List Selection) {responsePath : List Name},
          NormalSelectionSetObservableResponsePath schema normalParentType
            selectionSet responsePath
          -> ∀ variableDefinitions fuel targetParent leftField rightField
                (targetLeftArguments targetRightArguments : List Argument)
                (leftRuntime rightRuntime : Name),
              Validation.selectionSetValid schema variableDefinitions
                normalParentType selectionSet
              -> selectionSetDirectiveFree selectionSet
              -> selectionSetNormal schema normalParentType selectionSet
              -> selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
              -> ∃ runtimeType fieldSpine,
                  schema.typeIncludesObjectBool normalParentType runtimeType = true
                  ∧ SelectedFieldSpineRuntimeValid schema normalParentType
                      runtimeType fieldSpine
                  ∧ (PathLocalSupportValidNormal schema runtimeType
                        leftCurrentSelectionSet
                      -> PathLocalSupportValidNormal schema runtimeType
                          rightCurrentSelectionSet
                      -> SelectedPathSelectionSetContextReady schema
                          normalParentType runtimeType leftCurrentSelectionSet
                          selectionSet
                      -> SelectedPathSelectionSetContextReady schema
                          normalParentType runtimeType rightCurrentSelectionSet
                          selectionSet
                      -> SelectedPathSelectionSetsResponseDataDiff schema
                          rootSelectionSet leftInitialSelectionSet
                          rightInitialSelectionSet leftInitialSpine
                          rightInitialSpine variableValues fuel fuel
                          normalParentType normalParentType runtimeType
                          runtimeType targetParent leftField rightField
                          targetLeftArguments targetRightArguments leftRuntime
                          rightRuntime leftCurrentSelectionSet
                          rightCurrentSelectionSet fieldSpine fieldSpine
                          selectionSet selectionSet) := by
  intro hschema normalParentType leftCurrentSelectionSet
    rightCurrentSelectionSet selectionSet responsePath hpath
    variableDefinitions fuel targetParent leftField rightField
    targetLeftArguments targetRightArguments leftRuntime rightRuntime hvalid
    hfree hnormal hfuel
  rcases
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_observableResponsePath_valid_normal_pair_support_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema normalParentType leftCurrentSelectionSet
        rightCurrentSelectionSet selectionSet hpath variableDefinitions
        fuel targetParent leftField rightField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime hvalid hfree
        hnormal hfuel with
    ⟨selectedRuntimeType, selectedFieldSpine, hselectedInclude,
      hselectedSpineValid, hdataBuilder⟩
  refine ⟨
    selectedRuntimeType,
    selectedFieldSpine,
    hselectedInclude,
    hselectedSpineValid,
    ?_
  ⟩
  intro hleftSupport hrightSupport hleftContextReady hrightContextReady
  exact
    selectedPathSelectionSetsResponseDataDiff_of_dataNot
      hselectedInclude hselectedInclude hselectedSpineValid
      hselectedSpineValid
      (hdataBuilder hleftSupport hrightSupport
        (fun hobject => hleftContextReady.1 hobject)
        (fun hobject => hrightContextReady.1 hobject)
        (fun hnonObject {directives} {bodySelectionSet} hmem =>
          hleftContextReady.2 hnonObject
            (directives := directives) (bodySelectionSet := bodySelectionSet)
            hmem)
        (fun hnonObject {directives} {bodySelectionSet} hmem =>
          hrightContextReady.2 hnonObject
            (directives := directives) (bodySelectionSet := bodySelectionSet)
            hmem))

theorem selectedPathSelectionSetsResponseDataDiff_of_right_abstract_typeCondition_mem
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntimeType rightRuntimeType
      targetParent leftField rightField
      : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {left right : List Selection}
    : objectTypeNameBool schema rightParentType = false
      -> objectTypeNameBool schema rightRuntimeType = true
      -> schema.typeIncludesObjectBool rightParentType rightRuntimeType = true
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema rightParentType right
      -> rightRuntimeType ∈ right.filterMap inlineFragmentTypeCondition?
      -> (∀ {directives rightBodySelectionSet},
            Selection.inlineFragment (some rightRuntimeType) directives
                rightBodySelectionSet
              ∈ right
            -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
                leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
                rightInitialSpine variableValues leftFuel rightFuel
                leftParentType rightRuntimeType leftRuntimeType rightRuntimeType
                targetParent leftField rightField targetLeftArguments
                targetRightArguments leftRuntime rightRuntime
                leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
                rightSpine left rightBodySelectionSet)
      -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftField rightField targetLeftArguments targetRightArguments
          leftRuntime rightRuntime leftCurrentSelectionSet
          rightCurrentSelectionSet leftSpine rightSpine left right := by
  intro hrightNonObject hrightRuntimeObject hrightInclude hrightFree
    hrightNormal hrightRuntimeMem hbody
  rcases
      selectionSetNormal_inlineFragment_mem_of_abstract_typeCondition_mem
        hrightNormal hrightNonObject hrightRuntimeMem with
    ⟨rightDirectives, rightBodySelectionSet, hrightMem⟩
  have hrightDirectives : rightDirectives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hrightFree hrightMem
  subst rightDirectives
  exact
    selectedPathSelectionSetsResponseDataDiff_of_right_abstract_inlineFragment_body
      hrightNonObject hrightRuntimeObject hrightInclude hrightFree
      hrightNormal hrightMem (hbody hrightMem)

theorem selectedPathSelectionSetsResponseDataDiff_of_left_abstract_typeCondition_mem
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntimeType rightRuntimeType
      targetParent leftField rightField
      : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {left right : List Selection}
    : objectTypeNameBool schema leftParentType = false
      -> objectTypeNameBool schema leftRuntimeType = true
      -> schema.typeIncludesObjectBool leftParentType leftRuntimeType = true
      -> selectionSetDirectiveFree left
      -> selectionSetNormal schema leftParentType left
      -> leftRuntimeType ∈ left.filterMap inlineFragmentTypeCondition?
      -> (∀ {directives leftBodySelectionSet},
            Selection.inlineFragment (some leftRuntimeType) directives
                leftBodySelectionSet
              ∈ left
            -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
                leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
                rightInitialSpine variableValues leftFuel rightFuel
                leftRuntimeType rightParentType leftRuntimeType rightRuntimeType
                targetParent leftField rightField targetLeftArguments
                targetRightArguments leftRuntime rightRuntime
                leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
                rightSpine leftBodySelectionSet right)
      -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftField rightField targetLeftArguments targetRightArguments
          leftRuntime rightRuntime leftCurrentSelectionSet
          rightCurrentSelectionSet leftSpine rightSpine left right := by
  intro hleftNonObject hleftRuntimeObject hleftInclude hleftFree
    hleftNormal hleftRuntimeMem hbody
  rcases
      selectionSetNormal_inlineFragment_mem_of_abstract_typeCondition_mem
        hleftNormal hleftNonObject hleftRuntimeMem with
    ⟨leftDirectives, leftBodySelectionSet, hleftMem⟩
  have hleftDirectives : leftDirectives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hleftFree hleftMem
  subst leftDirectives
  exact
    selectedPathSelectionSetsResponseDataDiff_of_left_abstract_inlineFragment_body
      hleftNonObject hleftRuntimeObject hleftInclude hleftFree
      hleftNormal hleftMem (hbody hleftMem)

theorem selectedPathSelectionSetsResponseDataDiff_of_right_abstract_missing_runtime
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntimeType rightRuntimeType
      targetParent leftField rightField
      : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {left right : List Selection}
    : schema.typeIncludesObjectBool leftParentType leftRuntimeType = true
      -> schema.typeIncludesObjectBool rightParentType rightRuntimeType = true
      -> SelectedFieldSpineRuntimeValid schema leftParentType leftRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType rightRuntimeType rightSpine
      -> objectTypeNameBool schema rightParentType = false
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema rightParentType right
      -> rightRuntimeType ∉ right.filterMap inlineFragmentTypeCondition?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField targetLeftArguments
                  targetRightArguments leftRuntime rightRuntime)
                targetParent leftField rightField targetLeftArguments
                targetRightArguments)
              variableValues (leftFuel + 1) leftRuntimeType
              (projectionTargetResolverValue
                (.object leftRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.ResponseValue.object [])
      -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftField rightField targetLeftArguments targetRightArguments
          leftRuntime rightRuntime leftCurrentSelectionSet
          rightCurrentSelectionSet leftSpine rightSpine left right := by
  intro hleftInclude hrightInclude hleftSpineValid hrightSpineValid
    hrightNonObject hrightFree hrightNormal hrightMissing hleftNotEmpty
  exact
    selectedPathSelectionSetsResponseDataDiff_of_dataNot
      hleftInclude hrightInclude hleftSpineValid hrightSpineValid
      (by
        intro hsemantic
        have hrightEq :=
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_missing_runtime_eq_empty
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet rightCurrentSelectionSet
            leftInitialSpine rightInitialSpine rightSpine variableValues
            rightFuel targetParent leftField rightField rightParentType
            rightRuntimeType targetLeftArguments targetRightArguments
            leftRuntime rightRuntime FieldPairProbeTag.right
            hrightNonObject hrightFree hrightNormal hrightMissing
        exact hleftNotEmpty (by simpa [hrightEq] using hsemantic))

theorem selectedPathSelectionSetsResponseDataDiff_of_left_abstract_missing_runtime
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntimeType rightRuntimeType
      targetParent leftField rightField
      : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {left right : List Selection}
    : schema.typeIncludesObjectBool leftParentType leftRuntimeType = true
      -> schema.typeIncludesObjectBool rightParentType rightRuntimeType = true
      -> SelectedFieldSpineRuntimeValid schema leftParentType leftRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType rightRuntimeType rightSpine
      -> objectTypeNameBool schema leftParentType = false
      -> selectionSetDirectiveFree left
      -> selectionSetNormal schema leftParentType left
      -> leftRuntimeType ∉ left.filterMap inlineFragmentTypeCondition?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object [])
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField targetLeftArguments
                  targetRightArguments leftRuntime rightRuntime)
                targetParent leftField rightField targetLeftArguments
                targetRightArguments)
              variableValues (rightFuel + 1) rightRuntimeType
              (projectionTargetResolverValue
                (.object rightRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data
      -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightRuntimeType targetParent
          leftField rightField targetLeftArguments targetRightArguments
          leftRuntime rightRuntime leftCurrentSelectionSet
          rightCurrentSelectionSet leftSpine rightSpine left right := by
  intro hleftInclude hrightInclude hleftSpineValid hrightSpineValid
    hleftNonObject hleftFree hleftNormal hleftMissing hrightNotEmpty
  exact
    selectedPathSelectionSetsResponseDataDiff_of_dataNot
      hleftInclude hrightInclude hleftSpineValid hrightSpineValid
      (by
        intro hsemantic
        have hleftEq :=
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_missing_runtime_eq_empty
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet leftCurrentSelectionSet
            leftInitialSpine rightInitialSpine leftSpine variableValues
            leftFuel targetParent leftField rightField leftParentType
            leftRuntimeType targetLeftArguments targetRightArguments
            leftRuntime rightRuntime FieldPairProbeTag.left hleftNonObject
            hleftFree hleftNormal hleftMissing
        exact hrightNotEmpty (by simpa [hleftEq] using hsemantic))

theorem
    responseData_not_semanticEquivalent_empty_object_of_fieldPairOrDeepSuccess_selectedPathProbe_object_valid_normal_contextReady_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ variableDefinitions parentType currentSelectionSet
            (selectionSet : List Selection) fuel targetParent leftField
            rightField (targetLeftArguments targetRightArguments : List Argument)
            (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag),
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> SelectedFieldSpineRuntimeValid schema parentType parentType spine
          -> PathLocalSupportValidNormal schema parentType currentSelectionSet
          -> SelectedPathSelectionSetContextReady schema parentType parentType
              currentSelectionSet selectionSet
          -> selectionSet ≠ []
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent leftField
                      rightField targetLeftArguments targetRightArguments
                      leftRuntime rightRuntime)
                    targetParent leftField rightField targetLeftArguments
                    targetRightArguments)
                  variableValues (fuel + 1) parentType
                  (projectionTargetResolverValue
                    (.object parentType
                      (FieldPairSelectedPathProbeRef.target tag
                        currentSelectionSet spine)))
                  selectionSet).data
                (Execution.ResponseValue.object []) := by
  intro hschema variableDefinitions parentType currentSelectionSet
    selectionSet fuel targetParent leftField rightField targetLeftArguments
    targetRightArguments leftRuntime rightRuntime tag hvalid hfree hnormal
    hobject hfuel hspineValid hsupport hcontextReady hnonempty
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_contextReady_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size selectionSet + 1)
        parentType variableDefinitions selectionSet fuel parentType
        targetParent leftField rightField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime tag currentSelectionSet
        spine (by omega) hfuel hvalid hfree hnormal hspineValid
        hsupport hcontextReady with
    ⟨fields, errors, hresponse⟩
  exact
    responseData_not_semanticEquivalent_empty_object_of_valid_normal_object_nonempty_response
      schema
      (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
        (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          targetParent leftField rightField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime)
        targetParent leftField rightField targetLeftArguments
        targetRightArguments)
      variableValues (fuel + 1) parentType
      (projectionTargetResolverValue
        (.object parentType
          (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
            spine)))
      hobject hfree hnormal hnonempty hresponse

theorem
    responseData_empty_object_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_object_valid_normal_contextReady_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ variableDefinitions parentType currentSelectionSet
            (selectionSet : List Selection) fuel targetParent leftField
            rightField (targetLeftArguments targetRightArguments : List Argument)
            (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag),
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> SelectedFieldSpineRuntimeValid schema parentType parentType spine
          -> PathLocalSupportValidNormal schema parentType currentSelectionSet
          -> SelectedPathSelectionSetContextReady schema parentType parentType
              currentSelectionSet selectionSet
          -> selectionSet ≠ []
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.ResponseValue.object [])
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent leftField
                      rightField targetLeftArguments targetRightArguments
                      leftRuntime rightRuntime)
                    targetParent leftField rightField targetLeftArguments
                    targetRightArguments)
                  variableValues (fuel + 1) parentType
                  (projectionTargetResolverValue
                    (.object parentType
                      (FieldPairSelectedPathProbeRef.target tag
                        currentSelectionSet spine)))
                  selectionSet).data := by
  intro hschema variableDefinitions parentType currentSelectionSet
    selectionSet fuel targetParent leftField rightField targetLeftArguments
    targetRightArguments leftRuntime rightRuntime tag hvalid hfree hnormal
    hobject hfuel hspineValid hsupport hcontextReady hnonempty
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_contextReady_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size selectionSet + 1)
        parentType variableDefinitions selectionSet fuel parentType
        targetParent leftField rightField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime tag currentSelectionSet
        spine (by omega) hfuel hvalid hfree hnormal hspineValid
        hsupport hcontextReady with
    ⟨fields, errors, hresponse⟩
  exact
    responseData_empty_object_not_semanticEquivalent_of_valid_normal_object_nonempty_response
      schema
      (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
        (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          targetParent leftField rightField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime)
        targetParent leftField rightField targetLeftArguments
        targetRightArguments)
      variableValues (fuel + 1) parentType
      (projectionTargetResolverValue
        (.object parentType
          (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
            spine)))
      hobject hfree hnormal hnonempty hresponse

theorem
    selectedPathSelectionSetsResponseDataDiff_of_right_abstract_missing_runtime_left_object_nonempty
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {leftVariableDefinitions : List VariableDefinition} {leftFuel rightFuel : Nat}
    {leftParentType rightParentType rightRuntimeType targetParent leftField rightField
      : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {left right : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = false
      -> schema.typeIncludesObjectBool rightParentType rightRuntimeType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType leftParentType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType rightRuntimeType rightSpine
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> SelectedPathSelectionSetContextReady schema leftParentType
          leftParentType leftCurrentSelectionSet left
      -> left ≠ []
      -> rightRuntimeType ∉ right.filterMap inlineFragmentTypeCondition?
      -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftParentType rightRuntimeType targetParent
          leftField rightField targetLeftArguments targetRightArguments
          leftRuntime rightRuntime leftCurrentSelectionSet
          rightCurrentSelectionSet leftSpine rightSpine left right := by
  intro hschema hleftValid hleftFree hrightFree hleftNormal hrightNormal
    hleftObject hrightNonObject hrightInclude hleftFuel hleftSpineValid
    hrightSpineValid hleftSupport hleftContextReady hleftNonempty
    hrightMissing
  have hleftNotEmpty :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftField
              rightField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField targetLeftArguments
            targetRightArguments)
          variableValues (leftFuel + 1) leftParentType
          (projectionTargetResolverValue
            (.object leftParentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftCurrentSelectionSet leftSpine)))
          left).data
        (Execution.ResponseValue.object []) :=
    responseData_not_semanticEquivalent_empty_object_of_fieldPairOrDeepSuccess_selectedPathProbe_object_valid_normal_contextReady_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      leftSpine variableValues hschema leftVariableDefinitions
      leftParentType leftCurrentSelectionSet left leftFuel targetParent
      leftField rightField targetLeftArguments targetRightArguments
      leftRuntime rightRuntime FieldPairProbeTag.left hleftValid hleftFree
      hleftNormal hleftObject hleftFuel hleftSpineValid hleftSupport
      hleftContextReady hleftNonempty
  exact
    selectedPathSelectionSetsResponseDataDiff_of_right_abstract_missing_runtime
      (schema := schema) (rootSelectionSet := rootSelectionSet)
      (leftInitialSelectionSet := leftInitialSelectionSet)
      (rightInitialSelectionSet := rightInitialSelectionSet)
      (leftInitialSpine := leftInitialSpine)
      (rightInitialSpine := rightInitialSpine)
      (leftSpine := leftSpine) (rightSpine := rightSpine)
      (variableValues := variableValues) (leftFuel := leftFuel)
      (rightFuel := rightFuel) (leftParentType := leftParentType)
      (rightParentType := rightParentType)
      (leftRuntimeType := leftParentType)
      (rightRuntimeType := rightRuntimeType)
      (targetParent := targetParent) (leftField := leftField)
      (rightField := rightField)
      (targetLeftArguments := targetLeftArguments)
      (targetRightArguments := targetRightArguments)
      (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
      (leftCurrentSelectionSet := leftCurrentSelectionSet)
      (rightCurrentSelectionSet := rightCurrentSelectionSet)
      (left := left) (right := right)
      (typeIncludesObjectBool_self_of_objectTypeNameBool schema
        hleftObject)
      hrightInclude hleftSpineValid hrightSpineValid hrightNonObject
      hrightFree hrightNormal hrightMissing hleftNotEmpty

theorem
    selectedPathSelectionSetsResponseDataDiff_of_left_abstract_missing_runtime_right_object_nonempty
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {rightVariableDefinitions : List VariableDefinition} {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntimeType targetParent leftField rightField
      : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {left right : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = false
      -> objectTypeNameBool schema rightParentType = true
      -> schema.typeIncludesObjectBool leftParentType leftRuntimeType = true
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType leftRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType rightParentType rightSpine
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> SelectedPathSelectionSetContextReady schema rightParentType
          rightParentType rightCurrentSelectionSet right
      -> right ≠ []
      -> leftRuntimeType ∉ left.filterMap inlineFragmentTypeCondition?
      -> SelectedPathSelectionSetsResponseDataDiff schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine variableValues leftFuel rightFuel leftParentType
          rightParentType leftRuntimeType rightParentType targetParent
          leftField rightField targetLeftArguments targetRightArguments
          leftRuntime rightRuntime leftCurrentSelectionSet
          rightCurrentSelectionSet leftSpine rightSpine left right := by
  intro hschema hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftNonObject hrightObject hleftInclude hrightFuel
    hleftSpineValid hrightSpineValid hrightSupport hrightContextReady
    hrightNonempty hleftMissing
  have hrightNotEmpty :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object [])
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftField
              rightField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField targetLeftArguments
            targetRightArguments)
          variableValues (rightFuel + 1) rightParentType
          (projectionTargetResolverValue
            (.object rightParentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet rightSpine)))
          right).data :=
    responseData_empty_object_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_object_valid_normal_contextReady_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      rightSpine variableValues hschema rightVariableDefinitions
      rightParentType rightCurrentSelectionSet right rightFuel targetParent
      leftField rightField targetLeftArguments targetRightArguments
      leftRuntime rightRuntime FieldPairProbeTag.right hrightValid
      hrightFree hrightNormal hrightObject hrightFuel hrightSpineValid
      hrightSupport hrightContextReady hrightNonempty
  exact
    selectedPathSelectionSetsResponseDataDiff_of_left_abstract_missing_runtime
      (schema := schema) (rootSelectionSet := rootSelectionSet)
      (leftInitialSelectionSet := leftInitialSelectionSet)
      (rightInitialSelectionSet := rightInitialSelectionSet)
      (leftInitialSpine := leftInitialSpine)
      (rightInitialSpine := rightInitialSpine)
      (leftSpine := leftSpine) (rightSpine := rightSpine)
      (variableValues := variableValues) (leftFuel := leftFuel)
      (rightFuel := rightFuel) (leftParentType := leftParentType)
      (rightParentType := rightParentType)
      (leftRuntimeType := leftRuntimeType)
      (rightRuntimeType := rightParentType)
      (targetParent := targetParent) (leftField := leftField)
      (rightField := rightField)
      (targetLeftArguments := targetLeftArguments)
      (targetRightArguments := targetRightArguments)
      (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
      (leftCurrentSelectionSet := leftCurrentSelectionSet)
      (rightCurrentSelectionSet := rightCurrentSelectionSet)
      (left := left) (right := right)
      hleftInclude
      (typeIncludesObjectBool_self_of_objectTypeNameBool schema
        hrightObject)
      hleftSpineValid hrightSpineValid hleftNonObject hleftFree
      hleftNormal hleftMissing hrightNotEmpty

theorem selectedPathSelectionSetsResponseDataDiffRightPruned_of_left_object_nonempty
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine leftSpine
      : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {leftVariableDefinitions : List VariableDefinition}
    {leftFuel rightFuel : Nat}
    {leftParentType rightParentType rightRuntimeType targetParent leftField rightField
      : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet : List Selection}
    {left right : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> selectionSetDirectiveFree left
      -> selectionSetNormal schema leftParentType left
      -> objectTypeNameBool schema leftParentType = true
      -> schema.typeIncludesObjectBool rightParentType rightRuntimeType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType leftParentType leftSpine
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> SelectedPathSelectionSetContextReady schema leftParentType
          leftParentType leftCurrentSelectionSet left
      -> left ≠ []
      -> SelectedPathSelectionSetsResponseDataDiffRightPruned schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues leftFuel
          rightFuel leftParentType rightParentType leftParentType
          rightRuntimeType targetParent leftField rightField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet leftSpine left right := by
  intro hschema hleftValid hleftFree hleftNormal hleftObject hrightInclude
    hleftFuel hleftSpineValid hleftSupport hleftContextReady
    hleftNonempty
  have hleftNotEmpty :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftField
              rightField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField targetLeftArguments
            targetRightArguments)
          variableValues (leftFuel + 1) leftParentType
          (projectionTargetResolverValue
            (.object leftParentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftCurrentSelectionSet leftSpine)))
          left).data
        (Execution.ResponseValue.object []) :=
    responseData_not_semanticEquivalent_empty_object_of_fieldPairOrDeepSuccess_selectedPathProbe_object_valid_normal_contextReady_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      leftSpine variableValues hschema leftVariableDefinitions
      leftParentType leftCurrentSelectionSet left leftFuel targetParent
      leftField rightField targetLeftArguments targetRightArguments
      leftRuntime rightRuntime FieldPairProbeTag.left hleftValid hleftFree
      hleftNormal hleftObject hleftFuel hleftSpineValid hleftSupport
      hleftContextReady hleftNonempty
  exact
    selectedPathSelectionSetsResponseDataDiffRightPruned_of_dataNot
      (schema := schema) (rootSelectionSet := rootSelectionSet)
      (leftInitialSelectionSet := leftInitialSelectionSet)
      (rightInitialSelectionSet := rightInitialSelectionSet)
      (leftInitialSpine := leftInitialSpine)
      (rightInitialSpine := rightInitialSpine)
      (variableValues := variableValues) (leftFuel := leftFuel)
      (rightFuel := rightFuel) (leftParentType := leftParentType)
      (rightParentType := rightParentType)
      (leftRuntimeType := leftParentType)
      (rightRuntimeType := rightRuntimeType)
      (targetParent := targetParent) (leftField := leftField)
      (rightField := rightField)
      (targetLeftArguments := targetLeftArguments)
      (targetRightArguments := targetRightArguments)
      (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
      (leftCurrentSelectionSet := leftCurrentSelectionSet)
      (leftSpine := leftSpine) (left := left) (right := right)
      (typeIncludesObjectBool_self_of_objectTypeNameBool schema
        hleftObject)
      hrightInclude hleftSpineValid hleftNotEmpty

theorem selectedPathSelectionSetsResponseDataDiffLeftPruned_of_right_object_nonempty
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine rightSpine
      : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {rightVariableDefinitions : List VariableDefinition}
    {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntimeType targetParent leftField rightField
      : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {rightCurrentSelectionSet : List Selection}
    {left right : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema rightParentType = true
      -> schema.typeIncludesObjectBool leftParentType leftRuntimeType = true
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> SelectedFieldSpineRuntimeValid schema rightParentType rightParentType rightSpine
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> SelectedPathSelectionSetContextReady schema rightParentType
          rightParentType rightCurrentSelectionSet right
      -> right ≠ []
      -> SelectedPathSelectionSetsResponseDataDiffLeftPruned schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues leftFuel
          rightFuel leftParentType rightParentType leftRuntimeType
          rightParentType targetParent leftField rightField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          rightCurrentSelectionSet rightSpine left right := by
  intro hschema hrightValid hrightFree hrightNormal hrightObject
    hleftInclude hrightFuel hrightSpineValid hrightSupport
    hrightContextReady hrightNonempty
  have hrightNotEmpty :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object [])
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftField
              rightField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField targetLeftArguments
            targetRightArguments)
          variableValues (rightFuel + 1) rightParentType
          (projectionTargetResolverValue
            (.object rightParentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet rightSpine)))
          right).data :=
    responseData_empty_object_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_object_valid_normal_contextReady_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      rightSpine variableValues hschema rightVariableDefinitions
      rightParentType rightCurrentSelectionSet right rightFuel targetParent
      leftField rightField targetLeftArguments targetRightArguments
      leftRuntime rightRuntime FieldPairProbeTag.right hrightValid
      hrightFree hrightNormal hrightObject hrightFuel hrightSpineValid
      hrightSupport hrightContextReady hrightNonempty
  exact
    selectedPathSelectionSetsResponseDataDiffLeftPruned_of_dataNot
      (schema := schema) (rootSelectionSet := rootSelectionSet)
      (leftInitialSelectionSet := leftInitialSelectionSet)
      (rightInitialSelectionSet := rightInitialSelectionSet)
      (leftInitialSpine := leftInitialSpine)
      (rightInitialSpine := rightInitialSpine)
      (variableValues := variableValues) (leftFuel := leftFuel)
      (rightFuel := rightFuel) (leftParentType := leftParentType)
      (rightParentType := rightParentType)
      (leftRuntimeType := leftRuntimeType)
      (rightRuntimeType := rightParentType)
      (targetParent := targetParent) (leftField := leftField)
      (rightField := rightField)
      (targetLeftArguments := targetLeftArguments)
      (targetRightArguments := targetRightArguments)
      (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
      (rightCurrentSelectionSet := rightCurrentSelectionSet)
      (rightSpine := rightSpine) (left := left) (right := right)
      hleftInclude
      (typeIncludesObjectBool_self_of_objectTypeNameBool schema
        hrightObject)
      hrightSpineValid hrightNotEmpty

theorem
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_abstract_missing_ok_of_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (targetLeftArguments targetRightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = false
      -> selectionSetDirectiveFree childSelectionSet
      -> selectionSetNormal schema fieldDefinition.outputType.namedType childSelectionSet
      -> selectedObservableFieldSpineNext? fieldName arguments spine = none
      -> abstractRuntimeForFieldHeadDeep? schema parentType fieldName arguments
            parentType currentSelectionSet
          = some runtimeType
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> runtimeType ∉ childSelectionSet.filterMap inlineFragmentTypeCondition?
      -> leafProbeFuel fieldDefinition.outputType + 1 ≤ fuel
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1)
              (projectionTargetResolverValue
                (.object sourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
              responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], fieldErrors)
          ∧ responseValue ≠ Execution.ResponseValue.null := by
  intro hlookup hcomposite hnonObject hchildFree hchildNormal
    hselectedNone hruntime hinclude hmissing hfuel
  let childFuel := fuel - leafProbeFuel fieldDefinition.outputType - 1
  have hchildFuelEq :
      childFuel + 1 = fuel - leafProbeFuel fieldDefinition.outputType := by
    dsimp [childFuel]
    omega
  have hchildResponseRaw :
      Execution.executeSelectionSetAsResponse schema
        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
          (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            targetParent leftField rightField targetLeftArguments
            targetRightArguments leftRuntime rightRuntime)
          targetParent leftField rightField targetLeftArguments
          targetRightArguments)
        variableValues (childFuel + 1) runtimeType
        (projectionTargetResolverValue
          (.object runtimeType
            (FieldPairSelectedPathProbeRef.target tag
              (fieldPairPathLocalNextSelectionSet schema parentType
                runtimeType fieldName arguments currentSelectionSet)
              [])))
        childSelectionSet =
      ({ data := Execution.ResponseValue.object [], errors := 0 } :
        Execution.Response) :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_missing_runtime_eq_empty
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet
      (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
        fieldName arguments currentSelectionSet)
      leftInitialSpine rightInitialSpine [] variableValues childFuel
      targetParent leftField rightField
      fieldDefinition.outputType.namedType runtimeType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime tag
      hnonObject hchildFree hchildNormal hmissing
  have hchildResponse :
      Execution.executeSelectionSetAsResponse schema
        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
          (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            targetParent leftField rightField targetLeftArguments
            targetRightArguments leftRuntime rightRuntime)
          targetParent leftField rightField targetLeftArguments
          targetRightArguments)
        variableValues
        (fuel - leafProbeFuel fieldDefinition.outputType) runtimeType
        (projectionTargetResolverValue
          (.object runtimeType
            (FieldPairSelectedPathProbeRef.target tag
              (fieldPairPathLocalNextSelectionSet schema parentType
                runtimeType fieldName arguments currentSelectionSet)
              [])))
        childSelectionSet =
      ({ data := Execution.ResponseValue.object [], errors := 0 } :
        Execution.Response) := by
    simpa [hchildFuelEq] using hchildResponseRaw
  exact
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_abstractFallback_ok_of_child_response
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet currentSelectionSet leftInitialSpine
      rightInitialSpine spine variableValues fuel targetParent leftField
      rightField parentType fieldName sourceRuntimeType responseName
      targetLeftArguments targetRightArguments arguments leftRuntime
      rightRuntime tag childSelectionSet fieldDefinition runtimeType []
      0 hlookup hcomposite hnonObject hselectedNone hruntime hinclude
      (by omega) hchildResponse

theorem compositeChildResponse_of_selectedPathFieldChildrenReady
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      currentSelectionSet selectionSet
      : List Selection}
    {leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {fuel : Nat} {targetParent leftField rightField parentType : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name} {tag : FieldPairProbeTag}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
        leftInitialSpine rightInitialSpine spine variableValues fuel
        targetParent leftField rightField parentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime tag selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> ∃ childRuntimeType childSpine responseFields childErrors,
          SelectedPathCompositeFieldChildSource schema parentType fieldName
            arguments currentSelectionSet spine fieldDefinition
            childRuntimeType childSpine
          ∧ schema.typeIncludesObjectBool
              fieldDefinition.outputType.namedType childRuntimeType
            = true
          ∧ leafProbeFuel fieldDefinition.outputType ≤ fuel
          ∧ Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField targetLeftArguments
                targetRightArguments)
              variableValues
              (fuel - leafProbeFuel fieldDefinition.outputType)
              childRuntimeType
              (projectionTargetResolverValue
                (.object childRuntimeType
                  (FieldPairSelectedPathProbeRef.target tag
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      childRuntimeType fieldName arguments currentSelectionSet)
                    childSpine)))
              childSelectionSet
            = ({
                  data := Execution.ResponseValue.object responseFields,
                  errors := childErrors
                }
                : Execution.Response) := by
  intro hready hmem hlookup hcomposite
  rcases hready responseName fieldName arguments directives
      childSelectionSet hmem with
    ⟨candidateDefinition, hcandidateLookup, hfuel, hcase⟩
  have hcandidateEq : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidateDefinition
  rcases hcase with hleaf | hcase
  · rw [hcomposite] at hleaf
    simp at hleaf
  rcases hcase with hselected | hcase
  · rcases hselected with
      ⟨childRuntimeType, tail, responseFields, childErrors, hselected,
        hruntimeCase, hinclude, hchildResponse⟩
    exact ⟨
      childRuntimeType,
      tail,
      responseFields,
      childErrors,
      Or.inl ⟨hselected, hruntimeCase⟩,
      hinclude,
      hfuel,
      hchildResponse
    ⟩
  rcases hcase with hobjectCase | habstractFallback
  · rcases hobjectCase with
      ⟨responseFields, childErrors, hobjectOutput, hchildResponse⟩
    exact ⟨
      fieldDefinition.outputType.namedType,
      selectedObservableFieldSpineTailForRuntime
        fieldDefinition.outputType.namedType fieldName arguments spine,
      responseFields,
      childErrors,
      Or.inr (Or.inl ⟨hobjectOutput, rfl, rfl⟩),
      typeIncludesObjectBool_self_of_objectTypeNameBool schema hobjectOutput,
      hfuel,
      hchildResponse
    ⟩
  · rcases habstractFallback with
      ⟨childRuntimeType, responseFields, childErrors, hcomposite,
        hnonObject, hselectedNone, hruntime, hinclude,
        hchildResponse⟩
    exact ⟨
      childRuntimeType,
      [],
      responseFields,
      childErrors,
      Or.inr (Or.inr ⟨hcomposite, hnonObject, hselectedNone, hruntime, rfl⟩),
      hinclude,
      hfuel,
      hchildResponse
    ⟩

end GroundTypeNormalization

end NormalForm

end GraphQL
