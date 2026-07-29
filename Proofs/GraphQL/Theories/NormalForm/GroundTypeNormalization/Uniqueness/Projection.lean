import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Probes

/-!
Projection resolver support for semantic-separation probes.

The projection resolver has three reference modes:

* `root` is the synthetic parent object used to project a selected field.
* `target` is the child object delegated back to an arbitrary base resolver.
* `filler` is used by deep-success fallback values for non-target sibling fields.

This first slice proves the target-mode execution bridge. Later separation lemmas
can combine it with object probes and sibling-success facts.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

inductive ProjectionResolverRef (ObjectRef : Type) where
  | root (ref : ObjectRef)
  | target (ref : ObjectRef)
  | filler

def projectionResolverValue {ObjectRef : Type}
    (wrap : ObjectRef -> ProjectionResolverRef ObjectRef)
    : Execution.ResolverValue ObjectRef
      -> Execution.ResolverValue (ProjectionResolverRef ObjectRef)
  | .null => .null
  | .scalar value => .scalar value
  | .object typeName ref => .object typeName (wrap ref)
  | .list values => .list (values.map (projectionResolverValue wrap))

def projectionRootResolverValue {ObjectRef : Type}
    : Execution.ResolverValue ObjectRef
      -> Execution.ResolverValue (ProjectionResolverRef ObjectRef) :=
  projectionResolverValue ProjectionResolverRef.root

def projectionTargetResolverValue {ObjectRef : Type}
    : Execution.ResolverValue ObjectRef
      -> Execution.ResolverValue (ProjectionResolverRef ObjectRef) :=
  projectionResolverValue ProjectionResolverRef.target

def projectionRootRef? {ObjectRef : Type}
    : ProjectionResolverRef ObjectRef -> Option ObjectRef
  | .root ref => some ref
  | .target _ref => none
  | .filler => none

def projectionTargetRef? {ObjectRef : Type}
    : ProjectionResolverRef ObjectRef -> Option ObjectRef
  | .root _ref => none
  | .target ref => some ref
  | .filler => none

def lowerProjectionResolverValue? {ObjectRef : Type}
    (unwrap : ProjectionResolverRef ObjectRef -> Option ObjectRef)
    : Execution.ResolverValue (ProjectionResolverRef ObjectRef)
      -> Option (Execution.ResolverValue ObjectRef)
  | .null => some .null
  | .scalar value => some (.scalar value)
  | .object typeName ref => (unwrap ref).map (.object typeName)
  | .list values =>
      (values.mapM (lowerProjectionResolverValue? unwrap)).map
        Execution.ResolverValue.list

mutual
  theorem lowerProjectionResolverValue?_projectionRootResolverValue {ObjectRef : Type}
      : ∀ value : Execution.ResolverValue ObjectRef,
          lowerProjectionResolverValue? projectionRootRef?
            (projectionRootResolverValue value)
          = some value
    | .null => by
        simp [projectionRootResolverValue, projectionResolverValue,
          lowerProjectionResolverValue?]
    | .scalar value => by
        simp [projectionRootResolverValue, projectionResolverValue,
          lowerProjectionResolverValue?]
    | .object typeName ref => by
        simp [projectionRootResolverValue, projectionResolverValue,
          lowerProjectionResolverValue?, projectionRootRef?]
    | .list values => by
        simpa [projectionRootResolverValue, projectionResolverValue,
          lowerProjectionResolverValue?, Function.comp_def] using
          lowerProjectionResolverValues?_map_projectionRootResolverValue
            values

  theorem lowerProjectionResolverValues?_map_projectionRootResolverValue
      {ObjectRef : Type}
      : ∀ values : List (Execution.ResolverValue ObjectRef),
          (values.map projectionRootResolverValue).mapM
            (lowerProjectionResolverValue? projectionRootRef?)
          = some values
    | [] => by
        simp
    | value :: rest => by
        simp [lowerProjectionResolverValue?_projectionRootResolverValue value,
          lowerProjectionResolverValues?_map_projectionRootResolverValue rest]
end

mutual
  theorem lowerProjectionResolverValue?_projectionTargetResolverValue {ObjectRef : Type}
      : ∀ value : Execution.ResolverValue ObjectRef,
          lowerProjectionResolverValue? projectionTargetRef?
            (projectionTargetResolverValue value)
          = some value
    | .null => by
        simp [projectionTargetResolverValue, projectionResolverValue,
          lowerProjectionResolverValue?]
    | .scalar value => by
        simp [projectionTargetResolverValue, projectionResolverValue,
          lowerProjectionResolverValue?]
    | .object typeName ref => by
        simp [projectionTargetResolverValue, projectionResolverValue,
          lowerProjectionResolverValue?, projectionTargetRef?]
    | .list values => by
        simpa [projectionTargetResolverValue, projectionResolverValue,
          lowerProjectionResolverValue?, Function.comp_def] using
          lowerProjectionResolverValues?_map_projectionTargetResolverValue
            values

  theorem lowerProjectionResolverValues?_map_projectionTargetResolverValue
      {ObjectRef : Type}
      : ∀ values : List (Execution.ResolverValue ObjectRef),
          (values.map projectionTargetResolverValue).mapM
            (lowerProjectionResolverValue? projectionTargetRef?)
          = some values
    | [] => by
        simp
    | value :: rest => by
        simp [lowerProjectionResolverValue?_projectionTargetResolverValue
            value,
          lowerProjectionResolverValues?_map_projectionTargetResolverValue
            rest]
end

mutual
  theorem lowerProjectionRoot_projectionTargetResolverValue_eq {ObjectRef : Type}
      : ∀ (value lowered : Execution.ResolverValue ObjectRef),
          lowerProjectionResolverValue? projectionRootRef?
              (projectionTargetResolverValue value)
            = some lowered
          -> lowered = value
    | .null, lowered, hroot => by
        simp [projectionTargetResolverValue, projectionResolverValue,
          lowerProjectionResolverValue?] at hroot
        exact hroot.symm
    | .scalar value, lowered, hroot => by
        simp [projectionTargetResolverValue, projectionResolverValue,
          lowerProjectionResolverValue?] at hroot
        exact hroot.symm
    | .object typeName ref, lowered, hroot => by
        simp [projectionTargetResolverValue, projectionResolverValue,
          lowerProjectionResolverValue?, projectionRootRef?] at hroot
    | .list values, lowered, hroot => by
        simp [projectionTargetResolverValue, projectionResolverValue,
          lowerProjectionResolverValue?] at hroot
        rcases hroot with ⟨loweredValues, hmap, hvalue⟩
        subst lowered
        have hmap' :
            (values.map projectionTargetResolverValue).mapM
                (lowerProjectionResolverValue? projectionRootRef?) =
              some loweredValues := by
          simpa [projectionTargetResolverValue, Function.comp_def] using hmap
        have hvalues :
            loweredValues = values :=
          lowerProjectionRoot_projectionTargetResolverValues_eq values
            loweredValues hmap'
        subst loweredValues
        rfl

  theorem lowerProjectionRoot_projectionTargetResolverValues_eq {ObjectRef : Type}
      : ∀ (values loweredValues : List (Execution.ResolverValue ObjectRef)),
          (values.map projectionTargetResolverValue).mapM
              (lowerProjectionResolverValue? projectionRootRef?)
            = some loweredValues
          -> loweredValues = values
    | [], loweredValues, hroot => by
        simp at hroot
        exact hroot
    | value :: rest, loweredValues, hroot => by
        cases hhead :
            lowerProjectionResolverValue? projectionRootRef?
              (projectionTargetResolverValue value) with
        | none =>
            simp [hhead] at hroot
        | some loweredHead =>
            cases htail :
                (rest.map projectionTargetResolverValue).mapM
                  (lowerProjectionResolverValue? projectionRootRef?) with
            | none =>
                simp [hhead, htail] at hroot
            | some loweredTail =>
                simp [hhead, htail] at hroot
                subst loweredValues
                have hheadEq :
                    loweredHead = value :=
                  lowerProjectionRoot_projectionTargetResolverValue_eq value
                    loweredHead hhead
                have htailEq :
                    loweredTail = rest :=
                  lowerProjectionRoot_projectionTargetResolverValues_eq rest
                    loweredTail htail
                subst loweredHead
                subst loweredTail
                rfl
end

theorem runtimeObjectType?_projectionResolverValue
    {ObjectRef : Type}
    (wrap : ObjectRef -> ProjectionResolverRef ObjectRef)
    (value : Execution.ResolverValue ObjectRef)
    : Execution.runtimeObjectType? (projectionResolverValue wrap value)
      = Execution.runtimeObjectType? value := by
  cases value <;> simp [projectionResolverValue,
    Execution.runtimeObjectType?]

theorem doesFragmentTypeApplyBool_projectionResolverValue
    {ObjectRef : Type} (schema : Schema) (parentType typeCondition : Name)
    (wrap : ObjectRef -> ProjectionResolverRef ObjectRef)
    (source : Execution.ResolverValue ObjectRef)
    : Execution.doesFragmentTypeApplyBool schema parentType
        (projectionResolverValue wrap source) typeCondition
      = Execution.doesFragmentTypeApplyBool schema parentType source typeCondition := by
  simp [Execution.doesFragmentTypeApplyBool,
    runtimeObjectType?_projectionResolverValue]

mutual
  theorem collectSelection_projectionResolverValue
      {ObjectRef : Type} (schema : Schema)
      (variableValues : Execution.VariableValues)
      (wrap : ObjectRef -> ProjectionResolverRef ObjectRef)
      : ∀ (parentType : Name) (source : Execution.ResolverValue ObjectRef)
            (selection : Selection),
          Execution.collectSelection schema variableValues parentType
            (projectionResolverValue wrap source) selection
          = Execution.collectSelection schema variableValues parentType source selection
    | parentType, source,
      .field responseName fieldName arguments directives selectionSet => by
        simp [Execution.collectSelection]
    | parentType, source, .inlineFragment none directives selectionSet => by
        by_cases hallow :
            Execution.selectionDirectivesAllowBool variableValues directives
              = true
        · simp [Execution.collectSelection, hallow,
            collectFields_projectionResolverValue schema variableValues wrap
              parentType source selectionSet]
        · have hallowFalse :
              Execution.selectionDirectivesAllowBool variableValues directives
                = false := by
            cases h :
                Execution.selectionDirectivesAllowBool variableValues
                  directives
            · rfl
            · contradiction
          simp [Execution.collectSelection, hallowFalse]
    | parentType, source, .inlineFragment (some typeCondition) directives
        selectionSet => by
        by_cases hallow :
            Execution.selectionDirectivesAllowBool variableValues directives
              = true
        · by_cases happly :
              Execution.doesFragmentTypeApplyBool schema parentType source
                typeCondition = true
          · have happlyProjected :
                Execution.doesFragmentTypeApplyBool schema parentType
                  (projectionResolverValue wrap source) typeCondition =
                    true := by
              simpa [doesFragmentTypeApplyBool_projectionResolverValue]
                using happly
            simp [Execution.collectSelection, hallow, happly,
              happlyProjected,
              collectFields_projectionResolverValue schema variableValues wrap
                parentType source selectionSet]
          · have happlyFalse :
                Execution.doesFragmentTypeApplyBool schema parentType source
                  typeCondition = false := by
              cases h :
                  Execution.doesFragmentTypeApplyBool schema parentType source
                    typeCondition
              · rfl
              · contradiction
            have happlyProjectedFalse :
                Execution.doesFragmentTypeApplyBool schema parentType
                  (projectionResolverValue wrap source) typeCondition =
                    false := by
              simpa [doesFragmentTypeApplyBool_projectionResolverValue]
                using happlyFalse
            simp [Execution.collectSelection, hallow, happlyFalse,
              happlyProjectedFalse]
        · have hallowFalse :
              Execution.selectionDirectivesAllowBool variableValues directives
                = false := by
            cases h :
                Execution.selectionDirectivesAllowBool variableValues
                  directives
            · rfl
            · contradiction
          simp [Execution.collectSelection, hallowFalse]

  theorem collectFields_projectionResolverValue
      {ObjectRef : Type} (schema : Schema)
      (variableValues : Execution.VariableValues)
      (wrap : ObjectRef -> ProjectionResolverRef ObjectRef)
      : ∀ (parentType : Name) (source : Execution.ResolverValue ObjectRef)
            (selectionSet : List Selection),
          Execution.collectFields schema variableValues parentType
            (projectionResolverValue wrap source) selectionSet
          = Execution.collectFields schema variableValues parentType source selectionSet
    | parentType, source, [] => by
        simp [Execution.collectFields]
    | parentType, source, selection :: rest => by
        simp [Execution.collectFields,
          collectSelection_projectionResolverValue schema variableValues wrap
            parentType source selection,
          collectFields_projectionResolverValue schema variableValues wrap
            parentType source rest]

  theorem collectSubfields_projectionResolverValue
      {ObjectRef : Type} (schema : Schema)
      (variableValues : Execution.VariableValues)
      (wrap : ObjectRef -> ProjectionResolverRef ObjectRef)
      : ∀ (objectType : Name) (source : Execution.ResolverValue ObjectRef)
            (fields : List Execution.ExecutableField),
          Execution.collectSubfields schema variableValues objectType
            (projectionResolverValue wrap source) fields
          = Execution.collectSubfields schema variableValues objectType source fields
    | objectType, source, [] => by
        simp [Execution.collectSubfields]
    | objectType, source, field :: fields => by
        simp [Execution.collectSubfields,
          collectFields_projectionResolverValue schema variableValues wrap
            objectType source field.selectionSet,
          collectFields_projectionResolverValue schema variableValues wrap
            objectType source (Execution.mergedFieldSelectionSet fields)]
end

theorem collectFields_projectionTargetResolverValue
    {ObjectRef : Type} (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : Execution.collectFields schema variableValues parentType
        (projectionTargetResolverValue source) selectionSet
      = Execution.collectFields schema variableValues parentType source selectionSet := by
  simpa [projectionTargetResolverValue] using
    collectFields_projectionResolverValue schema variableValues
      ProjectionResolverRef.target parentType source selectionSet

def fieldPairProjectionTarget
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (parentType fieldName : Name) (arguments : List Argument)
    : Prop :=
  parentType = targetParent
  ∧ ((fieldName = leftField ∧ Argument.argumentsEquivalent arguments leftArguments)
      ∨ (fieldName = rightField ∧ Argument.argumentsEquivalent arguments rightArguments))

theorem fieldPairProjectionTarget_iff_of_argumentsEquivalent
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (parentType fieldName : Name)
    (firstArguments laterArguments : List Argument)
    : Argument.argumentsEquivalent firstArguments laterArguments
      -> (fieldPairProjectionTarget targetParent leftField rightField
            leftArguments rightArguments parentType fieldName firstArguments
          ↔ fieldPairProjectionTarget targetParent leftField rightField
              leftArguments rightArguments parentType fieldName laterArguments) := by
  intro harguments
  have hleftIff :
      Argument.argumentsEquivalent firstArguments leftArguments
        ↔ Argument.argumentsEquivalent laterArguments leftArguments := by
    constructor
    · intro hfirst
      exact argumentsEquivalent_trans
        (FieldMerge.argumentsEquivalent_symm harguments) hfirst
    · intro hlater
      exact argumentsEquivalent_trans harguments hlater
  have hrightIff :
      Argument.argumentsEquivalent firstArguments rightArguments
        ↔ Argument.argumentsEquivalent laterArguments rightArguments := by
    constructor
    · intro hfirst
      exact argumentsEquivalent_trans
        (FieldMerge.argumentsEquivalent_symm harguments) hfirst
    · intro hlater
      exact argumentsEquivalent_trans harguments hlater
  constructor
  · intro htarget
    rcases htarget with ⟨hparent, hfield⟩
    refine ⟨hparent, ?_⟩
    rcases hfield with hleft | hright
    · exact Or.inl ⟨hleft.1, hleftIff.mp hleft.2⟩
    · exact Or.inr ⟨hright.1, hrightIff.mp hright.2⟩
  · intro htarget
    rcases htarget with ⟨hparent, hfield⟩
    refine ⟨hparent, ?_⟩
    rcases hfield with hleft | hright
    · exact Or.inl ⟨hleft.1, hleftIff.mpr hleft.2⟩
    · exact Or.inr ⟨hright.1, hrightIff.mpr hright.2⟩

noncomputable def fieldPairOrDeepSuccessResolvers {ObjectRef : Type}
    (schema : Schema) (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    : Execution.Resolvers (ProjectionResolverRef ObjectRef) where
  resolve parentType fieldName arguments source := by
    classical
    let success :=
      deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
        (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef)
    let delegateTarget :=
      match lowerProjectionResolverValue? projectionTargetRef? source with
      | some lowered =>
          (base.resolve parentType fieldName arguments lowered).map
            projectionTargetResolverValue
      | none => success.resolve parentType fieldName arguments source
    exact
      if fieldPairProjectionTarget targetParent leftField rightField
          leftArguments rightArguments parentType fieldName arguments then
        match lowerProjectionResolverValue? projectionRootRef? source with
        | some lowered =>
            (base.resolve parentType fieldName arguments lowered).map
              projectionTargetResolverValue
        | none => delegateTarget
      else
        delegateTarget
  resolve_argumentsEquivalent := by
    classical
    intro parentType fieldName firstArguments laterArguments source
      harguments
    let success :=
      deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
        (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef)
    let firstDelegateTarget :=
      match lowerProjectionResolverValue? projectionTargetRef? source with
      | some lowered =>
          (base.resolve parentType fieldName firstArguments lowered).map
            projectionTargetResolverValue
      | none => success.resolve parentType fieldName firstArguments source
    let laterDelegateTarget :=
      match lowerProjectionResolverValue? projectionTargetRef? source with
      | some lowered =>
          (base.resolve parentType fieldName laterArguments lowered).map
            projectionTargetResolverValue
      | none => success.resolve parentType fieldName laterArguments source
    have htargetIff :=
      fieldPairProjectionTarget_iff_of_argumentsEquivalent targetParent
        leftField rightField leftArguments rightArguments parentType
        fieldName firstArguments laterArguments harguments
    have hdelegateTarget : firstDelegateTarget = laterDelegateTarget := by
      cases hlower :
          lowerProjectionResolverValue? projectionTargetRef? source with
      | none =>
          simp [firstDelegateTarget, laterDelegateTarget, hlower,
            success.resolve_argumentsEquivalent parentType fieldName
              firstArguments laterArguments source harguments]
      | some lowered =>
          simp [firstDelegateTarget, laterDelegateTarget, hlower,
            base.resolve_argumentsEquivalent parentType fieldName
              firstArguments laterArguments lowered harguments]
    by_cases hfirst :
        fieldPairProjectionTarget targetParent leftField rightField
          leftArguments rightArguments parentType fieldName firstArguments
    · have hlater :
          fieldPairProjectionTarget targetParent leftField rightField
            leftArguments rightArguments parentType fieldName laterArguments :=
        htargetIff.mp hfirst
      cases hroot :
          lowerProjectionResolverValue? projectionRootRef? source with
      | none =>
          simp [success, firstDelegateTarget, laterDelegateTarget, hfirst,
            hlater, hdelegateTarget]
      | some lowered =>
          simp [hfirst, hlater,
            base.resolve_argumentsEquivalent parentType fieldName
              firstArguments laterArguments lowered harguments]
    · have hlater :
          ¬ fieldPairProjectionTarget targetParent leftField rightField
            leftArguments rightArguments parentType fieldName laterArguments := by
        intro hlater
        exact hfirst (htargetIff.mpr hlater)
      simp [success, firstDelegateTarget, laterDelegateTarget, hfirst,
        hlater, hdelegateTarget]

theorem fieldPairOrDeepSuccessResolvers_left_root
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments arguments : List Argument)
    (source : Execution.ResolverValue ObjectRef)
    : Argument.argumentsEquivalent arguments leftArguments
      -> (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
            targetParent leftField rightField leftArguments rightArguments).resolve
            targetParent leftField arguments (projectionRootResolverValue source)
          = (base.resolve targetParent leftField arguments source).map
              projectionTargetResolverValue := by
  intro harguments
  classical
  have htarget :
      fieldPairProjectionTarget targetParent leftField rightField
        leftArguments rightArguments targetParent leftField arguments := by
    exact ⟨rfl, Or.inl ⟨rfl, harguments⟩⟩
  simp [fieldPairOrDeepSuccessResolvers, htarget,
    lowerProjectionResolverValue?_projectionRootResolverValue]

theorem fieldPairOrDeepSuccessResolvers_right_root
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments arguments : List Argument)
    (source : Execution.ResolverValue ObjectRef)
    : Argument.argumentsEquivalent arguments rightArguments
      -> (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
            targetParent leftField rightField leftArguments rightArguments).resolve
            targetParent rightField arguments (projectionRootResolverValue source)
          = (base.resolve targetParent rightField arguments source).map
              projectionTargetResolverValue := by
  intro harguments
  classical
  have htarget :
      fieldPairProjectionTarget targetParent leftField rightField
        leftArguments rightArguments targetParent rightField arguments := by
    exact ⟨rfl, Or.inr ⟨rfl, harguments⟩⟩
  simp [fieldPairOrDeepSuccessResolvers, htarget,
    lowerProjectionResolverValue?_projectionRootResolverValue]

theorem fieldPairOrDeepSuccessResolvers_other_root
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef)
    (targetParent leftField rightField parentType fieldName runtimeType : Name)
    (leftArguments rightArguments arguments : List Argument)
    (ref : ObjectRef)
    : ¬ fieldPairProjectionTarget targetParent leftField rightField
          leftArguments rightArguments parentType fieldName arguments
      -> (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
            targetParent leftField rightField leftArguments rightArguments).resolve
            parentType fieldName arguments
            (.object runtimeType (ProjectionResolverRef.root ref))
          = (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
              (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef)).resolve
              parentType fieldName arguments
              (.object runtimeType (ProjectionResolverRef.root ref)) := by
  intro htarget
  classical
  simp [fieldPairOrDeepSuccessResolvers, htarget,
    lowerProjectionResolverValue?, projectionTargetRef?]

theorem fieldPairOrDeepSuccessResolvers_target
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef)
    (targetParent leftField rightField parentType fieldName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (source : Execution.ResolverValue ObjectRef)
    : (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
        targetParent leftField rightField leftArguments rightArguments).resolve
        parentType fieldName arguments (projectionTargetResolverValue source)
      = (base.resolve parentType fieldName arguments source).map
          projectionTargetResolverValue := by
  classical
  by_cases htarget :
      fieldPairProjectionTarget targetParent leftField rightField
        leftArguments rightArguments parentType fieldName arguments
  · cases hroot :
        lowerProjectionResolverValue? projectionRootRef?
          (projectionTargetResolverValue source) with
    | none =>
        simp [fieldPairOrDeepSuccessResolvers, htarget, hroot,
          lowerProjectionResolverValue?_projectionTargetResolverValue]
    | some lowered =>
        have hlowered : lowered = source :=
          lowerProjectionRoot_projectionTargetResolverValue_eq source
            lowered hroot
        subst lowered
        simp [fieldPairOrDeepSuccessResolvers, htarget, hroot]
  · simp [fieldPairOrDeepSuccessResolvers, htarget,
      lowerProjectionResolverValue?_projectionTargetResolverValue]

theorem fieldPairOrDeepSuccessResolvers_target_object
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef)
    (targetParent leftField rightField parentType fieldName runtimeType : Name)
    (leftArguments rightArguments arguments : List Argument)
    (ref : ObjectRef)
    : (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
        targetParent leftField rightField leftArguments rightArguments).resolve
        parentType fieldName arguments
        (.object runtimeType (ProjectionResolverRef.target ref))
      = (base.resolve parentType fieldName arguments (.object runtimeType ref)).map
          projectionTargetResolverValue := by
  classical
  by_cases htarget :
      fieldPairProjectionTarget targetParent leftField rightField
        leftArguments rightArguments parentType fieldName arguments
  · simp [fieldPairOrDeepSuccessResolvers, htarget,
      lowerProjectionResolverValue?, projectionRootRef?,
      projectionTargetRef?]
  · simp [fieldPairOrDeepSuccessResolvers, htarget,
      lowerProjectionResolverValue?, projectionTargetRef?]

theorem fieldPairOrDeepSuccessResolvers_filler_object
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef)
    (targetParent leftField rightField parentType fieldName runtimeType : Name)
    (leftArguments rightArguments arguments : List Argument)
    : (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
        targetParent leftField rightField leftArguments rightArguments).resolve
        parentType fieldName arguments
        (.object runtimeType
          (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef))
      = (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
          (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef)).resolve
          parentType fieldName arguments
          (.object runtimeType
            (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef)) := by
  classical
  by_cases htarget :
      fieldPairProjectionTarget targetParent leftField rightField
        leftArguments rightArguments parentType fieldName arguments
  · simp [fieldPairOrDeepSuccessResolvers, htarget,
      lowerProjectionResolverValue?, projectionRootRef?,
      projectionTargetRef?]
  · simp [fieldPairOrDeepSuccessResolvers, htarget,
      lowerProjectionResolverValue?, projectionTargetRef?]

mutual
  theorem
      executeCollectedFields_fieldPairOrDeepSuccessResolvers_filler_object_eq_deepSuccessWithRef
      {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
      (base : Execution.Resolvers ObjectRef) (variableValues : Execution.VariableValues)
      (targetParent leftField rightField : Name)
      (leftArguments rightArguments : List Argument)
      : ∀ (fuel : Nat) (runtimeType : Name)
            (fields : List (Name × List Execution.ExecutableField)),
          Execution.executeCollectedFields schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
              targetParent leftField rightField leftArguments rightArguments)
            variableValues fuel
            (.object runtimeType
              (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef))
            fields
          = Execution.executeCollectedFields schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef))
              variableValues fuel
              (.object runtimeType
                (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef))
              fields
    | fuel, runtimeType, [] => by
        simp [Execution.executeCollectedFields]
    | fuel, runtimeType, (responseName, fields) :: rest => by
        simp [Execution.executeCollectedFields,
          executeField_fieldPairOrDeepSuccessResolvers_filler_object_eq_deepSuccessWithRef
            schema rootSelectionSet base variableValues targetParent
            leftField rightField leftArguments rightArguments fuel
            runtimeType responseName fields,
          executeCollectedFields_fieldPairOrDeepSuccessResolvers_filler_object_eq_deepSuccessWithRef
            schema rootSelectionSet base variableValues targetParent
            leftField rightField leftArguments rightArguments fuel
            runtimeType rest]

  theorem executeField_fieldPairOrDeepSuccessResolvers_filler_object_eq_deepSuccessWithRef
      {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
      (base : Execution.Resolvers ObjectRef) (variableValues : Execution.VariableValues)
      (targetParent leftField rightField : Name)
      (leftArguments rightArguments : List Argument)
      : ∀ (fuel : Nat) (runtimeType responseName : Name)
            (fields : List Execution.ExecutableField),
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
              targetParent leftField rightField leftArguments rightArguments)
            variableValues fuel
            (.object runtimeType
              (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef))
            responseName fields
          = Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef))
              variableValues fuel
              (.object runtimeType
                (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef))
              responseName fields
    | fuel, runtimeType, responseName, [] => by
        simp [Execution.executeField]
    | 0, runtimeType, responseName, field :: fields => by
        simp [Execution.executeField]
    | fuel + 1, runtimeType, responseName, field :: fields => by
        cases hlookup : schema.lookupField field.parentType field.fieldName with
        | none =>
            simp [Execution.executeField, hlookup,
              deepSelectionSetSuccessResolversWithRef]
        | some fieldDefinition =>
            have hcomplete :=
              completeValue_fieldPairOrDeepSuccessResolvers_deepSuccessWithRef_value
                schema rootSelectionSet base variableValues targetParent
                leftField rightField leftArguments rightArguments fuel
                fieldDefinition.outputType (field :: fields)
                field.parentType field.fieldName
            simpa [Execution.executeField, hlookup,
              deepSelectionSetSuccessResolversWithRef,
              fieldPairOrDeepSuccessResolvers_filler_object schema
                rootSelectionSet base targetParent leftField rightField
                field.parentType field.fieldName runtimeType leftArguments
                rightArguments field.arguments] using
              congrArg (Execution.singleFieldResult responseName) hcomplete

  theorem completeValue_fieldPairOrDeepSuccessResolvers_deepSuccessWithRef_value
      {ObjectRef : Type} (schema : Schema)
      (rootSelectionSet : List Selection)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (targetParent leftField rightField : Name)
      (leftArguments rightArguments : List Argument)
      : ∀ (fuel : Nat) (fieldType : TypeRef)
            (fields : List Execution.ExecutableField)
            (parentType fieldName : Name),
          Execution.completeValue schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
              targetParent leftField rightField leftArguments rightArguments)
            variableValues fuel fieldType fields
            (deepSelectionSetSuccessResolverValueWithRef schema rootSelectionSet
              (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef)
              parentType fieldName fieldType)
          = Execution.completeValue schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef))
              variableValues fuel fieldType fields
              (deepSelectionSetSuccessResolverValueWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef)
                parentType fieldName fieldType)
    | 0, fieldType, fields, parentType, fieldName => by
        simp [Execution.completeValue, Execution.outOfFuel]
    | fuel + 1, .nonNull inner, fields, parentType, fieldName => by
        simp [Execution.completeValue,
          deepSelectionSetSuccessResolverValueWithRef,
          completeValue_fieldPairOrDeepSuccessResolvers_deepSuccessWithRef_value
            schema rootSelectionSet base variableValues targetParent
            leftField rightField leftArguments rightArguments (fuel + 1)
            inner fields parentType fieldName]
    | fuel + 1, .list inner, fields, parentType, fieldName => by
        simp [Execution.completeValue,
          deepSelectionSetSuccessResolverValueWithRef,
          Execution.completeValueList, Execution.catchBubbleAsNull]
    | fuel + 1, .named typeName, fields, parentType, fieldName => by
        by_cases hcomposite :
            (TypeRef.named typeName).isCompositeBool schema = true
        · by_cases hobject : objectTypeNameBool schema typeName = true
          · by_cases hinclude :
                schema.typeIncludesObjectBool typeName typeName = true
            · simp [Execution.completeValue,
                deepSelectionSetSuccessResolverValueWithRef, hcomposite,
                hobject, hinclude,
                executeCollectedFields_fieldPairOrDeepSuccessResolvers_filler_object_eq_deepSuccessWithRef
                  schema rootSelectionSet base variableValues targetParent
                  leftField rightField leftArguments rightArguments fuel
                  typeName]
            · have hincludeFalse :
                  schema.typeIncludesObjectBool typeName typeName = false := by
                cases h : schema.typeIncludesObjectBool typeName typeName
                · rfl
                · contradiction
              simp [Execution.completeValue,
                deepSelectionSetSuccessResolverValueWithRef, hcomposite,
                hobject, hincludeFalse]
          · have hobjectFalse :
                objectTypeNameBool schema typeName = false := by
              cases h : objectTypeNameBool schema typeName
              · rfl
              · contradiction
            cases hruntime :
                abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType rootSelectionSet with
            | none =>
                by_cases hinclude :
                    schema.typeIncludesObjectBool typeName typeName = true
                · simp [Execution.completeValue,
                    deepSelectionSetSuccessResolverValueWithRef, hcomposite,
                    hobjectFalse, hruntime, hinclude,
                    executeCollectedFields_fieldPairOrDeepSuccessResolvers_filler_object_eq_deepSuccessWithRef
                      schema rootSelectionSet base variableValues targetParent
                      leftField rightField leftArguments rightArguments fuel
                      typeName]
                · have hincludeFalse :
                      schema.typeIncludesObjectBool typeName typeName =
                        false := by
                    cases h : schema.typeIncludesObjectBool typeName typeName
                    · rfl
                    · contradiction
                  simp [Execution.completeValue,
                    deepSelectionSetSuccessResolverValueWithRef, hcomposite,
                    hobjectFalse, hruntime, hincludeFalse]
            | some runtimeType =>
                by_cases hinclude :
                    schema.typeIncludesObjectBool typeName runtimeType = true
                · simp [Execution.completeValue,
                    deepSelectionSetSuccessResolverValueWithRef, hcomposite,
                    hobjectFalse, hruntime, hinclude,
                    executeCollectedFields_fieldPairOrDeepSuccessResolvers_filler_object_eq_deepSuccessWithRef
                      schema rootSelectionSet base variableValues targetParent
                      leftField rightField leftArguments rightArguments fuel
                      runtimeType]
                · have hincludeFalse :
                      schema.typeIncludesObjectBool typeName runtimeType =
                        false := by
                    cases h :
                        schema.typeIncludesObjectBool typeName runtimeType
                    · rfl
                    · contradiction
                  simp [Execution.completeValue,
                    deepSelectionSetSuccessResolverValueWithRef, hcomposite,
                    hobjectFalse, hruntime, hincludeFalse]
        · have hcompositeFalse :
              (TypeRef.named typeName).isCompositeBool schema = false := by
            cases h : (TypeRef.named typeName).isCompositeBool schema
            · rfl
            · contradiction
          simp [Execution.completeValue,
            deepSelectionSetSuccessResolverValueWithRef, hcompositeFalse]
end

theorem executeField_fieldPairOrDeepSuccessResolvers_other_root_eq_deepSuccessWithRef
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (targetParent leftField rightField parentType fieldName runtimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (ref : ObjectRef) (childSelectionSet : List Selection)
    : ¬ fieldPairProjectionTarget targetParent leftField rightField
          leftArguments rightArguments parentType fieldName arguments
      -> ∀ fuel,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
              targetParent leftField rightField leftArguments rightArguments)
            variableValues fuel
            (.object runtimeType (ProjectionResolverRef.root ref))
            responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler : ProjectionResolverRef ObjectRef))
              variableValues fuel
              (.object runtimeType (ProjectionResolverRef.root ref))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }] := by
  intro htarget fuel
  cases fuel with
  | zero =>
      simp [Execution.executeField]
  | succ fuel =>
      cases hlookup : schema.lookupField parentType fieldName with
      | none =>
          simp [Execution.executeField, hlookup,
            deepSelectionSetSuccessResolversWithRef]
      | some fieldDefinition =>
          have hcomplete :=
            completeValue_fieldPairOrDeepSuccessResolvers_deepSuccessWithRef_value
              schema rootSelectionSet base variableValues targetParent
              leftField rightField leftArguments rightArguments fuel
              fieldDefinition.outputType
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
              parentType fieldName
          simpa [Execution.executeField, hlookup,
            deepSelectionSetSuccessResolversWithRef,
            fieldPairOrDeepSuccessResolvers_other_root schema
              rootSelectionSet base targetParent leftField rightField
              parentType fieldName runtimeType leftArguments rightArguments
              arguments ref htarget] using
            congrArg (Execution.singleFieldResult responseName) hcomplete

mutual
  theorem
      executeCollectedFields_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
      (base : Execution.Resolvers ObjectRef) (variableValues : Execution.VariableValues)
      (targetParent leftField rightField : Name)
      (leftArguments rightArguments : List Argument)
      : ∀ (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
            (fields : List (Name × List Execution.ExecutableField)),
          Execution.executeCollectedFields schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
              targetParent leftField rightField leftArguments rightArguments)
            variableValues fuel (projectionTargetResolverValue source) fields
          = Execution.executeCollectedFields schema base variableValues fuel source fields
    | fuel, source, [] => by
        simp [Execution.executeCollectedFields]
    | fuel, source, (responseName, fields) :: rest => by
        simp [Execution.executeCollectedFields,
          executeField_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
            schema rootSelectionSet base variableValues targetParent leftField
            rightField leftArguments rightArguments fuel source responseName
            fields,
          executeCollectedFields_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
            schema rootSelectionSet base variableValues targetParent leftField
            rightField leftArguments rightArguments fuel source rest]

  theorem executeField_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      {ObjectRef : Type} (schema : Schema)
      (rootSelectionSet : List Selection)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (targetParent leftField rightField : Name)
      (leftArguments rightArguments : List Argument)
      : ∀ (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
            (responseName : Name) (fields : List Execution.ExecutableField),
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
              targetParent leftField rightField leftArguments rightArguments)
            variableValues fuel (projectionTargetResolverValue source)
            responseName fields
          = Execution.executeField schema base variableValues fuel source
              responseName fields
    | fuel, source, responseName, [] => by
        simp [Execution.executeField]
    | 0, source, responseName, field :: fields => by
        simp [Execution.executeField]
    | fuel + 1, source, responseName, field :: fields => by
        cases hlookup : schema.lookupField field.parentType field.fieldName with
        | none =>
            simp [Execution.executeField, hlookup]
        | some fieldDefinition =>
            cases hresolve :
                base.resolve field.parentType field.fieldName field.arguments
                  source with
            | none =>
                simp [Execution.executeField, hlookup,
                  fieldPairOrDeepSuccessResolvers_target schema
                    rootSelectionSet base targetParent leftField rightField
                    field.parentType field.fieldName leftArguments
                    rightArguments field.arguments source,
                  hresolve]
            | some resolved =>
                simp [Execution.executeField, hlookup,
                  fieldPairOrDeepSuccessResolvers_target schema
                    rootSelectionSet base targetParent leftField rightField
                    field.parentType field.fieldName leftArguments
                    rightArguments field.arguments source,
                  hresolve,
                  completeValue_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
                    schema rootSelectionSet base variableValues targetParent
                    leftField rightField leftArguments rightArguments fuel
                    fieldDefinition.outputType (field :: fields) resolved]

  theorem completeValue_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      {ObjectRef : Type} (schema : Schema)
      (rootSelectionSet : List Selection)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (targetParent leftField rightField : Name)
      (leftArguments rightArguments : List Argument)
      : ∀ (fuel : Nat) (fieldType : TypeRef)
            (fields : List Execution.ExecutableField)
            (value : Execution.ResolverValue ObjectRef),
          Execution.completeValue schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
              targetParent leftField rightField leftArguments rightArguments)
            variableValues fuel fieldType fields
            (projectionTargetResolverValue value)
          = Execution.completeValue schema base variableValues fuel fieldType fields value
    | 0, fieldType, fields, value => by
        simp [Execution.completeValue, Execution.outOfFuel]
    | fuel + 1, .nonNull inner, fields, value => by
        simp [Execution.completeValue,
          completeValue_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
            schema rootSelectionSet base variableValues targetParent leftField
            rightField leftArguments rightArguments (fuel + 1) inner fields
            value]
    | fuel + 1, .named typeName, fields, .null => by
        simp [projectionTargetResolverValue, projectionResolverValue,
          Execution.completeValue]
    | fuel + 1, .named typeName, fields, .scalar value => by
        simp [projectionTargetResolverValue, projectionResolverValue,
          Execution.completeValue]
    | fuel + 1, .named typeName, fields, .object runtimeType ref => by
        by_cases hinclude :
            schema.typeIncludesObjectBool typeName runtimeType = true
        · simp [projectionTargetResolverValue, projectionResolverValue,
            Execution.completeValue, hinclude]
          have hcollect :
              Execution.collectFields schema variableValues runtimeType
                (Execution.ResolverValue.object runtimeType
                  (ProjectionResolverRef.target ref))
                (Execution.mergedFieldSelectionSet fields)
              =
              Execution.collectFields schema variableValues runtimeType
                (Execution.ResolverValue.object runtimeType ref)
                (Execution.mergedFieldSelectionSet fields) := by
            simpa [projectionTargetResolverValue, projectionResolverValue]
              using
              collectFields_projectionTargetResolverValue schema
                variableValues runtimeType
                (Execution.ResolverValue.object runtimeType ref)
                (Execution.mergedFieldSelectionSet fields)
          rw [hcollect]
          have hexecute :
              Execution.executeCollectedFields schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
                  targetParent leftField rightField leftArguments
                  rightArguments)
                variableValues fuel
                (Execution.ResolverValue.object runtimeType
                  (ProjectionResolverRef.target ref))
                (Execution.collectFields schema variableValues runtimeType
                  (Execution.ResolverValue.object runtimeType ref)
                  (Execution.mergedFieldSelectionSet fields))
              =
              Execution.executeCollectedFields schema base variableValues fuel
                (Execution.ResolverValue.object runtimeType ref)
                (Execution.collectFields schema variableValues runtimeType
                  (Execution.ResolverValue.object runtimeType ref)
                  (Execution.mergedFieldSelectionSet fields)) := by
            simpa [projectionTargetResolverValue, projectionResolverValue]
              using
              executeCollectedFields_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
                schema rootSelectionSet base variableValues targetParent
                leftField rightField leftArguments rightArguments fuel
                (Execution.ResolverValue.object runtimeType ref)
                (Execution.collectFields schema variableValues runtimeType
                  (Execution.ResolverValue.object runtimeType ref)
                  (Execution.mergedFieldSelectionSet fields))
          rw [hexecute]
        · have hincludeFalse :
              schema.typeIncludesObjectBool typeName runtimeType = false := by
            cases h : schema.typeIncludesObjectBool typeName runtimeType
            · rfl
            · contradiction
          simp [projectionTargetResolverValue, projectionResolverValue,
            Execution.completeValue, hincludeFalse]
    | fuel + 1, .named typeName, fields, .list values => by
        simp [projectionTargetResolverValue, projectionResolverValue,
          Execution.completeValue]
    | fuel + 1, .list inner, fields, .null => by
        simp [projectionTargetResolverValue, projectionResolverValue,
          Execution.completeValue]
    | fuel + 1, .list inner, fields, .scalar value => by
        simp [projectionTargetResolverValue, projectionResolverValue,
          Execution.completeValue]
    | fuel + 1, .list inner, fields, .object runtimeType ref => by
        simp [projectionTargetResolverValue, projectionResolverValue,
          Execution.completeValue]
    | fuel + 1, .list inner, fields, .list values => by
        have hlist :=
          completeValueList_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
            schema rootSelectionSet base variableValues targetParent leftField
            rightField leftArguments rightArguments fuel inner fields values
        simpa [projectionTargetResolverValue, projectionResolverValue,
          Execution.completeValue] using
          congrArg
            (Execution.catchBubbleAsNull Execution.ResponseValue.list)
            hlist

  theorem completeValueList_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
      (base : Execution.Resolvers ObjectRef) (variableValues : Execution.VariableValues)
      (targetParent leftField rightField : Name)
      (leftArguments rightArguments : List Argument)
      : ∀ (fuel : Nat) (itemType : TypeRef)
            (fields : List Execution.ExecutableField)
            (values : List (Execution.ResolverValue ObjectRef)),
          Execution.completeValueList schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
              targetParent leftField rightField leftArguments rightArguments)
            variableValues fuel itemType fields
            (values.map projectionTargetResolverValue)
          = Execution.completeValueList schema base variableValues fuel itemType
              fields values
    | fuel, itemType, fields, [] => by
        simp [Execution.completeValueList]
    | fuel, itemType, fields, value :: values => by
        simp [Execution.completeValueList,
          completeValue_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
            schema rootSelectionSet base variableValues targetParent leftField
            rightField leftArguments rightArguments fuel itemType fields value,
          completeValueList_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
            schema rootSelectionSet base variableValues targetParent leftField
            rightField leftArguments rightArguments fuel itemType fields
            values]
end

theorem executeSelectionSet_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef) (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef) (selectionSet : List Selection)
    : Execution.executeSelectionSet schema
        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
          targetParent leftField rightField leftArguments rightArguments)
        variableValues fuel parentType (projectionTargetResolverValue source)
        selectionSet
      = Execution.executeSelectionSet schema base variableValues fuel parentType
          source selectionSet := by
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
  rw [collectFields_projectionTargetResolverValue schema variableValues
    parentType source selectionSet]
  exact
    executeCollectedFields_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet base variableValues targetParent leftField
      rightField leftArguments rightArguments fuel source
      (Execution.collectFields schema variableValues parentType source
        selectionSet)

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef) (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef) (selectionSet : List Selection)
    : Execution.executeSelectionSetAsResponse schema
        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
          targetParent leftField rightField leftArguments rightArguments)
        variableValues fuel parentType (projectionTargetResolverValue source)
        selectionSet
      = Execution.executeSelectionSetAsResponse schema base variableValues fuel
          parentType source selectionSet := by
  simp [Execution.executeSelectionSetAsResponse,
    executeSelectionSet_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet base variableValues fuel targetParent leftField
      rightField leftArguments rightArguments parentType source selectionSet]

theorem executeField_fieldPairOrDeepSuccessResolvers_left_root
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (source : Execution.ResolverValue ObjectRef)
    (childSelectionSet : List Selection)
    : Argument.argumentsEquivalent arguments leftArguments
      -> ∀ fuel,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
              targetParent leftField rightField leftArguments rightArguments)
            variableValues fuel (projectionRootResolverValue source) responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := leftField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.executeField schema base variableValues fuel source
              responseName
              [{
                parentType := targetParent
                responseName := responseName
                fieldName := leftField
                arguments := arguments
                selectionSet := childSelectionSet
              }] := by
  intro harguments
  intro fuel
  cases fuel with
  | zero =>
      simp [Execution.executeField]
  | succ fuel =>
      cases hlookup : schema.lookupField targetParent leftField with
      | none =>
          simp [Execution.executeField, hlookup]
      | some fieldDefinition =>
          cases hresolve :
              base.resolve targetParent leftField arguments source with
          | none =>
              simp [Execution.executeField, hlookup,
                fieldPairOrDeepSuccessResolvers_left_root schema
                  rootSelectionSet base targetParent leftField rightField
                  leftArguments rightArguments arguments source harguments,
                hresolve]
          | some resolved =>
              simp [Execution.executeField, hlookup,
                fieldPairOrDeepSuccessResolvers_left_root schema
                  rootSelectionSet base targetParent leftField rightField
                  leftArguments rightArguments arguments source harguments,
                hresolve,
                completeValue_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
                  schema rootSelectionSet base variableValues targetParent
                  leftField rightField leftArguments rightArguments fuel
                  fieldDefinition.outputType
                  [{
                    parentType := targetParent
                    responseName := responseName
                    fieldName := leftField
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }] resolved]

theorem executeField_fieldPairOrDeepSuccessResolvers_right_root
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (source : Execution.ResolverValue ObjectRef)
    (childSelectionSet : List Selection)
    : Argument.argumentsEquivalent arguments rightArguments
      -> ∀ fuel,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
              targetParent leftField rightField leftArguments rightArguments)
            variableValues fuel (projectionRootResolverValue source) responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := rightField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.executeField schema base variableValues fuel source
              responseName
              [{
                parentType := targetParent
                responseName := responseName
                fieldName := rightField
                arguments := arguments
                selectionSet := childSelectionSet
              }] := by
  intro harguments
  intro fuel
  cases fuel with
  | zero =>
      simp [Execution.executeField]
  | succ fuel =>
      cases hlookup : schema.lookupField targetParent rightField with
      | none =>
          simp [Execution.executeField, hlookup]
      | some fieldDefinition =>
          cases hresolve :
              base.resolve targetParent rightField arguments source with
          | none =>
              simp [Execution.executeField, hlookup,
                fieldPairOrDeepSuccessResolvers_right_root schema
                  rootSelectionSet base targetParent leftField rightField
                  leftArguments rightArguments arguments source harguments,
                hresolve]
          | some resolved =>
              simp [Execution.executeField, hlookup,
                fieldPairOrDeepSuccessResolvers_right_root schema
                  rootSelectionSet base targetParent leftField rightField
                  leftArguments rightArguments arguments source harguments,
                hresolve,
                completeValue_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
                  schema rootSelectionSet base variableValues targetParent
                  leftField rightField leftArguments rightArguments fuel
                  fieldDefinition.outputType
                  [{
                    parentType := targetParent
                    responseName := responseName
                    fieldName := rightField
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }] resolved]

end GroundTypeNormalization

end NormalForm

end GraphQL
