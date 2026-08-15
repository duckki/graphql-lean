import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.CachedRefinement.TreeSoundness.Invariants

/-!
Completion preservation for recursively sound cache trees.

This layer proves erasure and recursive soundness for fields, lists, and nested
value completion.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

theorem visitSelection_field_output_eq_uncached_of_cacheContinuationSound
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (fields : List ExecutableField)
    (output : FieldCacheValue ObjectRef)
    (hfield
      : executableField parentType responseName fieldName arguments selectionSet ∈ fields)
    (hsound
      : OutputCacheContinuationSoundForFields schema resolvers variableValues
          completionFuel source fields output)
    (hfresh
      : ∀ fieldDefinition resolved,
          schema.lookupField parentType fieldName = some fieldDefinition
          -> coerceAndResolveFieldValue schema resolvers variableValues fieldDefinition
                parentType fieldName arguments source
              = some resolved
          -> CompletionCacheSound schema resolvers variableValues
              completionFuel fieldDefinition.outputType selectionSet resolved none)
    : outputVisitResult
        (visitSelection schema resolvers variableValues (completionFuel + 1)
          parentType source
          (.field responseName fieldName arguments directives selectionSet) output)
      = ExecutionUngroupedUncached.visitSelection schema resolvers variableValues
          (completionFuel + 1) parentType source
          (.field responseName fieldName arguments directives selectionSet)
          output.output := by
  by_cases hallows :
      selectionDirectivesAllowBool variableValues directives = true
  · let field :=
      executableField parentType responseName fieldName arguments selectionSet
    have hexec :=
      executeField_output_of_completionCacheSound schema resolvers variableValues
        completionFuel source (objectField? responseName output) field
        (by
          intro fieldDefinition resolved hlookup hresolve
          change (schema.lookupField parentType fieldName = some fieldDefinition) at hlookup
          exact hfresh fieldDefinition resolved hlookup hresolve)
        (by
          intro fieldDefinition previous hlookup hprevious
          change (schema.lookupField parentType fieldName = some fieldDefinition) at hlookup
          change (objectField? responseName output = some previous) at hprevious
          have hfield' : field ∈ fields := by
            simpa [field] using hfield
          exact hsound field fieldDefinition previous hfield' hprevious hlookup)
    dsimp [field, executableField,
      ExecutionUngroupedUncached.executableField] at hexec
    have hpreviousOut := objectField?_output (ObjectRef := ObjectRef)
      responseName output
    simp [visitSelection, ExecutionUngroupedUncached.visitSelection, hallows,
      mergeResponseFieldResult_output, executableField,
      ExecutionUngroupedUncached.executableField]
    rw [hexec]
    rw [hpreviousOut]
  · have hfalse :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases h : selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    simp [visitSelection, ExecutionUngroupedUncached.visitSelection, hfalse,
      outputVisitResult, visitOk, ExecutionUngroupedUncached.visitOk]

theorem completeValueList_output_of_completeValue
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (selectionSet : List Selection)
    (hcomplete
      : ∀ value previous?,
          outputResult FieldCacheValue.output
            (completeValue schema resolvers variableValues fuel itemType selectionSet
              value previous?)
          = ExecutionUngroupedUncached.completeValue schema resolvers variableValues
              fuel itemType selectionSet value
              (previous?.map FieldCacheValue.output))
    : ∀ values previousValues,
        outputResult outputValues
          (completeValueList schema resolvers variableValues fuel itemType
            selectionSet values previousValues)
        = ExecutionUngroupedUncached.completeValueList schema resolvers
            variableValues fuel itemType selectionSet values
            (outputValues previousValues)
  | [], [] => by
      simp [completeValueList, ExecutionUngroupedUncached.completeValueList,
        outputResult]
  | [], _previous :: _rest => by
      simp [completeValueList, ExecutionUngroupedUncached.completeValueList,
        outputResult]
  | value :: values, [] => by
      have hhead := hcomplete value none
      have htail :=
        completeValueList_output_of_completeValue schema resolvers variableValues
          fuel itemType selectionSet hcomplete values []
      simp [completeValueList, ExecutionUngroupedUncached.completeValueList]
      rw [combine_cons_output, hhead, htail]
      simp
  | value :: values, previous :: previousValues => by
      cases previous with
      | null =>
          have htail :=
            completeValueList_output_of_completeValue schema resolvers
              variableValues fuel itemType selectionSet hcomplete values
              previousValues
          simp [completeValueList, ExecutionUngroupedUncached.completeValueList]
          rw [combine_cons_output, htail]
          simp [outputResult]
      | scalar previousValue =>
          have hhead :=
            hcomplete value (some (FieldCacheValue.scalar previousValue))
          have htail :=
            completeValueList_output_of_completeValue schema resolvers
              variableValues fuel itemType selectionSet hcomplete values
              previousValues
          simp [completeValueList, ExecutionUngroupedUncached.completeValueList]
          rw [combine_cons_output, hhead, htail]
          simp
      | object previousSource fields =>
          have hhead :=
            hcomplete value (some (FieldCacheValue.object previousSource fields))
          have htail :=
            completeValueList_output_of_completeValue schema resolvers
              variableValues fuel itemType selectionSet hcomplete values
              previousValues
          simp [completeValueList, ExecutionUngroupedUncached.completeValueList]
          rw [combine_cons_output, hhead, htail]
          simp
      | list sourceValues? cachedValues =>
          have hhead :=
            hcomplete value (some (FieldCacheValue.list sourceValues? cachedValues))
          have htail :=
            completeValueList_output_of_completeValue schema resolvers
              variableValues fuel itemType selectionSet hcomplete values
              previousValues
          simp [completeValueList, ExecutionUngroupedUncached.completeValueList]
          rw [combine_cons_output, hhead, htail]
          simp

theorem FieldCacheTreesSound.of_combine_cons_ok
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (selectionSet : List Selection)
    (source : ResolverValue ObjectRef)
    (sources : List (ResolverValue ObjectRef))
    (head : Result (FieldCacheValue ObjectRef))
    (tail : Result (List (FieldCacheValue ObjectRef)))
    (completedValues : List (FieldCacheValue ObjectRef)) (errors : Nat)
    : FieldCacheTreeSound schema resolvers variableValues fuel selectionSet source
        (resultValueOrNull head)
      -> (∀ tailValues tailErrors,
            tail = .ok (tailValues, tailErrors)
            -> FieldCacheTreesSound schema resolvers variableValues fuel
                selectionSet sources tailValues)
      -> Result.combine List.cons head tail = .ok (completedValues, errors)
      -> FieldCacheTreesSound schema resolvers variableValues fuel selectionSet
          (source :: sources) completedValues := by
  intro hhead htail hcombine
  cases head with
  | error headErrors =>
      cases tail <;> simp [Result.combine] at hcombine
  | ok headResult =>
      rcases headResult with ⟨headValue, headErrors⟩
      cases tail with
      | error tailErrors =>
          simp [Result.combine] at hcombine
      | ok tailResult =>
          rcases tailResult with ⟨tailValues, tailErrors⟩
          simp [Result.combine] at hcombine
          rcases hcombine with ⟨rfl, rfl⟩
          exact
            FieldCacheTreesSound.cons
              (by simpa [resultValueOrNull] using hhead)
              (htail tailValues tailErrors rfl)

theorem completeValueList_result_treeSound_of_completeValue
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (universeSet active : List Selection)
    (hcomplete
      : ∀ value previous?,
          (∀ previous,
            previous? = some previous
            -> FieldCacheTreeSound schema resolvers variableValues fuel
                universeSet value previous)
          -> FieldCacheTreeSound schema resolvers variableValues fuel universeSet
              value
              (resultValueOrNull
                (completeValue schema resolvers variableValues fuel itemType active
                  value previous?)))
    : ∀ values previousValues,
        FieldCacheTreesPrefixSound schema resolvers variableValues fuel universeSet
          values previousValues
        -> ∀ completedValues errors,
            completeValueList schema resolvers variableValues fuel itemType active
                values previousValues
              = .ok (completedValues, errors)
            -> FieldCacheTreesSound schema resolvers variableValues fuel universeSet
                values completedValues
  | [], [], FieldCacheTreesPrefixSound.nil _, completedValues, errors, hok => by
      simp [completeValueList] at hok
      rcases hok with ⟨rfl, rfl⟩
      exact FieldCacheTreesSound.nil
  | [],
    _previous :: _previousRest,
    hprefix,
    completedValues,
    errors,
    _hok => by
      cases hprefix
  | value :: values,
    [],
    FieldCacheTreesPrefixSound.nil _,
    completedValues,
    errors,
    hok => by
      have hhead := hcomplete value none (by
        intro previous hprevious
        simp at hprevious)
      have htail :=
        completeValueList_result_treeSound_of_completeValue schema resolvers
          variableValues fuel itemType universeSet active hcomplete values []
          (FieldCacheTreesPrefixSound.nil values)
      exact
        FieldCacheTreesSound.of_combine_cons_ok schema resolvers variableValues
          fuel universeSet value values
          (completeValue schema resolvers variableValues fuel itemType active value
            none)
          (completeValueList schema resolvers variableValues fuel itemType active
            values [])
          completedValues errors hhead htail (by
            simpa [completeValueList] using hok)
  | value :: values,
    previous :: previousValues,
    FieldCacheTreesPrefixSound.cons hprevious hprefix,
    completedValues,
    errors,
    hok => by
      let head : Result (FieldCacheValue ObjectRef) :=
        match previous with
        | .null => .ok (.null, 0)
        | _ =>
            completeValue schema resolvers variableValues fuel itemType active
              value (some previous)
      have hhead :
          FieldCacheTreeSound schema resolvers variableValues fuel universeSet
            value (resultValueOrNull head) := by
        cases previous with
        | null => simpa [head, resultValueOrNull] using hprevious
        | scalar previousValue =>
            simpa [head] using
              hcomplete value (some (.scalar previousValue)) (by
                intro candidate hcandidate
                injection hcandidate with hcandidate
                subst candidate
                exact hprevious)
        | object previousSource previousFields =>
            simpa [head] using
              hcomplete value (some (.object previousSource previousFields)) (by
                intro candidate hcandidate
                injection hcandidate with hcandidate
                subst candidate
                exact hprevious)
        | list sourceValues previousValues =>
            simpa [head] using
              hcomplete value (some (.list sourceValues previousValues)) (by
                intro candidate hcandidate
                injection hcandidate with hcandidate
                subst candidate
                exact hprevious)
      have htail :=
        completeValueList_result_treeSound_of_completeValue schema resolvers
          variableValues fuel itemType universeSet active hcomplete values
          previousValues hprefix
      exact
        FieldCacheTreesSound.of_combine_cons_ok schema resolvers variableValues
          fuel universeSet value values head
          (completeValueList schema resolvers variableValues fuel itemType active
            values previousValues)
          completedValues errors hhead htail (by
            cases previous <;> simpa [completeValueList, head] using hok)

theorem completeValueList_output_eq_uncached_of_completeValue_and_prefixSound
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (universeSet active : List Selection)
    (hcomplete
      : ∀ value previous?,
          (∀ previous,
            previous? = some previous
            -> FieldCacheTreeSound schema resolvers variableValues fuel
                universeSet value previous)
          -> outputResult FieldCacheValue.output
                (completeValue schema resolvers variableValues fuel itemType active
                  value previous?)
              = ExecutionUngroupedUncached.completeValue schema resolvers
                  variableValues fuel itemType active value
                  (previous?.map FieldCacheValue.output))
    : ∀ values previousValues,
        FieldCacheTreesPrefixSound schema resolvers variableValues fuel universeSet
          values previousValues
        -> outputResult outputValues
              (completeValueList schema resolvers variableValues fuel itemType active
                values previousValues)
            = ExecutionUngroupedUncached.completeValueList schema resolvers
                variableValues fuel itemType active values
                (outputValues previousValues)
  | [], [], FieldCacheTreesPrefixSound.nil _ => by
      simp [completeValueList, ExecutionUngroupedUncached.completeValueList,
        outputResult]
  | [], _previous :: _previousRest, hprefix => by
      cases hprefix
  | value :: values, [], FieldCacheTreesPrefixSound.nil _ => by
      have hhead := hcomplete value none (by
        intro previous hprevious
        simp at hprevious)
      have htail :=
        completeValueList_output_eq_uncached_of_completeValue_and_prefixSound
          schema resolvers variableValues fuel itemType universeSet active hcomplete
          values [] (FieldCacheTreesPrefixSound.nil values)
      simp [completeValueList, ExecutionUngroupedUncached.completeValueList]
      rw [combine_cons_output, hhead, htail]
      simp
  | value :: values,
    previous :: previousValues,
    FieldCacheTreesPrefixSound.cons hprevious hprefix => by
      have htail :=
        completeValueList_output_eq_uncached_of_completeValue_and_prefixSound
          schema resolvers variableValues fuel itemType universeSet active hcomplete
          values previousValues hprefix
      cases previous with
      | null =>
          simp [completeValueList, ExecutionUngroupedUncached.completeValueList]
          rw [combine_cons_output, htail]
          simp [outputResult]
      | scalar previousValue =>
          have hhead :=
            hcomplete value (some (.scalar previousValue)) (by
              intro candidate hcandidate
              injection hcandidate with hcandidate
              subst candidate
              exact hprevious)
          simp [completeValueList, ExecutionUngroupedUncached.completeValueList]
          rw [combine_cons_output, hhead, htail]
          simp
      | object previousSource previousFields =>
          have hhead :=
            hcomplete value (some (.object previousSource previousFields)) (by
              intro candidate hcandidate
              injection hcandidate with hcandidate
              subst candidate
              exact hprevious)
          simp [completeValueList, ExecutionUngroupedUncached.completeValueList]
          rw [combine_cons_output, hhead, htail]
          simp
      | list sourceValues previousValues =>
          have hhead :=
            hcomplete value (some (.list sourceValues previousValues)) (by
              intro candidate hcandidate
              injection hcandidate with hcandidate
              subst candidate
              exact hprevious)
          simp [completeValueList, ExecutionUngroupedUncached.completeValueList]
          rw [combine_cons_output, hhead, htail]
          simp

theorem CompletionCacheSound.zero {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (fieldType : TypeRef) (selectionSet : List Selection)
    (value : ResolverValue ObjectRef)
    (previous? : Option (FieldCacheValue ObjectRef))
    : CompletionCacheSound schema resolvers variableValues 0 fieldType selectionSet
        value previous? := by
  simp [CompletionCacheSound, completeValue,
    ExecutionUngroupedUncached.completeValue, outputResult, outOfFuel]

theorem CompletionCacheSound.null {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (fuel : Nat) (fieldType : TypeRef) (selectionSet : List Selection)
    (value : ResolverValue ObjectRef)
    : CompletionCacheSound schema resolvers variableValues fuel fieldType
        selectionSet value (some .null) := by
  cases fuel <;>
    simp [CompletionCacheSound, completeValue,
      ExecutionUngroupedUncached.completeValue, outputResult, outOfFuel]

theorem CompletionCacheSound.scalar {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (fuel : Nat) (fieldType : TypeRef) (selectionSet : List Selection)
    (value : ResolverValue ObjectRef) (previousValue : String)
    : CompletionCacheSound schema resolvers variableValues fuel fieldType
        selectionSet value (some (.scalar previousValue)) := by
  cases fuel <;>
    simp [CompletionCacheSound, completeValue,
      ExecutionUngroupedUncached.completeValue, outputResult, outOfFuel]

theorem CompletionCacheSound.nonNull {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (fuel : Nat) (inner : TypeRef) (selectionSet : List Selection)
    (value : ResolverValue ObjectRef)
    (previous? : Option (FieldCacheValue ObjectRef))
    : CompletionCacheSound schema resolvers variableValues fuel inner selectionSet
        value previous?
      -> CompletionCacheSound schema resolvers variableValues fuel (.nonNull inner)
          selectionSet value previous? := by
  intro hsound
  cases fuel with
  | zero =>
      exact CompletionCacheSound.zero schema resolvers variableValues
        (.nonNull inner) selectionSet value previous?
  | succ fuel =>
      cases previous? with
      | none =>
          unfold CompletionCacheSound at hsound ⊢
          simp only [completeValue]
          rw [nonNullCompletion_output, hsound]
          simp [ExecutionUngroupedUncached.completeValue]
      | some previous =>
          cases previous with
          | null =>
              exact CompletionCacheSound.null schema resolvers variableValues
                (fuel + 1) (.nonNull inner) selectionSet value
          | scalar previousValue =>
              exact CompletionCacheSound.scalar schema resolvers variableValues
                (fuel + 1) (.nonNull inner) selectionSet value previousValue
          | object previousSource fields =>
              unfold CompletionCacheSound at hsound ⊢
              simp only [completeValue]
              rw [nonNullCompletion_output, hsound]
              simp [ExecutionUngroupedUncached.completeValue]
          | list sourceValues? values =>
              unfold CompletionCacheSound at hsound ⊢
              simp only [completeValue]
              rw [nonNullCompletion_output, hsound]
              simp [ExecutionUngroupedUncached.completeValue]

theorem CompletionCacheSound.object_of_visitSubfields {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (parentType runtimeType : Name)
    (ref : ObjectRef) (previousSource : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    (fields : List (Name × FieldCacheValue ObjectRef))
    : schema.typeIncludesObjectBool parentType runtimeType = true
      -> outputVisitResult
            (visitSubfields schema resolvers variableValues fuel runtimeType
              (.object runtimeType ref) selectionSet
              (.object previousSource fields))
          = ExecutionUngroupedUncached.visitSubfields schema resolvers variableValues
              fuel runtimeType (.object runtimeType ref) selectionSet
              (.object (outputFields fields))
      -> CompletionCacheSound schema resolvers variableValues (fuel + 1)
          (.named parentType) selectionSet (.object runtimeType ref)
          (some (.object previousSource fields)) := by
  intro hinclude hvisit
  simp [CompletionCacheSound, completeValue,
    ExecutionUngroupedUncached.completeValue, hinclude, reuseOrCreateObject?,
    ExecutionUngroupedUncached.reuseOrCreateObject?]
  exact
    catchVisitBubbleAsNull_output_of_outputVisitResult
      (visitSubfields schema resolvers variableValues fuel runtimeType
        (.object runtimeType ref) selectionSet
        (.object previousSource fields))
      (ExecutionUngroupedUncached.visitSubfields schema resolvers variableValues
        fuel runtimeType (.object runtimeType ref) selectionSet
        (.object (outputFields fields)))
      hvisit

theorem CompletionCacheSound.fresh_object_of_visitSubfields {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (parentType runtimeType : Name)
    (ref : ObjectRef) (selectionSet : List Selection)
    : schema.typeIncludesObjectBool parentType runtimeType = true
      -> outputVisitResult
            (visitSubfields schema resolvers variableValues fuel runtimeType
              (.object runtimeType ref) selectionSet
              (.object (.object runtimeType ref) []))
          = ExecutionUngroupedUncached.visitSubfields schema resolvers
              variableValues fuel runtimeType (.object runtimeType ref)
              selectionSet (.object [])
      -> CompletionCacheSound schema resolvers variableValues (fuel + 1)
          (.named parentType) selectionSet (.object runtimeType ref) none := by
  intro hinclude hvisit
  simp [CompletionCacheSound, completeValue,
    ExecutionUngroupedUncached.completeValue, hinclude, reuseOrCreateObject?,
    ExecutionUngroupedUncached.reuseOrCreateObject?]
  exact
    catchVisitBubbleAsNull_output_of_outputVisitResult
      (visitSubfields schema resolvers variableValues fuel runtimeType
        (.object runtimeType ref) selectionSet
        (.object (.object runtimeType ref) []))
      (ExecutionUngroupedUncached.visitSubfields schema resolvers variableValues
        fuel runtimeType (.object runtimeType ref) selectionSet (.object []))
      hvisit

theorem CompletionCacheSound.list {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (fuel : Nat) (inner : TypeRef) (selectionSet : List Selection)
    (values : List (ResolverValue ObjectRef))
    (sourceValues? : Option (List (ResolverValue ObjectRef)))
    (previousValues : List (FieldCacheValue ObjectRef))
    : (∀ value previous?,
        CompletionCacheSound schema resolvers variableValues fuel inner selectionSet
          value previous?)
      -> CompletionCacheSound schema resolvers variableValues (fuel + 1)
          (.list inner) selectionSet (.list values)
          (some (.list sourceValues? previousValues)) := by
  intro hsound
  have hlist :=
    completeValueList_output_of_completeValue schema resolvers variableValues fuel
      inner selectionSet hsound values previousValues
  simp [CompletionCacheSound, completeValue,
    ExecutionUngroupedUncached.completeValue, reuseOrCreateList?,
    ExecutionUngroupedUncached.reuseOrCreateList?]
  rw [catchBubbleAsNull_list_output, hlist]

theorem CompletionCacheSound.of_treeSound_and_visit {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (universeSet active : List Selection)
    (expectedName : Name) (maxFuel : Nat)
    (hvisit
      : ∀ visitFuel runtimeType ref cachedFields,
          visitFuel < maxFuel
          -> schema.typeIncludesObjectBool expectedName runtimeType = true
          -> OutputCacheTreeSoundForGroups schema resolvers variableValues visitFuel
              (.object runtimeType ref)
              (GraphQL.Execution.collectFields schema variableValues runtimeType
                (.object runtimeType ref) universeSet)
              (.object (.object runtimeType ref) cachedFields)
          -> outputVisitResult
                (visitSubfields schema resolvers variableValues visitFuel runtimeType
                  (.object runtimeType ref) active
                  (.object (.object runtimeType ref) cachedFields))
              = ExecutionUngroupedUncached.visitSubfields schema resolvers
                  variableValues visitFuel runtimeType (.object runtimeType ref)
                  active (.object (outputFields cachedFields)))
    : ∀ fuel fieldType value previous?,
        fuel ≤ maxFuel
        -> fieldType.namedType = expectedName
        -> (∀ previous,
              previous? = some previous
              -> FieldCacheTreeSound schema resolvers variableValues fuel universeSet
                  value previous)
        -> CompletionCacheSound schema resolvers variableValues fuel fieldType active
            value previous? := by
  intro fuel fieldType value previous? hfuel hnamed hprevious
  cases fuel with
  | zero =>
      exact
        CompletionCacheSound.zero schema resolvers variableValues fieldType active
          value previous?
  | succ completionFuel =>
      cases fieldType with
      | nonNull inner =>
          apply CompletionCacheSound.nonNull schema resolvers variableValues
          exact
            CompletionCacheSound.of_treeSound_and_visit schema resolvers
              variableValues universeSet active expectedName maxFuel hvisit
              (completionFuel + 1) inner value previous? hfuel hnamed hprevious
      | named typeName =>
          cases previous? with
          | none =>
              cases value with
              | null =>
                  simp [CompletionCacheSound, completeValue,
                    ExecutionUngroupedUncached.completeValue, outputResult]
              | scalar scalarValue =>
                  by_cases hcomposite :
                      (TypeRef.named typeName).isCompositeBool schema = true
                  · simp [CompletionCacheSound, completeValue,
                      ExecutionUngroupedUncached.completeValue, hcomposite,
                      outputResult]
                  · have hfalse :
                        (TypeRef.named typeName).isCompositeBool schema = false := by
                      cases h : (TypeRef.named typeName).isCompositeBool schema
                      · rfl
                      · contradiction
                    simp [CompletionCacheSound, completeValue,
                      ExecutionUngroupedUncached.completeValue, hfalse,
                      outputResult]
              | object runtimeType ref =>
                  by_cases hinclude :
                      schema.typeIncludesObjectBool typeName runtimeType = true
                  · apply
                      CompletionCacheSound.fresh_object_of_visitSubfields schema
                        resolvers variableValues completionFuel typeName runtimeType
                        ref active hinclude
                    exact
                      hvisit completionFuel runtimeType ref
                        [] (by omega) (by rw [← hnamed]; exact hinclude)
                        (OutputCacheTreeSoundForGroups.empty_object schema resolvers
                          variableValues completionFuel (.object runtimeType ref)
                          (.object runtimeType ref)
                          (GraphQL.Execution.collectFields schema variableValues
                            runtimeType (.object runtimeType ref) universeSet))
                  · have hfalse :
                        schema.typeIncludesObjectBool typeName runtimeType = false := by
                      cases h :
                        schema.typeIncludesObjectBool typeName runtimeType
                      · rfl
                      · contradiction
                    simp [CompletionCacheSound, completeValue,
                      ExecutionUngroupedUncached.completeValue, hfalse,
                      outputResult]
              | list values =>
                  simp [CompletionCacheSound, completeValue,
                    ExecutionUngroupedUncached.completeValue, outputResult]
          | some previous =>
              cases previous with
              | null =>
                  exact
                    CompletionCacheSound.null schema resolvers variableValues
                      (completionFuel + 1) (.named typeName) active value
              | scalar previousValue =>
                  exact
                    CompletionCacheSound.scalar schema resolvers variableValues
                      (completionFuel + 1) (.named typeName) active value
                      previousValue
              | object previousSource previousFields =>
                  have htree :=
                    hprevious (.object previousSource previousFields) rfl
                  cases htree with
                  | object _ _ runtimeType ref _ houtput =>
                      by_cases hinclude :
                          schema.typeIncludesObjectBool typeName runtimeType = true
                      · apply
                          CompletionCacheSound.object_of_visitSubfields schema
                            resolvers variableValues completionFuel typeName
                            runtimeType ref (.object runtimeType ref) active
                            previousFields hinclude
                        exact
                          hvisit completionFuel runtimeType ref
                            previousFields (by omega)
                            (by rw [← hnamed]; exact hinclude)
                            houtput
                      · have hfalse :
                            schema.typeIncludesObjectBool typeName runtimeType
                              = false := by
                          cases h :
                            schema.typeIncludesObjectBool typeName runtimeType
                          · rfl
                          · contradiction
                        simp [CompletionCacheSound, completeValue,
                          ExecutionUngroupedUncached.completeValue, hfalse,
                          outputResult]
              | list sourceValues? previousValues =>
                  have htree :=
                    hprevious (.list sourceValues? previousValues) rfl
                  cases htree <;>
                    simp [CompletionCacheSound, completeValue,
                      ExecutionUngroupedUncached.completeValue, outputResult]
      | list inner =>
          cases previous? with
          | none =>
              cases value with
              | list values =>
                  have hprefix :
                      FieldCacheTreesPrefixSound schema resolvers variableValues
                        completionFuel universeSet values [] :=
                    FieldCacheTreesPrefixSound.nil values
                  have hlist :=
                    completeValueList_output_eq_uncached_of_completeValue_and_prefixSound
                      schema resolvers variableValues completionFuel inner
                      universeSet active
                      (by
                        intro item previous? hitem
                        exact
                          CompletionCacheSound.of_treeSound_and_visit schema
                            resolvers variableValues universeSet active expectedName
                            maxFuel hvisit completionFuel inner item previous?
                            (by omega) hnamed hitem)
                      values [] hprefix
                  simp [CompletionCacheSound, completeValue,
                    ExecutionUngroupedUncached.completeValue,
                    reuseOrCreateList?,
                    ExecutionUngroupedUncached.reuseOrCreateList?]
                  rw [catchBubbleAsNull_list_output, hlist]
                  simp [outputValues]
              | null =>
                  simp [CompletionCacheSound, completeValue,
                    ExecutionUngroupedUncached.completeValue, outputResult]
              | scalar scalarValue =>
                  simp [CompletionCacheSound, completeValue,
                    ExecutionUngroupedUncached.completeValue, outputResult]
              | object runtimeType ref =>
                  simp [CompletionCacheSound, completeValue,
                    ExecutionUngroupedUncached.completeValue, outputResult]
          | some previous =>
              cases previous with
              | null =>
                  exact
                    CompletionCacheSound.null schema resolvers variableValues
                      (completionFuel + 1) (.list inner) active value
              | scalar previousValue =>
                  exact
                    CompletionCacheSound.scalar schema resolvers variableValues
                      (completionFuel + 1) (.list inner) active value previousValue
              | object previousSource previousFields =>
                  have htree :=
                    hprevious (.object previousSource previousFields) rfl
                  cases htree <;>
                    simp [CompletionCacheSound, completeValue,
                      ExecutionUngroupedUncached.completeValue, outputResult]
              | list sourceValues? previousValues =>
                  have htree :=
                    hprevious (.list sourceValues? previousValues) rfl
                  cases htree with
                  | cachedList _ _ sourceValues values hvalues =>
                      have hprefix :=
                        FieldCacheTreesSound.toPrefixSound schema resolvers
                          variableValues completionFuel universeSet hvalues
                      have hlist :=
                        completeValueList_output_eq_uncached_of_completeValue_and_prefixSound
                          schema resolvers variableValues completionFuel inner
                          universeSet active
                          (by
                            intro item previous? hitem
                            exact
                              CompletionCacheSound.of_treeSound_and_visit schema
                                resolvers variableValues universeSet active
                                expectedName maxFuel hvisit completionFuel inner item
                                previous? (by omega) hnamed hitem)
                          sourceValues previousValues hprefix
                      simp [CompletionCacheSound, completeValue,
                        ExecutionUngroupedUncached.completeValue,
                        reuseOrCreateList?,
                        ExecutionUngroupedUncached.reuseOrCreateList?]
                      rw [catchBubbleAsNull_list_output, hlist]
                  | finalList _ _ sourceValues values hvalues =>
                      have hprefix :=
                        FieldCacheTreesSound.toPrefixSound schema resolvers
                          variableValues completionFuel universeSet hvalues
                      have hlist :=
                        completeValueList_output_eq_uncached_of_completeValue_and_prefixSound
                          schema resolvers variableValues completionFuel inner
                          universeSet active
                          (by
                            intro item previous? hitem
                            exact
                              CompletionCacheSound.of_treeSound_and_visit schema
                                resolvers variableValues universeSet active
                                expectedName maxFuel hvisit completionFuel inner item
                                previous? (by omega) hnamed hitem)
                          sourceValues previousValues hprefix
                      simp [CompletionCacheSound, completeValue,
                        ExecutionUngroupedUncached.completeValue,
                        reuseOrCreateList?,
                        ExecutionUngroupedUncached.reuseOrCreateList?]
                      rw [catchBubbleAsNull_list_output, hlist]
termination_by fuel fieldType _value _previous? _hprevious =>
  (fuel, sizeOf fieldType)
decreasing_by
  all_goals
    try subst_vars
    simp_wf
    repeat first
      | apply Prod.Lex.left; omega
      | apply Prod.Lex.right
    try omega

theorem FieldCacheTreeSound.completeValue_result_of_treeSound_and_visit
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (universeSet active : List Selection)
    (expectedName : Name) (maxFuel : Nat)
    (hvisit
      : ∀ visitFuel runtimeType ref cachedFields,
          visitFuel < maxFuel
          -> schema.typeIncludesObjectBool expectedName runtimeType = true
          -> OutputCacheTreeSoundForGroups schema resolvers variableValues visitFuel
              (.object runtimeType ref)
              (GraphQL.Execution.collectFields schema variableValues runtimeType
                (.object runtimeType ref) universeSet)
              (.object (.object runtimeType ref) cachedFields)
          -> OutputCacheTreeSoundForGroups schema resolvers variableValues visitFuel
              (.object runtimeType ref)
              (GraphQL.Execution.collectFields schema variableValues runtimeType
                (.object runtimeType ref) universeSet)
              (visitSubfields schema resolvers variableValues visitFuel runtimeType
                (.object runtimeType ref) active
                (.object (.object runtimeType ref) cachedFields)).value)
    : ∀ fuel fieldType value previous?,
        fuel ≤ maxFuel
        -> fieldType.namedType = expectedName
        -> (∀ previous,
              previous? = some previous
              -> FieldCacheTreeSound schema resolvers variableValues fuel universeSet
                  value previous)
        -> FieldCacheTreeSound schema resolvers variableValues fuel universeSet value
            (resultValueOrNull
              (completeValue schema resolvers variableValues fuel fieldType active
                value previous?)) := by
  intro fuel fieldType value previous? hfuel hnamed hprevious
  cases fuel with
  | zero =>
      exact FieldCacheTreeSound.zero universeSet value _
  | succ completionFuel =>
      cases fieldType with
      | nonNull inner =>
          cases previous? with
          | none =>
              simpa [completeValue] using
                FieldCacheTreeSound.resultValueOrNull_nonNullCompletion schema
                  resolvers variableValues (completionFuel + 1) universeSet value
                  (completeValue schema resolvers variableValues
                    (completionFuel + 1) inner active value none)
                  (FieldCacheTreeSound.completeValue_result_of_treeSound_and_visit
                    schema resolvers variableValues universeSet active expectedName
                    maxFuel hvisit (completionFuel + 1) inner value none hfuel
                    hnamed hprevious)
          | some previous =>
              have htree := hprevious previous rfl
              cases previous with
              | null =>
                  simpa [completeValue, resultValueOrNull] using htree
              | scalar previousValue =>
                  cases htree
                  simpa [completeValue, resultValueOrNull] using
                    (FieldCacheTreeSound.null (schema := schema)
                      (resolvers := resolvers) (variableValues := variableValues)
                      completionFuel universeSet (.scalar previousValue))
              | object previousSource previousFields =>
                  simpa [completeValue] using
                    FieldCacheTreeSound.resultValueOrNull_nonNullCompletion schema
                      resolvers variableValues (completionFuel + 1) universeSet value
                      (completeValue schema resolvers variableValues
                        (completionFuel + 1) inner active value
                        (some (.object previousSource previousFields)))
                      (FieldCacheTreeSound.completeValue_result_of_treeSound_and_visit
                        schema resolvers variableValues universeSet active
                        expectedName maxFuel hvisit (completionFuel + 1) inner value
                        (some (.object previousSource previousFields)) (by
                          exact hfuel) hnamed (by
                          intro candidate hcandidate
                          injection hcandidate with hcandidate
                          subst candidate
                          exact htree))
              | list sourceValues? previousValues =>
                  simpa [completeValue] using
                    FieldCacheTreeSound.resultValueOrNull_nonNullCompletion schema
                      resolvers variableValues (completionFuel + 1) universeSet value
                      (completeValue schema resolvers variableValues
                        (completionFuel + 1) inner active value
                        (some (.list sourceValues? previousValues)))
                      (FieldCacheTreeSound.completeValue_result_of_treeSound_and_visit
                        schema resolvers variableValues universeSet active
                        expectedName maxFuel hvisit (completionFuel + 1) inner value
                        (some (.list sourceValues? previousValues)) (by
                          exact hfuel) hnamed (by
                          intro candidate hcandidate
                          injection hcandidate with hcandidate
                          subst candidate
                          exact htree))
      | named typeName =>
          cases previous? with
          | none =>
              cases value with
              | null =>
                  simpa [completeValue, resultValueOrNull] using
                    (FieldCacheTreeSound.null (schema := schema)
                      (resolvers := resolvers) (variableValues := variableValues)
                      completionFuel universeSet (.null))
              | scalar scalarValue =>
                  by_cases hcomposite :
                      (TypeRef.named typeName).isCompositeBool schema = true
                  · simpa [completeValue, hcomposite, resultValueOrNull] using
                      (FieldCacheTreeSound.null (schema := schema)
                        (resolvers := resolvers) (variableValues := variableValues)
                        completionFuel universeSet (.scalar scalarValue))
                  · have hfalse :
                        (TypeRef.named typeName).isCompositeBool schema = false := by
                      cases h : (TypeRef.named typeName).isCompositeBool schema
                      · rfl
                      · contradiction
                    simpa [completeValue, hfalse, resultValueOrNull] using
                      (FieldCacheTreeSound.scalar (schema := schema)
                        (resolvers := resolvers) (variableValues := variableValues)
                        completionFuel universeSet scalarValue)
              | object runtimeType ref =>
                  by_cases hinclude :
                      schema.typeIncludesObjectBool typeName runtimeType = true
                  · let initial : FieldCacheValue ObjectRef :=
                      .object (.object runtimeType ref) []
                    have hinitial :
                        OutputCacheTreeSoundForGroups schema resolvers variableValues
                          completionFuel (.object runtimeType ref)
                          (GraphQL.Execution.collectFields schema variableValues
                            runtimeType (.object runtimeType ref) universeSet)
                          initial :=
                      OutputCacheTreeSoundForGroups.empty_object schema resolvers
                        variableValues completionFuel (.object runtimeType ref)
                        (.object runtimeType ref)
                        (GraphQL.Execution.collectFields schema variableValues
                          runtimeType (.object runtimeType ref) universeSet)
                    let visited :=
                      visitSubfields schema resolvers variableValues completionFuel
                        runtimeType (.object runtimeType ref) active initial
                    have hpost :=
                      hvisit completionFuel runtimeType ref [] (by omega)
                        (by rw [← hnamed]; exact hinclude) hinitial
                    rcases
                        visitSubfields_value_object schema resolvers variableValues
                          completionFuel runtimeType (.object runtimeType ref) active
                          (.object runtimeType ref) [] with
                      ⟨resultFields, hvalue⟩
                    change visited.value = .object (.object runtimeType ref) resultFields
                      at hvalue
                    cases hstatus : visited.status with
                    | error errors =>
                        simpa [completeValue, hinclude, reuseOrCreateObject?, initial,
                          visited, hstatus, catchVisitBubbleAsNull,
                          resultValueOrNull] using
                          (FieldCacheTreeSound.null (schema := schema)
                            (resolvers := resolvers)
                            (variableValues := variableValues) completionFuel
                            universeSet (.object runtimeType ref))
                    | ok ok =>
                        rcases ok with ⟨_unit, errors⟩
                        rw [hvalue] at hpost
                        simpa [completeValue, hinclude, reuseOrCreateObject?, initial,
                          visited, hstatus, catchVisitBubbleAsNull,
                          resultValueOrNull, hvalue] using
                          (FieldCacheTreeSound.object completionFuel universeSet
                            runtimeType ref resultFields hpost)
                  · have hfalse :
                        schema.typeIncludesObjectBool typeName runtimeType = false := by
                      cases h : schema.typeIncludesObjectBool typeName runtimeType
                      · rfl
                      · contradiction
                    simpa [completeValue, hfalse, resultValueOrNull] using
                      (FieldCacheTreeSound.null (schema := schema)
                        (resolvers := resolvers) (variableValues := variableValues)
                        completionFuel universeSet (.object runtimeType ref))
              | list values =>
                  simpa [completeValue, resultValueOrNull] using
                    (FieldCacheTreeSound.null (schema := schema)
                      (resolvers := resolvers) (variableValues := variableValues)
                      completionFuel universeSet (.list values))
          | some previous =>
              have htree := hprevious previous rfl
              cases previous with
              | null =>
                  simpa [completeValue, resultValueOrNull] using htree
              | scalar previousValue =>
                  simpa [completeValue, resultValueOrNull] using
                    (FieldCacheTreeSound.null (schema := schema)
                      (resolvers := resolvers) (variableValues := variableValues)
                      completionFuel universeSet value)
              | object previousSource previousFields =>
                  cases htree with
                  | object _ _ runtimeType ref _ houtput =>
                      by_cases hinclude :
                          schema.typeIncludesObjectBool typeName runtimeType = true
                      · let previous : FieldCacheValue ObjectRef :=
                          .object (.object runtimeType ref) previousFields
                        let visited :=
                          visitSubfields schema resolvers variableValues
                            completionFuel runtimeType (.object runtimeType ref) active
                            previous
                        have hpost :=
                          hvisit completionFuel runtimeType ref previousFields (by omega)
                            (by rw [← hnamed]; exact hinclude)
                            houtput
                        rcases
                            visitSubfields_value_object schema resolvers
                              variableValues completionFuel runtimeType
                              (.object runtimeType ref) active
                              (.object runtimeType ref) previousFields with
                          ⟨resultFields, hvalue⟩
                        change
                          visited.value =
                            .object (.object runtimeType ref) resultFields at hvalue
                        cases hstatus : visited.status with
                        | error errors =>
                            simpa [completeValue, hinclude, reuseOrCreateObject?,
                              previous, visited, hstatus, catchVisitBubbleAsNull,
                              resultValueOrNull] using
                              (FieldCacheTreeSound.null (schema := schema)
                                (resolvers := resolvers)
                                (variableValues := variableValues) completionFuel
                                universeSet (.object runtimeType ref))
                        | ok ok =>
                            rcases ok with ⟨_unit, errors⟩
                            rw [hvalue] at hpost
                            simpa [completeValue, hinclude, reuseOrCreateObject?,
                              previous, visited, hstatus, catchVisitBubbleAsNull,
                              resultValueOrNull, hvalue] using
                              (FieldCacheTreeSound.object completionFuel universeSet
                                runtimeType ref resultFields hpost)
                      · have hfalse :
                            schema.typeIncludesObjectBool typeName runtimeType
                              = false := by
                          cases h :
                            schema.typeIncludesObjectBool typeName runtimeType
                          · rfl
                          · contradiction
                        simpa [completeValue, hfalse, resultValueOrNull] using
                          (FieldCacheTreeSound.null (schema := schema)
                            (resolvers := resolvers)
                            (variableValues := variableValues) completionFuel
                            universeSet (.object runtimeType ref))
              | list sourceValues? previousValues =>
                  cases htree with
                  | cachedList _ _ sourceValues _ _ =>
                      simpa [completeValue, resultValueOrNull] using
                        (FieldCacheTreeSound.null (schema := schema)
                          (resolvers := resolvers)
                          (variableValues := variableValues) completionFuel
                          universeSet (.list sourceValues))
                  | finalList _ _ sourceValues _ _ =>
                      simpa [completeValue, resultValueOrNull] using
                        (FieldCacheTreeSound.null (schema := schema)
                          (resolvers := resolvers)
                          (variableValues := variableValues) completionFuel
                          universeSet (.list sourceValues))
      | list inner =>
          cases previous? with
          | none =>
              cases value with
              | list values =>
                  generalize hcompleted :
                    completeValueList schema resolvers variableValues completionFuel
                        inner active values []
                      = completed
                  cases completed with
                  | error errors =>
                      simpa [completeValue, reuseOrCreateList?, hcompleted,
                        catchBubbleAsNull, resultValueOrNull] using
                        (FieldCacheTreeSound.null (schema := schema)
                          (resolvers := resolvers)
                          (variableValues := variableValues) completionFuel
                          universeSet (.list values))
                  | ok completed =>
                      rcases completed with ⟨completedValues, errors⟩
                      have hvalues :=
                        completeValueList_result_treeSound_of_completeValue schema
                          resolvers variableValues completionFuel inner universeSet
                          active
                          (by
                            intro item previous? hitem
                            exact
                              FieldCacheTreeSound.completeValue_result_of_treeSound_and_visit
                                schema resolvers variableValues universeSet active
                                expectedName maxFuel hvisit completionFuel inner item
                                previous? (by omega) hnamed hitem)
                          values [] (FieldCacheTreesPrefixSound.nil values)
                          completedValues errors hcompleted
                      by_cases hcomposite : inner.isCompositeBool schema = true
                      · simpa [completeValue, reuseOrCreateList?, hcompleted,
                          catchBubbleAsNull, resultValueOrNull, hcomposite] using
                          (FieldCacheTreeSound.cachedList completionFuel universeSet
                            values completedValues hvalues)
                      · have hfalse : inner.isCompositeBool schema = false := by
                          cases h : inner.isCompositeBool schema
                          · rfl
                          · contradiction
                        simpa [completeValue, reuseOrCreateList?, hcompleted,
                          catchBubbleAsNull, resultValueOrNull, hfalse] using
                          (FieldCacheTreeSound.finalList completionFuel universeSet
                            values completedValues hvalues)
              | null =>
                  simpa [completeValue, resultValueOrNull] using
                    (FieldCacheTreeSound.null (schema := schema)
                      (resolvers := resolvers) (variableValues := variableValues)
                      completionFuel universeSet (.null))
              | scalar scalarValue =>
                  simpa [completeValue, resultValueOrNull] using
                    (FieldCacheTreeSound.null (schema := schema)
                      (resolvers := resolvers) (variableValues := variableValues)
                      completionFuel universeSet (.scalar scalarValue))
              | object runtimeType ref =>
                  simpa [completeValue, resultValueOrNull] using
                    (FieldCacheTreeSound.null (schema := schema)
                      (resolvers := resolvers) (variableValues := variableValues)
                      completionFuel universeSet (.object runtimeType ref))
          | some previous =>
              have htree := hprevious previous rfl
              cases previous with
              | null =>
                  simpa [completeValue, resultValueOrNull] using htree
              | scalar previousValue =>
                  cases htree
                  simpa [completeValue, resultValueOrNull] using
                    (FieldCacheTreeSound.null (schema := schema)
                      (resolvers := resolvers) (variableValues := variableValues)
                      completionFuel universeSet (.scalar previousValue))
              | object previousSource previousFields =>
                  cases htree with
                  | object _ _ runtimeType ref _ _ =>
                      simpa [completeValue, resultValueOrNull] using
                        (FieldCacheTreeSound.null (schema := schema)
                          (resolvers := resolvers)
                          (variableValues := variableValues) completionFuel
                          universeSet (.object runtimeType ref))
              | list sourceValues? previousValues =>
                  cases htree with
                  | cachedList _ _ sourceValues values hvalues =>
                      have hprefix :=
                        FieldCacheTreesSound.toPrefixSound schema resolvers
                          variableValues completionFuel universeSet hvalues
                      generalize hcompleted :
                        completeValueList schema resolvers variableValues
                            completionFuel inner active sourceValues previousValues
                          = completed
                      cases completed with
                      | error errors =>
                          simpa [completeValue, reuseOrCreateList?, hcompleted,
                            catchBubbleAsNull, resultValueOrNull] using
                            (FieldCacheTreeSound.null (schema := schema)
                              (resolvers := resolvers)
                              (variableValues := variableValues) completionFuel
                              universeSet (.list sourceValues))
                      | ok completed =>
                          rcases completed with ⟨completedValues, errors⟩
                          have hcompletedValues :=
                            completeValueList_result_treeSound_of_completeValue
                              schema resolvers variableValues completionFuel inner
                              universeSet active
                              (by
                                intro item previous? hitem
                                exact
                                  FieldCacheTreeSound.completeValue_result_of_treeSound_and_visit
                                    schema resolvers variableValues universeSet
                                    active expectedName maxFuel hvisit completionFuel
                                    inner item previous? (by omega) hnamed hitem)
                              sourceValues previousValues hprefix completedValues
                              errors hcompleted
                          simpa [completeValue, reuseOrCreateList?, hcompleted,
                            catchBubbleAsNull, resultValueOrNull] using
                            (FieldCacheTreeSound.cachedList completionFuel universeSet
                              sourceValues completedValues hcompletedValues)
                  | finalList _ _ sourceValues values hvalues =>
                      have hprefix :=
                        FieldCacheTreesSound.toPrefixSound schema resolvers
                          variableValues completionFuel universeSet hvalues
                      generalize hcompleted :
                        completeValueList schema resolvers variableValues
                            completionFuel inner active sourceValues previousValues
                          = completed
                      cases completed with
                      | error errors =>
                          simpa [completeValue, reuseOrCreateList?, hcompleted,
                            catchBubbleAsNull, resultValueOrNull] using
                            (FieldCacheTreeSound.null (schema := schema)
                              (resolvers := resolvers)
                              (variableValues := variableValues) completionFuel
                              universeSet (.list sourceValues))
                      | ok completed =>
                          rcases completed with ⟨completedValues, errors⟩
                          have hcompletedValues :=
                            completeValueList_result_treeSound_of_completeValue
                              schema resolvers variableValues completionFuel inner
                              universeSet active
                              (by
                                intro item previous? hitem
                                exact
                                  FieldCacheTreeSound.completeValue_result_of_treeSound_and_visit
                                    schema resolvers variableValues universeSet
                                    active expectedName maxFuel hvisit completionFuel
                                    inner item previous? (by omega) hnamed hitem)
                              sourceValues previousValues hprefix completedValues
                              errors hcompleted
                          simpa [completeValue, reuseOrCreateList?, hcompleted,
                            catchBubbleAsNull, resultValueOrNull] using
                            (FieldCacheTreeSound.finalList completionFuel universeSet
                              sourceValues completedValues hcompletedValues)
termination_by fuel fieldType _value _previous? _hprevious =>
  (fuel, sizeOf fieldType)
decreasing_by
  all_goals
    try subst_vars
    simp_wf
    repeat first
      | apply Prod.Lex.left; omega
      | apply Prod.Lex.right
    try omega

theorem executeField_result_continuationTreeSound
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (source : ResolverValue ObjectRef) (field : ExecutableField)
    (previous? : Option (FieldCacheValue ObjectRef))
    (universeSet : List Selection)
    (hcomplete
      : ∀ fieldDefinition resolved completionPrevious?,
          schema.lookupField field.parentType field.fieldName = some fieldDefinition
          -> (∀ previous,
                completionPrevious? = some previous
                -> FieldCacheTreeSound schema resolvers variableValues completionFuel
                    universeSet resolved previous)
          -> FieldCacheTreeSound schema resolvers variableValues completionFuel
              universeSet resolved
              (resultValueOrNull
                (completeValue schema resolvers variableValues completionFuel
                  fieldDefinition.outputType field.selectionSet resolved
                  completionPrevious?)))
    (hprevious
      : ∀ fieldDefinition previous,
          schema.lookupField field.parentType field.fieldName = some fieldDefinition
          -> previous? = some previous
          -> FieldCacheContinuationTreeSound schema resolvers variableValues
              completionFuel universeSet previous)
    : FieldCacheContinuationTreeSound schema resolvers variableValues completionFuel
        universeSet
        (resultValueOrNull
          (executeField schema resolvers variableValues completionFuel source
            previous? field)) := by
  unfold executeField
  cases hlookup : schema.lookupField field.parentType field.fieldName with
  | none => simp [resultValueOrNull, FieldCacheContinuationTreeSound]
  | some fieldDefinition =>
      cases previous? with
      | none =>
          cases hcoerce
                : coerceArgumentValues schema variableValues fieldDefinition.arguments
                    field.arguments with
          | error =>
              simp only [hlookup, hcoerce]
              change
                FieldCacheContinuationTreeSound schema resolvers variableValues
                  completionFuel universeSet
                  (resultValueOrNull
                    (handleFieldError fieldDefinition.outputType))
              cases fieldDefinition.outputType <;>
                simp [handleFieldError, resultValueOrNull,
                  FieldCacheContinuationTreeSound]
          | success coercedArguments =>
              cases hresolve
                    : resolveFieldValue resolvers field.parentType field.fieldName
                        coercedArguments source with
              | none =>
                  simp only [hlookup, hcoerce, hresolve]
                  change
                    FieldCacheContinuationTreeSound schema resolvers variableValues
                      completionFuel universeSet
                      (resultValueOrNull
                        (handleFieldError fieldDefinition.outputType))
                  cases fieldDefinition.outputType <;>
                    simp [handleFieldError, resultValueOrNull,
                      FieldCacheContinuationTreeSound]
              | some resolved =>
                  simp only [hlookup, hcoerce, hresolve]
                  exact
                    FieldCacheTreeSound.toContinuationTreeSound schema resolvers
                      variableValues completionFuel universeSet resolved _
                      (hcomplete fieldDefinition resolved none hlookup (by
                        intro previous hprevious
                        simp at hprevious))
      | some previous =>
          have hpreviousTree := hprevious fieldDefinition previous hlookup rfl
          cases previous with
          | null =>
              simp [reusablePreviousValue?, resultValueOrNull,
                FieldCacheContinuationTreeSound]
          | scalar previousValue =>
              by_cases hcomposite :
                  fieldDefinition.outputType.isCompositeBool schema = true
              · simp [reusablePreviousValue?, hcomposite, resultValueOrNull,
                  FieldCacheContinuationTreeSound]
              · have hfalse :
                    fieldDefinition.outputType.isCompositeBool schema = false := by
                  cases h : fieldDefinition.outputType.isCompositeBool schema
                  · rfl
                  · contradiction
                simp [reusablePreviousValue?, hfalse, resultValueOrNull,
                  FieldCacheContinuationTreeSound]
          | object previousSource previousFields =>
              have htree :
                  FieldCacheTreeSound schema resolvers variableValues
                    completionFuel universeSet previousSource
                    (.object previousSource previousFields) := by
                simpa [FieldCacheContinuationTreeSound] using hpreviousTree
              simp [reusablePreviousValue?]
              exact
                FieldCacheTreeSound.toContinuationTreeSound schema resolvers
                  variableValues completionFuel universeSet previousSource _
                  (hcomplete fieldDefinition previousSource
                    (some (.object previousSource previousFields)) hlookup (by
                      intro candidate hcandidate
                      injection hcandidate with hcandidate
                      subst candidate
                      exact htree))
          | list sourceValues? previousValues =>
              cases sourceValues? with
              | none =>
                  by_cases hcomposite :
                      fieldDefinition.outputType.isCompositeBool schema = true
                  · simp [reusablePreviousValue?, hcomposite, resultValueOrNull,
                      FieldCacheContinuationTreeSound]
                  · have hfalse :
                        fieldDefinition.outputType.isCompositeBool schema = false := by
                      cases h : fieldDefinition.outputType.isCompositeBool schema
                      · rfl
                      · contradiction
                    simp [reusablePreviousValue?, hfalse, resultValueOrNull,
                      FieldCacheContinuationTreeSound]
              | some sourceValues =>
                  have htree :
                      FieldCacheTreeSound schema resolvers variableValues
                        completionFuel universeSet (.list sourceValues)
                        (.list (some sourceValues) previousValues) := by
                    simpa [FieldCacheContinuationTreeSound] using hpreviousTree
                  simp [reusablePreviousValue?]
                  exact
                    FieldCacheTreeSound.toContinuationTreeSound schema resolvers
                      variableValues completionFuel universeSet (.list sourceValues)
                      _
                      (hcomplete fieldDefinition (.list sourceValues)
                        (some (.list (some sourceValues) previousValues)) hlookup (by
                          intro candidate hcandidate
                          injection hcandidate with hcandidate
                          subst candidate
                          exact htree))

end ExecutionUngrouped
end Algorithms

end GraphQL
