import Proofs.GraphQL.Algorithms.ExecutionUngrouped.CachedRefinement.Erasure

/-!
Internal cache alignment and local traversal erasure.

This layer combines source alignment with cache absorption and lifts local
cached steps to the uncached visitor interface.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

def FieldCacheInternallyAligned {ObjectRef : Type} : FieldCacheValue ObjectRef -> Prop
  | .list (some sourceValues) values =>
      FieldCacheSourcesAligned sourceValues values
  | _ => True

def ObjectFieldCachesInternallyAligned {ObjectRef : Type}
    (output : FieldCacheValue ObjectRef)
    : Prop :=
  ∀ responseName previous,
    objectField? responseName output = some previous
    -> FieldCacheInternallyAligned previous

theorem FieldCacheSourceAligned.internallyAligned {ObjectRef : Type}
    {source : ResolverValue ObjectRef}
    : ∀ {value : FieldCacheValue ObjectRef},
        FieldCacheSourceAligned source value -> FieldCacheInternallyAligned value
  | .null, _haligned => by trivial
  | .scalar _value, _haligned => by trivial
  | .object _source _fields, _haligned => by trivial
  | .list none _values, _haligned => by trivial
  | .list (some sourceValues) values, haligned => by
      cases haligned with
      | cachedList _ _ halignedValues => exact halignedValues

theorem FieldCacheInternallyAligned.of_absorptionShape {ObjectRef : Type}
    {base output : FieldCacheValue ObjectRef}
    : FieldCacheInternallyAligned base
      -> FieldCacheAbsorptionShape base output
      -> FieldCacheInternallyAligned output := by
  intro haligned hshape
  cases hshape with
  | null => exact haligned
  | toNull _base => trivial
  | scalar _value => trivial
  | object _hfields => trivial
  | @list sourceValues? baseValues outputValues hvalues =>
      cases sourceValues? with
      | none => trivial
      | some sourceValues =>
          exact
            FieldCacheSourcesAligned.of_listAbsorptionShape haligned hvalues

theorem executeField_result_internallyAligned {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (source : ResolverValue ObjectRef) (previous : FieldCacheValue ObjectRef)
    (field : ExecutableField)
    : FieldCacheInternallyAligned previous
      -> FieldCacheInternallyAligned
          (resultValueOrNull
            (executeField schema resolvers variableValues completionFuel source
              (some previous) field)) := by
  intro hprevious
  unfold executeField
  cases hlookup : schema.lookupField field.parentType field.fieldName with
  | none => trivial
  | some fieldDefinition =>
      cases previous with
      | null => trivial
      | scalar previousValue =>
          by_cases hcomposite :
              fieldDefinition.outputType.isCompositeBool schema = true
          · simp [reusablePreviousValue?, hcomposite, resultValueOrNull,
              FieldCacheInternallyAligned]
          · have hfalse :
                fieldDefinition.outputType.isCompositeBool schema = false := by
              cases h : fieldDefinition.outputType.isCompositeBool schema
              · rfl
              · contradiction
            simp [reusablePreviousValue?, hfalse, resultValueOrNull,
              FieldCacheInternallyAligned]
      | object previousSource fields =>
          exact (completeValue_sourceAligned schema resolvers variableValues
                  completionFuel fieldDefinition.outputType field.selectionSet
                  previousSource (some (.object previousSource fields))
                  (by
                    intro cached h
                    cases h
                    exact FieldCacheSourceAligned.object previousSource fields)
                ).internallyAligned
      | list sourceValues? values =>
          cases sourceValues? with
          | none =>
              by_cases hcomposite :
                  fieldDefinition.outputType.isCompositeBool schema = true
              · simp [reusablePreviousValue?, hcomposite, resultValueOrNull,
                  FieldCacheInternallyAligned]
              · have hfalse :
                    fieldDefinition.outputType.isCompositeBool schema = false := by
                  cases h : fieldDefinition.outputType.isCompositeBool schema
                  · rfl
                  · contradiction
                simp [reusablePreviousValue?, hfalse, resultValueOrNull,
                  FieldCacheInternallyAligned]
          | some sourceValues =>
              exact (completeValue_sourceAligned schema resolvers variableValues
                      completionFuel fieldDefinition.outputType field.selectionSet
                      (.list sourceValues) (some (.list (some sourceValues) values))
                      (by
                        intro cached h
                        cases h
                        exact
                          FieldCacheSourceAligned.cachedList sourceValues values
                            hprevious)).internallyAligned

theorem executeField_none_result_internallyAligned {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (source : ResolverValue ObjectRef) (field : ExecutableField)
    : FieldCacheInternallyAligned
        (resultValueOrNull
          (executeField schema resolvers variableValues completionFuel source none
            field)) := by
  unfold executeField
  cases hlookup : schema.lookupField field.parentType field.fieldName with
  | none => trivial
  | some fieldDefinition =>
      cases hresolve
            : resolvers.resolve field.parentType field.fieldName field.arguments
                source with
      | none =>
          change
            FieldCacheInternallyAligned
              (resultValueOrNull
                (handleFieldError fieldDefinition.outputType))
          have hnull :
              resultValueOrNull
                  (handleFieldError (ObjectRef := ObjectRef)
                    fieldDefinition.outputType)
                = .null := by
            cases fieldDefinition.outputType <;>
              rfl
          rw [hnull]
          trivial
      | some resolved =>
          exact (completeValue_sourceAligned schema resolvers variableValues
                  completionFuel fieldDefinition.outputType field.selectionSet resolved
                  none (by intro previous h; cases h)).internallyAligned

theorem executeField_cacheAbsorptionShape {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (source : ResolverValue ObjectRef) (previous : FieldCacheValue ObjectRef)
    (field : ExecutableField)
    : FieldCacheMergeReady previous
      -> FieldCacheInternallyAligned previous
      -> FieldCacheAbsorptionShape previous
          (resultValueOrNull
            (executeField schema resolvers variableValues completionFuel source
              (some previous) field)) := by
  intro hpreviousReady hpreviousAligned
  unfold executeField
  cases hlookup : schema.lookupField field.parentType field.fieldName with
  | none =>
      simp [resultValueOrNull]
      exact FieldCacheAbsorptionShape.toNull previous
  | some fieldDefinition =>
      cases previous with
      | null =>
          simp [reusablePreviousValue?, resultValueOrNull]
          exact FieldCacheAbsorptionShape.null
      | scalar previousValue =>
          by_cases hcomposite :
              fieldDefinition.outputType.isCompositeBool schema = true
          · simp [reusablePreviousValue?, hcomposite, resultValueOrNull]
            exact FieldCacheAbsorptionShape.toNull (.scalar previousValue)
          · have hfalse :
                fieldDefinition.outputType.isCompositeBool schema = false := by
              cases h : fieldDefinition.outputType.isCompositeBool schema
              · rfl
              · contradiction
            simp [reusablePreviousValue?, hfalse, resultValueOrNull]
            exact FieldCacheAbsorptionShape.scalar previousValue
      | object previousSource fields =>
          exact
            completeValue_cacheAbsorptionShape schema resolvers variableValues
              completionFuel fieldDefinition.outputType field.selectionSet
              previousSource (.object previousSource fields) hpreviousReady
              (FieldCacheSourceAligned.object previousSource fields)
      | list sourceValues? values =>
          cases sourceValues? with
          | none =>
              by_cases hcomposite :
                  fieldDefinition.outputType.isCompositeBool schema = true
              · simp [reusablePreviousValue?, hcomposite, resultValueOrNull]
                exact
                  FieldCacheAbsorptionShape.toNull (.list none values)
              · have hfalse :
                    fieldDefinition.outputType.isCompositeBool schema = false := by
                  cases h : fieldDefinition.outputType.isCompositeBool schema
                  · rfl
                  · contradiction
                simp [reusablePreviousValue?, hfalse, resultValueOrNull]
                exact
                  FieldCacheAbsorptionShape.refl_of_ready (.list none values)
                    hpreviousReady
          | some sourceValues =>
              exact
                completeValue_cacheAbsorptionShape schema resolvers variableValues
                  completionFuel fieldDefinition.outputType field.selectionSet
                  (.list sourceValues) (.list (some sourceValues) values)
                  hpreviousReady
                  (FieldCacheSourceAligned.cachedList sourceValues values
                    hpreviousAligned)

theorem executeField_result_absorbs_previous {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (source : ResolverValue ObjectRef) (previous : FieldCacheValue ObjectRef)
    (field : ExecutableField)
    : FieldCacheMergeReady previous
      -> FieldCacheInternallyAligned previous
      -> FieldCacheAbsorbs previous
          (resultValueOrNull
            (executeField schema resolvers variableValues completionFuel source
              (some previous) field)) := by
  intro hpreviousReady hpreviousAligned
  exact (executeField_cacheAbsorptionShape schema resolvers variableValues
          completionFuel source previous field hpreviousReady
          hpreviousAligned).to_absorbs

theorem ObjectFieldCachesInternallyAligned.mergeResponseFieldIntoObject
    {ObjectRef : Type} (output incoming : FieldCacheValue ObjectRef)
    (responseName : Name)
    : ObjectFieldCachesInternallyAligned output
      -> FieldCacheInternallyAligned incoming
      -> (∀ previous,
            objectField? responseName output = some previous
            -> FieldCacheAbsorbs previous incoming)
      -> ObjectFieldCachesInternallyAligned
          (mergeResponseFieldIntoObject responseName incoming output) := by
  intro houtput hincoming habsorbs fieldResponseName previous hprevious
  unfold ObjectFieldCachesInternallyAligned at houtput
  cases output with
  | null =>
      simp [GraphQL.Algorithms.ExecutionUngrouped.mergeResponseFieldIntoObject,
        objectField?] at hprevious
  | scalar value =>
      simp [GraphQL.Algorithms.ExecutionUngrouped.mergeResponseFieldIntoObject,
        objectField?] at hprevious
  | list sourceValues? values =>
      simp [GraphQL.Algorithms.ExecutionUngrouped.mergeResponseFieldIntoObject,
        objectField?] at hprevious
  | object objectSource fields =>
      have hlookup :
          lookupField? fieldResponseName
              (mergeResponseField responseName incoming fields)
            = some previous := by
        simpa [GraphQL.Algorithms.ExecutionUngrouped.mergeResponseFieldIntoObject,
          objectField?] using hprevious
      by_cases htarget : fieldResponseName = responseName
      · subst fieldResponseName
        rw [lookupField?_mergeResponseField_self] at hlookup
        cases hexisting : lookupField? responseName fields with
        | none =>
            simp [hexisting] at hlookup
            subst previous
            exact hincoming
        | some existing =>
            simp [hexisting] at hlookup
            subst previous
            rw [habsorbs existing (by simp [objectField?, hexisting])]
            exact hincoming
      · rw [lookupField?_mergeResponseField_other fieldResponseName responseName
          incoming htarget] at hlookup
        exact houtput fieldResponseName previous (by
          simpa [objectField?] using hlookup)

theorem visitFieldResult_internallyAligned {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection) (output : FieldCacheValue ObjectRef)
    : ObjectFieldCachesInternallyAligned output
      -> FieldCacheInternallyAligned
          (resultValueOrNull
            (match fuel with
              | 0 =>
                  match objectField? responseName output with
                  | some previous => .ok (previous, 0)
                  | none => outOfFuel
              | completionFuel + 1 =>
                  executeField schema resolvers variableValues completionFuel source
                    (objectField? responseName output)
                    (executableField parentType responseName fieldName arguments
                      selectionSet))) := by
  intro houtput
  cases fuel with
  | zero =>
      cases hprevious : objectField? responseName output with
      | none =>
          simp [outOfFuel, resultValueOrNull, FieldCacheInternallyAligned]
      | some previous =>
          simpa [hprevious, resultValueOrNull] using
            houtput responseName previous hprevious
  | succ completionFuel =>
      cases hprevious : objectField? responseName output with
      | none =>
          simpa [hprevious] using
            executeField_none_result_internallyAligned schema resolvers
              variableValues completionFuel source
              (executableField parentType responseName fieldName arguments
                selectionSet)
      | some previous =>
          simpa [hprevious] using
            executeField_result_internallyAligned schema resolvers variableValues
              completionFuel source previous
              (executableField parentType responseName fieldName arguments
                selectionSet)
              (houtput responseName previous hprevious)

theorem visitFieldResult_absorbs_previous {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection) (output : FieldCacheValue ObjectRef)
    : FieldCacheMergeReady output
      -> ObjectFieldCachesInternallyAligned output
      -> ∀ previous,
          objectField? responseName output = some previous
          -> FieldCacheAbsorbs previous
              (resultValueOrNull
                (match fuel with
                  | 0 =>
                      match objectField? responseName output with
                      | some previous => .ok (previous, 0)
                      | none => outOfFuel
                  | completionFuel + 1 =>
                      executeField schema resolvers variableValues completionFuel
                        source (objectField? responseName output)
                        (executableField parentType responseName fieldName arguments
                          selectionSet))) := by
  intro hready haligned previous hprevious
  have hpreviousReady : FieldCacheMergeReady previous := by
    cases output with
    | null => simp [objectField?] at hprevious
    | scalar value => simp [objectField?] at hprevious
    | list sourceValues? values => simp [objectField?] at hprevious
    | object objectSource fields =>
        exact
          lookupField?_some_cacheReady objectSource responseName fields previous
            hready (by simpa [objectField?] using hprevious)
  cases fuel with
  | zero =>
      simpa [hprevious, resultValueOrNull] using
        FieldCacheAbsorbs.refl_of_ready previous hpreviousReady
  | succ completionFuel =>
      simpa [hprevious] using
        executeField_result_absorbs_previous schema resolvers variableValues
          completionFuel source previous
          (executableField parentType responseName fieldName arguments selectionSet)
          hpreviousReady (haligned responseName previous hprevious)

mutual
  theorem visitSelection_objectFieldCachesInternallyAligned {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      : ∀ selection output,
          FieldCacheMergeReady output
          -> ObjectFieldCachesInternallyAligned output
          -> ObjectFieldCachesInternallyAligned
              (visitSelection schema resolvers variableValues fuel parentType source
                selection output).value := by
    intro selection output hready haligned
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp only [visitSelection, hallows, if_true,
            mergeResponseFieldResult]
          apply
            ObjectFieldCachesInternallyAligned.mergeResponseFieldIntoObject output
              _ responseName haligned
          · exact
              visitFieldResult_internallyAligned schema resolvers variableValues
                fuel parentType source responseName fieldName arguments selectionSet
                output haligned
          · exact
              visitFieldResult_absorbs_previous schema resolvers variableValues fuel
                parentType source responseName fieldName arguments selectionSet output
                hready haligned
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simpa [visitSelection, hfalse] using haligned
    | inlineFragment typeCondition directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · cases typeCondition with
          | none =>
              simpa [visitSelection, hallows] using
                visitSubfields_objectFieldCachesInternallyAligned schema resolvers
                  variableValues fuel parentType source selectionSet output hready
                  haligned
          | some typeCondition =>
              by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source typeCondition =
                    true
              · simpa [visitSelection, hallows, happly] using
                  visitSubfields_objectFieldCachesInternallyAligned schema
                    resolvers variableValues fuel parentType source selectionSet
                    output hready haligned
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType source typeCondition =
                      false := by
                  cases h :
                      doesFragmentTypeApplyBool schema parentType source typeCondition
                  · rfl
                  · contradiction
                simpa [visitSelection, hallows, hfalse] using haligned
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          cases typeCondition <;> simpa [visitSelection, hfalse] using haligned
  termination_by selection output _hready _haligned => (sizeOf selection, 0)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem visitSubfields_objectFieldCachesInternallyAligned {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      : ∀ selectionSet output,
          FieldCacheMergeReady output
          -> ObjectFieldCachesInternallyAligned output
          -> ObjectFieldCachesInternallyAligned
              (visitSubfields schema resolvers variableValues fuel parentType source
                selectionSet output).value := by
    intro selectionSet output hready haligned
    cases selectionSet with
    | nil => simpa [visitSubfields] using haligned
    | cons selection rest =>
        let head :=
          visitSelection schema resolvers variableValues fuel parentType source
            selection output
        have hheadReady : FieldCacheMergeReady head.value :=
          visitSelection_cacheReady schema resolvers variableValues fuel parentType
            source selection output hready
        have hheadAligned : ObjectFieldCachesInternallyAligned head.value :=
          visitSelection_objectFieldCachesInternallyAligned schema resolvers
            variableValues fuel parentType source selection output hready haligned
        cases hstatus : head.status with
        | error errors =>
            simpa [visitSubfields, head, hstatus] using hheadAligned
        | ok ok =>
            have htailAligned :=
              visitSubfields_objectFieldCachesInternallyAligned schema resolvers
                variableValues fuel parentType source rest head.value hheadReady
                hheadAligned
            simpa [visitSubfields, head, hstatus] using htailAligned
  termination_by selectionSet output _hready _haligned => (sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega
end

theorem visitSubfields_output_eq_uncached_and_invariant {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (Invariant : FieldCacheValue ObjectRef -> Prop)
    (hselection
      : ∀ selection output,
          Invariant output
          -> outputVisitResult
                  (visitSelection schema resolvers variableValues fuel parentType source
                    selection output)
                = ExecutionUngroupedUncached.visitSelection schema resolvers
                    variableValues fuel parentType source selection output.output
              ∧ Invariant
                  (visitSelection schema resolvers variableValues fuel parentType source
                    selection output).value)
    : ∀ selectionSet output,
        Invariant output
        -> outputVisitResult
                (visitSubfields schema resolvers variableValues fuel parentType source
                  selectionSet output)
              = ExecutionUngroupedUncached.visitSubfields schema resolvers variableValues
                  fuel parentType source selectionSet output.output
            ∧ Invariant
                (visitSubfields schema resolvers variableValues fuel parentType source
                  selectionSet output).value
  | [], output, hinvariant => by
      simp [visitSubfields, ExecutionUngroupedUncached.visitSubfields,
        outputVisitResult, visitOk, ExecutionUngroupedUncached.visitOk,
        hinvariant]
  | selection :: rest, output, hinvariant => by
      unfold visitSubfields ExecutionUngroupedUncached.visitSubfields
      generalize hhead :
        visitSelection schema resolvers variableValues fuel parentType source
            selection output
          = head
      have hstep := hselection selection output hinvariant
      rw [hhead] at hstep
      rcases hstep with ⟨hstepOutput, hstepInvariant⟩
      cases hstatus : head.status with
      | error errors =>
          have huncachedHead :
              ExecutionUngroupedUncached.visitSelection schema resolvers
                  variableValues fuel parentType source selection output.output
                = (head.value.output, .error errors) := by
            rw [← hstepOutput]
            simp [outputVisitResult, hstatus]
          constructor
          · simp [hstatus, huncachedHead, outputVisitResult]
          · simpa [hstatus] using hstepInvariant
      | ok ok =>
          have huncachedHead :
              ExecutionUngroupedUncached.visitSelection schema resolvers
                  variableValues fuel parentType source selection output.output
                = (head.value.output, .ok ok) := by
            rw [← hstepOutput]
            simp [outputVisitResult, hstatus]
          have htail :=
            visitSubfields_output_eq_uncached_and_invariant schema resolvers
              variableValues fuel parentType source Invariant hselection rest
              head.value hstepInvariant
          rcases htail with ⟨htailOutput, htailInvariant⟩
          constructor
          · simp [hstatus, huncachedHead, outputVisitResult, combineVisitStatus,
              ExecutionUngroupedUncached.combineVisitStatus]
            rw [← htailOutput]
            simp [outputVisitResult]
          · simpa [hstatus] using htailInvariant

theorem executeRootSelectionSet_eq_uncached_of_outputVisitResult
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selectionSet : List Selection)
    : outputVisitResult
          (visitSubfields schema resolvers variableValues fuel parentType source
            selectionSet (.object source []))
        = ExecutionUngroupedUncached.visitSubfields schema resolvers variableValues
            fuel parentType source selectionSet (.object [])
      -> executeRootSelectionSet schema resolvers variableValues fuel parentType
            source selectionSet
          = ExecutionUngroupedUncached.executeRootSelectionSet schema resolvers
              variableValues fuel parentType source selectionSet := by
  intro hvisit
  unfold executeRootSelectionSet ExecutionUngroupedUncached.executeRootSelectionSet
  generalize hcached :
    visitSubfields schema resolvers variableValues fuel parentType source
        selectionSet (FieldCacheValue.object source [])
      =
      cachedVisited
  rw [hcached] at hvisit
  rw [← hvisit]
  rcases cachedVisited with ⟨value, status⟩
  cases status with
  | error errors =>
      simp [outputVisitResult, outputRootResult, outputResult]
  | ok result =>
      rcases result with ⟨_unit, errors⟩
      cases value <;> simp [outputVisitResult, outputRootResult, outputResult]

theorem executeQueryWithFuel_eq_uncached_of_outputVisitResult
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : outputVisitResult
          (visitSubfields schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues) fuel
            (operation.rootType schema) source operation.selectionSet
            (.object source []))
        = ExecutionUngroupedUncached.visitSubfields schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues) fuel
            (operation.rootType schema) source operation.selectionSet (.object [])
      -> executeQueryWithFuel schema resolvers variableValues operation fuel source
          = ExecutionUngroupedUncached.executeQueryWithFuel schema resolvers
              variableValues operation fuel source := by
  intro hvisit
  unfold executeQueryWithFuel ExecutionUngroupedUncached.executeQueryWithFuel
  by_cases hroot : rootSourceAppliesBool schema operation source = true
  · simp [hroot]
    exact
      congrArg Execution.selectionSetResultToResponse
        (executeRootSelectionSet_eq_uncached_of_outputVisitResult schema
          resolvers (GraphQL.Execution.coerceVariableValues operation variableValues)
          fuel (operation.rootType schema) source operation.selectionSet hvisit)
  · simp [hroot]

end ExecutionUngrouped
end Algorithms

end GraphQL
