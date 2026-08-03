import Proofs.GraphQL.Algorithms.ExecutionUngrouped.CachedRefinement.InternalAlignment

/-!
Resolver-source soundness for cached field values.

This layer connects each reusable cached response position to its original
resolver call and compatible executable fields.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

def PreviousCacheSound {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (source : ResolverValue ObjectRef)
    (fieldDefinition : FieldDefinition) (field : ExecutableField)
    (previous : FieldCacheValue ObjectRef)
    : Prop :=
  reusablePreviousValue? schema fieldDefinition.outputType previous = none
  -> ExecutionUngroupedUncached.reusablePreviousValue? schema
          fieldDefinition.outputType (some previous.output)
        = none
      ∧ match previous with
        | .object previousSource _fields =>
            resolvers.resolve field.parentType field.fieldName field.arguments source
            = some previousSource
        | .list (some sourceValues) _values =>
            resolvers.resolve field.parentType field.fieldName field.arguments source
            = some (.list sourceValues)
        | _ => False

def FieldPreviousCacheSound {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (source : ResolverValue ObjectRef)
    (previous? : Option (FieldCacheValue ObjectRef)) (field : ExecutableField)
    : Prop :=
  ∀ fieldDefinition previous,
    schema.lookupField field.parentType field.fieldName = some fieldDefinition
    -> previous? = some previous
    -> PreviousCacheSound schema resolvers source fieldDefinition field previous

def CompletionCacheSound {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (fuel : Nat) (fieldType : TypeRef) (selectionSet : List Selection)
    (value : ResolverValue ObjectRef)
    (previous? : Option (FieldCacheValue ObjectRef))
    : Prop :=
  outputResult FieldCacheValue.output
    (completeValue schema resolvers variableValues fuel fieldType selectionSet
      value previous?)
  = ExecutionUngroupedUncached.completeValue schema resolvers variableValues
      fuel fieldType selectionSet value
      (previous?.map FieldCacheValue.output)

def FieldPreviousCacheContinuationSound {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (completionFuel : Nat)
    (source : ResolverValue ObjectRef) (fieldDefinition : FieldDefinition)
    (field : ExecutableField) (previous : FieldCacheValue ObjectRef)
    : Prop :=
  PreviousCacheSound schema resolvers source fieldDefinition field previous
  ∧ match previous with
    | .object previousSource _fields =>
        CompletionCacheSound schema resolvers variableValues
          completionFuel fieldDefinition.outputType field.selectionSet previousSource
          (some previous)
    | .list (some sourceValues) _values =>
        CompletionCacheSound schema resolvers variableValues
          completionFuel fieldDefinition.outputType field.selectionSet
          (.list sourceValues)
          (some previous)
    | _ => True

def GlobalFieldPreviousCacheSound {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef)
    : Prop :=
  ∀ (source : ResolverValue ObjectRef) (output : FieldCacheValue ObjectRef)
      (parentType responseName fieldName : Name) (arguments : List Argument)
      (selectionSet : List Selection) previous,
    objectField? responseName output = some previous
    -> FieldPreviousCacheSound schema resolvers source (some previous)
        (executableField parentType responseName fieldName arguments selectionSet)

theorem reusablePreviousValue?_scalar_ne_none_of_nonComposite
    {ObjectRef : Type} (schema : Schema) (fieldType : TypeRef) (value : String)
    : fieldType.isCompositeBool schema = false
      -> reusablePreviousValue? schema fieldType
            (FieldCacheValue.scalar (ObjectRef := ObjectRef) value)
          ≠ none := by
  intro hcomposite hnone
  simp [reusablePreviousValue?, hcomposite] at hnone

theorem reusablePreviousValue?_list_none_ne_none_of_nonComposite
    {ObjectRef : Type} (schema : Schema) (fieldType : TypeRef)
    (values : List (FieldCacheValue ObjectRef))
    : fieldType.isCompositeBool schema = false
      -> reusablePreviousValue? schema fieldType (.list none values) ≠ none := by
  intro hcomposite hnone
  simp [reusablePreviousValue?, hcomposite] at hnone

theorem PreviousCacheSound.null {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (source : ResolverValue ObjectRef)
    (fieldDefinition : FieldDefinition) (field : ExecutableField)
    : PreviousCacheSound schema resolvers source fieldDefinition field .null := by
  intro hreuse
  simp [reusablePreviousValue?] at hreuse

theorem PreviousCacheSound.scalar_of_nonComposite {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source : ResolverValue ObjectRef) (fieldDefinition : FieldDefinition)
    (field : ExecutableField) (value : String)
    : fieldDefinition.outputType.isCompositeBool schema = false
      -> PreviousCacheSound schema resolvers source fieldDefinition field
          (.scalar value) := by
  intro hcomposite hreuse
  exact False.elim
    (reusablePreviousValue?_scalar_ne_none_of_nonComposite schema
      fieldDefinition.outputType value hcomposite hreuse)

theorem PreviousCacheSound.list_none_of_nonComposite {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source : ResolverValue ObjectRef) (fieldDefinition : FieldDefinition)
    (field : ExecutableField) (values : List (FieldCacheValue ObjectRef))
    : fieldDefinition.outputType.isCompositeBool schema = false
      -> PreviousCacheSound schema resolvers source fieldDefinition field
          (.list none values) := by
  intro hcomposite hreuse
  exact False.elim
    (reusablePreviousValue?_list_none_ne_none_of_nonComposite schema
      fieldDefinition.outputType values hcomposite hreuse)

theorem PreviousCacheSound.object {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (source previousSource : ResolverValue ObjectRef)
    (fieldDefinition : FieldDefinition) (field : ExecutableField)
    (fields : List (Name × FieldCacheValue ObjectRef))
    : ExecutionUngroupedUncached.reusablePreviousValue? schema
          fieldDefinition.outputType
          (some (ResponseValue.object (outputFields fields)))
        = none
      -> resolvers.resolve field.parentType field.fieldName field.arguments source
          = some previousSource
      -> PreviousCacheSound schema resolvers source fieldDefinition field
          (.object previousSource fields) := by
  intro hreuseOut hresolve _hreuse
  constructor
  · simpa using hreuseOut
  · exact hresolve

theorem PreviousCacheSound.object_of_composite {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source previousSource : ResolverValue ObjectRef)
    (fieldDefinition : FieldDefinition) (field : ExecutableField)
    (fields : List (Name × FieldCacheValue ObjectRef))
    : fieldDefinition.outputType.isCompositeBool schema = true
      -> resolvers.resolve field.parentType field.fieldName field.arguments source
          = some previousSource
      -> PreviousCacheSound schema resolvers source fieldDefinition field
          (.object previousSource fields) := by
  intro hcomposite hresolve
  apply PreviousCacheSound.object schema resolvers source previousSource
    fieldDefinition field fields
  · simp [ExecutionUngroupedUncached.reusablePreviousValue?, hcomposite]
  · exact hresolve

theorem PreviousCacheSound.list_some {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (source : ResolverValue ObjectRef)
    (sourceValues : List (ResolverValue ObjectRef))
    (fieldDefinition : FieldDefinition) (field : ExecutableField)
    (values : List (FieldCacheValue ObjectRef))
    : ExecutionUngroupedUncached.reusablePreviousValue? schema
          fieldDefinition.outputType (some (ResponseValue.list (outputValues values)))
        = none
      -> resolvers.resolve field.parentType field.fieldName field.arguments source
          = some (.list sourceValues)
      -> PreviousCacheSound schema resolvers source fieldDefinition field
          (.list (some sourceValues) values) := by
  intro hreuseOut hresolve _hreuse
  constructor
  · simpa using hreuseOut
  · exact hresolve

theorem PreviousCacheSound.list_some_of_composite {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source : ResolverValue ObjectRef)
    (sourceValues : List (ResolverValue ObjectRef))
    (fieldDefinition : FieldDefinition) (field : ExecutableField)
    (values : List (FieldCacheValue ObjectRef))
    : fieldDefinition.outputType.isCompositeBool schema = true
      -> resolvers.resolve field.parentType field.fieldName field.arguments source
          = some (.list sourceValues)
      -> PreviousCacheSound schema resolvers source fieldDefinition field
          (.list (some sourceValues) values) := by
  intro hcomposite hresolve
  apply PreviousCacheSound.list_some schema resolvers source sourceValues
    fieldDefinition field values
  · simp [ExecutionUngroupedUncached.reusablePreviousValue?, hcomposite]
  · exact hresolve

theorem PreviousCacheSound.of_isCompositeBool_eq {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source : ResolverValue ObjectRef)
    (leftDefinition rightDefinition : FieldDefinition)
    (field : ExecutableField) (previous : FieldCacheValue ObjectRef)
    : leftDefinition.outputType.isCompositeBool schema
        = rightDefinition.outputType.isCompositeBool schema
      -> PreviousCacheSound schema resolvers source leftDefinition field previous
      -> PreviousCacheSound schema resolvers source rightDefinition field previous := by
  intro hcomposite hsound hreuseRight
  cases previous with
  | null =>
      simp [reusablePreviousValue?] at hreuseRight
  | scalar value =>
      have hreuseLeft :
          reusablePreviousValue? schema leftDefinition.outputType
              (FieldCacheValue.scalar (ObjectRef := ObjectRef) value)
            =
            none := by
        simp [reusablePreviousValue?] at hreuseRight ⊢
        simpa [hcomposite] using hreuseRight
      rcases hsound hreuseLeft with ⟨hreuseOutLeft, hsource⟩
      constructor
      · simp [ExecutionUngroupedUncached.reusablePreviousValue?] at hreuseOutLeft ⊢
        simpa [hcomposite] using hreuseOutLeft
      · exact hsource
  | object previousSource fields =>
      have hreuseLeft :
          reusablePreviousValue? schema leftDefinition.outputType
              (FieldCacheValue.object previousSource fields)
            =
            none := by
        simp [reusablePreviousValue?]
      rcases hsound hreuseLeft with ⟨hreuseOutLeft, hsource⟩
      constructor
      · simp [ExecutionUngroupedUncached.reusablePreviousValue?] at hreuseOutLeft ⊢
        simpa [hcomposite] using hreuseOutLeft
      · exact hsource
  | list sourceValues? values =>
      cases sourceValues? with
      | none =>
          have hreuseLeft :
              reusablePreviousValue? schema leftDefinition.outputType
                  (FieldCacheValue.list none values)
                =
                none := by
            simp [reusablePreviousValue?] at hreuseRight ⊢
            simpa [hcomposite] using hreuseRight
          rcases hsound hreuseLeft with ⟨hreuseOutLeft, hsource⟩
          constructor
          · simp [ExecutionUngroupedUncached.reusablePreviousValue?] at hreuseOutLeft ⊢
            simpa [hcomposite] using hreuseOutLeft
          · exact hsource
      | some sourceValues =>
          have hreuseLeft :
              reusablePreviousValue? schema leftDefinition.outputType
                  (FieldCacheValue.list (some sourceValues) values)
                =
                none := by
            simp [reusablePreviousValue?]
          rcases hsound hreuseLeft with ⟨hreuseOutLeft, hsource⟩
          constructor
          · simp [ExecutionUngroupedUncached.reusablePreviousValue?] at hreuseOutLeft ⊢
            simpa [hcomposite] using hreuseOutLeft
          · exact hsource

theorem PreviousCacheSound.resultValueOrNull_nonNullCompletion {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source : ResolverValue ObjectRef) (fieldDefinition : FieldDefinition)
    (field : ExecutableField) (result : Result (FieldCacheValue ObjectRef))
    : PreviousCacheSound schema resolvers source fieldDefinition field
        (resultValueOrNull result)
      -> PreviousCacheSound schema resolvers source fieldDefinition field
          (resultValueOrNull (nonNullCompletion result)) := by
  intro hsound
  cases result with
  | error errors =>
      exact PreviousCacheSound.null schema resolvers source fieldDefinition field
  | ok result =>
      rcases result with ⟨value, errors⟩
      cases value with
      | null =>
          cases errors <;>
            exact PreviousCacheSound.null schema resolvers source fieldDefinition field
      | scalar scalarValue =>
          simpa [resultValueOrNull, nonNullCompletion] using hsound
      | object previousSource fields =>
          simpa [resultValueOrNull, nonNullCompletion] using hsound
      | list sourceValues? values =>
          simpa [resultValueOrNull, nonNullCompletion] using hsound

theorem completeValue_fresh_result_previousCacheSound {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    : ∀ fuel fieldType selectionSet value parentSource fieldDefinition field,
        GraphQL.FieldMerge.sameResponseShape schema fieldType fieldDefinition.outputType
        -> resolvers.resolve field.parentType field.fieldName field.arguments parentSource
            = some value
        -> PreviousCacheSound schema resolvers parentSource fieldDefinition field
            (resultValueOrNull
              (completeValue schema resolvers variableValues fuel fieldType
                selectionSet value none))
  | 0, _fieldType, _selectionSet, _value, parentSource, fieldDefinition, field,
    _hshape, _hresolve => by
      simp [completeValue, resultValueOrNull]
      exact PreviousCacheSound.null schema resolvers parentSource fieldDefinition field
  | fuel + 1, .nonNull inner, selectionSet, value, parentSource, fieldDefinition,
    field, hshape, hresolve => by
      cases hfieldType : fieldDefinition.outputType with
      | nonNull laterInner =>
          let innerDefinition : FieldDefinition :=
            { fieldDefinition with outputType := laterInner }
          have hinnerShape :
              GraphQL.FieldMerge.sameResponseShape schema inner
                innerDefinition.outputType := by
            simpa [innerDefinition, hfieldType,
              GraphQL.FieldMerge.sameResponseShape] using hshape
          have hinner :=
            completeValue_fresh_result_previousCacheSound schema resolvers
              variableValues (fuel + 1) inner selectionSet value parentSource
              innerDefinition field hinnerShape hresolve
          have hcompEq :
              innerDefinition.outputType.isCompositeBool schema
                =
                fieldDefinition.outputType.isCompositeBool schema := by
            simp [innerDefinition, hfieldType, TypeRef.isCompositeBool,
              TypeRef.namedType]
          have hsoundForOuter :=
            PreviousCacheSound.of_isCompositeBool_eq schema resolvers parentSource
              innerDefinition fieldDefinition field
              (resultValueOrNull
                (completeValue schema resolvers variableValues (fuel + 1) inner
                  selectionSet value none))
              hcompEq hinner
          simpa [completeValue] using
            PreviousCacheSound.resultValueOrNull_nonNullCompletion schema resolvers
              parentSource fieldDefinition field
              (completeValue schema resolvers variableValues (fuel + 1) inner
                selectionSet value none)
              hsoundForOuter
      | named name =>
          simp [hfieldType, GraphQL.FieldMerge.sameResponseShape] at hshape
      | list inner =>
          simp [hfieldType, GraphQL.FieldMerge.sameResponseShape] at hshape
  | fuel + 1, .named typeName, selectionSet, value, parentSource,
    fieldDefinition, field, hshape, hresolve => by
      cases value with
      | null =>
          simp [completeValue, resultValueOrNull]
          exact PreviousCacheSound.null schema resolvers parentSource fieldDefinition
            field
      | scalar scalarValue =>
          by_cases hcomposite :
              (TypeRef.named typeName).isCompositeBool schema = true
          · simp [completeValue, hcomposite, resultValueOrNull]
            exact PreviousCacheSound.null schema resolvers parentSource
              fieldDefinition field
          · have hcompositeFalse :
                (TypeRef.named typeName).isCompositeBool schema = false := by
              cases h : (TypeRef.named typeName).isCompositeBool schema
              · rfl
              · contradiction
            have hshapeComposite :=
              sameResponseShape_isCompositeBool_eq schema (TypeRef.named typeName)
                fieldDefinition.outputType hshape
            have hlaterComposite :
                fieldDefinition.outputType.isCompositeBool schema = false := by
              rw [← hshapeComposite]
              exact hcompositeFalse
            simp [completeValue, hcompositeFalse, resultValueOrNull]
            exact
              PreviousCacheSound.scalar_of_nonComposite schema resolvers
                parentSource fieldDefinition field scalarValue hlaterComposite
      | object runtimeType ref =>
          by_cases hinclude :
              schema.typeIncludesObjectBool typeName runtimeType = true
          · have hfirstComposite :
                (TypeRef.named typeName).isCompositeBool schema = true :=
              named_isCompositeBool_eq_true_of_typeIncludesObjectBool schema
                typeName runtimeType hinclude
            have hshapeComposite :=
              sameResponseShape_isCompositeBool_eq schema (TypeRef.named typeName)
                fieldDefinition.outputType hshape
            have hlaterComposite :
                fieldDefinition.outputType.isCompositeBool schema = true := by
              rw [← hshapeComposite]
              exact hfirstComposite
            generalize hvisited :
              visitSubfields schema resolvers variableValues fuel runtimeType
                  (ResolverValue.object runtimeType ref) selectionSet
                  (FieldCacheValue.object (ResolverValue.object runtimeType ref) [])
              =
              visited
            have hobject :=
              visitSubfields_value_object schema resolvers variableValues fuel
                runtimeType (ResolverValue.object runtimeType ref) selectionSet
                (ResolverValue.object runtimeType ref) []
            rw [hvisited] at hobject
            cases hstatus : visited.status with
            | error errors =>
                simp [completeValue, hinclude, hvisited, hstatus,
                  catchVisitBubbleAsNull, resultValueOrNull, reuseOrCreateObject?]
                exact PreviousCacheSound.null schema resolvers parentSource
                  fieldDefinition field
            | ok ok =>
                rcases hobject with ⟨resultFields, hvalue⟩
                rcases ok with ⟨_unit, errors⟩
                simp [completeValue, hinclude, hvisited, hstatus,
                  catchVisitBubbleAsNull, resultValueOrNull, reuseOrCreateObject?,
                  hvalue]
                exact
                  PreviousCacheSound.object_of_composite schema resolvers
                    parentSource (ResolverValue.object runtimeType ref)
                    fieldDefinition field resultFields hlaterComposite hresolve
          · have hincludeFalse :
                schema.typeIncludesObjectBool typeName runtimeType = false := by
              cases h : schema.typeIncludesObjectBool typeName runtimeType
              · rfl
              · contradiction
            simp [completeValue, hincludeFalse, resultValueOrNull]
            exact PreviousCacheSound.null schema resolvers parentSource
              fieldDefinition field
      | list values =>
          simp [completeValue, resultValueOrNull]
          exact PreviousCacheSound.null schema resolvers parentSource fieldDefinition
            field
  | fuel + 1, .list inner, selectionSet, value, parentSource, fieldDefinition,
    field, hshape, hresolve => by
      cases value with
      | list values =>
          by_cases hcomposite : inner.isCompositeBool schema = true
          · have hshapeComposite :=
              sameResponseShape_isCompositeBool_eq schema (TypeRef.list inner)
                fieldDefinition.outputType hshape
            have hlaterComposite :
                fieldDefinition.outputType.isCompositeBool schema = true := by
              rw [← hshapeComposite]
              simpa [TypeRef.isCompositeBool, TypeRef.namedType] using hcomposite
            generalize hcompleted :
              completeValueList schema resolvers variableValues fuel inner
                  selectionSet values []
              =
              completed
            cases completed with
            | error errors =>
                simp [completeValue, hcomposite, hcompleted, catchBubbleAsNull,
                  resultValueOrNull, reuseOrCreateList?]
                exact PreviousCacheSound.null schema resolvers parentSource
                  fieldDefinition field
            | ok completed =>
                rcases completed with ⟨completedValues, errors⟩
                simp [completeValue, hcomposite, hcompleted, catchBubbleAsNull,
                  resultValueOrNull, reuseOrCreateList?]
                exact
                  PreviousCacheSound.list_some_of_composite schema resolvers
                    parentSource values fieldDefinition field completedValues
                    hlaterComposite hresolve
          · have hcompositeFalse : inner.isCompositeBool schema = false := by
              cases h : inner.isCompositeBool schema
              · rfl
              · contradiction
            have hshapeComposite :=
              sameResponseShape_isCompositeBool_eq schema (TypeRef.list inner)
                fieldDefinition.outputType hshape
            have hlaterComposite :
                fieldDefinition.outputType.isCompositeBool schema = false := by
              rw [← hshapeComposite]
              simpa [TypeRef.isCompositeBool, TypeRef.namedType] using hcompositeFalse
            generalize hcompleted :
              completeValueList schema resolvers variableValues fuel inner
                  selectionSet values []
              =
              completed
            cases completed with
            | error errors =>
                simp [completeValue, hcompositeFalse, hcompleted, catchBubbleAsNull,
                  resultValueOrNull, reuseOrCreateList?]
                exact PreviousCacheSound.null schema resolvers parentSource
                  fieldDefinition field
            | ok completed =>
                rcases completed with ⟨completedValues, errors⟩
                simp [completeValue, hcompositeFalse, hcompleted, catchBubbleAsNull,
                  resultValueOrNull, reuseOrCreateList?]
                exact
                  PreviousCacheSound.list_none_of_nonComposite schema resolvers
                    parentSource fieldDefinition field completedValues
                    hlaterComposite
      | null =>
          simp [completeValue, resultValueOrNull]
          exact PreviousCacheSound.null schema resolvers parentSource fieldDefinition
            field
      | scalar scalarValue =>
          simp [completeValue, resultValueOrNull]
          exact PreviousCacheSound.null schema resolvers parentSource fieldDefinition
            field
      | object runtimeType ref =>
          simp [completeValue, resultValueOrNull]
          exact PreviousCacheSound.null schema resolvers parentSource fieldDefinition
            field

theorem executeField_none_result_previousCacheSound_of_sameResponseShape
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (source : ResolverValue ObjectRef)
    (first later : ExecutableField)
    (firstDefinition laterDefinition : FieldDefinition)
    : schema.lookupField first.parentType first.fieldName = some firstDefinition
      -> schema.lookupField later.parentType later.fieldName = some laterDefinition
      -> GraphQL.FieldMerge.sameResponseShape schema firstDefinition.outputType
          laterDefinition.outputType
      -> resolvers.resolve first.parentType first.fieldName first.arguments source
          = resolvers.resolve later.parentType later.fieldName later.arguments source
      -> PreviousCacheSound schema resolvers source laterDefinition later
          (resultValueOrNull
            (executeField schema resolvers variableValues completionFuel source none
              first)) := by
  intro hlookupFirst _hlookupLater hshape hresolveEq
  unfold executeField
  simp [hlookupFirst]
  cases hresolveFirst :
      resolvers.resolve first.parentType first.fieldName first.arguments source with
  | none =>
      simp [handleFieldError, resultValueOrNull]
      cases firstDefinition.outputType <;>
        exact PreviousCacheSound.null schema resolvers source laterDefinition later
  | some resolved =>
      have hresolveLater :
          resolvers.resolve later.parentType later.fieldName later.arguments source
            =
            some resolved := by
        rw [← hresolveEq]
        exact hresolveFirst
      simp
      exact
        completeValue_fresh_result_previousCacheSound schema resolvers
          variableValues completionFuel firstDefinition.outputType
          first.selectionSet resolved source laterDefinition later hshape
          hresolveLater

theorem PreviousCacheSound.mergeResponse_left {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source : ResolverValue ObjectRef) (fieldDefinition : FieldDefinition)
    (field : ExecutableField)
    (previous incoming : FieldCacheValue ObjectRef)
    : PreviousCacheSound schema resolvers source fieldDefinition field previous
      -> PreviousCacheSound schema resolvers source fieldDefinition field
          (mergeResponse previous incoming) := by
  intro hsound
  cases previous with
  | null =>
      simp [mergeResponse]
      exact PreviousCacheSound.null schema resolvers source fieldDefinition field
  | scalar value =>
      cases incoming with
      | null =>
          simp [mergeResponse]
          exact PreviousCacheSound.null schema resolvers source fieldDefinition field
      | scalar incomingValue =>
          simp [mergeResponse]
          exact hsound
      | object incomingSource incomingFields =>
          simp [mergeResponse]
          exact hsound
      | list sourceValues? values =>
          simp [mergeResponse]
          exact hsound
  | object previousSource fields =>
      cases incoming with
      | null =>
          simp [mergeResponse]
          exact PreviousCacheSound.null schema resolvers source fieldDefinition field
      | scalar value =>
          simp [mergeResponse]
          exact hsound
      | object incomingSource incomingFields =>
          simp [mergeResponse]
          intro hreuse
          have hsoundPrevious := hsound (by simp [reusablePreviousValue?])
          rcases hsoundPrevious with ⟨hreuseOut, hresolve⟩
          constructor
          · simpa [ExecutionUngroupedUncached.reusablePreviousValue?] using hreuseOut
          · exact hresolve
      | list sourceValues? values =>
          simp [mergeResponse]
          exact hsound
  | list sourceValues? values =>
      cases incoming with
      | null =>
          simp [mergeResponse]
          exact PreviousCacheSound.null schema resolvers source fieldDefinition field
      | scalar value =>
          simp [mergeResponse]
          exact hsound
      | object incomingSource incomingFields =>
          simp [mergeResponse]
          exact hsound
      | list incomingSourceValues? incomingValues =>
          simp [mergeResponse]
          intro hreuse
          cases sourceValues? with
          | none =>
              have hreusePrevious :
                  reusablePreviousValue? schema fieldDefinition.outputType
                      (FieldCacheValue.list none values)
                    =
                    none := by
                simp [reusablePreviousValue?] at hreuse ⊢
                exact hreuse
              have hsoundPrevious := hsound hreusePrevious
              rcases hsoundPrevious with ⟨hreuseOut, hresolve⟩
              constructor
              · simpa [ExecutionUngroupedUncached.reusablePreviousValue?] using
                  hreuseOut
              · exact hresolve
          | some sourceValues =>
              have hreusePrevious :
                  reusablePreviousValue? schema fieldDefinition.outputType
                      (FieldCacheValue.list (some sourceValues) values)
                    =
                    none := by
                simp [reusablePreviousValue?]
              have hsoundPrevious := hsound hreusePrevious
              rcases hsoundPrevious with ⟨hreuseOut, hresolve⟩
              constructor
              · simpa [ExecutionUngroupedUncached.reusablePreviousValue?] using
                  hreuseOut
              · exact hresolve

theorem PreviousCacheSound.of_absorptionShape {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source : ResolverValue ObjectRef) (fieldDefinition : FieldDefinition)
    (field : ExecutableField)
    (previous output : FieldCacheValue ObjectRef)
    : PreviousCacheSound schema resolvers source fieldDefinition field previous
      -> FieldCacheAbsorptionShape previous output
      -> PreviousCacheSound schema resolvers source fieldDefinition field output := by
  intro hsound hshape
  have hmerged :=
    PreviousCacheSound.mergeResponse_left schema resolvers source fieldDefinition
      field previous output hsound
  rw [hshape.to_absorbs] at hmerged
  exact hmerged

def OutputCacheSoundForFields {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (source : ResolverValue ObjectRef)
    (fields : List ExecutableField)
    (output : FieldCacheValue ObjectRef)
    : Prop :=
  ∀ field fieldDefinition previous,
    field ∈ fields
    -> objectField? field.responseName output = some previous
    -> schema.lookupField field.parentType field.fieldName = some fieldDefinition
    -> PreviousCacheSound schema resolvers source fieldDefinition field previous

theorem OutputCacheSoundForFields.fieldPreviousCacheSound {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source : ResolverValue ObjectRef)
    (fields : List ExecutableField)
    (output : FieldCacheValue ObjectRef)
    (field : ExecutableField)
    : OutputCacheSoundForFields schema resolvers source fields output
      -> field ∈ fields
      -> FieldPreviousCacheSound schema resolvers source
          (objectField? field.responseName output) field := by
  intro hsound hfield fieldDefinition previous hlookup hprevious
  exact hsound field fieldDefinition previous hfield hprevious hlookup

theorem OutputCacheSoundForFields.empty_object {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source objectSource : ResolverValue ObjectRef)
    (fields : List ExecutableField)
    : OutputCacheSoundForFields schema resolvers source fields
        (.object objectSource []) := by
  intro field fieldDefinition previous _hfield hprevious _hlookup
  simp [objectField?, lookupField?] at hprevious

theorem OutputCacheSoundForFields.mono {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source : ResolverValue ObjectRef)
    (sourceFields targetFields : List ExecutableField)
    (output : FieldCacheValue ObjectRef)
    : (∀ field, field ∈ targetFields -> field ∈ sourceFields)
      -> OutputCacheSoundForFields schema resolvers source sourceFields output
      -> OutputCacheSoundForFields schema resolvers source targetFields output := by
  intro hsubset hsound field fieldDefinition previous hfield hprevious hlookup
  exact hsound field fieldDefinition previous (hsubset field hfield) hprevious hlookup

theorem OutputCacheSoundForFields.mergeResponseFieldIntoObject {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source : ResolverValue ObjectRef)
    (fields : List ExecutableField)
    (output incoming : FieldCacheValue ObjectRef) (responseName : Name)
    : OutputCacheSoundForFields schema resolvers source fields output
      -> (∀ field fieldDefinition,
            field ∈ fields
            -> field.responseName = responseName
            -> schema.lookupField field.parentType field.fieldName = some fieldDefinition
            -> PreviousCacheSound schema resolvers source fieldDefinition field incoming)
      -> OutputCacheSoundForFields schema resolvers source fields
          (mergeResponseFieldIntoObject responseName incoming output) := by
  intro hsound hincoming field fieldDefinition previous hfield hprevious hlookup
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
  | object objectSource outputFields =>
      simp [GraphQL.Algorithms.ExecutionUngrouped.mergeResponseFieldIntoObject,
        objectField?] at hprevious
      by_cases htarget : field.responseName = responseName
      · have hpreviousLookup :
            lookupField? field.responseName
                (mergeResponseField responseName incoming outputFields)
              =
              some previous := by
          exact hprevious
        rw [htarget] at hpreviousLookup
        rw [lookupField?_mergeResponseField_self] at hpreviousLookup
        cases hlookupExisting : lookupField? responseName outputFields with
        | none =>
            simp [hlookupExisting] at hpreviousLookup
            subst previous
            exact hincoming field fieldDefinition hfield htarget hlookup
        | some existing =>
            simp [hlookupExisting] at hpreviousLookup
            subst previous
            exact
              PreviousCacheSound.mergeResponse_left schema resolvers source
                fieldDefinition field existing incoming
                (hsound field fieldDefinition existing hfield
                  (by simp [objectField?, htarget, hlookupExisting]) hlookup)
      · have hpreviousLookup :
            lookupField? field.responseName
                (mergeResponseField responseName incoming outputFields)
              =
              some previous := by
          exact hprevious
        have hlookupOld :
            lookupField? field.responseName outputFields = some previous := by
          rw [lookupField?_mergeResponseField_other field.responseName responseName
            incoming htarget] at hpreviousLookup
          exact hpreviousLookup
        exact hsound field fieldDefinition previous hfield
          (by simp [objectField?, hlookupOld]) hlookup

def OutputCacheContinuationSoundForFields {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (completionFuel : Nat)
    (source : ResolverValue ObjectRef) (fields : List ExecutableField)
    (output : FieldCacheValue ObjectRef)
    : Prop :=
  ∀ field fieldDefinition previous,
    field ∈ fields
    -> objectField? field.responseName output = some previous
    -> schema.lookupField field.parentType field.fieldName = some fieldDefinition
    -> FieldPreviousCacheContinuationSound schema resolvers variableValues
        completionFuel source fieldDefinition field previous

theorem OutputCacheContinuationSoundForFields.fieldPrevious {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (source : ResolverValue ObjectRef)
    (completionFuel : Nat)
    (fields : List ExecutableField) (output : FieldCacheValue ObjectRef)
    (field : ExecutableField)
    : OutputCacheContinuationSoundForFields schema resolvers variableValues
        completionFuel source fields output
      -> field ∈ fields
      -> ∀ fieldDefinition previous,
          schema.lookupField field.parentType field.fieldName = some fieldDefinition
          -> objectField? field.responseName output = some previous
          -> FieldPreviousCacheContinuationSound schema resolvers variableValues
              completionFuel source fieldDefinition field previous := by
  intro hsound hfield fieldDefinition previous hlookup hprevious
  exact hsound field fieldDefinition previous hfield hprevious hlookup

theorem OutputCacheContinuationSoundForFields.to_previousCacheSound
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (source : ResolverValue ObjectRef)
    (completionFuel : Nat)
    (fields : List ExecutableField) (output : FieldCacheValue ObjectRef)
    : OutputCacheContinuationSoundForFields schema resolvers variableValues
        completionFuel source fields output
      -> OutputCacheSoundForFields schema resolvers source fields output := by
  intro hsound field fieldDefinition previous hfield hprevious hlookup
  exact (hsound field fieldDefinition previous hfield hprevious hlookup).1

theorem OutputCacheContinuationSoundForFields.empty_object {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (completionFuel : Nat)
    (source objectSource : ResolverValue ObjectRef)
    (fields : List ExecutableField)
    : OutputCacheContinuationSoundForFields schema resolvers variableValues
        completionFuel source fields (.object objectSource []) := by
  intro field fieldDefinition previous _hfield hprevious _hlookup
  simp [objectField?, lookupField?] at hprevious

theorem OutputCacheContinuationSoundForFields.mono {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (source : ResolverValue ObjectRef)
    (completionFuel : Nat)
    (sourceFields targetFields : List ExecutableField)
    (output : FieldCacheValue ObjectRef)
    : (∀ field, field ∈ targetFields -> field ∈ sourceFields)
      -> OutputCacheContinuationSoundForFields schema resolvers variableValues
          completionFuel source sourceFields output
      -> OutputCacheContinuationSoundForFields schema resolvers variableValues
          completionFuel source targetFields output := by
  intro hsubset hsound field fieldDefinition previous hfield hprevious hlookup
  exact hsound field fieldDefinition previous (hsubset field hfield) hprevious hlookup

theorem OutputCacheContinuationSoundForFields.updateResponseName
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (source : ResolverValue ObjectRef)
    (completionFuel : Nat)
    (fields : List ExecutableField) (output incoming : FieldCacheValue ObjectRef)
    (responseName : Name)
    : OutputCacheContinuationSoundForFields schema resolvers variableValues
        completionFuel source fields output
      -> (∀ field fieldDefinition previous,
            field ∈ fields
            -> field.responseName = responseName
            -> objectField? responseName
                  (mergeResponseFieldIntoObject responseName incoming output)
                = some previous
            -> schema.lookupField field.parentType field.fieldName = some fieldDefinition
            -> FieldPreviousCacheContinuationSound schema resolvers variableValues
                completionFuel source fieldDefinition field previous)
      -> OutputCacheContinuationSoundForFields schema resolvers variableValues
          completionFuel source fields
          (mergeResponseFieldIntoObject responseName incoming output) := by
  intro hsound hupdated field fieldDefinition previous hfield hprevious hlookup
  by_cases htarget : field.responseName = responseName
  · exact hupdated field fieldDefinition previous hfield htarget
      (by simpa [htarget] using hprevious) hlookup
  · cases output with
    | null =>
        simp [mergeResponseFieldIntoObject, objectField?] at hprevious
    | scalar value =>
        simp [mergeResponseFieldIntoObject, objectField?] at hprevious
    | list sourceValues? values =>
        simp [mergeResponseFieldIntoObject, objectField?] at hprevious
    | object objectSource outputFields =>
        have hpreviousLookup :
            lookupField? field.responseName
                (mergeResponseField responseName incoming outputFields)
              = some previous := by
          simpa [mergeResponseFieldIntoObject, objectField?] using hprevious
        have hlookupOld :
            lookupField? field.responseName outputFields = some previous := by
          rw [lookupField?_mergeResponseField_other field.responseName responseName
            incoming htarget] at hpreviousLookup
          exact hpreviousLookup
        exact hsound field fieldDefinition previous hfield
          (by simp [objectField?, hlookupOld]) hlookup

def OutputCacheSoundForGroups {ObjectRef : Type} (schema : Schema)
    (resolvers : Resolvers ObjectRef) (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    (output : FieldCacheValue ObjectRef)
    : Prop :=
  ∀ responseName fields field fieldDefinition previous,
    (responseName, fields) ∈ groups
    -> field ∈ fields
    -> objectField? responseName output = some previous
    -> schema.lookupField field.parentType field.fieldName = some fieldDefinition
    -> PreviousCacheSound schema resolvers source fieldDefinition field previous

theorem OutputCacheSoundForGroups.fieldPreviousCacheSound {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    (output : FieldCacheValue ObjectRef)
    (field : ExecutableField) (fields : List ExecutableField)
    : OutputCacheSoundForGroups schema resolvers source groups output
      -> (field.responseName, fields) ∈ groups
      -> field ∈ fields
      -> FieldPreviousCacheSound schema resolvers source
          (objectField? field.responseName output) field := by
  intro hsound hgroup hfield fieldDefinition previous hlookup hprevious
  exact
    hsound field.responseName fields field fieldDefinition previous hgroup hfield
      hprevious hlookup

theorem OutputCacheSoundForGroups.empty_object {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source objectSource : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    : OutputCacheSoundForGroups schema resolvers source groups
        (.object objectSource []) := by
  intro responseName fields field fieldDefinition previous _hgroup _hfield
    hprevious _hlookup
  simp [objectField?, lookupField?] at hprevious

theorem OutputCacheSoundForGroups.mergeResponseFieldIntoObject {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    (output incoming : FieldCacheValue ObjectRef) (responseName : Name)
    : OutputCacheSoundForGroups schema resolvers source groups output
      -> (∀ fields field fieldDefinition,
            (responseName, fields) ∈ groups
            -> field ∈ fields
            -> schema.lookupField field.parentType field.fieldName = some fieldDefinition
            -> PreviousCacheSound schema resolvers source fieldDefinition field incoming)
      -> OutputCacheSoundForGroups schema resolvers source groups
          (mergeResponseFieldIntoObject responseName incoming output) := by
  intro hsound hincoming targetName fields field fieldDefinition previous hgroup
    hfield hprevious hlookup
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
  | object objectSource outputFields =>
      simp [GraphQL.Algorithms.ExecutionUngrouped.mergeResponseFieldIntoObject,
        objectField?] at hprevious
      by_cases htarget : targetName = responseName
      · subst targetName
        have hpreviousLookup :
            lookupField? responseName
                (mergeResponseField responseName incoming outputFields)
              =
              some previous := by
          exact hprevious
        rw [lookupField?_mergeResponseField_self] at hpreviousLookup
        cases hlookupExisting : lookupField? responseName outputFields with
        | none =>
            simp [hlookupExisting] at hpreviousLookup
            subst previous
            exact hincoming fields field fieldDefinition hgroup hfield hlookup
        | some existing =>
            simp [hlookupExisting] at hpreviousLookup
            subst previous
            exact
              PreviousCacheSound.mergeResponse_left schema resolvers source
                fieldDefinition field existing incoming
                (hsound responseName fields field fieldDefinition existing hgroup
                  hfield (by simp [objectField?, hlookupExisting]) hlookup)
      · have hpreviousLookup :
            lookupField? targetName
                (mergeResponseField responseName incoming outputFields)
              =
              some previous := by
          exact hprevious
        have hlookupOld :
            lookupField? targetName outputFields = some previous := by
          rw [lookupField?_mergeResponseField_other targetName responseName
            incoming htarget] at hpreviousLookup
          exact hpreviousLookup
        exact hsound targetName fields field fieldDefinition previous hgroup hfield
          (by simp [objectField?, hlookupOld]) hlookup

theorem collectedGroup_sameResponseShape_of_fieldCompatible
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType responseName : Name)
    (groups : List (Name × List ExecutableField))
    (fields : List ExecutableField)
    (first later : ExecutableField)
    (firstDefinition laterDefinition : FieldDefinition)
    : ExecutionUngroupedUncached.Eager.CollectedGroupsResponseName groups
      -> ExecutionUngroupedUncached.Eager.CollectedGroupsParent parentType groups
      -> ExecutionUngroupedUncached.Eager.CollectedGroupsFieldValidationMergeCompatible
          groups
      -> (responseName, fields) ∈ groups
      -> first ∈ fields
      -> later ∈ fields
      -> schema.lookupField first.parentType first.fieldName = some firstDefinition
      -> schema.lookupField later.parentType later.fieldName = some laterDefinition
      -> GraphQL.FieldMerge.sameResponseShape schema firstDefinition.outputType
          laterDefinition.outputType := by
  intro hresponses hparents hcompatible hgroup hfirst hlater hlookupFirst
    hlookupLater
  have hresponseEq : first.responseName = later.responseName := by
    rw [hresponses responseName fields hgroup first hfirst,
      hresponses responseName fields hgroup later hlater]
  have hfieldEq : first.fieldName = later.fieldName :=
    (hcompatible responseName fields hgroup first later hfirst hlater hresponseEq).1
  have hparentFirst : first.parentType = parentType :=
    hparents responseName fields hgroup first hfirst
  have hparentLater : later.parentType = parentType :=
    hparents responseName fields hgroup later hlater
  have hlookupLaterAtFirst :
      schema.lookupField first.parentType first.fieldName = some laterDefinition := by
    rw [hparentFirst, hfieldEq]
    rw [hparentLater] at hlookupLater
    exact hlookupLater
  rw [hlookupFirst] at hlookupLaterAtFirst
  injection hlookupLaterAtFirst with hdefinitionEq
  subst laterDefinition
  exact GraphQL.FieldMerge.sameResponseShape_refl schema firstDefinition.outputType
    (SchemaWellFormedness.schemaWellFormed_lookupField_outputType hschema
      hlookupFirst)

theorem executeField_none_result_previousCacheSound_of_collectedGroup
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (parentType responseName : Name) (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    (fields : List ExecutableField)
    (first later : ExecutableField)
    (firstDefinition laterDefinition : FieldDefinition)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ExecutionUngroupedUncached.Eager.CollectedGroupsResponseName groups
      -> ExecutionUngroupedUncached.Eager.CollectedGroupsParent parentType groups
      -> ExecutionUngroupedUncached.Eager.CollectedGroupsFieldValidationMergeCompatible
          groups
      -> ExecutionUngroupedUncached.Eager.CollectedGroupsResolveStable resolvers
          source groups
      -> (responseName, fields) ∈ groups
      -> first ∈ fields
      -> later ∈ fields
      -> schema.lookupField first.parentType first.fieldName = some firstDefinition
      -> schema.lookupField later.parentType later.fieldName = some laterDefinition
      -> PreviousCacheSound schema resolvers source laterDefinition later
          (resultValueOrNull
            (executeField schema resolvers variableValues completionFuel source none
              first)) := by
  intro hschema hresponses hparents hcompatible hstable hgroup hfirst hlater
    hlookupFirst hlookupLater
  have hshape :=
    collectedGroup_sameResponseShape_of_fieldCompatible schema hschema parentType
      responseName groups fields first later firstDefinition laterDefinition
      hresponses hparents hcompatible hgroup hfirst hlater hlookupFirst
      hlookupLater
  have hresponseEq : first.responseName = later.responseName := by
    rw [hresponses responseName fields hgroup first hfirst,
      hresponses responseName fields hgroup later hlater]
  have hresolveEq :
      resolvers.resolve first.parentType first.fieldName first.arguments source
        =
        resolvers.resolve later.parentType later.fieldName later.arguments
          source :=
    (ExecutionUngroupedUncached.Eager.CollectedGroupsResolveStable.group
        resolvers source groups responseName fields hstable hgroup)
      first later hfirst hlater hresponseEq
  exact
    executeField_none_result_previousCacheSound_of_sameResponseShape schema
      resolvers variableValues completionFuel source first later firstDefinition
      laterDefinition hlookupFirst hlookupLater hshape hresolveEq

theorem executableFields_sameResponseShape_of_fieldCompatible
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType : Name) (fields : List ExecutableField)
    (first later : ExecutableField)
    (firstDefinition laterDefinition : FieldDefinition)
    : ExecutionUngroupedUncached.Eager.ExecutableFieldsParent parentType fields
      -> ExecutionUngroupedUncached.Eager.ExecutableFieldsFieldValidationMergeCompatible
          fields
      -> first ∈ fields
      -> later ∈ fields
      -> first.responseName = later.responseName
      -> schema.lookupField first.parentType first.fieldName = some firstDefinition
      -> schema.lookupField later.parentType later.fieldName = some laterDefinition
      -> GraphQL.FieldMerge.sameResponseShape schema firstDefinition.outputType
          laterDefinition.outputType := by
  intro hparents hcompatible hfirst hlater hresponseEq hlookupFirst hlookupLater
  have hfieldEq : first.fieldName = later.fieldName :=
    (hcompatible first later hfirst hlater hresponseEq).1
  have hparentFirst : first.parentType = parentType := hparents first hfirst
  have hparentLater : later.parentType = parentType := hparents later hlater
  have hlookupLaterAtFirst :
      schema.lookupField first.parentType first.fieldName = some laterDefinition := by
    rw [hparentFirst, hfieldEq]
    rw [hparentLater] at hlookupLater
    exact hlookupLater
  rw [hlookupFirst] at hlookupLaterAtFirst
  injection hlookupLaterAtFirst with hdefinitionEq
  subst laterDefinition
  exact GraphQL.FieldMerge.sameResponseShape_refl schema firstDefinition.outputType
    (SchemaWellFormedness.schemaWellFormed_lookupField_outputType hschema
      hlookupFirst)

theorem executableFields_resolve_eq_of_fieldCompatible
    {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    (source : ResolverValue ObjectRef)
    (parentType : Name) (fields : List ExecutableField)
    (first later : ExecutableField)
    : ExecutionUngroupedUncached.Eager.ExecutableFieldsParent parentType fields
      -> ExecutionUngroupedUncached.Eager.ExecutableFieldsFieldValidationMergeCompatible
          fields
      -> first ∈ fields
      -> later ∈ fields
      -> first.responseName = later.responseName
      -> resolvers.resolve first.parentType first.fieldName first.arguments source
          = resolvers.resolve later.parentType later.fieldName later.arguments
              source := by
  intro hparents hcompatible hfirst hlater hresponseEq
  rcases hcompatible first later hfirst hlater hresponseEq with
    ⟨hfieldEq, hargumentsEq⟩
  have hparentFirst : first.parentType = parentType := hparents first hfirst
  have hparentLater : later.parentType = parentType := hparents later hlater
  rw [hparentFirst, hparentLater, hfieldEq]
  exact resolvers.resolve_argumentsEquivalent parentType later.fieldName
    first.arguments later.arguments source hargumentsEq

theorem executeField_none_result_previousCacheSound_of_executableFields
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (fields : List ExecutableField)
    (first later : ExecutableField)
    (firstDefinition laterDefinition : FieldDefinition)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ExecutionUngroupedUncached.Eager.ExecutableFieldsParent parentType fields
      -> ExecutionUngroupedUncached.Eager.ExecutableFieldsFieldValidationMergeCompatible
          fields
      -> first ∈ fields
      -> later ∈ fields
      -> first.responseName = later.responseName
      -> schema.lookupField first.parentType first.fieldName = some firstDefinition
      -> schema.lookupField later.parentType later.fieldName = some laterDefinition
      -> PreviousCacheSound schema resolvers source laterDefinition later
          (resultValueOrNull
            (executeField schema resolvers variableValues completionFuel source none
              first)) := by
  intro hschema hparents hcompatible hfirst hlater hresponseEq hlookupFirst
    hlookupLater
  have hshape :=
    executableFields_sameResponseShape_of_fieldCompatible schema hschema
      parentType fields first later firstDefinition laterDefinition hparents
      hcompatible hfirst hlater hresponseEq hlookupFirst hlookupLater
  have hresolveEq :=
    executableFields_resolve_eq_of_fieldCompatible resolvers source parentType
      fields first later hparents hcompatible hfirst hlater hresponseEq
  exact
    executeField_none_result_previousCacheSound_of_sameResponseShape schema
      resolvers variableValues completionFuel source first later firstDefinition
      laterDefinition hlookupFirst hlookupLater hshape hresolveEq

theorem executeField_none_result_previousCacheSound_of_matchingResponse
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (parentType responseName : Name) (source : ResolverValue ObjectRef)
    (fields : List ExecutableField)
    (first later : ExecutableField)
    (firstDefinition laterDefinition : FieldDefinition)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ExecutionUngroupedUncached.Eager.ExecutableFieldsParent parentType fields
      -> ExecutionUngroupedUncached.Eager.ExecutableFieldsFieldValidationMergeCompatible
          fields
      -> first ∈ fields
      -> later ∈ fields
      -> first.responseName = responseName
      -> later.responseName = responseName
      -> schema.lookupField first.parentType first.fieldName = some firstDefinition
      -> schema.lookupField later.parentType later.fieldName = some laterDefinition
      -> PreviousCacheSound schema resolvers source laterDefinition later
          (resultValueOrNull
            (executeField schema resolvers variableValues completionFuel source none
              first)) := by
  intro hschema hparents hcompatible hfirst hlater hfirstResponse hlaterResponse
    hlookupFirst hlookupLater
  have hresponseEq : first.responseName = later.responseName := by
    rw [hfirstResponse, hlaterResponse]
  exact
    executeField_none_result_previousCacheSound_of_executableFields schema
      resolvers variableValues completionFuel parentType source fields first later
      firstDefinition laterDefinition hschema hparents hcompatible hfirst hlater
      hresponseEq hlookupFirst hlookupLater

theorem OutputCacheSoundForFields.merge_executeField_none {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (fields : List ExecutableField)
    (output : FieldCacheValue ObjectRef)
    (first : ExecutableField)
    (firstDefinition : FieldDefinition)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ExecutionUngroupedUncached.Eager.ExecutableFieldsParent parentType fields
      -> ExecutionUngroupedUncached.Eager.ExecutableFieldsFieldValidationMergeCompatible
          fields
      -> OutputCacheSoundForFields schema resolvers source fields output
      -> first ∈ fields
      -> schema.lookupField first.parentType first.fieldName = some firstDefinition
      -> OutputCacheSoundForFields schema resolvers source fields
          (GraphQL.Algorithms.ExecutionUngrouped.mergeResponseFieldIntoObject
            first.responseName
            (resultValueOrNull
              (executeField schema resolvers variableValues completionFuel source none
                first))
            output) := by
  intro hschema hparents hcompatible hsound hfirst hlookupFirst
  apply OutputCacheSoundForFields.mergeResponseFieldIntoObject
  · exact hsound
  · intro later laterDefinition hlater hlaterResponse hlookupLater
    exact
      executeField_none_result_previousCacheSound_of_matchingResponse schema
        resolvers variableValues completionFuel parentType first.responseName source
        fields first later firstDefinition laterDefinition hschema hparents
        hcompatible hfirst hlater rfl hlaterResponse hlookupFirst hlookupLater

theorem OutputCacheSoundForFields.merge_executeField {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (fields : List ExecutableField) (output : FieldCacheValue ObjectRef)
    (first : ExecutableField) (firstDefinition : FieldDefinition)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ExecutionUngroupedUncached.Eager.ExecutableFieldsParent parentType fields
      -> ExecutionUngroupedUncached.Eager.ExecutableFieldsFieldValidationMergeCompatible
          fields
      -> OutputCacheSoundForFields schema resolvers source fields output
      -> FieldCacheMergeReady output
      -> ObjectFieldCachesInternallyAligned output
      -> first ∈ fields
      -> schema.lookupField first.parentType first.fieldName = some firstDefinition
      -> OutputCacheSoundForFields schema resolvers source fields
          (GraphQL.Algorithms.ExecutionUngrouped.mergeResponseFieldIntoObject
            first.responseName
            (resultValueOrNull
              (executeField schema resolvers variableValues completionFuel source
                (objectField? first.responseName output) first))
            output) := by
  intro hschema hparents hcompatible hsound hready haligned hfirst hlookupFirst
  apply OutputCacheSoundForFields.mergeResponseFieldIntoObject
  · exact hsound
  · intro later laterDefinition hlater hlaterResponse hlookupLater
    cases hprevious : objectField? first.responseName output with
    | none =>
        simpa [hprevious] using
          executeField_none_result_previousCacheSound_of_matchingResponse schema
            resolvers variableValues completionFuel parentType first.responseName
            source fields first later firstDefinition laterDefinition hschema
            hparents hcompatible hfirst hlater rfl hlaterResponse hlookupFirst
            hlookupLater
    | some previous =>
        have hpreviousReady : FieldCacheMergeReady previous := by
          cases output with
          | null => simp [objectField?] at hprevious
          | scalar value => simp [objectField?] at hprevious
          | list sourceValues? values => simp [objectField?] at hprevious
          | object objectSource outputFields =>
              exact
                lookupField?_some_cacheReady objectSource first.responseName
                  outputFields previous hready
                  (by simpa [objectField?] using hprevious)
        have hpreviousAligned : FieldCacheInternallyAligned previous :=
          haligned first.responseName previous hprevious
        have hpreviousSound :
            PreviousCacheSound schema resolvers source laterDefinition later
              previous :=
          hsound later laterDefinition previous hlater
            (by simpa [hlaterResponse] using hprevious) hlookupLater
        have hshape :=
          executeField_cacheAbsorptionShape schema resolvers variableValues
            completionFuel source previous first hpreviousReady hpreviousAligned
        simpa [hprevious] using
          PreviousCacheSound.of_absorptionShape schema resolvers source
            laterDefinition later previous
            (resultValueOrNull
              (executeField schema resolvers variableValues completionFuel source
                (some previous) first))
            hpreviousSound hshape

end ExecutionUngrouped
end Algorithms

end GraphQL
