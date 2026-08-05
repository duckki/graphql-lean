import Proofs.GraphQL.Algorithms.ExecutionBreadth.Semantics.Queue
import Proofs.GraphQL.SchemaWellFormedness.PossibleTypes

/-!
Final wrapper facts for breadth execution.

The local proof surface below is rebuilt against the current runtime model: shared fuel
bound arithmetic, query-envelope reductions, root drain readiness, and the final
`breadthExecutionPreservesSpecExecution` theorem.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionBreadth

open GraphQL.Execution

variable {ObjectRef : Type}

theorem list_find?_some_mem {α : Type} (p : α -> Bool) (a : α)
    : ∀ l : List α, l.find? p = some a -> a ∈ l
  | [], h => by simp at h
  | x :: xs, h => by
      cases hp : p x with
      | true =>
          simp [List.find?, hp] at h
          subst a
          simp
      | false =>
          simp [List.find?, hp] at h
          exact List.mem_cons_of_mem x (list_find?_some_mem p a xs h)

theorem objectType_name_mem_objectTypes (schema : Schema) {objectName : Name}
    : schema.objectType objectName
      -> objectName ∈ schema.objectTypes.map ObjectType.name := by
  intro hobject
  rcases hobject with ⟨objectType, hlookup⟩
  have hlookup' :
      List.find? (fun typeDefinition => typeDefinition.name == objectName)
          schema.allTypes = some (TypeDefinition.object objectType) := by
    simpa [Schema.lookupType] using hlookup
  have hmemAll : TypeDefinition.object objectType ∈ schema.allTypes :=
    list_find?_some_mem (fun typeDefinition => typeDefinition.name == objectName)
      (TypeDefinition.object objectType) schema.allTypes hlookup'
  have hnameBool := List.find?_some hlookup'
  have hname : objectType.name = objectName := by
    simpa [TypeDefinition.name] using hnameBool
  subst objectName
  have hmemTypes : TypeDefinition.object objectType ∈ schema.types := by
    simp [Schema.allTypes, Schema.builtinScalarDefinitions] at hmemAll
    exact hmemAll
  have hobjectMem : objectType ∈ schema.objectTypes := by
    simp [Schema.objectTypes, List.mem_filterMap]
    exact ⟨TypeDefinition.object objectType, hmemTypes, rfl⟩
  exact List.mem_map.mpr ⟨objectType, hobjectMem, rfl⟩

theorem schemaWellFormed_possibleType_mem_objectTypes (schema : Schema)
    : SchemaWellFormedness.schemaWellFormed schema
      -> objectName ∈ schema.getPossibleTypes typeName
      -> objectName ∈ schema.objectTypes.map ObjectType.name := by
  intro hschema hpossible
  exact objectType_name_mem_objectTypes schema
    (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
      hschema typeName objectName hpossible)

theorem name_mem_erase_of_ne_of_mem (x y : Name)
    : ∀ ys : List Name, x ≠ y -> x ∈ ys -> x ∈ ys.erase y
  | [], _hne, hmem => by simp at hmem
  | z :: zs, hne, hmem => by
      cases hyz : (z == y) with
      | true =>
          have hz : z = y := by simpa using hyz
          subst z
          simp [List.erase_cons_head]
          simp at hmem
          rcases hmem with hhead | htail
          · exact False.elim (hne hhead)
          · exact htail
      | false =>
          simp [List.erase_cons_tail, hyz]
          simp at hmem
          rcases hmem with hhead | htail
          · exact Or.inl hhead
          · exact Or.inr (name_mem_erase_of_ne_of_mem x y zs hne htail)

theorem name_nodup_length_le_of_mem
    : ∀ xs ys : List Name, xs.Nodup -> (∀ x, x ∈ xs -> x ∈ ys) -> xs.length <= ys.length
  | [], _ys, _hnodup, _hmem => by simp
  | x :: xs, ys, hnodup, hmem => by
      have hxys : x ∈ ys := hmem x (by simp)
      have hnodup' := hnodup
      simp at hnodup'
      rcases hnodup' with ⟨hxnot, hxsNodup⟩
      have htailMem : ∀ y, y ∈ xs -> y ∈ ys.erase x := by
        intro y hy
        have hyys : y ∈ ys := hmem y (by simp [hy])
        have hyne : y ≠ x := by
          intro hyeq
          subst y
          exact hxnot hy
        exact name_mem_erase_of_ne_of_mem y x ys hyne hyys
      have htail :=
        name_nodup_length_le_of_mem xs (ys.erase x) hxsNodup htailMem
      have heraseLen := List.length_erase_of_mem hxys
      have hysPos : 0 < ys.length := List.length_pos_of_mem hxys
      rw [heraseLen] at htail
      have hlt : xs.length < ys.length :=
        (Nat.le_sub_one_iff_lt hysPos).mp htail
      simpa using Nat.succ_le_of_lt hlt

theorem schemaWellFormed_possibleTypes_length_le_objectTypes
    (schema : Schema) (typeName : Name)
    : SchemaWellFormedness.schemaWellFormed schema
      -> (schema.getPossibleTypes typeName).length <= schema.objectTypes.length := by
  intro hschema
  simpa using
    name_nodup_length_le_of_mem
      (schema.getPossibleTypes typeName)
      (schema.objectTypes.map ObjectType.name)
      (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema typeName)
      (fun objectName hpossible =>
        schemaWellFormed_possibleType_mem_objectTypes
          schema hschema hpossible)

theorem specQueryFuelBound_le_preservationFuelBound
    (schema : Schema) (operation : Operation)
    : specQueryFuelBound schema operation <= preservationFuelBound schema operation := by
  unfold preservationFuelBound
  exact Nat.le_max_left _ _

theorem breadthQueryFuelBound_le_preservationFuelBound
    (schema : Schema) (operation : Operation)
    : breadthQueryFuelBound schema operation
      <= preservationFuelBound schema operation := by
  unfold preservationFuelBound
  exact Nat.le_max_right _ _

theorem specQueryFuelBound_pos (schema : Schema) (operation : Operation)
    : 0 < specQueryFuelBound schema operation := by
  unfold specQueryFuelBound
  omega

theorem breadthQueryFuelBound_pos (schema : Schema) (operation : Operation)
    : 0 < breadthQueryFuelBound schema operation := by
  unfold breadthQueryFuelBound
  omega

theorem preservationFuelBound_pos (schema : Schema) (operation : Operation)
    : 0 < preservationFuelBound schema operation := by
  exact Nat.lt_of_lt_of_le (specQueryFuelBound_pos schema operation)
    (specQueryFuelBound_le_preservationFuelBound schema operation)

theorem executeQueryWithFuel_eq_spec_of_rootSourceAppliesBool_false
    (schema : Schema) (operation : Operation)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : rootSourceAppliesBool schema operation source = false
      -> executeQueryWithFuel schema (ResolverMap.fromSpecResolvers resolvers)
            variableValues operation fuel source
          = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
              operation fuel source := by
  intro hroot
  simp [executeQueryWithFuel, GraphQL.Execution.executeQueryWithFuel, hroot]

theorem executeQueryWithFuel_eq_spec_of_rootSelectionSet_eq
    (schema : Schema) (operation : Operation)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : rootSourceAppliesBool schema operation source = true
      -> executeRootSelectionSet schema (ResolverMap.fromSpecResolvers resolvers)
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            fuel (operation.rootType schema) source operation.selectionSet
          = GraphQL.Execution.executeRootSelectionSet schema resolvers
              (GraphQL.Execution.coerceVariableValues operation variableValues)
              fuel (operation.rootType schema) source operation.selectionSet
      -> executeQueryWithFuel schema (ResolverMap.fromSpecResolvers resolvers)
            variableValues operation fuel source
          = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
              operation fuel source := by
  intro hroot hselection
  simp [executeQueryWithFuel, GraphQL.Execution.executeQueryWithFuel, hroot,
    hselection, GraphQL.Execution.selectionSetResultToResponse]
  rfl

theorem spec_executeRootSelectionSet_empty
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    : GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues fuel
        parentType source []
      = .ok ([], 0) := by
  simp [GraphQL.Execution.executeRootSelectionSet,
    GraphQL.Execution.executeCollectedFields, GraphQL.Execution.collectFields]

theorem executeRootSelectionSet_eq_spec_empty
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    : executeRootSelectionSet schema (ResolverMap.fromSpecResolvers resolvers)
        variableValues fuel parentType source []
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          fuel parentType source [] := by
  rw [queue_executeRootSelectionSet_empty, spec_executeRootSelectionSet_empty]

theorem breadthExecutionPreservesSpecExecution_of_empty_root_selectionSet
    (schema : Schema) (operation : Operation)
    (hselectionSet : operation.selectionSet = [])
    : breadthExecutionPreservesSpecExecution schema operation := by
  intro _hschema _hvalid ObjectRef resolvers variableValues source _hvars
  by_cases hroot : rootSourceAppliesBool schema operation source = true
  · apply executeQueryWithFuel_eq_spec_of_rootSelectionSet_eq
      (ObjectRef := ObjectRef) schema operation resolvers variableValues
      (preservationFuelBound schema operation) source hroot
    simpa [hselectionSet] using
      executeRootSelectionSet_eq_spec_empty (ObjectRef := ObjectRef)
        schema resolvers
        (GraphQL.Execution.coerceVariableValues operation variableValues)
        (preservationFuelBound schema operation) (operation.rootType schema) source
  · exact
      let hfalse : rootSourceAppliesBool schema operation source = false := by
        cases h : rootSourceAppliesBool schema operation source with
        | false =>
            rfl
        | true =>
            have htrue : rootSourceAppliesBool schema operation source = true := by
              simpa using h
            exact False.elim (hroot htrue)
      executeQueryWithFuel_eq_spec_of_rootSourceAppliesBool_false
        (ObjectRef := ObjectRef) schema operation resolvers variableValues
        (preservationFuelBound schema operation) source hfalse

theorem completeExecutionTrace_eq_of_rootObjectResult
    (trace : ExecutionTrace)
    (result : Result (List (Name × ResponseValue)))
    : completeFrames trace.reverse ∅
        = {
          valueStack := [[objectResultFromFields result]]
          fieldStore := []
        }
      -> completeExecutionTrace trace = result := by
  intro htrace
  unfold completeExecutionTrace
  rw [htrace]
  cases result with
  | error errors =>
      rfl
  | ok result =>
      rcases result with ⟨fields, errors⟩
      rfl

theorem executeRootSelectionSet_eq_spec_of_drain_ready
    (schema : Schema) (operation : Operation)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> rootSourceAppliesBool schema operation source = true
      -> expectedDrainQueueReady schema resolvers variableValues fuel
          (scheduleExpectedScope schema variableValues (operation.rootType schema)
            [source] [fuel] operation.selectionSet []).fst
      -> executeRootSelectionSet schema (ResolverMap.fromSpecResolvers resolvers)
            variableValues fuel (operation.rootType schema) source operation.selectionSet
          = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
              fuel (operation.rootType schema) source operation.selectionSet := by
  intro hschema hroot hready
  let expectedRootWork : ExpectedPendingChildWork ObjectRef :=
    { work :=
        { runtimeType := (operation.rootType schema)
          selectionSet := operation.selectionSet
          source := source }
      specFuel := fuel }
  let expectedScheduled :=
    scheduleExpectedScope schema variableValues (operation.rootType schema)
      [source] [fuel] operation.selectionSet
      ([] : ExpectedScheduleQueue ObjectRef)
  let runtimeScheduled :=
    scheduleScope schema variableValues (operation.rootType schema) [source]
      operation.selectionSet ([] : ScheduleQueue ObjectRef)
  have hscheduledQueue :
      expectedScheduleQueueToQueue expectedScheduled.fst =
        runtimeScheduled.fst := by
    simpa [expectedScheduled, runtimeScheduled, expectedScheduleQueueToQueue] using
      expectedScheduleQueueToQueue_scheduleExpectedScope
        (ObjectRef := ObjectRef) schema variableValues (operation.rootType schema)
        [source] [fuel] operation.selectionSet
        ([] : ExpectedScheduleQueue ObjectRef)
  have hscheduledFrame :
      expectedScheduled.snd = runtimeScheduled.snd := by
    simpa [expectedScheduled, runtimeScheduled, expectedScheduleQueueToQueue] using
      scheduleExpectedScope_frame
        (ObjectRef := ObjectRef) schema variableValues (operation.rootType schema)
        [source] [fuel] operation.selectionSet
        ([] : ExpectedScheduleQueue ObjectRef)
  have hdrain :=
    queue_drainLoopMatchesExpectedSpec_of_ready
      (ObjectRef := ObjectRef) schema resolvers variableValues fuel
      expectedScheduled.fst
      (by simpa [expectedScheduled] using hready)
  unfold drainLoopMatchesExpectedSpec expectedQueueTraceMatchesSpec at hdrain
  have hdrainRuntime :
      completeFrames
          (drainLoop schema (ResolverMap.fromSpecResolvers resolvers)
            variableValues fuel runtimeScheduled.fst).reverse ∅ =
        expectedScheduleQueueCompletionStack schema resolvers variableValues
          expectedScheduled.fst := by
    simpa [runtimeScheduled, hscheduledQueue.symm] using hdrain
  have hrootFrame :
      completeFrames [runtimeScheduled.snd]
          (expectedScheduleQueueCompletionStack schema resolvers variableValues
            expectedScheduled.fst) =
        { valueStack :=
            [[expectedPendingChildWorkSpecResult schema resolvers variableValues
              expectedRootWork]]
          fieldStore := [] } := by
    have hsingleton :=
      queue_completeFrames_scheduleExpectedScope_singleton
        (ObjectRef := ObjectRef) schema resolvers variableValues
        expectedRootWork ([] : ExpectedScheduleQueue ObjectRef)
        ([] : ValueStack)
        (by simp [expectedScheduleQueueItemsNonempty])
    simpa [expectedRootWork, expectedScheduled, hscheduledFrame,
      expectedScheduleQueueCompletionStack] using hsingleton
  have hcollect :
      collectFieldsByKey schema variableValues (operation.rootType schema)
          operation.selectionSet =
        GraphQL.Execution.collectFields schema variableValues
          (operation.rootType schema) source operation.selectionSet :=
    collectFieldsByKey_eq_collectFields_root_source
      (ObjectRef := ObjectRef) schema operation variableValues source
      hschema hroot
  have hspecResult :
      expectedPendingChildWorkSpecResult schema resolvers variableValues
          expectedRootWork =
        objectResultFromFields
          (GraphQL.Execution.executeRootSelectionSet schema resolvers
            variableValues fuel (operation.rootType schema) source
            operation.selectionSet) := by
    simp [expectedPendingChildWorkSpecResult, expectedRootWork,
      GraphQL.Execution.executeRootSelectionSet, hcollect]
  rw [queue_executeRootSelectionSet_trace]
  apply completeExecutionTrace_eq_of_rootObjectResult
  simp [List.reverse_cons, queue_completeFrames_append]
  rw [hdrainRuntime]
  simpa [hspecResult] using hrootFrame

theorem expectedRootScheduleQueue_fuelsAligned
    (schema : Schema) (operation : Operation)
    (variableValues : VariableValues)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    : expectedScheduleQueueFuelsAligned
        (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [fuel] operation.selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst := by
  have hlength : [fuel].length = [source].length := by
    rfl
  simpa using
    scheduleExpectedScope_fuelsAligned
      (ObjectRef := ObjectRef) schema variableValues (operation.rootType schema)
      [source] [fuel] operation.selectionSet
      ([] : ExpectedScheduleQueue ObjectRef)
      hlength
      (by simp [expectedScheduleQueueFuelsAligned])

theorem expectedRootScheduleQueue_itemsNonempty
    (schema : Schema) (operation : Operation)
    (variableValues : VariableValues)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    : expectedScheduleQueueItemsNonempty
        (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [fuel] operation.selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst := by
  simpa using
    scheduleExpectedScope_itemsNonempty
      (ObjectRef := ObjectRef) schema variableValues (operation.rootType schema)
      [source] [fuel] operation.selectionSet
      ([] : ExpectedScheduleQueue ObjectRef)
      (by simp [expectedScheduleQueueItemsNonempty])

theorem expectedRootScheduleQueue_keysDistinct
    (schema : Schema) (operation : Operation)
    (variableValues : VariableValues)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    : expectedScheduleQueueKeysDistinct
        (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [fuel] operation.selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst := by
  simpa using
    scheduleExpectedScope_keysDistinct
      (ObjectRef := ObjectRef) schema variableValues (operation.rootType schema)
      [source] [fuel] operation.selectionSet
      ([] : ExpectedScheduleQueue ObjectRef)
      (by simp [expectedScheduleQueueKeysDistinct])

theorem fieldDefinitionsCompleteValueFuelBound_fold_start_le
    (fields : List FieldDefinition) (start : Nat)
    : start
      <= fields.foldl
          (fun bound fieldDefinition =>
            max bound (typeRefCompleteValueFuelBound fieldDefinition.outputType))
          start := by
  induction fields generalizing start with
  | nil =>
      exact Nat.le_refl start
  | cons head tail ih =>
      exact Nat.le_trans
        (Nat.le_max_left start (typeRefCompleteValueFuelBound head.outputType))
        (ih (max start (typeRefCompleteValueFuelBound head.outputType)))

theorem typeRefCompleteValueFuelBound_le_fieldDefinitionsFold_of_mem
    (fields : List FieldDefinition) (start : Nat)
    (fieldDefinition : FieldDefinition)
    : fieldDefinition ∈ fields
      -> typeRefCompleteValueFuelBound fieldDefinition.outputType
          <= fields.foldl
              (fun bound fieldDefinition =>
                max bound (typeRefCompleteValueFuelBound fieldDefinition.outputType))
              start := by
  intro hmem
  induction fields generalizing start with
  | nil =>
      simp at hmem
  | cons head tail ih =>
      simp at hmem
      rcases hmem with hhead | htail
      · subst fieldDefinition
        have hstep :
            typeRefCompleteValueFuelBound head.outputType <=
              max start (typeRefCompleteValueFuelBound head.outputType) :=
          Nat.le_max_right _ _
        exact Nat.le_trans hstep
          (fieldDefinitionsCompleteValueFuelBound_fold_start_le
            tail (max start (typeRefCompleteValueFuelBound head.outputType)))
      · exact ih (max start (typeRefCompleteValueFuelBound head.outputType)) htail

theorem typeRefCompleteValueFuelBound_le_fieldDefinitionsCompleteValueFuelBound
    (fields : List FieldDefinition) (fieldDefinition : FieldDefinition)
    : fieldDefinition ∈ fields
      -> typeRefCompleteValueFuelBound fieldDefinition.outputType
          <= fieldDefinitionsCompleteValueFuelBound fields := by
  intro hmem
  simpa [fieldDefinitionsCompleteValueFuelBound] using
    typeRefCompleteValueFuelBound_le_fieldDefinitionsFold_of_mem
      fields 0 fieldDefinition hmem

theorem typeRefCompleteValueFuelBound_le_typeDefinitionCompleteValueFuelBound
    (typeDefinition : TypeDefinition) (fields : List FieldDefinition)
    (fieldDefinition : FieldDefinition)
    : typeDefinition.fields? = some fields
      -> fieldDefinition ∈ fields
      -> typeRefCompleteValueFuelBound fieldDefinition.outputType
          <= typeDefinitionCompleteValueFuelBound typeDefinition := by
  intro hfields hmem
  cases typeDefinition with
  | object objectType =>
      simp [TypeDefinition.fields?] at hfields
      subst fields
      simpa [typeDefinitionCompleteValueFuelBound] using
        typeRefCompleteValueFuelBound_le_fieldDefinitionsCompleteValueFuelBound
          objectType.fields fieldDefinition hmem
  | interface interfaceType =>
      simp [TypeDefinition.fields?] at hfields
      subst fields
      simpa [typeDefinitionCompleteValueFuelBound] using
        typeRefCompleteValueFuelBound_le_fieldDefinitionsCompleteValueFuelBound
          interfaceType.fields fieldDefinition hmem
  | builtinScalar scalar =>
      simp [TypeDefinition.fields?] at hfields
  | customScalar scalar =>
      simp [TypeDefinition.fields?] at hfields
  | union unionType =>
      simp [TypeDefinition.fields?] at hfields
  | enum enumType =>
      simp [TypeDefinition.fields?] at hfields
  | inputObject inputObjectType =>
      simp [TypeDefinition.fields?] at hfields

theorem typeDefinitionsCompleteValueFuelBound_fold_start_le
    (types : List TypeDefinition) (start : Nat)
    : start
      <= types.foldl
          (fun bound typeDefinition =>
            max bound (typeDefinitionCompleteValueFuelBound typeDefinition))
          start := by
  induction types generalizing start with
  | nil =>
      exact Nat.le_refl start
  | cons head tail ih =>
      exact Nat.le_trans
        (Nat.le_max_left start (typeDefinitionCompleteValueFuelBound head))
        (ih (max start (typeDefinitionCompleteValueFuelBound head)))

theorem typeDefinitionCompleteValueFuelBound_le_schemaTypesFold_of_mem
    (types : List TypeDefinition) (start : Nat)
    (typeDefinition : TypeDefinition)
    : typeDefinition ∈ types
      -> typeDefinitionCompleteValueFuelBound typeDefinition
          <= types.foldl
              (fun bound typeDefinition =>
                max bound (typeDefinitionCompleteValueFuelBound typeDefinition))
              start := by
  intro hmem
  induction types generalizing start with
  | nil =>
      simp at hmem
  | cons head tail ih =>
      simp at hmem
      rcases hmem with hhead | htail
      · subst typeDefinition
        have hstep :
            typeDefinitionCompleteValueFuelBound head <=
              max start (typeDefinitionCompleteValueFuelBound head) :=
          Nat.le_max_right _ _
        exact Nat.le_trans hstep
          (typeDefinitionsCompleteValueFuelBound_fold_start_le
            tail (max start (typeDefinitionCompleteValueFuelBound head)))
      · exact ih (max start (typeDefinitionCompleteValueFuelBound head)) htail

theorem typeDefinitionCompleteValueFuelBound_le_schemaCompleteValueFuelBound
    (schema : Schema) (typeDefinition : TypeDefinition)
    : typeDefinition ∈ schema.types
      -> typeDefinitionCompleteValueFuelBound typeDefinition
          <= schemaCompleteValueFuelBound schema := by
  intro hmem
  simpa [schemaCompleteValueFuelBound] using
    typeDefinitionCompleteValueFuelBound_le_schemaTypesFold_of_mem
      schema.types 0 typeDefinition hmem

theorem lookupField_typeRefCompleteValueFuelBound_le_schemaCompleteValueFuelBound
    (schema : Schema) (parentType fieldName : Name) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> typeRefCompleteValueFuelBound fieldDefinition.outputType
          <= schemaCompleteValueFuelBound schema := by
  intro hlookup
  cases htype : schema.lookupType parentType with
  | none =>
      simp [Schema.lookupField, htype] at hlookup
  | some typeDefinition =>
      cases hfields : typeDefinition.fields? with
      | none =>
          simp [Schema.lookupField, htype, hfields] at hlookup
      | some fields =>
          have hfieldLookup :
              fields.find? (fun field => field.name == fieldName) =
                some fieldDefinition := by
            simpa [Schema.lookupField, htype, hfields] using hlookup
          have hfieldMem : fieldDefinition ∈ fields :=
            List.mem_of_find?_eq_some hfieldLookup
          have htypeMemAll : typeDefinition ∈ schema.allTypes := by
            simpa [Schema.lookupType] using List.mem_of_find?_eq_some htype
          rcases List.mem_append.mp
              (by simpa [Schema.allTypes] using htypeMemAll) with
            hbuiltin | hschemaType
          · simp [Schema.builtinScalarDefinitions] at hbuiltin
            rcases hbuiltin with hbuiltin | hbuiltin | hbuiltin | hbuiltin | hbuiltin
            · subst typeDefinition
              simp [TypeDefinition.fields?] at hfields
            · subst typeDefinition
              simp [TypeDefinition.fields?] at hfields
            · subst typeDefinition
              simp [TypeDefinition.fields?] at hfields
            · subst typeDefinition
              simp [TypeDefinition.fields?] at hfields
            · subst typeDefinition
              simp [TypeDefinition.fields?] at hfields
          · exact Nat.le_trans
              (typeRefCompleteValueFuelBound_le_typeDefinitionCompleteValueFuelBound
                typeDefinition fields fieldDefinition hfields hfieldMem)
              (typeDefinitionCompleteValueFuelBound_le_schemaCompleteValueFuelBound
                schema typeDefinition hschemaType)

theorem expectedQueueItemStepFuelReady_of_fieldBudgetReady
    (schema : Schema) (item : ExpectedQueueItem ObjectRef)
    : expectedQueueItemFieldBudgetReady schema item
      -> expectedQueueItemStepFuelReady schema item := by
  intro hbudget
  unfold expectedQueueItemStepFuelReady
  cases hlookup : schema.lookupField item.key.parentType item.key.fieldName with
  | none =>
      intro segment hsegment fuel hfuel
      have hsegmentBudget := hbudget segment hsegment fuel hfuel
      unfold specFuelFieldBudget at hsegmentBudget
      omega
  | some fieldDefinition =>
      intro segment hsegment fuel hfuel
      have hsegmentBudget := hbudget segment hsegment fuel hfuel
      have hschemaFuel : schemaCompleteValueFuelBound schema < fuel := by
        unfold specFuelFieldBudget at hsegmentBudget
        omega
      exact Nat.lt_of_le_of_lt
        (lookupField_typeRefCompleteValueFuelBound_le_schemaCompleteValueFuelBound
          schema item.key.parentType item.key.fieldName fieldDefinition hlookup)
        hschemaFuel

theorem expectedScheduleQueueFieldFuelReady_of_fieldBudgetReady
    (schema : Schema) (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueFieldBudgetReady schema queue
      -> expectedScheduleQueueFieldFuelReady schema queue := by
  intro hbudget item hitem
  exact expectedQueueItemStepFuelReady_of_fieldBudgetReady
    (ObjectRef := ObjectRef) schema item (hbudget item hitem)

theorem expectedChildQueueForItem_fieldBudgetReady
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    : expectedQueueItemFieldBudgetReady schema item
      -> expectedScheduleQueueFieldBudgetReady schema
          (expectedChildQueueForItem schema resolvers variableValues item).fst := by
  intro hbudget
  unfold expectedChildQueueForItem
  cases hlookup : schema.lookupField item.key.parentType item.key.fieldName with
  | none =>
      simp [expectedScheduleQueueFieldBudgetReady]
  | some fieldDefinition =>
      have hfieldBound :
          typeRefCompleteValueFuelBound fieldDefinition.outputType <=
            schemaCompleteValueFuelBound schema :=
        lookupField_typeRefCompleteValueFuelBound_le_schemaCompleteValueFuelBound
          schema item.key.parentType item.key.fieldName fieldDefinition hlookup
      have hwork :
          expectedPendingChildWorkScopeBudgetReady schema
            (expectedPendingChildWorkForItem schema resolvers
              fieldDefinition.outputType item) :=
        expectedPendingChildWorkForItem_scopeBudgetReady
          (ObjectRef := ObjectRef) schema resolvers fieldDefinition.outputType item
          hfieldBound hbudget
      simpa [hlookup] using
        scheduleExpectedPendingChildWork_fieldBudgetReady
          (ObjectRef := ObjectRef) schema variableValues
          (expectedPendingChildWorkForItem schema resolvers
            fieldDefinition.outputType item)
          ([] : ExpectedScheduleQueue ObjectRef)
          hwork
          (by simp [expectedScheduleQueueFieldBudgetReady])

def expectedScheduleQueueFuelsAllEq (fuel : Nat) (queue : ExpectedScheduleQueue ObjectRef)
    : Prop :=
  ∀ item,
    item ∈ queue
    -> ∀ segment,
        segment ∈ item.segments
        -> ∀ segmentFuel, segmentFuel ∈ segment.specFuels -> segmentFuel = fuel

theorem expectedScheduleQueueFuelsAllEq_enqueueExpectedSegment
    (fuel : Nat) (key : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : (∀ segmentFuel, segmentFuel ∈ segment.specFuels -> segmentFuel = fuel)
      -> expectedScheduleQueueFuelsAllEq fuel queue
      -> expectedScheduleQueueFuelsAllEq fuel
          (enqueueExpectedSegment key segment queue) := by
  intro hsegment hqueue
  induction queue with
  | nil =>
      intro item hitem itemSegment hitemSegment segmentFuel hfuel
      simp [enqueueExpectedSegment] at hitem
      subst item
      simp at hitemSegment
      subst itemSegment
      exact hsegment segmentFuel hfuel
  | cons item rest ih =>
      by_cases hkey : scheduleKeyEqBool key item.key = true
      · intro candidate hcandidate candidateSegment hcandidateSegment segmentFuel hfuel
        simp [enqueueExpectedSegment, hkey] at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · subst candidate
          simp at hcandidateSegment
          rcases hcandidateSegment with hcandidateSegment | hcandidateSegment
          · exact hqueue item (by simp) candidateSegment hcandidateSegment
              segmentFuel hfuel
          · subst candidateSegment
            exact hsegment segmentFuel hfuel
        · exact hqueue candidate (by simp [hcandidate]) candidateSegment
            hcandidateSegment segmentFuel hfuel
      · have hkeyFalse : scheduleKeyEqBool key item.key = false := by
          cases h : scheduleKeyEqBool key item.key with
          | false => rfl
          | true => exact False.elim (hkey h)
        have hrest :
            expectedScheduleQueueFuelsAllEq fuel rest := by
          intro restItem hrestItem
          exact hqueue restItem (by simp [hrestItem])
        have ihRest := ih hrest
        intro candidate hcandidate candidateSegment hcandidateSegment segmentFuel hfuel
        simp [enqueueExpectedSegment, hkeyFalse] at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · subst candidate
          exact hqueue item (by simp) candidateSegment hcandidateSegment
            segmentFuel hfuel
        · exact ihRest candidate hcandidate candidateSegment hcandidateSegment
            segmentFuel hfuel

theorem expectedScheduleQueueFuelsAllEq_scheduleExpectedScope_root
    (schema : Schema) (operation : Operation)
    (variableValues : VariableValues)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    : expectedScheduleQueueFuelsAllEq fuel
        (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [fuel] operation.selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst := by
  let groups := collectFieldsByKey schema variableValues (operation.rootType schema)
    operation.selectionSet
  let keyedGroups :=
    groups.map (fun group =>
      (scheduleKeyForFields (operation.rootType schema) group.fst group.snd, group.snd))
  have hfold :
      ∀ (groups0 : List (ScheduleKey × List ExecutableField))
        (queue : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueFuelsAllEq fuel queue ->
          expectedScheduleQueueFuelsAllEq fuel
            (groups0.foldl
              (fun queue group =>
                enqueueExpectedSegment group.fst
                  { segment :=
                      { sources := [source]
                        childSelectionSet := childSelectionSetForFields group.snd }
                    specFuels := [fuel] }
                  queue)
              queue) := by
    intro groups0
    induction groups0 with
    | nil =>
        intro queue hqueue
        exact hqueue
    | cons group rest ih =>
        intro queue hqueue
        apply ih
        exact expectedScheduleQueueFuelsAllEq_enqueueExpectedSegment
          (ObjectRef := ObjectRef) fuel group.fst
          { segment :=
              { sources := [source]
                childSelectionSet := childSelectionSetForFields group.snd }
            specFuels := [fuel] }
          queue
          (by
            intro segmentFuel hfuel
            simp at hfuel
            exact hfuel)
          hqueue
  simpa [scheduleExpectedScope, groups, keyedGroups] using
    hfold keyedGroups ([] : ExpectedScheduleQueue ObjectRef)
      (by
        intro item hitem
        simp at hitem)

theorem expectedRootScheduleQueue_stepFuelReady
    (schema : Schema) (operation : Operation)
    (variableValues : VariableValues)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    : schemaCompleteValueFuelBound schema < fuel
      -> expectedScheduleQueueFieldFuelReady schema
          (scheduleExpectedScope schema variableValues (operation.rootType schema)
            [source] [fuel] operation.selectionSet
            ([] : ExpectedScheduleQueue ObjectRef)).fst := by
  intro hfuelBound
  have hall :=
    expectedScheduleQueueFuelsAllEq_scheduleExpectedScope_root
      (ObjectRef := ObjectRef) schema operation variableValues fuel source
  intro item hitem
  unfold expectedQueueItemStepFuelReady
  cases hlookup : schema.lookupField item.key.parentType item.key.fieldName with
  | none =>
      intro segment hsegment segmentFuel hsegmentFuel
      have hfuelEq := hall item hitem segment hsegment segmentFuel hsegmentFuel
      subst segmentFuel
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) hfuelBound
  | some fieldDefinition =>
      intro segment hsegment segmentFuel hsegmentFuel
      have hfuelEq := hall item hitem segment hsegment segmentFuel hsegmentFuel
      subst segmentFuel
      exact Nat.lt_of_le_of_lt
        (lookupField_typeRefCompleteValueFuelBound_le_schemaCompleteValueFuelBound
          schema item.key.parentType item.key.fieldName fieldDefinition hlookup)
        hfuelBound

theorem schemaCompleteValueFuelBound_lt_specQueryFuelBound
    (schema : Schema) (operation : Operation)
    : schemaCompleteValueFuelBound schema < specQueryFuelBound schema operation := by
  unfold specQueryFuelBound
  omega

theorem schemaCompleteValueFuelBound_lt_preservationFuelBound
    (schema : Schema) (operation : Operation)
    : schemaCompleteValueFuelBound schema < preservationFuelBound schema operation := by
  exact Nat.lt_of_lt_of_le
    (schemaCompleteValueFuelBound_lt_specQueryFuelBound schema operation)
    (specQueryFuelBound_le_preservationFuelBound schema operation)

theorem specFuelScopeBudget_root_preservation (schema : Schema) (operation : Operation)
    : specFuelScopeBudget schema operation.selectionSet
        (preservationFuelBound schema operation) := by
  have hspec :
      specFuelScopeBudget schema operation.selectionSet
        (specQueryFuelBound schema operation) := by
    unfold specFuelScopeBudget specQueryFuelBound Operation.size
    omega
  exact Nat.lt_of_lt_of_le hspec
    (specQueryFuelBound_le_preservationFuelBound schema operation)

theorem expectedRootScheduleQueue_fieldBudgetReady_preservation
    (schema : Schema) (operation : Operation)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    : expectedScheduleQueueFieldBudgetReady schema
        (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [preservationFuelBound schema operation]
          operation.selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst := by
  apply scheduleExpectedScope_fieldBudgetReady
  · intro fuel hfuel
    simp at hfuel
    subst fuel
    exact specFuelScopeBudget_root_preservation schema operation
  · simp [expectedScheduleQueueFieldBudgetReady]

theorem expectedRootScheduleQueue_stepFuelReady_preservation
    (schema : Schema) (operation : Operation)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    : expectedScheduleQueueFieldFuelReady schema
        (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [preservationFuelBound schema operation]
          operation.selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst := by
  exact expectedRootScheduleQueue_stepFuelReady
    (ObjectRef := ObjectRef) schema operation variableValues
    (preservationFuelBound schema operation) source
    (schemaCompleteValueFuelBound_lt_preservationFuelBound schema operation)

theorem expectedRootScheduleQueue_frontierBudget_le_breadthQueryFuelBound
    (schema : Schema) (operation : Operation)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    : expectedScheduleQueueFrontierBudget schema
        (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [preservationFuelBound schema operation]
          operation.selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst
      <= breadthQueryFuelBound schema operation := by
  have hfrontier :=
    expectedScheduleQueueFrontierBudget_le_rawShapeWeight
      (ObjectRef := ObjectRef) schema
      (scheduleExpectedScope schema variableValues (operation.rootType schema)
        [source] [preservationFuelBound schema operation]
        operation.selectionSet
        ([] : ExpectedScheduleQueue ObjectRef)).fst
  have hraw :
      expectedScheduleQueueRawShapeWeight schema
          (scheduleExpectedScope schema variableValues (operation.rootType schema)
            [source] [preservationFuelBound schema operation]
            operation.selectionSet
            ([] : ExpectedScheduleQueue ObjectRef)).fst <=
        SelectionSet.size operation.selectionSet *
          (schema.objectTypes.length + 1) := by
    simpa [expectedScheduleQueueRawShapeWeight] using
      scheduleExpectedScope_rawShapeWeight_le
        (ObjectRef := ObjectRef) schema variableValues (operation.rootType schema)
        [source] [preservationFuelBound schema operation]
        operation.selectionSet ([] : ExpectedScheduleQueue ObjectRef)
  have hwide :
      SelectionSet.size operation.selectionSet *
          (schema.objectTypes.length + 1) <=
        SelectionSet.size operation.selectionSet *
          (schema.objectTypes.length + 1) *
          (schema.objectTypes.length + 1) := by
    have hfactor : 1 <= schema.objectTypes.length + 1 := by omega
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_left
        (SelectionSet.size operation.selectionSet *
          (schema.objectTypes.length + 1)) hfactor
  unfold breadthQueryFuelBound Operation.size
  omega

theorem expectedRootScheduleQueue_drainBudget_le_breadthQueryFuelBound
    (schema : Schema) (operation : Operation)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    : expectedScheduleQueueDrainBudget schema []
        (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [preservationFuelBound schema operation]
          operation.selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst
      <= breadthQueryFuelBound schema operation := by
  have hbudget :=
    expectedScheduleQueueDrainBudget_le_shapeWeight
      (ObjectRef := ObjectRef) schema []
      (scheduleExpectedScope schema variableValues (operation.rootType schema)
        [source] [preservationFuelBound schema operation]
        operation.selectionSet
        ([] : ExpectedScheduleQueue ObjectRef)).fst
  have hshapeRaw :=
    expectedScheduleQueueShapeWeight_le_raw
      (ObjectRef := ObjectRef) schema
      (scheduleExpectedScope schema variableValues (operation.rootType schema)
        [source] [preservationFuelBound schema operation]
        operation.selectionSet
        ([] : ExpectedScheduleQueue ObjectRef)).fst
  have hraw :
      expectedScheduleQueueRawShapeWeight schema
          (scheduleExpectedScope schema variableValues (operation.rootType schema)
            [source] [preservationFuelBound schema operation]
            operation.selectionSet
            ([] : ExpectedScheduleQueue ObjectRef)).fst <=
        SelectionSet.size operation.selectionSet *
          (schema.objectTypes.length + 1) := by
    simpa [expectedScheduleQueueRawShapeWeight] using
      scheduleExpectedScope_rawShapeWeight_le
        (ObjectRef := ObjectRef) schema variableValues (operation.rootType schema)
        [source] [preservationFuelBound schema operation]
        operation.selectionSet ([] : ExpectedScheduleQueue ObjectRef)
  have hwide :
      SelectionSet.size operation.selectionSet *
          (schema.objectTypes.length + 1) <=
        SelectionSet.size operation.selectionSet *
          (schema.objectTypes.length + 1) *
          (schema.objectTypes.length + 1) := by
    have hfactor : 1 <= schema.objectTypes.length + 1 := by omega
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_left
        (SelectionSet.size operation.selectionSet *
          (schema.objectTypes.length + 1)) hfactor
  unfold breadthQueryFuelBound Operation.size
  omega

theorem expectedRootScheduleQueue_drainBudget_le_preservationFuelBound
    (schema : Schema) (operation : Operation)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    : expectedScheduleQueueDrainBudget schema []
        (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [preservationFuelBound schema operation]
          operation.selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst
      <= preservationFuelBound schema operation := by
  exact Nat.le_trans
    (expectedRootScheduleQueue_drainBudget_le_breadthQueryFuelBound
      (ObjectRef := ObjectRef) schema operation variableValues source)
    (breadthQueryFuelBound_le_preservationFuelBound schema operation)

theorem expectedRootScheduleQueue_runtimeDrainBudget_le_breadthQueryFuelBound
    (schema : Schema) (operation : Operation)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    : expectedScheduleQueueRuntimeDrainBudget schema resolvers []
        (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [preservationFuelBound schema operation]
          operation.selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst
      <= breadthQueryFuelBound schema operation := by
  have hruntime :=
    expectedScheduleQueueRuntimeDrainBudget_le_itemStepWeight
      (ObjectRef := ObjectRef) schema resolvers
      ([] : MaterializedPendingScopes)
      (scheduleExpectedScope schema variableValues (operation.rootType schema)
        [source] [preservationFuelBound schema operation]
        operation.selectionSet
        ([] : ExpectedScheduleQueue ObjectRef)).fst
  have hitemStep :
      expectedScheduleQueueRuntimeItemStepWeight schema
          (scheduleExpectedScope schema variableValues (operation.rootType schema)
            [source] [preservationFuelBound schema operation]
            operation.selectionSet
            ([] : ExpectedScheduleQueue ObjectRef)).fst <=
        selectionSetBreadthWeight schema operation.selectionSet := by
    have h :=
      scheduleExpectedScope_runtimeItemStepWeight_le
        (ObjectRef := ObjectRef) schema variableValues (operation.rootType schema)
        [source] [preservationFuelBound schema operation]
        operation.selectionSet ([] : ExpectedScheduleQueue ObjectRef)
    simpa [expectedScheduleQueueRuntimeItemStepWeight] using h
  have hfactor : 1 <= schema.objectTypes.length + 1 := by omega
  have hrecursive :
      selectionSetBreadthWeight schema operation.selectionSet <=
        selectionSetBreadthWeight schema operation.selectionSet *
          (schema.objectTypes.length + 1) := by
    simpa using
      Nat.mul_le_mul_left
        (selectionSetBreadthWeight schema operation.selectionSet) hfactor
  unfold breadthQueryFuelBound Operation.size
  omega

theorem expectedRootScheduleQueue_runtimeDrainBudget_le_preservationFuelBound
    (schema : Schema) (operation : Operation)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    : expectedScheduleQueueRuntimeDrainBudget schema resolvers []
        (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [preservationFuelBound schema operation]
          operation.selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst
      <= preservationFuelBound schema operation := by
  exact Nat.le_trans
    (expectedRootScheduleQueue_runtimeDrainBudget_le_breadthQueryFuelBound
      (ObjectRef := ObjectRef) schema operation resolvers variableValues source)
    (breadthQueryFuelBound_le_preservationFuelBound schema operation)

theorem expectedRootTailQueue_fieldBudgetReady_preservation
    (schema : Schema) (operation : Operation)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [preservationFuelBound schema operation]
          operation.selectionSet []).fst
        = item :: rest
      -> expectedScheduleQueueFieldBudgetReady schema
          (enqueueExpectedScheduleItems rest
            (expectedChildQueueForItem schema resolvers variableValues item).fst) := by
  intro hqueue
  let rootQueue :=
    (scheduleExpectedScope schema variableValues (operation.rootType schema)
      [source] [preservationFuelBound schema operation]
      operation.selectionSet ([] : ExpectedScheduleQueue ObjectRef)).fst
  have hrootBudget :
      expectedScheduleQueueFieldBudgetReady schema rootQueue := by
    simpa [rootQueue] using
      expectedRootScheduleQueue_fieldBudgetReady_preservation
        (ObjectRef := ObjectRef) schema operation variableValues source
  have hitemBudget :
      expectedQueueItemFieldBudgetReady schema item := by
    exact hrootBudget item (by simp [rootQueue, hqueue])
  have hrestBudget :
      expectedScheduleQueueFieldBudgetReady schema rest := by
    intro restItem hrestItem
    exact hrootBudget restItem (by simp [rootQueue, hqueue, hrestItem])
  have hchildBudget :
      expectedScheduleQueueFieldBudgetReady schema
        (expectedChildQueueForItem schema resolvers variableValues item).fst :=
    expectedChildQueueForItem_fieldBudgetReady
      (ObjectRef := ObjectRef) schema resolvers variableValues item hitemBudget
  exact enqueueExpectedScheduleItems_fieldBudgetReady
    (ObjectRef := ObjectRef) schema rest
    (expectedChildQueueForItem schema resolvers variableValues item).fst
    hchildBudget hrestBudget

theorem expectedRootTailQueue_shapeInvariants_preservation
    (schema : Schema) (operation : Operation)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [preservationFuelBound schema operation]
          operation.selectionSet []).fst
        = item :: rest
      -> expectedScheduleQueueFuelsAligned
            (enqueueExpectedScheduleItems rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst)
          ∧ expectedScheduleQueueItemsNonempty
              (enqueueExpectedScheduleItems rest
                (expectedChildQueueForItem schema resolvers variableValues item).fst)
          ∧ expectedScheduleQueueKeysDistinct
              (enqueueExpectedScheduleItems rest
                (expectedChildQueueForItem schema resolvers variableValues
                  item).fst) := by
  intro hqueue
  let rootQueue :=
    (scheduleExpectedScope schema variableValues (operation.rootType schema)
      [source] [preservationFuelBound schema operation]
      operation.selectionSet ([] : ExpectedScheduleQueue ObjectRef)).fst
  have hrootAligned :
      expectedScheduleQueueFuelsAligned rootQueue := by
    simpa [rootQueue] using
      expectedRootScheduleQueue_fuelsAligned
        (ObjectRef := ObjectRef) schema operation variableValues
        (preservationFuelBound schema operation) source
  have hrootNonempty :
      expectedScheduleQueueItemsNonempty rootQueue := by
    simpa [rootQueue] using
      expectedRootScheduleQueue_itemsNonempty
        (ObjectRef := ObjectRef) schema operation variableValues
        (preservationFuelBound schema operation) source
  have hrootDistinct :
      expectedScheduleQueueKeysDistinct rootQueue := by
    simpa [rootQueue] using
      expectedRootScheduleQueue_keysDistinct
        (ObjectRef := ObjectRef) schema operation variableValues
        (preservationFuelBound schema operation) source
  have hrestAligned :
      expectedScheduleQueueFuelsAligned rest := by
    intro restItem hrestItem
    exact hrootAligned restItem (by simp [rootQueue, hqueue, hrestItem])
  have hrestNonempty :
      expectedScheduleQueueItemsNonempty rest := by
    intro restItem hrestItem
    exact hrootNonempty restItem (by simp [rootQueue, hqueue, hrestItem])
  have hrootDistinctCons :
      expectedScheduleQueueKeysDistinct (item :: rest) := by
    simpa [rootQueue, hqueue] using hrootDistinct
  have hrestDistinct :
      expectedScheduleQueueKeysDistinct rest :=
    hrootDistinctCons.2
  constructor
  · exact enqueueExpectedScheduleItems_fuelsAligned rest
      (expectedChildQueueForItem schema resolvers variableValues item).fst
      (expectedChildQueueForItem_fuelsAligned
        (ObjectRef := ObjectRef) schema resolvers variableValues item)
      hrestAligned
  constructor
  · exact enqueueExpectedScheduleItems_itemsNonempty rest
      (expectedChildQueueForItem schema resolvers variableValues item).fst
      hrestNonempty
      (expectedChildQueueForItem_itemsNonempty
        (ObjectRef := ObjectRef) schema resolvers variableValues item)
  · exact enqueueExpectedScheduleItems_keysDistinct rest
      (expectedChildQueueForItem schema resolvers variableValues item).fst
      hrestDistinct
      (expectedChildQueueForItem_keysDistinct
        (ObjectRef := ObjectRef) schema resolvers variableValues item)

theorem expectedDrainQueueReady_of_drainBudget_and_stepBudget
    (schema : Schema)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    : (∀ (materialized : MaterializedChildSelections)
          (fuel : Nat) (item : ExpectedQueueItem ObjectRef)
          (rest : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueFuelsAligned (item :: rest)
        -> expectedScheduleQueueItemsNonempty (item :: rest)
        -> expectedScheduleQueueKeysDistinct (item :: rest)
        -> expectedScheduleQueueFieldBudgetReady schema (item :: rest)
        -> expectedScheduleQueueDrainBudget schema materialized (item :: rest) <= fuel + 1
        -> expectedScheduleQueueDrainBudget schema
              (materializeExpectedQueueItem item materialized)
              (enqueueExpectedScheduleItems rest
                (expectedChildQueueForItem schema resolvers variableValues item).fst)
            <= fuel)
      -> ∀ (materialized : MaterializedChildSelections)
            (fuel : Nat) (queue : ExpectedScheduleQueue ObjectRef),
          expectedScheduleQueueFuelsAligned queue
          -> expectedScheduleQueueItemsNonempty queue
          -> expectedScheduleQueueKeysDistinct queue
          -> expectedScheduleQueueFieldBudgetReady schema queue
          -> expectedScheduleQueueDrainBudget schema materialized queue <= fuel
          -> expectedDrainQueueReady schema resolvers variableValues fuel queue := by
  intro hstepBudget
  intro materialized fuel
  induction fuel generalizing materialized with
  | zero =>
      intro queue _haligned hnonempty _hdistinct _hfieldBudget hbudget
      cases queue with
      | nil =>
          simp [expectedDrainQueueReady]
      | cons item rest =>
          have hcurrent :
              0 < expectedQueueItemCurrentShapeCount item :=
            expectedQueueItemCurrentShapeCount_pos
              (ObjectRef := ObjectRef) item (hnonempty item (by simp))
          simp [expectedScheduleQueueDrainBudget] at hbudget
          omega
  | succ fuel ih =>
      intro queue haligned hnonempty hdistinct hfieldBudget hbudget
      cases queue with
      | nil =>
          simp [expectedDrainQueueReady]
      | cons item rest =>
          have hitemReady :
              expectedQueueItemStepFuelReady schema item :=
            expectedQueueItemStepFuelReady_of_fieldBudgetReady
              (ObjectRef := ObjectRef) schema item
              (hfieldBudget item (by simp))
          have hrestAligned :
              expectedScheduleQueueFuelsAligned rest := by
            intro restItem hrestItem
            exact haligned restItem (by simp [hrestItem])
          have hrestNonempty :
              expectedScheduleQueueItemsNonempty rest := by
            intro restItem hrestItem
            exact hnonempty restItem (by simp [hrestItem])
          have hdistinctCons :
              expectedScheduleQueueKeysDistinct (item :: rest) := hdistinct
          have hrestDistinct :
              expectedScheduleQueueKeysDistinct rest := hdistinctCons.2
          have hitemBudget :
              expectedQueueItemFieldBudgetReady schema item :=
            hfieldBudget item (by simp)
          have hrestBudget :
              expectedScheduleQueueFieldBudgetReady schema rest := by
            intro restItem hrestItem
            exact hfieldBudget restItem (by simp [hrestItem])
          have hchildAligned :
              expectedScheduleQueueFuelsAligned
                (expectedChildQueueForItem schema resolvers variableValues item).fst :=
            expectedChildQueueForItem_fuelsAligned
              (ObjectRef := ObjectRef) schema resolvers variableValues item
          have hchildNonempty :
              expectedScheduleQueueItemsNonempty
                (expectedChildQueueForItem schema resolvers variableValues item).fst :=
            expectedChildQueueForItem_itemsNonempty
              (ObjectRef := ObjectRef) schema resolvers variableValues item
          have hchildDistinct :
              expectedScheduleQueueKeysDistinct
                (expectedChildQueueForItem schema resolvers variableValues item).fst :=
            expectedChildQueueForItem_keysDistinct
              (ObjectRef := ObjectRef) schema resolvers variableValues item
          have hchildBudget :
              expectedScheduleQueueFieldBudgetReady schema
                (expectedChildQueueForItem schema resolvers variableValues item).fst :=
            expectedChildQueueForItem_fieldBudgetReady
              (ObjectRef := ObjectRef) schema resolvers variableValues item
              hitemBudget
          have htailAligned :
              expectedScheduleQueueFuelsAligned
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst) :=
            enqueueExpectedScheduleItems_fuelsAligned rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst
              hchildAligned hrestAligned
          have htailNonempty :
              expectedScheduleQueueItemsNonempty
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst) :=
            enqueueExpectedScheduleItems_itemsNonempty rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst
              hrestNonempty hchildNonempty
          have htailDistinct :
              expectedScheduleQueueKeysDistinct
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst) :=
            enqueueExpectedScheduleItems_keysDistinct rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst
              hrestDistinct hchildDistinct
          have htailBudgetReady :
              expectedScheduleQueueFieldBudgetReady schema
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst) :=
            enqueueExpectedScheduleItems_fieldBudgetReady
              (ObjectRef := ObjectRef) schema rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst
              hchildBudget hrestBudget
          have htailDrainBudget :
              expectedScheduleQueueDrainBudget schema
                  (materializeExpectedQueueItem item materialized)
                  (enqueueExpectedScheduleItems rest
                    (expectedChildQueueForItem schema resolvers variableValues item).fst) <=
                fuel :=
            hstepBudget materialized fuel item rest haligned hnonempty hdistinct
              hfieldBudget hbudget
          simp [expectedDrainQueueReady]
          exact ⟨haligned, hnonempty, hdistinct, hitemReady,
            ih (materializeExpectedQueueItem item materialized)
              (enqueueExpectedScheduleItems rest
                (expectedChildQueueForItem schema resolvers variableValues item).fst)
              htailAligned htailNonempty htailDistinct htailBudgetReady
              htailDrainBudget⟩

theorem expectedDrainQueueReady_of_runtimeDrainBudget_and_stepBudget
    (schema : Schema)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    : (∀ (materialized : MaterializedPendingScopes)
          (fuel : Nat) (item : ExpectedQueueItem ObjectRef)
          (rest : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueFuelsAligned (item :: rest)
        -> expectedScheduleQueueItemsNonempty (item :: rest)
        -> expectedScheduleQueueKeysDistinct (item :: rest)
        -> expectedScheduleQueueFieldBudgetReady schema (item :: rest)
        -> expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
              (item :: rest)
            <= fuel + 1
        -> expectedScheduleQueueRuntimeDrainBudget schema resolvers
              (materializeExpectedQueueItemRuntimeScopes schema resolvers item
                materialized)
              (enqueueExpectedScheduleItems rest
                (expectedChildQueueForItem schema resolvers variableValues item).fst)
            <= fuel)
      -> ∀ (materialized : MaterializedPendingScopes)
            (fuel : Nat) (queue : ExpectedScheduleQueue ObjectRef),
          expectedScheduleQueueFuelsAligned queue
          -> expectedScheduleQueueItemsNonempty queue
          -> expectedScheduleQueueKeysDistinct queue
          -> expectedScheduleQueueFieldBudgetReady schema queue
          -> expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized queue
              <= fuel
          -> expectedDrainQueueReady schema resolvers variableValues fuel queue := by
  intro hstepBudget
  intro materialized fuel
  induction fuel generalizing materialized with
  | zero =>
      intro queue _haligned hnonempty _hdistinct _hfieldBudget hbudget
      cases queue with
      | nil =>
          simp [expectedDrainQueueReady]
      | cons item rest =>
          have hcurrent :
              0 < expectedQueueItemCurrentShapeCount item :=
            expectedQueueItemCurrentShapeCount_pos
              (ObjectRef := ObjectRef) item (hnonempty item (by simp))
          simp [expectedScheduleQueueRuntimeDrainBudget] at hbudget
          omega
  | succ fuel ih =>
      intro queue haligned hnonempty hdistinct hfieldBudget hbudget
      cases queue with
      | nil =>
          simp [expectedDrainQueueReady]
      | cons item rest =>
          have hitemReady :
              expectedQueueItemStepFuelReady schema item :=
            expectedQueueItemStepFuelReady_of_fieldBudgetReady
              (ObjectRef := ObjectRef) schema item
              (hfieldBudget item (by simp))
          have hrestAligned :
              expectedScheduleQueueFuelsAligned rest := by
            intro restItem hrestItem
            exact haligned restItem (by simp [hrestItem])
          have hrestNonempty :
              expectedScheduleQueueItemsNonempty rest := by
            intro restItem hrestItem
            exact hnonempty restItem (by simp [hrestItem])
          have hdistinctCons :
              expectedScheduleQueueKeysDistinct (item :: rest) := hdistinct
          have hrestDistinct :
              expectedScheduleQueueKeysDistinct rest := hdistinctCons.2
          have hitemBudget :
              expectedQueueItemFieldBudgetReady schema item :=
            hfieldBudget item (by simp)
          have hrestBudget :
              expectedScheduleQueueFieldBudgetReady schema rest := by
            intro restItem hrestItem
            exact hfieldBudget restItem (by simp [hrestItem])
          have hchildAligned :
              expectedScheduleQueueFuelsAligned
                (expectedChildQueueForItem schema resolvers variableValues item).fst :=
            expectedChildQueueForItem_fuelsAligned
              (ObjectRef := ObjectRef) schema resolvers variableValues item
          have hchildNonempty :
              expectedScheduleQueueItemsNonempty
                (expectedChildQueueForItem schema resolvers variableValues item).fst :=
            expectedChildQueueForItem_itemsNonempty
              (ObjectRef := ObjectRef) schema resolvers variableValues item
          have hchildDistinct :
              expectedScheduleQueueKeysDistinct
                (expectedChildQueueForItem schema resolvers variableValues item).fst :=
            expectedChildQueueForItem_keysDistinct
              (ObjectRef := ObjectRef) schema resolvers variableValues item
          have hchildBudget :
              expectedScheduleQueueFieldBudgetReady schema
                (expectedChildQueueForItem schema resolvers variableValues item).fst :=
            expectedChildQueueForItem_fieldBudgetReady
              (ObjectRef := ObjectRef) schema resolvers variableValues item
              hitemBudget
          have htailAligned :
              expectedScheduleQueueFuelsAligned
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst) :=
            enqueueExpectedScheduleItems_fuelsAligned rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst
              hchildAligned hrestAligned
          have htailNonempty :
              expectedScheduleQueueItemsNonempty
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst) :=
            enqueueExpectedScheduleItems_itemsNonempty rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst
              hrestNonempty hchildNonempty
          have htailDistinct :
              expectedScheduleQueueKeysDistinct
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst) :=
            enqueueExpectedScheduleItems_keysDistinct rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst
              hrestDistinct hchildDistinct
          have htailBudgetReady :
              expectedScheduleQueueFieldBudgetReady schema
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst) :=
            enqueueExpectedScheduleItems_fieldBudgetReady
              (ObjectRef := ObjectRef) schema rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst
              hchildBudget hrestBudget
          have htailDrainBudget :
              expectedScheduleQueueRuntimeDrainBudget schema resolvers
                  (materializeExpectedQueueItemRuntimeScopes schema resolvers item
                    materialized)
                  (enqueueExpectedScheduleItems rest
                    (expectedChildQueueForItem schema resolvers variableValues item).fst) <=
                fuel :=
            hstepBudget materialized fuel item rest haligned hnonempty hdistinct
              hfieldBudget hbudget
          simp [expectedDrainQueueReady]
          exact ⟨haligned, hnonempty, hdistinct, hitemReady,
            ih (materializeExpectedQueueItemRuntimeScopes schema resolvers item
                materialized)
              (enqueueExpectedScheduleItems rest
                (expectedChildQueueForItem schema resolvers variableValues item).fst)
              htailAligned htailNonempty htailDistinct htailBudgetReady
              htailDrainBudget⟩

theorem expectedDrainQueueReady_of_runtimeDrainBudget_contains_and_stepBudget
    (schema : Schema)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    : (∀ (materialized : MaterializedPendingScopes)
          (fuel : Nat) (item : ExpectedQueueItem ObjectRef)
          (rest : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueFuelsAligned (item :: rest)
        -> expectedScheduleQueueItemsNonempty (item :: rest)
        -> expectedScheduleQueueKeysDistinct (item :: rest)
        -> expectedScheduleQueueFieldBudgetReady schema (item :: rest)
        -> expectedScheduleQueueContainsPendingScopeShapeList
            schema variableValues (item :: rest) materialized
        -> expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
              (item :: rest)
            <= fuel + 1
        -> expectedScheduleQueueRuntimeDrainBudget schema resolvers
                (materializeExpectedQueueItemRuntimeScopes schema resolvers item
                  materialized)
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst)
              <= fuel
            ∧ expectedScheduleQueueContainsPendingScopeShapeList
                schema variableValues
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst)
                (materializeExpectedQueueItemRuntimeScopes schema resolvers item
                  materialized))
      -> ∀ (materialized : MaterializedPendingScopes)
            (fuel : Nat) (queue : ExpectedScheduleQueue ObjectRef),
          expectedScheduleQueueFuelsAligned queue
          -> expectedScheduleQueueItemsNonempty queue
          -> expectedScheduleQueueKeysDistinct queue
          -> expectedScheduleQueueFieldBudgetReady schema queue
          -> expectedScheduleQueueContainsPendingScopeShapeList
              schema variableValues queue materialized
          -> expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized queue
              <= fuel
          -> expectedDrainQueueReady schema resolvers variableValues fuel queue := by
  intro hstepBudget
  intro materialized fuel
  induction fuel generalizing materialized with
  | zero =>
      intro queue _haligned hnonempty _hdistinct _hfieldBudget _hcontains hbudget
      cases queue with
      | nil =>
          simp [expectedDrainQueueReady]
      | cons item rest =>
          have hcurrent :
              0 < expectedQueueItemCurrentShapeCount item :=
            expectedQueueItemCurrentShapeCount_pos
              (ObjectRef := ObjectRef) item (hnonempty item (by simp))
          simp [expectedScheduleQueueRuntimeDrainBudget] at hbudget
          omega
  | succ fuel ih =>
      intro queue haligned hnonempty hdistinct hfieldBudget hcontains hbudget
      cases queue with
      | nil =>
          simp [expectedDrainQueueReady]
      | cons item rest =>
          have hitemReady :
              expectedQueueItemStepFuelReady schema item :=
            expectedQueueItemStepFuelReady_of_fieldBudgetReady
              (ObjectRef := ObjectRef) schema item
              (hfieldBudget item (by simp))
          have hrestAligned :
              expectedScheduleQueueFuelsAligned rest := by
            intro restItem hrestItem
            exact haligned restItem (by simp [hrestItem])
          have hrestNonempty :
              expectedScheduleQueueItemsNonempty rest := by
            intro restItem hrestItem
            exact hnonempty restItem (by simp [hrestItem])
          have hdistinctCons :
              expectedScheduleQueueKeysDistinct (item :: rest) := hdistinct
          have hrestDistinct :
              expectedScheduleQueueKeysDistinct rest := hdistinctCons.2
          have hitemBudget :
              expectedQueueItemFieldBudgetReady schema item :=
            hfieldBudget item (by simp)
          have hrestBudget :
              expectedScheduleQueueFieldBudgetReady schema rest := by
            intro restItem hrestItem
            exact hfieldBudget restItem (by simp [hrestItem])
          have hchildAligned :
              expectedScheduleQueueFuelsAligned
                (expectedChildQueueForItem schema resolvers variableValues item).fst :=
            expectedChildQueueForItem_fuelsAligned
              (ObjectRef := ObjectRef) schema resolvers variableValues item
          have hchildNonempty :
              expectedScheduleQueueItemsNonempty
                (expectedChildQueueForItem schema resolvers variableValues item).fst :=
            expectedChildQueueForItem_itemsNonempty
              (ObjectRef := ObjectRef) schema resolvers variableValues item
          have hchildDistinct :
              expectedScheduleQueueKeysDistinct
                (expectedChildQueueForItem schema resolvers variableValues item).fst :=
            expectedChildQueueForItem_keysDistinct
              (ObjectRef := ObjectRef) schema resolvers variableValues item
          have hchildBudget :
              expectedScheduleQueueFieldBudgetReady schema
                (expectedChildQueueForItem schema resolvers variableValues item).fst :=
            expectedChildQueueForItem_fieldBudgetReady
              (ObjectRef := ObjectRef) schema resolvers variableValues item
              hitemBudget
          have htailAligned :
              expectedScheduleQueueFuelsAligned
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst) :=
            enqueueExpectedScheduleItems_fuelsAligned rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst
              hchildAligned hrestAligned
          have htailNonempty :
              expectedScheduleQueueItemsNonempty
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst) :=
            enqueueExpectedScheduleItems_itemsNonempty rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst
              hrestNonempty hchildNonempty
          have htailDistinct :
              expectedScheduleQueueKeysDistinct
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst) :=
            enqueueExpectedScheduleItems_keysDistinct rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst
              hrestDistinct hchildDistinct
          have htailBudgetReady :
              expectedScheduleQueueFieldBudgetReady schema
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst) :=
            enqueueExpectedScheduleItems_fieldBudgetReady
              (ObjectRef := ObjectRef) schema rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst
              hchildBudget hrestBudget
          have hstep :=
            hstepBudget materialized fuel item rest haligned hnonempty hdistinct
              hfieldBudget hcontains hbudget
          rcases hstep with ⟨htailDrainBudget, htailContains⟩
          simp [expectedDrainQueueReady]
          exact ⟨haligned, hnonempty, hdistinct, hitemReady,
            ih (materializeExpectedQueueItemRuntimeScopes schema resolvers item
                materialized)
              (enqueueExpectedScheduleItems rest
                (expectedChildQueueForItem schema resolvers variableValues item).fst)
              htailAligned htailNonempty htailDistinct htailBudgetReady
              htailContains htailDrainBudget⟩

theorem expectedRuntimeDrainStepBudget_lookup_none
    (schema : Schema)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (materialized : MaterializedPendingScopes)
    (fuel : Nat) (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : schema.lookupField item.key.parentType item.key.fieldName = none
      -> expectedScheduleQueueItemsNonempty (item :: rest)
      -> expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
            (item :: rest)
          <= fuel + 1
      -> expectedScheduleQueueRuntimeDrainBudget schema resolvers
            (materializeExpectedQueueItemRuntimeScopes schema resolvers item materialized)
            (enqueueExpectedScheduleItems rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst)
          <= fuel := by
  intro hlookup hnonempty hbudget
  have hcurrent :
      0 < expectedQueueItemCurrentShapeCount item :=
    expectedQueueItemCurrentShapeCount_pos
      (ObjectRef := ObjectRef) item (hnonempty item (by simp))
  have hcredit :
      expectedQueueItemRuntimeCreditWeight schema resolvers materialized item = 0 :=
    expectedQueueItemRuntimeCreditWeight_lookup_none
      (ObjectRef := ObjectRef) schema resolvers materialized item hlookup
  have hmaterialized :
      materializeExpectedQueueItemRuntimeScopes schema resolvers item materialized =
        materialized :=
    materializeExpectedQueueItemRuntimeScopes_lookup_none
      (ObjectRef := ObjectRef) schema resolvers materialized item hlookup
  have hchild :
      (expectedChildQueueForItem schema resolvers variableValues item).fst = [] := by
    simp [expectedChildQueueForItem, hlookup]
  simp [expectedScheduleQueueRuntimeDrainBudget, hcredit, hmaterialized] at hbudget
  simpa [hmaterialized, hchild, enqueueExpectedScheduleItems] using
    (by omega : expectedScheduleQueueRuntimeDrainBudget schema resolvers
        materialized rest <= fuel)

theorem expectedRuntimeDrainStepBudget_of_childRuntimeBudget_le
    (schema : Schema)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (materialized : MaterializedPendingScopes)
    (fuel : Nat) (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : item.segments ≠ []
      -> expectedScheduleQueueRuntimeDrainBudget schema resolvers
            (materializeExpectedQueueItemRuntimeScopes schema resolvers item materialized)
            (enqueueExpectedScheduleItems rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst)
          <= expectedScheduleQueueRuntimeDrainBudget schema resolvers
                (materializeExpectedQueueItemRuntimeScopes schema resolvers item
                  materialized) rest
              + expectedQueueItemRuntimeCreditWeight schema resolvers materialized item
      -> expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
            (item :: rest)
          <= fuel + 1
      -> expectedScheduleQueueRuntimeDrainBudget schema resolvers
            (materializeExpectedQueueItemRuntimeScopes schema resolvers item materialized)
            (enqueueExpectedScheduleItems rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst)
          <= fuel := by
  intro hsegments henqueue hbudget
  have hcurrent :
      0 < expectedQueueItemCurrentShapeCount item :=
    expectedQueueItemCurrentShapeCount_pos
      (ObjectRef := ObjectRef) item hsegments
  simp [expectedScheduleQueueRuntimeDrainBudget] at hbudget
  omega

theorem expectedRuntimeDrainStepBudget_lookup_some_of_enqueue_le
    (schema : Schema)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (materialized : MaterializedPendingScopes)
    (fuel : Nat) (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedScheduleQueueItemsNonempty (item :: rest)
      -> expectedScheduleQueueRuntimeDrainBudget schema resolvers
            (materializeExpectedQueueItemRuntimeScopes schema resolvers item materialized)
            (enqueueExpectedScheduleItems rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst)
          <= expectedScheduleQueueRuntimeDrainBudget schema resolvers
                (materializeExpectedQueueItemRuntimeScopes schema resolvers item
                  materialized) rest
              + expectedQueueItemRuntimeCreditWeight schema resolvers materialized item
      -> expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
            (item :: rest)
          <= fuel + 1
      -> expectedScheduleQueueRuntimeDrainBudget schema resolvers
            (materializeExpectedQueueItemRuntimeScopes schema resolvers item materialized)
            (enqueueExpectedScheduleItems rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst)
          <= fuel := by
  intro _hlookup hnonempty henqueue hbudget
  exact expectedRuntimeDrainStepBudget_of_childRuntimeBudget_le
    (ObjectRef := ObjectRef) schema resolvers variableValues materialized
    fuel item rest
    (hnonempty item (by simp))
    henqueue hbudget

theorem expectedRuntimeDrainStepBudget_lookup_some_of_childStepWeight_le
    (schema : Schema)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (materialized : MaterializedPendingScopes)
    (fuel : Nat) (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedScheduleQueueItemsNonempty (item :: rest)
      -> expectedScheduleQueueRuntimeStepWeight schema
            (expectedChildQueueForItem schema resolvers variableValues item).fst
          <= expectedQueueItemRuntimeCreditWeight schema resolvers materialized item
      -> expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
            (item :: rest)
          <= fuel + 1
      -> expectedScheduleQueueRuntimeDrainBudget schema resolvers
            (materializeExpectedQueueItemRuntimeScopes schema resolvers item materialized)
            (enqueueExpectedScheduleItems rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst)
          <= fuel := by
  intro hlookup hnonempty hchild hbudget
  apply expectedRuntimeDrainStepBudget_lookup_some_of_enqueue_le
      (ObjectRef := ObjectRef) schema resolvers variableValues materialized
      fuel item rest fieldDefinition hlookup hnonempty
  · have henqueue :=
      expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedScheduleItems_le
        (ObjectRef := ObjectRef) schema resolvers
        (materializeExpectedQueueItemRuntimeScopes schema resolvers item
          materialized)
        rest
        (expectedChildQueueForItem schema resolvers variableValues item).fst
    exact Nat.le_trans henqueue (by omega)
  · exact hbudget

theorem expectedRuntimeDrainStepBudget_lookup_some_of_mergedChildStepWeight_le
    (schema : Schema)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (materialized : MaterializedPendingScopes)
    (fuel : Nat) (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedScheduleQueueItemsNonempty (item :: rest)
      -> expectedScheduleQueueKeysDistinct (item :: rest)
      -> expectedScheduleQueueMergedRuntimeStepWeight schema
            (expectedChildQueueForItem schema resolvers variableValues item).fst
          <= expectedQueueItemRuntimeCreditWeight schema resolvers materialized item
      -> expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
            (item :: rest)
          <= fuel + 1
      -> expectedScheduleQueueRuntimeDrainBudget schema resolvers
            (materializeExpectedQueueItemRuntimeScopes schema resolvers item materialized)
            (enqueueExpectedScheduleItems rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst)
          <= fuel := by
  intro hlookup hnonempty hdistinct hchild hbudget
  apply expectedRuntimeDrainStepBudget_lookup_some_of_enqueue_le
      (ObjectRef := ObjectRef) schema resolvers variableValues materialized
      fuel item rest fieldDefinition hlookup hnonempty
  · have hrestDistinct : expectedScheduleQueueKeysDistinct rest := hdistinct.2
    have henqueue :=
      expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedScheduleItems_merged_le
        (ObjectRef := ObjectRef) schema resolvers
        (materializeExpectedQueueItemRuntimeScopes schema resolvers item
          materialized)
        rest
        (expectedChildQueueForItem schema resolvers variableValues item).fst
        hrestDistinct
    exact Nat.le_trans henqueue (by omega)
  · exact hbudget

theorem expectedPendingChildWorkBreadthShapeWeight_lookup_some_le_runtimeCredit
    (schema : Schema)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    (item : ExpectedQueueItem ObjectRef)
    (fieldDefinition : FieldDefinition)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedPendingChildWorkBreadthShapeWeight schema
            (expectedPendingChildWorkForItem schema resolvers
              fieldDefinition.outputType item)
          <= expectedQueueItemRuntimeCreditWeight schema resolvers materialized item := by
  intro hschema hlookup
  have hactual :=
    expectedPendingChildWorkForItem_breadthShapeWeight_le_possibleRuntimeChildShapes
      (ObjectRef := ObjectRef) schema resolvers fieldDefinition.outputType item
  have hpossibleLength :
      (schema.getPossibleTypes fieldDefinition.outputType.namedType).length <=
        schema.objectTypes.length + 1 := by
    have hbase :=
      schemaWellFormed_possibleTypes_length_le_objectTypes
        schema fieldDefinition.outputType.namedType hschema
    omega
  have hpossible :=
    expectedQueueItemPossibleRuntimeChildShapes_breadthWeight_le_credit
      (ObjectRef := ObjectRef) schema fieldDefinition.outputType item
      hpossibleLength
  exact Nat.le_trans hactual
    (by
      simpa [expectedQueueItemRuntimeCreditWeight, hlookup] using hpossible)

theorem expectedChildQueueForItem_mergedRuntimeStepWeight_lookup_some_le_runtimeCredit
    (schema : Schema)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (materialized : MaterializedPendingScopes)
    (item : ExpectedQueueItem ObjectRef)
    (fieldDefinition : FieldDefinition)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedScheduleQueueMergedRuntimeStepWeight schema
            (expectedChildQueueForItem schema resolvers variableValues item).fst
          <= expectedQueueItemRuntimeCreditWeight schema resolvers materialized item := by
  intro hschema hlookup
  exact Nat.le_trans
    (expectedChildQueueForItem_mergedRuntimeStepWeight_lookup_some_le_pendingBreadthShapeWeight
      (ObjectRef := ObjectRef) schema resolvers variableValues item
      fieldDefinition hlookup)
    (expectedPendingChildWorkBreadthShapeWeight_lookup_some_le_runtimeCredit
      (ObjectRef := ObjectRef) schema resolvers materialized item
      fieldDefinition hschema hlookup)

theorem expectedRuntimeDrainStepBudget_of_ready
    (schema : Schema)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ (materialized : MaterializedPendingScopes)
            (fuel : Nat) (item : ExpectedQueueItem ObjectRef)
            (rest : ExpectedScheduleQueue ObjectRef),
          expectedScheduleQueueFuelsAligned (item :: rest)
          -> expectedScheduleQueueItemsNonempty (item :: rest)
          -> expectedScheduleQueueKeysDistinct (item :: rest)
          -> expectedScheduleQueueFieldBudgetReady schema (item :: rest)
          -> expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                (item :: rest)
              <= fuel + 1
          -> expectedScheduleQueueRuntimeDrainBudget schema resolvers
                (materializeExpectedQueueItemRuntimeScopes schema resolvers item
                  materialized)
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst)
              <= fuel := by
  intro hschema materialized fuel item rest _haligned hnonempty hdistinct
    _hfieldBudget hbudget
  cases hlookup : schema.lookupField item.key.parentType item.key.fieldName with
  | none =>
      exact expectedRuntimeDrainStepBudget_lookup_none
        (ObjectRef := ObjectRef) schema resolvers variableValues materialized
        fuel item rest hlookup hnonempty hbudget
  | some fieldDefinition =>
      exact expectedRuntimeDrainStepBudget_lookup_some_of_mergedChildStepWeight_le
        (ObjectRef := ObjectRef) schema resolvers variableValues materialized
        fuel item rest fieldDefinition hlookup hnonempty hdistinct
        (expectedChildQueueForItem_mergedRuntimeStepWeight_lookup_some_le_runtimeCredit
          (ObjectRef := ObjectRef) schema resolvers variableValues materialized
          item fieldDefinition hschema hlookup)
        hbudget

theorem expectedRootTailQueue_contains_materializedRuntimeScopes
    (schema : Schema) (operation : Operation)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [preservationFuelBound schema operation]
          operation.selectionSet []).fst
        = item :: rest
      -> expectedScheduleQueueContainsPendingScopeShapeList
          schema variableValues
          (enqueueExpectedScheduleItems rest
            (expectedChildQueueForItem schema resolvers variableValues item).fst)
          (materializeExpectedQueueItemRuntimeScopes schema resolvers item []) := by
  intro _hqueue
  cases hlookup : schema.lookupField item.key.parentType item.key.fieldName with
  | none =>
      simp [expectedChildQueueForItem, hlookup,
        materializeExpectedQueueItemRuntimeScopes,
        materializeExpectedPendingChildWorkScopes,
        expectedQueueItemRuntimeChildWork, expectedPendingChildWorkShapes,
        expectedScheduleQueueContainsPendingScopeShapeList,
        pendingScopeShapeMemberBool]
  | some fieldDefinition =>
      let work :=
        expectedPendingChildWorkForItem schema resolvers
          fieldDefinition.outputType item
      have htail :
          enqueueExpectedScheduleItems rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst =
            (scheduleExpectedPendingChildWork schema variableValues
              work rest).fst := by
        simpa [expectedChildQueueForItem, hlookup, work] using
          queue_enqueueExpectedScheduleItems_scheduleExpectedPendingChildWork_empty
            (ObjectRef := ObjectRef) schema variableValues work rest
      have hcontains :
          expectedScheduleQueueContainsPendingScopeShapeList
            schema variableValues
            (scheduleExpectedPendingChildWork schema variableValues
              work rest).fst
            (materializeExpectedPendingChildWorkScopes work []) := by
        apply scheduleExpectedPendingChildWork_contains_materialized_scopes
        intro shape hshape
        simp [pendingScopeShapeMemberBool] at hshape
      simpa [htail, materializeExpectedQueueItemRuntimeScopes,
        expectedQueueItemRuntimeChildWork, hlookup, work] using hcontains

theorem expectedDrainStepBudget_of_childRawShapeWeight_le
    (schema : Schema)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (materialized : MaterializedChildSelections)
    (fuel : Nat) (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : item.segments ≠ []
      -> expectedScheduleQueueRawShapeWeight schema
            (expectedChildQueueForItem schema resolvers variableValues item).fst
          <= expectedQueueItemUnmaterializedCreditWeight schema materialized item
      -> expectedScheduleQueueDrainBudget schema materialized (item :: rest) <= fuel + 1
      -> expectedScheduleQueueDrainBudget schema
            (materializeExpectedQueueItem item materialized)
            (enqueueExpectedScheduleItems rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst)
          <= fuel := by
  intro hsegments hchildRaw hbudget
  have hcurrent :
      0 < expectedQueueItemCurrentShapeCount item :=
    expectedQueueItemCurrentShapeCount_pos
      (ObjectRef := ObjectRef) item hsegments
  have henqueue :
      expectedScheduleQueueDrainBudget schema
          (materializeExpectedQueueItem item materialized)
          (enqueueExpectedScheduleItems rest
            (expectedChildQueueForItem schema resolvers variableValues item).fst) <=
        expectedScheduleQueueDrainBudget schema
          (materializeExpectedQueueItem item materialized) rest
          + expectedScheduleQueueRawShapeWeight schema
            (expectedChildQueueForItem schema resolvers variableValues item).fst :=
    expectedScheduleQueueDrainBudget_enqueueExpectedScheduleItems_ordered_le
      (ObjectRef := ObjectRef) schema
      (materializeExpectedQueueItem item materialized)
      rest
      (expectedChildQueueForItem schema resolvers variableValues item).fst
  simp [expectedScheduleQueueDrainBudget] at hbudget
  omega

theorem expectedDrainStepBudget_lookup_none
    (schema : Schema)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (materialized : MaterializedChildSelections)
    (fuel : Nat) (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : schema.lookupField item.key.parentType item.key.fieldName = none
      -> expectedScheduleQueueItemsNonempty (item :: rest)
      -> expectedScheduleQueueDrainBudget schema materialized (item :: rest) <= fuel + 1
      -> expectedScheduleQueueDrainBudget schema
            (materializeExpectedQueueItem item materialized)
            (enqueueExpectedScheduleItems rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst)
          <= fuel := by
  intro hlookup hnonempty hbudget
  apply expectedDrainStepBudget_of_childRawShapeWeight_le
      (ObjectRef := ObjectRef) schema resolvers variableValues
      materialized fuel item rest
  · exact hnonempty item (by simp)
  · rw [expectedChildQueueForItem_rawShapeWeight_lookup_none
      (ObjectRef := ObjectRef) schema resolvers variableValues item hlookup]
    omega
  · exact hbudget

theorem expectedDrainStepBudget_of_childDrainBudget_le
    (schema : Schema)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (materialized : MaterializedChildSelections)
    (fuel : Nat) (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : item.segments ≠ []
      -> expectedScheduleQueueDrainBudget schema
            (materializeExpectedQueueItem item materialized)
            (enqueueExpectedScheduleItems rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst)
          <= expectedScheduleQueueDrainBudget schema
                (materializeExpectedQueueItem item materialized) rest
              + expectedScheduleQueueDrainBudget schema []
                  (expectedChildQueueForItem schema resolvers variableValues item).fst
      -> expectedScheduleQueueDrainBudget schema []
            (expectedChildQueueForItem schema resolvers variableValues item).fst
          <= expectedQueueItemUnmaterializedCreditWeight schema materialized item
      -> expectedScheduleQueueDrainBudget schema materialized (item :: rest) <= fuel + 1
      -> expectedScheduleQueueDrainBudget schema
            (materializeExpectedQueueItem item materialized)
            (enqueueExpectedScheduleItems rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst)
          <= fuel := by
  intro hsegments henqueue hchild hbudget
  have hcurrent :
      0 < expectedQueueItemCurrentShapeCount item :=
    expectedQueueItemCurrentShapeCount_pos
      (ObjectRef := ObjectRef) item hsegments
  simp [expectedScheduleQueueDrainBudget] at hbudget
  omega

theorem expectedRootTailQueue_drainBudget_lookup_none
    (schema : Schema) (operation : Operation)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    (fuel : Nat)
    (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : schema.lookupField item.key.parentType item.key.fieldName = none
      -> preservationFuelBound schema operation = fuel + 1
      -> (scheduleExpectedScope schema variableValues (operation.rootType schema)
            [source] [preservationFuelBound schema operation]
            operation.selectionSet []).fst
          = item :: rest
      -> expectedScheduleQueueDrainBudget schema
            (materializeExpectedQueueItem item [])
            (enqueueExpectedScheduleItems rest
              (expectedChildQueueForItem schema resolvers variableValues item).fst)
          <= fuel := by
  intro hlookup hfuel hqueue
  have hrootNonempty :
      expectedScheduleQueueItemsNonempty (item :: rest) := by
    simpa [hqueue] using
      expectedRootScheduleQueue_itemsNonempty
        (ObjectRef := ObjectRef) schema operation variableValues
        (preservationFuelBound schema operation) source
  have hrootBudget :
      expectedScheduleQueueDrainBudget schema []
          (item :: rest) <= fuel + 1 := by
    have hqueueFuel :
        (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [fuel + 1] operation.selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst = item :: rest := by
      simpa [hfuel] using hqueue
    have hrootBudget' :
        expectedScheduleQueueDrainBudget schema []
            (scheduleExpectedScope schema variableValues (operation.rootType schema)
              [source] [preservationFuelBound schema operation]
              operation.selectionSet
              ([] : ExpectedScheduleQueue ObjectRef)).fst <=
          preservationFuelBound schema operation :=
      expectedRootScheduleQueue_drainBudget_le_preservationFuelBound
        (ObjectRef := ObjectRef) schema operation variableValues source
    simpa [hfuel, hqueueFuel] using hrootBudget'
  exact expectedDrainStepBudget_lookup_none
    (ObjectRef := ObjectRef) schema resolvers variableValues
    ([] : MaterializedChildSelections) fuel item rest
    hlookup hrootNonempty hrootBudget

theorem expectedDrainQueueReady_root_tail_preservationFuel
    (schema : Schema) (operation : Operation)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    (fuel : Nat)
    (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> rootSourceAppliesBool schema operation source = true
      -> preservationFuelBound schema operation = fuel + 1
      -> (scheduleExpectedScope schema variableValues (operation.rootType schema)
            [source] [preservationFuelBound schema operation]
            operation.selectionSet []).fst
          = item :: rest
      -> expectedDrainQueueReady schema resolvers variableValues fuel
          (enqueueExpectedScheduleItems rest
            (expectedChildQueueForItem schema resolvers variableValues item).fst) := by
  intro hschema _hvalid _hroot hfuel hqueue
  let tailQueue :=
    enqueueExpectedScheduleItems rest
      (expectedChildQueueForItem schema resolvers variableValues item).fst
  have hshape :
      expectedScheduleQueueFuelsAligned tailQueue
        ∧ expectedScheduleQueueItemsNonempty tailQueue
        ∧ expectedScheduleQueueKeysDistinct tailQueue := by
    simpa [tailQueue] using
      expectedRootTailQueue_shapeInvariants_preservation
        (ObjectRef := ObjectRef) schema operation resolvers variableValues
        source item rest hqueue
  have hbudget :
      expectedScheduleQueueFieldBudgetReady schema tailQueue := by
    simpa [tailQueue] using
      expectedRootTailQueue_fieldBudgetReady_preservation
        (ObjectRef := ObjectRef) schema operation resolvers variableValues
        source item rest hqueue
  have hfieldReady :
      expectedScheduleQueueFieldFuelReady schema tailQueue :=
    expectedScheduleQueueFieldFuelReady_of_fieldBudgetReady
      (ObjectRef := ObjectRef) schema tailQueue hbudget
  have hrootRuntimeBudget :
      expectedScheduleQueueRuntimeDrainBudget schema resolvers []
          (item :: rest) <= fuel + 1 := by
    have hrootRuntimeBudget' :
        expectedScheduleQueueRuntimeDrainBudget schema resolvers []
            (scheduleExpectedScope schema variableValues (operation.rootType schema)
              [source] [preservationFuelBound schema operation]
              operation.selectionSet
              ([] : ExpectedScheduleQueue ObjectRef)).fst <=
          preservationFuelBound schema operation :=
      expectedRootScheduleQueue_runtimeDrainBudget_le_preservationFuelBound
        (ObjectRef := ObjectRef) schema operation resolvers variableValues
        source
    have hqueueFuel :
        (scheduleExpectedScope schema variableValues (operation.rootType schema)
          [source] [fuel + 1] operation.selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst = item :: rest := by
      simpa [hfuel] using hqueue
    simpa [hfuel, hqueueFuel] using hrootRuntimeBudget'
  have htailRuntimeBudget :
      expectedScheduleQueueRuntimeDrainBudget schema resolvers
          (materializeExpectedQueueItemRuntimeScopes schema resolvers item [])
          tailQueue <= fuel :=
    expectedRuntimeDrainStepBudget_of_ready
      (ObjectRef := ObjectRef) schema resolvers variableValues hschema
      ([] : MaterializedPendingScopes) fuel item rest
      (by
        let rootQueue :=
          (scheduleExpectedScope schema variableValues (operation.rootType schema)
            [source] [preservationFuelBound schema operation]
            operation.selectionSet ([] : ExpectedScheduleQueue ObjectRef)).fst
        have hrootAligned :
            expectedScheduleQueueFuelsAligned rootQueue := by
          simpa [rootQueue] using
            expectedRootScheduleQueue_fuelsAligned
              (ObjectRef := ObjectRef) schema operation variableValues
              (preservationFuelBound schema operation) source
        simpa [rootQueue, hqueue] using hrootAligned)
      (by
        let rootQueue :=
          (scheduleExpectedScope schema variableValues (operation.rootType schema)
            [source] [preservationFuelBound schema operation]
            operation.selectionSet ([] : ExpectedScheduleQueue ObjectRef)).fst
        have hrootNonempty :
            expectedScheduleQueueItemsNonempty rootQueue := by
          simpa [rootQueue] using
            expectedRootScheduleQueue_itemsNonempty
              (ObjectRef := ObjectRef) schema operation variableValues
              (preservationFuelBound schema operation) source
        simpa [rootQueue, hqueue] using hrootNonempty)
      (by
        let rootQueue :=
          (scheduleExpectedScope schema variableValues (operation.rootType schema)
            [source] [preservationFuelBound schema operation]
            operation.selectionSet ([] : ExpectedScheduleQueue ObjectRef)).fst
        have hrootDistinct :
            expectedScheduleQueueKeysDistinct rootQueue := by
          simpa [rootQueue] using
            expectedRootScheduleQueue_keysDistinct
              (ObjectRef := ObjectRef) schema operation variableValues
              (preservationFuelBound schema operation) source
        simpa [rootQueue, hqueue] using hrootDistinct)
      (by
        let rootQueue :=
          (scheduleExpectedScope schema variableValues (operation.rootType schema)
            [source] [preservationFuelBound schema operation]
            operation.selectionSet ([] : ExpectedScheduleQueue ObjectRef)).fst
        have hrootBudget :
            expectedScheduleQueueFieldBudgetReady schema rootQueue := by
          simpa [rootQueue] using
            expectedRootScheduleQueue_fieldBudgetReady_preservation
              (ObjectRef := ObjectRef) schema operation variableValues source
        simpa [rootQueue, hqueue] using hrootBudget)
      hrootRuntimeBudget
  exact expectedDrainQueueReady_of_runtimeDrainBudget_and_stepBudget
    (ObjectRef := ObjectRef) schema resolvers variableValues
    (expectedRuntimeDrainStepBudget_of_ready
      (ObjectRef := ObjectRef) schema resolvers variableValues hschema)
    (materializeExpectedQueueItemRuntimeScopes schema resolvers item [])
    fuel tailQueue hshape.1 hshape.2.1 hshape.2.2 hbudget htailRuntimeBudget

theorem expectedDrainQueueReady_root_preservationFuel
    (schema : Schema) (operation : Operation)
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> rootSourceAppliesBool schema operation source = true
      -> expectedDrainQueueReady schema resolvers variableValues
          (preservationFuelBound schema operation)
          (scheduleExpectedScope schema variableValues (operation.rootType schema)
            [source] [preservationFuelBound schema operation]
            operation.selectionSet []).fst := by
  intro hschema hvalid hroot
  have hfuelPos := preservationFuelBound_pos schema operation
  cases hfuel : preservationFuelBound schema operation with
  | zero =>
      simp [hfuel] at hfuelPos
  | succ fuel =>
      cases hqueue
            : (scheduleExpectedScope schema variableValues (operation.rootType schema)
                [source] [preservationFuelBound schema operation]
                operation.selectionSet ([] : ExpectedScheduleQueue ObjectRef)).fst with
      | nil =>
          have hqueue' :
              (scheduleExpectedScope schema variableValues (operation.rootType schema)
                [source] [fuel + 1] operation.selectionSet
                ([] : ExpectedScheduleQueue ObjectRef)).fst = [] := by
            simpa [hfuel] using hqueue
          simp [expectedDrainQueueReady, hqueue']
      | cons item rest =>
          have hqueue' :
              (scheduleExpectedScope schema variableValues (operation.rootType schema)
                [source] [fuel + 1] operation.selectionSet
                ([] : ExpectedScheduleQueue ObjectRef)).fst = item :: rest := by
            simpa [hfuel] using hqueue
          simp [expectedDrainQueueReady, hqueue']
          constructor
          · simpa [hqueue] using
              expectedRootScheduleQueue_fuelsAligned
                (ObjectRef := ObjectRef) schema operation variableValues
                (preservationFuelBound schema operation) source
          constructor
          · simpa [hqueue] using
              expectedRootScheduleQueue_itemsNonempty
                (ObjectRef := ObjectRef) schema operation variableValues
                (preservationFuelBound schema operation) source
          constructor
          · simpa [hqueue] using
              expectedRootScheduleQueue_keysDistinct
                (ObjectRef := ObjectRef) schema operation variableValues
                (preservationFuelBound schema operation) source
          constructor
          · exact
              expectedRootScheduleQueue_stepFuelReady_preservation
                (ObjectRef := ObjectRef) schema operation variableValues source
                item (by simp [hqueue])
          · exact
              expectedDrainQueueReady_root_tail_preservationFuel
                (ObjectRef := ObjectRef) schema operation resolvers variableValues
                source fuel item rest hschema hvalid hroot hfuel hqueue

theorem breadthExecutionPreservesSpecExecution_proof
    (schema : Schema) (operation : Operation)
    : breadthExecutionPreservesSpecExecution schema operation := by
  intro hschema hvalid ObjectRef resolvers variableValues source _hvars
  let coercedVariableValues :=
    GraphQL.Execution.coerceVariableValues operation variableValues
  by_cases hroot : rootSourceAppliesBool schema operation source = true
  · apply executeQueryWithFuel_eq_spec_of_rootSelectionSet_eq
      (ObjectRef := ObjectRef) schema operation resolvers variableValues
      (preservationFuelBound schema operation) source hroot
    exact
      executeRootSelectionSet_eq_spec_of_drain_ready
        (ObjectRef := ObjectRef) schema operation resolvers coercedVariableValues
        (preservationFuelBound schema operation) source
        hschema hroot
        (expectedDrainQueueReady_root_preservationFuel
          (ObjectRef := ObjectRef) schema operation resolvers coercedVariableValues
          source hschema hvalid hroot)
  · exact
      let hfalse : rootSourceAppliesBool schema operation source = false := by
        cases h : rootSourceAppliesBool schema operation source with
        | false =>
            rfl
        | true =>
            have htrue : rootSourceAppliesBool schema operation source = true := by
              simpa using h
            exact False.elim (hroot htrue)
      executeQueryWithFuel_eq_spec_of_rootSourceAppliesBool_false
        (ObjectRef := ObjectRef) schema operation resolvers variableValues
        (preservationFuelBound schema operation) source hfalse

end ExecutionBreadth

end Algorithms

end GraphQL
