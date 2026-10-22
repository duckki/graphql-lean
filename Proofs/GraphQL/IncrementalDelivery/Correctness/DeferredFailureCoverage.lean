import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureCoverageAlgebra
import Proofs.GraphQL.IncrementalDelivery.Correctness.BasicFieldErrors

/-! Failure-aware response-position algebra for retained deferred partitions. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The partition outcomes retained by CollectExecutionGroups
-----------------------------------------------------------------------------------------

/-- Proof-only partition output: shared owners and the completed fields with child work.
These values describe retained execution outcomes, not settlements or a queue premise.
-/
abbrev CompletedPartition :=
  List DeferredFragment × Completion (List (Name × ResponseValue))

/-- Ordinary field-result combination of retained partition outcomes, including bubbling.
-/
def partitionResults : List CompletedPartition → Result (List (Name × ResponseValue))
  | [] => .ok ([], 0)
  | (_, completed) :: rest =>
      GraphQL.Execution.Result.combine List.append completed.result
        (partitionResults rest)

/-- The exact group/combine shape used to retain completed deferred partitions.
Child work is kept, and no ownership or settlement order is selected.
-/
def partitionWork (path : ResponsePath) : List CompletedPartition → Work
  | [] => .empty
  | (groups, completed) :: rest =>
      .combine (.executionGroup groups path completed.outcome completed.work)
        (partitionWork path rest)

/-- Successful partition results contribute every combined field position.
Witness: result-combination cases and list descent. Nullable errors and child work are
unrestricted, as are the number and metadata of a partition's shared owners.
-/
theorem partitionWork_success_positions (containers : Bool) (path : ResponsePath)
    (partitions : List CompletedPartition) (data : List (Name × ResponseValue))
    (errors : Nat) (completed : partitionResults partitions = .ok (data, errors))
    (address : Address) (producer : Option Occurrence)
    (cursors : ResponsePositions.Cursors)
    : (ResponsePositions.fields containers path data).Subset
        ((sourceTasks address producer cursors (partitionWork path partitions)).flatMap
          (SourceTask.positions containers)) := by
  induction partitions generalizing data errors address with
  | nil =>
      simp [partitionResults] at completed
      obtain ⟨rfl, _⟩ := completed
      intro position member
      simp [ResponsePositions.fields] at member
  | cons head tail ih =>
      obtain ⟨groups, head⟩ := head
      cases first : head.result with
      | error errors =>
          cases last : partitionResults tail <;>
            simp [partitionResults, first, last, GraphQL.Execution.Result.combine]
              at completed
      | ok initial =>
          obtain ⟨initial, initialErrors⟩ := initial
          cases last : partitionResults tail with
          | error errors =>
              simp [partitionResults, first, last, GraphQL.Execution.Result.combine]
                at completed
          | ok suffix =>
              obtain ⟨suffix, suffixErrors⟩ := suffix
              simp only [partitionResults, first, last, GraphQL.Execution.Result.combine,
                Except.ok.injEq, Prod.mk.injEq] at completed
              obtain ⟨rfl, rfl⟩ := completed
              have tailPositions := ih suffix suffixErrors last (address ++ [1])
              intro position member
              change position ∈ ResponsePositions.fields containers path (initial ++ suffix)
                at member
              rw [responsePositions_fields_append, List.mem_append] at member
              simp only [partitionWork, sourceTasks, List.flatMap_append, List.flatMap_cons,
                SourceTask.positions, Completion.outcome, TaskOutcome.deliveryResult, first, DeliveryPaths.result]
              rcases member with initialMember | suffixMember
              · exact List.mem_append_left _ (List.mem_append_left _ initialMember)
              · exact List.mem_append_right _ (tailPositions suffixMember)

/-- Bubbling of the combined deferred result identifies a retained failed group task.
Witness: inspect combination outcomes; a tail failure embeds through the right edge.
The task is real retained work, not a synthesized failure-scope premise.
-/
theorem partitionWork_failure_task (path : ResponsePath)
    (partitions : List CompletedPartition) (errors : Nat)
    (failed : partitionResults partitions = .error errors)
    : ∃ occurrence owners producer payload,
        TaskAt (partitionWork path partitions) occurrence owners producer payload
        ∧ payload.failure.isSome = true
        ∧ payload.path = path := by
  induction partitions generalizing errors with
  | nil => simp [partitionResults] at failed
  | cons head tail ih =>
      obtain ⟨groups, completed⟩ := head
      cases first : completed.result with
      | error errors =>
          have located := (StructuralEquivalence.Located.left
            (root := partitionWork path ((groups, completed) :: tail))
            StructuralEquivalence.Located.root)
          refine ⟨.executionGroup [0], groups.map (fun group => group.node.ref), none,
            .object path completed.deliveryResult, ?_, ?_, rfl⟩
          · exact (StructuralEquivalence.TaskAt.executionGroup
              (by simpa only [partitionWork, Completion.deliveryResult, List.nil_append,
                Work.withoutDeclarations] using located)).toCurrent
          · simp [Payload.failure, Completion.deliveryResult, Completion.outcome,
              TaskOutcome.deliveryResult, first]
      | ok data =>
          cases last : partitionResults tail with
          | ok suffix =>
              simp [partitionResults, first, last, GraphQL.Execution.Result.combine]
                at failed
          | error errors =>
              obtain ⟨occurrence, owners, producer, payload, known, fails, attachment⟩ :=
                ih errors last
              obtain ⟨occurrence, owners, producer, embedded⟩ := TaskAt.in_combine_right known
                (.executionGroup groups path completed.outcome completed.work)
              exact ⟨occurrence, owners, producer, payload, embedded, fails, attachment⟩

-----------------------------------------------------------------------------------------
-- Combining the initial object and retained deferred outcomes
-----------------------------------------------------------------------------------------

/-- Nonbubbling deferred partitions contribute all positions of the combined object.
Witness: the initial container and fields are immediate; suffix fields occur in retained
group payloads. This is a source-inventory inclusion, with no failure-scope assumptions.
-/
theorem partitionWork_success_inventory (initial : List (Name × ResponseValue))
    (initialWork : Work) (partitions : List CompletedPartition) (containers : Bool)
    (suffix : List (Name × ResponseValue)) (suffixErrors : Nat)
    (future : partitionResults partitions = .ok (suffix, suffixErrors))
    : (ResponsePositions.value containers [] (.object (initial ++ suffix))).Subset
        (ResponsePositions.value containers [] (.object initial)
          ++ (sourceTasks [] none (ResponsePositions.listCursors [] (.object initial))
                (.combine initialWork (partitionWork [] partitions))).flatMap
              (SourceTask.positions containers)) := by
  have tailPositions := partitionWork_success_positions containers [] partitions suffix
    suffixErrors future [1] none (ResponsePositions.listCursors [] (.object initial))
  intro position member
  simp only [ResponsePositions.value, responsePositions_fields_append] at member
  rcases List.mem_append.mp member with root | fields
  · exact List.mem_append_left _ (List.mem_append_left _ root)
  · rcases List.mem_append.mp fields with prefixMember | suffixMember
    · exact List.mem_append_left _ (List.mem_append_right _ prefixMember)
    · exact List.mem_append_right _
        (by simpa only [sourceTasks, List.flatMap_append, List.mem_append, List.nil_append]
          using (Or.inr (tailPositions suffixMember) : _ ∨ _))

/-- Deferred partitions cover the response obtained by combining their retained results
with the initial fields. Witness: successful field positions are retained in source work;
bubbling supplies an actual failed task at the root. Initial and nullable errors are
unrestricted. This is partition algebra, not yet ordinary-versus-mixed execution equality.
-/
theorem preparedResponseCovers_partitions (initial : List (Name × ResponseValue))
    (initialErrors : Nat) (initialWork : Work) (partitions : List CompletedPartition)
    (containers : Bool)
    : PreparedResponseCovers
        (selectionSetResultToResponse
          (GraphQL.Execution.Result.combine List.append (.ok (initial, initialErrors))
            (partitionResults partitions))).data
        { data := .object initial, errors := initialErrors }
        (.combine initialWork (partitionWork [] partitions)) containers := by
  cases future : partitionResults partitions with
  | error errors =>
      obtain ⟨occurrence, owners, producer, payload, known, fails, attachment⟩ :=
        partitionWork_failure_task [] partitions errors future
      obtain ⟨occurrence, owners, producer, embedded⟩ :=
        TaskAt.in_combine_right known initialWork
      intro position member
      simp only [GraphQL.Execution.Result.combine, selectionSetResultToResponse,
        GraphQL.Execution.selectionSetResultToResponse, ResponsePositions.value,
        List.mem_singleton] at member
      subst position
      exact Or.inr
        ⟨
          occurrence,
          owners,
          producer,
          payload,
          embedded,
          fails,
          Or.inl (by simp [attachment])
        ⟩
  | ok result =>
      obtain ⟨suffix, suffixErrors⟩ := result
      have inventory := partitionWork_success_inventory initial initialWork partitions
        containers suffix suffixErrors future
      intro position member
      simp only [GraphQL.Execution.Result.combine, selectionSetResultToResponse,
        GraphQL.Execution.selectionSetResultToResponse, ResponsePositions.value] at member
      exact Or.inl (inventory member)

/-- Field-result equivalence transports partition coverage to the ordinary field order.
Witness: successful response positions permute into the source inventory; bubbling
identifies a real root-attached failed task. No null-path lookup is transported across a
permutation, and duplicate raw response names therefore require no extra premise here.
-/
theorem preparedResponseCovers_equivalentPartitions
    (initial : List (Name × ResponseValue)) (initialErrors : Nat) (initialWork : Work)
    (partitions : List CompletedPartition) (containers : Bool)
    (ordinary : Result (List (Name × ResponseValue)))
    (equivalent
      : TypedResponse.FieldResultsEquivalent ordinary
          (GraphQL.Execution.Result.combine List.append (.ok (initial, initialErrors))
            (partitionResults partitions)))
    : PreparedResponseCovers (selectionSetResultToResponse ordinary).data
        { data := .object initial, errors := initialErrors }
        (.combine initialWork (partitionWork [] partitions)) containers := by
  cases future : partitionResults partitions with
  | error errors =>
      cases ordinary with
      | ok data =>
          simp [TypedResponse.FieldResultsEquivalent, future,
            GraphQL.Execution.Result.combine] at equivalent
      | error errors =>
          obtain ⟨occurrence, owners, producer, payload, known, fails, attachment⟩ :=
            partitionWork_failure_task [] partitions _ future
          obtain ⟨occurrence, owners, producer, embedded⟩ :=
            TaskAt.in_combine_right known initialWork
          intro position member
          simp only [selectionSetResultToResponse,
            GraphQL.Execution.selectionSetResultToResponse, ResponsePositions.value,
            List.mem_singleton] at member
          subst position
          exact Or.inr
            ⟨
              occurrence,
              owners,
              producer,
              payload,
              embedded,
              fails,
              Or.inl (by simp [attachment])
            ⟩
  | ok result =>
      obtain ⟨suffix, suffixErrors⟩ := result
      cases ordinary with
      | error errors =>
          simp [TypedResponse.FieldResultsEquivalent, future,
            GraphQL.Execution.Result.combine] at equivalent
      | ok data =>
          obtain ⟨data, errors⟩ := data
          simp only [future, GraphQL.Execution.Result.combine,
            TypedResponse.FieldResultsEquivalent] at equivalent
          have positions := (responsePositions_fields_perm containers [] equivalent.1).append_left
            (if containers then [[]] else [])
          have inventory := partitionWork_success_inventory initial initialWork partitions
            containers suffix suffixErrors future
          intro position member
          exact Or.inl (inventory (positions.mem_iff.mp member))

-----------------------------------------------------------------------------------------
-- Actual CollectExecutionGroups retains exactly the computed partition outcomes
-----------------------------------------------------------------------------------------

attribute [local simp] Semantics.id_pure_eq Semantics.id_bind_eq Semantics.id_map_eq
  Semantics.run_bind Semantics.run_map

/-- Each actual collected partition is retained with its exact result and child work.
Witness: collector-list induction through the same state transitions. The supplied local
result equation is a field-execution comparison obligation, not a queue or wire law.
-/
theorem collectExecutionGroups_retains_results (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (partitions : List (NodeRefs × CollectedFieldsMap)) (path : ResponsePath)
    (deferMap : DeferMap) (state : NodeRef)
    (matched
      : ∀ partition ∈ partitions,
          ∀ next,
            ((executeExecutionGroup schema resolvers variables fuel parentType source
                partition.2 path partition.1 deferMap).run
              next).1.result
            = GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                parentType source (Semantics.eraseGroups partition.2))
    : ∃ completed,
        ((collectExecutionGroups schema resolvers variables fuel parentType source
            partitions path deferMap).run
            state).1
          = partitionWork path completed
        ∧ partitionResults completed
          = GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
              parentType source
              (partitions.flatMap (fun partition => Semantics.eraseGroups partition.2))
        ∧ completed.map Prod.fst
          = partitions.map
              (fun partition =>
                partition.1.filterMap (lookupDeferredFragment? deferMap)) := by
  induction partitions generalizing state with
  | nil =>
      refine ⟨[], ?_, ?_, rfl⟩
      · simp [collectExecutionGroups, partitionWork]
      · simp [partitionResults, GraphQL.Execution.executeCollectedFields]
  | cons head tail ih =>
      obtain ⟨usages, fields⟩ := head
      let first := (executeExecutionGroup schema resolvers variables fuel parentType source
        fields path usages deferMap).run state
      have resultEq := matched (usages, fields) (by simp) state
      obtain ⟨rest, retained, results, owners⟩ := ih first.2
        (fun partition member => matched partition (by simp [member]))
      refine ⟨(usages.filterMap (lookupDeferredFragment? deferMap), first.1) :: rest,
        ?_, ?_, ?_⟩
      · simpa [collectExecutionGroups, first, partitionWork] using retained
      · change GraphQL.Execution.Result.combine List.append first.1.result
          (partitionResults rest) = _
        change first.1.result = _ at resultEq
        rw [resultEq, results]
        simp only [List.flatMap_cons]
        exact (TypedResponse.basicFields_append_result schema resolvers variables fuel
          parentType source (Semantics.eraseGroups fields)
          (tail.flatMap (fun partition => Semantics.eraseGroups partition.2))).symm
      · simp [owners]

-----------------------------------------------------------------------------------------
-- The actual plan executor under local field-result agreement
-----------------------------------------------------------------------------------------

/-- Actual execution-plan coverage follows from per-partition field-result agreement,
allowing a reference field order equivalent to the plan's partition order.
Witness: replay the executor's exact state sequence, retain its computed group outcomes,
and apply the failure-aware partition algebra. No source, matching, notice, or successful
execution assumption is introduced. Nested mixed field-result comparison remains separate.
-/
theorem executeExecutionPlan_equivalent_coverage (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (newDeferUsages : List DeferUsage) (plan : ExecutionPlan) (deferUsageSet : NodeRefs)
    (deferMap : DeferMap) (state : NodeRef) (containers : Bool)
    (ordinary : Result (List (Name × ResponseValue)))
    (equivalent
      : TypedResponse.FieldResultsEquivalent ordinary
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source
            (Semantics.eraseGroups plan.collectedFieldsMap
              ++ plan.newCollectedFieldsMaps.flatMap
                  (fun partition => Semantics.eraseGroups partition.2))))
    (immediate
      : ∀ next,
          ((executeCollectedFields schema resolvers variables fuel parentType source
              plan.collectedFieldsMap [] deferUsageSet
              (getNewDeferMap newDeferUsages [] deferMap)).run
            next).1.result
          = GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
              parentType source (Semantics.eraseGroups plan.collectedFieldsMap))
    (deferred
      : ∀ partition ∈ plan.newCollectedFieldsMaps,
          ∀ next,
            ((executeExecutionGroup schema resolvers variables fuel parentType source
                partition.2 [] partition.1
                (getNewDeferMap newDeferUsages [] deferMap)).run
              next).1.result
            = GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                parentType source (Semantics.eraseGroups partition.2))
    : let completed :=
        ((executeExecutionPlan schema resolvers variables fuel parentType
            source newDeferUsages plan [] deferUsageSet deferMap).run
          state).1
      PreparedResponseCovers
        (selectionSetResultToResponse ordinary).data
        (selectionSetResultToResponse completed.result) completed.work containers := by
  let initial := (executeCollectedFields schema resolvers variables fuel parentType source
    plan.collectedFieldsMap [] deferUsageSet
    (getNewDeferMap newDeferUsages [] deferMap)).run state
  have initialEq := immediate state
  change initial.1.result = _ at initialEq
  rw [TypedResponse.basicFields_append_result, ← initialEq] at equivalent
  dsimp only
  cases outcome : initial.1.result with
  | error errors =>
      have actual : ((executeExecutionPlan schema resolvers variables fuel parentType
          source newDeferUsages plan [] deferUsageSet deferMap).run state).1 = initial.1 := by
        simp [executeExecutionPlan, initial, outcome]
      rw [actual, outcome]
      cases future : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source (plan.newCollectedFieldsMaps.flatMap
            (fun partition => Semantics.eraseGroups partition.2))
      all_goals
        cases ordinary with
        | ok data =>
            simp [TypedResponse.FieldResultsEquivalent, GraphQL.Execution.Result.combine,
              outcome, future]
              at equivalent
        | error count =>
            simp only [GraphQL.Execution.selectionSetResultToResponse,
              selectionSetResultToResponse]
            intro position member
            exact Or.inl (List.mem_append_left _ member)
  | ok data =>
      obtain ⟨data, errors⟩ := data
      obtain ⟨partitions, retained, results, owners⟩ := collectExecutionGroups_retains_results
        schema resolvers variables fuel parentType source plan.newCollectedFieldsMaps []
        (getNewDeferMap newDeferUsages [] deferMap) initial.2 deferred
      let declarations := newDeferUsages.filterMap (fun usage =>
        lookupDeferredFragment? (getNewDeferMap newDeferUsages [] deferMap) usage.ref)
      let declaredWork := Work.declareGroups declarations (partitionWork [] partitions)
      have actual : ((executeExecutionPlan schema resolvers variables fuel parentType
          source newDeferUsages plan [] deferUsageSet deferMap).run state).1
          = { initial.1 with work := .combine initial.1.work declaredWork } := by
        simp [executeExecutionPlan, initial, outcome, retained, declaredWork, declarations]
      rw [outcome, ← results] at equivalent
      have covered := preparedResponseCovers_equivalentPartitions data errors initial.1.work
        partitions containers ordinary equivalent
      rw [actual]
      simpa only [outcome, selectionSetResultToResponse,
        GraphQL.Execution.selectionSetResultToResponse]
        using covered.declareGroups_right declarations

/-- The plan-order specialization uses reflexive ordinary field-result equivalence.
Witness: `executeExecutionPlan_equivalent_coverage`; local field completion equations are
still required, and no response correctness assumption is added to the queue contract.
-/
theorem executeExecutionPlan_partition_coverage (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (newDeferUsages : List DeferUsage) (plan : ExecutionPlan) (deferUsageSet : NodeRefs)
    (deferMap : DeferMap) (state : NodeRef) (containers : Bool)
    (immediate
      : ∀ next,
          ((executeCollectedFields schema resolvers variables fuel parentType source
              plan.collectedFieldsMap [] deferUsageSet
              (getNewDeferMap newDeferUsages [] deferMap)).run
            next).1.result
          = GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
              parentType source (Semantics.eraseGroups plan.collectedFieldsMap))
    (deferred
      : ∀ partition ∈ plan.newCollectedFieldsMaps,
          ∀ next,
            ((executeExecutionGroup schema resolvers variables fuel parentType source
                partition.2 [] partition.1
                (getNewDeferMap newDeferUsages [] deferMap)).run
              next).1.result
            = GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                parentType source (Semantics.eraseGroups partition.2))
    : let completed :=
        ((executeExecutionPlan schema resolvers variables fuel parentType source
            newDeferUsages plan [] deferUsageSet deferMap).run
          state).1
      PreparedResponseCovers
        (GraphQL.Execution.selectionSetResultToResponse
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source
            (Semantics.eraseGroups plan.collectedFieldsMap
              ++ plan.newCollectedFieldsMaps.flatMap
                  (fun partition => Semantics.eraseGroups partition.2)))).data
        (selectionSetResultToResponse completed.result) completed.work containers :=
  executeExecutionPlan_equivalent_coverage schema resolvers variables fuel parentType
    source newDeferUsages plan deferUsageSet deferMap state containers _
    (TypedResponse.FieldResultsEquivalent.refl _) immediate deferred

end GraphQL.IncrementalDelivery.Correctness
