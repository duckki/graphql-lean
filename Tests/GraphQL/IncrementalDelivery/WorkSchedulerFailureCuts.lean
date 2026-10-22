import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailurePlacement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureAnnouncementCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MixedFailureHealth
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Stream failure cuts retain per-node counts across unrelated stream and object failures. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerFailureCuts
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Two distinct failed streams do not accumulate each other's errors
-----------------------------------------------------------------------------------------

private def left : DeliveryNode := { ref := 0, path := [.field "left"] }
private def right : DeliveryNode := { ref := 1, path := [.field "right"] }

private def independentWork : Execution.Work :=
  .combine (.stream left [({ result := .error 2 }, .empty)])
    (.stream right [({ result := .error 3 }, .empty)])

private def independentInputs : List (List GraphEvent) :=
  [[.streamFailure left 2], [.streamFailure right 3]]

private def independentAtoms : List Execution.WorkQueueEvent :=
  ((State.initialize (Work.fromExecution independentWork)).runNormalized
    independentInputs).2.flatten.flatMap
    publicationAtoms

private def independentCuts : FailureCuts := [(0, .item [0] 0), (1, .item [1] 0)]

/-- Independent stream failures retain their two exact output positions and failing tasks.
Witness: evaluate the actual runner and attach each located failed item to its own notice.
This raw finite fixture exercises the count theorem, which does not require generated work.
-/
private theorem independent_cuts
    : StreamFailureCuts independentWork independentAtoms independentCuts := by
  refine ⟨rfl, ?_⟩
  intro entry member
  rcases List.mem_cons.mp member with same | last
  · subst entry
    exact ⟨left, 2, none, rfl, TaskAt.item (work := independentWork) (address := [0])
      (result := { result := .error 2 }) (by cbv) rfl⟩
  · have same := List.mem_singleton.mp last
    subst entry
    exact ⟨right, 3, none, rfl, TaskAt.item (work := independentWork) (address := [1])
      (result := { result := .error 3 }) (by cbv) rfl⟩

/-- Distinct closure refs keep the actual output's stream actions ordered.
Witness: the first closes only the left ref and the second only the right ref.
-/
private theorem independent_ordered
    : (independentAtoms.filterMap streamAction).Pairwise StreamAction.Before := by
  change [(left.ref, true), (right.ref, true)].Pairwise StreamAction.Before
  simp [StreamAction.Before, left, right]

/-- The second stream reports three errors, not the sum of both streams' five errors.
Witness: exact counting under the same two-cut inventory, at each actual closing position.
-/
theorem independent_counts
    : NodeFailureCause independentWork (failedBefore independentCuts 0) left.ref 2
      ∧ NodeFailureCause independentWork (failedBefore independentCuts 1) right.ref 3
      ∧ (independentCuts.map Prod.snd).Nodup := by
  exact ⟨
    independent_cuts.nodeErrors independent_ordered rfl (by decide),
    independent_cuts.nodeErrors independent_ordered rfl (by decide),
    independent_cuts.unique independent_ordered
  ⟩

-----------------------------------------------------------------------------------------
-- An actual generated object failure precedes the streamed non-null item failure
-----------------------------------------------------------------------------------------

private def selections : List Selection :=
  [field "strict" [] [.stream], defer [field "required"]]

private def mixedWork : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1.work

private def stream : DeliveryNode := { ref := 1, path := [.field "strict"] }
private def group : DeliveryNode := { ref := 0, path := [] }

private def entries : List (TaskOutcome ResponseValue × Execution.Work) :=
  [
    ({ result := .ok (.scalar "x", 0) }, .empty),
    ({ result := .error 1, cause := some 1 }, .empty)
  ]

private def first : GraphEvent :=
  .streamItems stream [⟨.item [0, 0, 1] 0, ⟨.scalar "x", 0⟩, {}⟩]

private def objectFailure : GraphEvent := .taskFailure (.executionGroup [1, 0]) 1

private def mixedInputs : List (List GraphEvent) :=
  [[first], [objectFailure], [.streamFailure stream 1]]

private def mixedAtoms : List Execution.WorkQueueEvent :=
  ((State.initialize (Work.fromExecution mixedWork)).runNormalized
    mixedInputs).2.flatten.flatMap
    publicationAtoms

private def mixedCuts : FailureCuts := [(2, .item [0, 0, 1] 1)]

/-- Real execution generates the streamed list and the independent failed deferred group.
Witness: the finite fixture is defined by that root execution itself.
-/
private theorem mixed_generated : ExecutedWork mixedWork :=
  ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0, selections, rfl⟩

/-- The stream keeps the two outcomes computed by non-null item completion.
Witness: its exact structural location in the generated root work.
-/
private theorem stream_located
    : Located mixedWork [0, 0, 1] (.stream stream entries) none [] := by cbv

/-- The deferred object task has its exact independent one-error outcome.
Witness: locate the generated execution group and project its task descriptor.
-/
private theorem object_known
    : TaskAt mixedWork (.executionGroup [1, 0]) [group.ref] none
        (.object [] (.error 1)) :=
  TaskAt.executionGroup (result := { result := .error 1, cause := some 1 })
    (groups := [⟨group, []⟩]) (children := .empty) (owners := []) (by cbv)

/-- This mixed failure sequence obeys the existing source contract and actual start checks.
Witness: exact outcomes, successful first item, fresh root settlements, and failure at
the stream's next ordinal. No output-admission premise is supplied.
-/
theorem mixed_source_valid
    : ValidGraphEvents mixedWork mixedInputs.flatten
      ∧ inputsStarted mixedWork mixedInputs = true := by
  have firstMatch : first.MatchesWork mixedWork := by
    intro supplied member
    have same := List.mem_singleton.mp member
    subst supplied
    exact ⟨[stream.ref], none,
      TaskAt.item (result := { result := .ok (.scalar "x", 0) })
        stream_located rfl, by cbv⟩
  have firstValid : ValidGraphEvents mixedWork [first] :=
    .append .nil firstMatch (by simp [first, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, _, stream_located, by simp, by simp,
        (by intro source impossible; cases impossible), rfl⟩
  have two : ValidGraphEvents mixedWork [first, objectFailure] :=
    .append firstValid ⟨[group.ref], none, [], object_known⟩
      (by simp [first, objectFailure, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, object_known, by intro source impossible; cases impossible⟩
  refine ⟨.append two ?_ ?_ ?_, by cbv⟩
  · exact ⟨_, _, _, _, stream_located,
    { result := .error 1, cause := some 1 }, .empty, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · simp [first, objectFailure, GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨_, _, _, _, stream_located,
      (by intro source impossible; cases impossible),
        { result := .error 1, cause := some 1 }, .empty, rfl, rfl⟩

/-- The two error notices are emitted independently, after the one successful item.
Witness: evaluate the actual normalized runner, including final termination.
-/
theorem mixed_output
    : mixedAtoms
      = [
        .streamValues stream [⟨.scalar "x", 0⟩] [] [],
        .groupFailure group 1,
        .streamFailure stream 1,
        .workQueueTermination
      ] := by cbv

/-- The actual mixed failures have complete counts and announced owners in one inventory.
Witness: the general inventory construction, with no assumed output explanation or
failure witness. Cancellation safety remains the separate licensing obligation.
-/
theorem mixed_announced_inventory
    : let queue := State.initialize (Work.fromExecution mixedWork)
      let initial := (queue.initialGroups ++ queue.initialStreams).map DeliveryNode.ref
      ∃ failures,
        CompleteFailureInventory mixedWork mixedAtoms failures
        ∧ FailureReportingWitness mixedWork initial mixedAtoms failures :=
  createWorkQueue_announcedFailureInventory_exists mixed_generated
    mixed_source_valid.1 mixed_source_valid.2

/-- Causal failures, announcements, and direct-safe owners share one actual mixed inventory.
Witness: the general replay theorem, without supplying independently chosen inventories
or assuming output admission. Ancestor and producer cancellation remain separate.
-/
theorem mixed_direct_safe_inventory
    : let queue := State.initialize (Work.fromExecution mixedWork)
      let initial := (queue.initialGroups ++ queue.initialStreams).map DeliveryNode.ref
      ∃ failures,
        CausalFailureInventory mixedWork mixedAtoms failures
        ∧ (∀ entry ∈ failures,
            ∃ owners,
              TaskHasOwners mixedWork entry.2 owners
              ∧ ∃ ref ∈ owners, ref ∈ announcedRefs initial (mixedAtoms.take entry.1))
        ∧ ∀ before cut occurrence after,
            failures = before ++ (cut, occurrence) :: after
            → ∃ owners owner,
                TaskHasOwners mixedWork occurrence owners
                ∧ owner ∈ owners
                ∧ ∀ prior priorOwners,
                    prior ∈ before.map Prod.snd
                    → TaskHasOwners mixedWork prior priorOwners
                    → owner ∉ priorOwners :=
  createWorkQueue_failureInventory_withDirectSafety mixed_generated
    mixed_source_valid.1 mixed_source_valid.2

/-- The interleaved group closure retains its exact failed object settlement.
Witness: the generic queue/publisher provenance theorem at the actual second output atom.
-/
theorem mixed_group_failure_source
    : GroupFailureOrigin mixedWork mixedInputs.flatten group 1 := by
  apply createWorkQueue_runNormalized_atomicGroupFailure_source mixed_generated mixed_source_valid.1
  change Execution.WorkQueueEvent.groupFailure group 1 ∈ mixedAtoms
  rw [mixed_output]
  simp

/-- The stream-only cut labels its actual error notice at unbatched index two.
Witness: the reported error identifies the generated second item.
-/
private theorem mixed_cuts : StreamFailureCuts mixedWork mixedAtoms mixedCuts := by
  refine ⟨by rw [mixed_output]; rfl, ?_⟩
  intro entry member
  have same := List.mem_singleton.mp member
  subst entry
  exact ⟨
    stream,
    1,
    none,
    by rw [mixed_output]; rfl,
    TaskAt.item (result := { result := .error 1, cause := some 1 }) stream_located rfl
  ⟩

/-- An earlier object failure contributes zero to the later stream's error total.
Witness: apply generated role separation, then permute to the actual failure order.
The complete failure inventory and its cut licensing are not asserted by this count test.
-/
theorem mixed_stream_error_count
    : NodeFailureCause mixedWork [.executionGroup [1, 0], .item [0, 0, 1] 1] stream.ref
        1 := by
  have ordered := createWorkQueue_runNormalized_atomicStreamActions_ordered mixed_source_valid.1
  have counts := mixed_cuts.nodeErrors_with_objects ordered mixed_generated
    (index := 2) (stream := stream) (errors := 1) (by rw [mixed_output]; rfl)
    [.executionGroup [1, 0]] (by
      intro occurrence member
      have same := List.mem_singleton.mp member
      subst occurrence
      exact ⟨[group.ref], none, [], 1, object_known⟩)
  exact nodeErrors_of_perm counts (List.Perm.swap _ _ [])

-----------------------------------------------------------------------------------------
-- The full object/stream witness retains both failure cuts at their actual boundaries
-----------------------------------------------------------------------------------------

private def mixedObjectCuts : FailureCuts := [(1, .executionGroup [1, 0])]
private def mixedFullCuts : FailureCuts := mixedObjectCuts ++ mixedCuts

/-- The cut partition changes only list order, never a cut's output position.
Witness: the full history has the object failure before the stream failure.
-/
private theorem mixed_partition : mixedFullCuts.Perm (mixedCuts ++ mixedObjectCuts) :=
  List.Perm.swap _ _ []

/-- Source notifications retain exactly the displayed object cut.
Witness: evaluate the actual host batches and their complete failure labels.
-/
private theorem mixed_object_cuts
    : let queue := State.initialize (Work.fromExecution mixedWork)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      sourceObjectFailureCuts 0 (queue.sourceRunBlocks publisher mixedInputs).2.2
      = mixedObjectCuts := by cbv

/-- The real mixed replay has one ordered complete inventory, not just separate counts.
Witness: fixed source descriptors establish bounds, unique reachable failures, and
exact group/stream counts for these concrete cuts. The separate existence theorem
checks the implementation's reporting-availability construction.
-/
theorem mixed_complete_inventory
    : CompleteFailureInventory mixedWork mixedAtoms mixedFullCuts := by
  have itemKnown : TaskAt mixedWork (.item [0, 0, 1] 1) [stream.ref] none
      (.item stream (.error 1)) :=
    TaskAt.item (result := { result := .error 1, cause := some 1 })
      stream_located (index := 1) rfl
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · intro entry member
    simp only [mixedFullCuts, mixedObjectCuts, mixedCuts, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨by rw [mixed_output]; decide, .root ⟨_, _, object_known⟩, _, _, _, object_known, rfl⟩
    · exact ⟨by rw [mixed_output]; decide, .root ⟨_, _, itemKnown⟩, _, _, _, itemKnown, rfl⟩
  · intro index node errors selected
    rw [mixed_output] at selected
    match index with
    | 0 | 2 => cases selected
    | 1 =>
        have same : group = node ∧ 1 = errors := by simpa using selected
        rcases same with ⟨rfl, rfl⟩
        exact (show NodeFailureCause mixedWork (failedBefore mixedFullCuts 1) group.ref 1 from
          ⟨.executionGroup [1, 0], by simp [failedBefore, mixedFullCuts, mixedObjectCuts, mixedCuts],
            _, _, _, object_known, by simp, rfl, by decide⟩).toCauses
    | index + 3 => cases index <;> simp at selected
  · intro index node errors selected
    rw [mixed_output] at selected
    match index with
    | 0 | 1 => cases selected
    | 2 =>
        have same : stream = node ∧ 1 = errors := by simpa using selected
        rcases same with ⟨rfl, rfl⟩
        exact ⟨
          .item [0, 0, 1] 1,
          by simp [failedBefore, mixedFullCuts, mixedObjectCuts, mixedCuts],
          _,
          _,
          _,
          itemKnown,
          by simp,
          rfl,
          by decide
        ⟩
    | index + 3 => cases index <;> simp at selected

/-- Inventory existence needs no hand-written cut labels or supplied publication matching.
Witness: the generated valid started replay theorem constructs both source partitions.
-/
theorem mixed_complete_inventory_exists
    : ∃ failures, CompleteFailureInventory mixedWork mixedAtoms failures :=
  createWorkQueue_completeFailureInventory_exists mixed_generated mixed_source_valid.1
    mixed_source_valid.2

/-- First-report placement leaves already reported object and stream failures in place.
Witness: each candidate's own boundary is a reporting closure of its sole owner.
-/
theorem mixed_reported_cuts
    : reportedFailureCuts mixedWork mixedAtoms mixedFullCuts = mixedFullCuts := by
  have objectSelected : firstReportedFailureCut mixedWork mixedAtoms
      (1, .executionGroup [1, 0]) = some 1 := by
    apply firstReportedFailureCut_eq_some (by decide)
      ⟨group, 1, .inl (by rw [mixed_output]; rfl),
        [group.ref], ⟨_, _, object_known⟩, by simp⟩
    exact fun _ after _ => after
  have streamSelected : firstReportedFailureCut mixedWork mixedAtoms
      (2, .item [0, 0, 1] 1) = some 2 := by
    apply firstReportedFailureCut_eq_some (by decide)
      ⟨stream, 1, .inr (by rw [mixed_output]; rfl),
        [stream.ref], ⟨_, _, TaskAt.item (result := { result := .error 1, cause := some 1 })
            stream_located (index := 1) rfl⟩, by simp⟩
    exact fun _ after _ => after
  simp only [reportedFailureCuts, mixedFullCuts, mixedObjectCuts, mixedCuts,
    List.cons_append, List.nil_append, List.filterMap_cons, placeReportedFailure,
    objectSelected, streamSelected, Option.map_some, List.filterMap_nil]
  exact List.mergeSort_of_pairwise (by simp)

/-- Both mixed cuts have open owners under the same actual output, without admission.
Witness: general first-report openness, with placement fixed by the preceding theorem.
-/
theorem mixed_failure_owners_open
    : let queue := State.initialize (Work.fromExecution mixedWork)
      ∀ entry ∈ mixedFullCuts,
        ∃ owners,
          TaskHasOwners mixedWork entry.2 owners
          ∧ ∃ ref ∈ owners,
              Open ((queue.initialGroups ++ queue.initialStreams).map DeliveryNode.ref)
                (mixedAtoms.take entry.1) ref := by
  rw [← mixed_reported_cuts]
  exact createWorkQueue_reportedFailureCuts_open mixed_generated mixed_source_valid.1 mixedFullCuts

/-- Equal output indices retain silent object-source order before the stream candidate.
Witness: evaluate the proof-side stable merge without identifying the distinct tasks.
-/
theorem equal_position_merge
    : mergeFailureCuts [(1, .executionGroup [0]), (1, .executionGroup [1])]
        [(1, .item [2] 0)]
      = [(1, .executionGroup [0]), (1, .executionGroup [1]), (1, .item [2] 0)] := by cbv

/-- The actual object candidate is visible at its group closure, before the stream cut.
Witness: the general complete-count theorem derives the full source inventory, then
uses the fixed cut partition without counting a later stream failure early.
-/
theorem mixed_group_error_count
    : NodeFailureCauses mixedWork (failedBefore mixedFullCuts 1) group.ref 1 := by
  exact mixed_complete_inventory.2.2.2.1 1 group 1 (by rw [mixed_output]; rfl)

/-- Both kinds of closure use the same actual object/stream candidate inventory.
Witness: the stream wrapper recovers object provenance from the real source blocks.
-/
theorem mixed_stream_complete_count
    : NodeFailureCause mixedWork (failedBefore mixedFullCuts 2) stream.ref 1 := by
  exact mixed_complete_inventory.2.2.2.2 2 stream 1 (by rw [mixed_output]; rfl)

private def reversedInputs : List (List GraphEvent) :=
  [[first], [.streamFailure stream 1], [objectFailure]]

private def reversedAtoms : List Execution.WorkQueueEvent :=
  ((State.initialize (Work.fromExecution mixedWork)).runNormalized
    reversedInputs).2.flatten.flatMap
    publicationAtoms

private def reversedStreamCuts : FailureCuts := [(1, .item [0, 0, 1] 1)]

private def reversedFullCuts : FailureCuts :=
  reversedStreamCuts ++ [(2, .executionGroup [1, 0])]

/-- Reversing the two independent failures still satisfies every source and start check.
Witness: the successful first item supplies the stream cursor; both failure producers
are absent and their identities are fresh in either order.
-/
private theorem reversed_source_valid
    : ValidGraphEvents mixedWork reversedInputs.flatten
      ∧ inputsStarted mixedWork reversedInputs = true := by
  have firstMatch : first.MatchesWork mixedWork := by
    intro supplied member
    have same := List.mem_singleton.mp member
    subst supplied
    exact ⟨[stream.ref], none,
      TaskAt.item (result := { result := .ok (.scalar "x", 0) })
        stream_located rfl, by cbv⟩
  have firstValid : ValidGraphEvents mixedWork [first] :=
    .append .nil firstMatch (by simp [first, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, _, stream_located, by simp, by simp,
        (by intro source impossible; cases impossible), rfl⟩
  have two : ValidGraphEvents mixedWork [first, .streamFailure stream 1] :=
    .append firstValid
      ⟨_, _, _, _, stream_located,
        { result := .error 1, cause := some 1 },
        .empty, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
      (by simp [first, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, _, stream_located,
        (by intro source impossible; cases impossible),
          { result := .error 1, cause := some 1 }, .empty, rfl, rfl⟩
  exact ⟨
    .append two ⟨[group.ref], none, [], object_known⟩
      (by simp [first, objectFailure, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, object_known, by intro source impossible; cases impossible⟩,
    by cbv
  ⟩

/-- The earlier stream cut labels the actual failed item, without an object-cut premise.
Witness: evaluate the reordered runner and locate the same second stream item.
-/
private theorem reversed_cuts
    : StreamFailureCuts mixedWork reversedAtoms reversedStreamCuts := by
  refine ⟨by cbv, ?_⟩
  intro entry member
  have same := List.mem_singleton.mp member
  subst entry
  exact ⟨
    stream,
    1,
    none,
    by cbv,
    TaskAt.item (result := { result := .error 1, cause := some 1 }) stream_located rfl
  ⟩

/-- The later object failure retains an owner untouched by the earlier failed stream item.
Witness: both fixed descriptors retain their distinct object and stream owner refs.
-/
theorem reversed_object_direct_safe
    : ∃ owners owner,
        TaskHasOwners mixedWork (.executionGroup [1, 0]) owners
        ∧ owner ∈ owners
        ∧ ∀ prior priorOwners,
            prior ∈ [.item [0, 0, 1] 1]
            → TaskHasOwners mixedWork prior priorOwners
            → owner ∉ priorOwners := by
  refine ⟨[group.ref], group.ref, ⟨none, _, object_known⟩, by simp, ?_⟩
  intro prior priorOwners member known
  obtain rfl := List.mem_singleton.mp member
  obtain ⟨producer, payload, descriptor⟩ := known
  have itemKnown : TaskAt mixedWork (.item [0, 0, 1] 1) [stream.ref] none
      (.item stream (.error 1)) :=
    TaskAt.item (result := { result := .error 1, cause := some 1 })
      stream_located (index := 1) rfl
  rw [(descriptor.unique itemKnown).1]
  simp [group, stream]

/-- A previously failed stream adds no errors to the later group completion.
Witness: complete mixed counting under actual source-block cuts, not a chosen subset.
-/
theorem reversed_group_error_count
    : NodeFailureCauses mixedWork (failedBefore reversedFullCuts 2) group.ref 1 := by
  exact (show NodeFailureCause mixedWork (failedBefore reversedFullCuts 2) group.ref 1 from
    ⟨.executionGroup [1, 0], by simp [failedBefore, reversedFullCuts, reversedStreamCuts],
      _, _, _, object_known, by simp, rfl, by decide⟩).toCauses

/-- The same failure totals hold when all source events arrive in one host batch.
Witness: exact block construction preserves unbatched cut positions across host batching.
-/
theorem joined_group_error_count
    : (((State.initialize (Work.fromExecution mixedWork)).runNormalized
          [reversedInputs.flatten]).2.flatten.flatMap
          publicationAtoms)
        = reversedAtoms
      ∧ NodeFailureCauses mixedWork (failedBefore reversedFullCuts 2) group.ref 1 :=
  ⟨by cbv, reversed_group_error_count⟩

/-- Every object cut names the generated deferred task's fixed failing outcome.
Witness: the original located object descriptor, retaining its one-error count.
-/
private theorem mixed_objects (entry) (member : entry ∈ mixedObjectCuts)
    : ∃ owners producer path errors,
        TaskAt mixedWork entry.2 owners producer (.object path (.error errors)) := by
  have same := List.mem_singleton.mp member
  subst entry
  exact ⟨[group.ref], none, [], 1, object_known⟩

/-- The later stream failure is admitted without dropping the earlier object failure.
Witness: mixed-cut transport, generated role separation, and actual stream openness.
-/
theorem mixed_stream_event_allowed (matching : PublicationMatching)
    : EventAllowed mixedWork
        (((State.initialize (Work.fromExecution mixedWork)).initialGroups
          ++ (State.initialize (Work.fromExecution mixedWork)).initialStreams).map
          DeliveryNode.ref)
        matching (mixedAtoms.take 2) mixedFullCuts (.streamFailure stream 1) := by
  have selected : mixedAtoms[2]? = some (.streamFailure stream 1) := by rw [mixed_output]; rfl
  exact mixed_cuts.eventAllowed_mixed mixed_partition mixed_objects mixed_generated
    (createWorkQueue_runNormalized_atomicStreamActions_ordered mixed_source_valid.1)
    selected
    (createWorkQueue_runNormalized_streamOpenAt mixed_generated mixed_source_valid.1
      selected List.mem_cons_self)

/-- Both cuts form a licensed failure witness for the actual mixed output.
Witness: record the root object failure at index one; then use the mixed root-stream
licensing theorem at index two. The second check retains the preceding object cut.
No assumption about full event admission or publication matching is supplied.
-/
theorem mixed_failures_licensed (matching : PublicationMatching)
    : FailureWitness mixedWork
        (((State.initialize (Work.fromExecution mixedWork)).initialGroups
          ++ (State.initialize (Work.fromExecution mixedWork)).initialStreams).map
          DeliveryNode.ref)
        matching mixedAtoms mixedFullCuts := by
  let initial := ((State.initialize (Work.fromExecution mixedWork)).initialGroups ++
    (State.initialize (Work.fromExecution mixedWork)).initialStreams).map DeliveryNode.ref
  have initialEq : initial = [group.ref, stream.ref] := by dsimp [initial]; cbv
  have empty : FailureWitness mixedWork initial matching (mixedAtoms.take 1) [] := by
    intro before cut occurrence after impossible
    have sizes := congrArg List.length impossible
    simp at sizes
  have objectOpen : Open initial (mixedAtoms.take 1) group.ref := by
    simp [Open, announcedRefs, pendingRefs, completedRefs, eventPending, eventCompleted,
      mixed_output, initialEq, group, stream]
  have firstWitness : FailureWitness mixedWork initial matching (mixedAtoms.take 1)
      mixedObjectCuts := by
    simpa only [mixed_output, List.take_succ_cons, List.take_zero, List.length_cons,
      List.length_nil, List.nil_append, mixedObjectCuts]
      using empty.record object_known rfl
        (.root ⟨[group.ref], _, object_known⟩) ⟨group.ref, List.mem_cons_self, objectOpen⟩
        (fun cancelled => cancelled.nonempty rfl)
  have beforeSecond : FailureWitness mixedWork initial matching (mixedAtoms.take 2)
      mixedObjectCuts := by
    simpa [mixed_output] using firstWitness.append [.groupFailure group 1]
  have secondTask : TaskAt mixedWork (.item [0, 0, 1] 1) [stream.ref] none
      (.item stream (.error 1)) :=
          TaskAt.item (result := { result := .error 1, cause := some 1 }) stream_located rfl
  have selected : mixedAtoms[2]? = some (.streamFailure stream 1) := by rw [mixed_output]; rfl
  have active : ¬TaskCancelled mixedWork matching (mixedAtoms.take 2) mixedObjectCuts
      (.item [0, 0, 1] 1) :=
    mixed_cuts.rootStream_not_cancelled_mixed mixed_partition mixed_objects
      (by simp [mixedFullCuts, mixedObjectCuts, mixedCuts]) mixed_generated
      (createWorkQueue_runNormalized_atomicStreamActions_ordered mixed_source_valid.1)
      (NodeAt.stream stream_located) List.mem_cons_self selected rfl
  have secondWitness := beforeSecond.record secondTask rfl
    (.root ⟨[stream.ref], _, secondTask⟩)
    ⟨stream.ref, List.mem_cons_self,
      createWorkQueue_runNormalized_streamOpenAt mixed_generated mixed_source_valid.1
        selected List.mem_cons_self⟩ active
  simpa [mixed_output, mixedFullCuts, mixedCuts, initial]
    using secondWitness.append [.streamFailure stream 1, .workQueueTermination]

-----------------------------------------------------------------------------------------
-- Two execution-generated failures are licensed under one nonempty cut history
-----------------------------------------------------------------------------------------

namespace RootFailures

private def selections : List Selection :=
  [
    field "strict" [] [.stream (.boolean true) none (.int 1)] (some "left"),
    field "strict" [] [.stream (.boolean true) none (.int 1)] (some "right")
  ]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1.work

private def inputs : List (List GraphEvent) :=
  [[.streamFailure left 1], [.streamFailure right 1]]

private def atoms : List Execution.WorkQueueEvent :=
  ((State.initialize (Work.fromExecution work)).runNormalized inputs).2.flatten.flatMap
    publicationAtoms

private def cuts : FailureCuts := [(0, .item [0, 0, 1] 0), (1, .item [0, 1, 0, 1] 0)]

/-- The fixture is exactly a finite root execution; its defining equation is the witness. -/
private theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0, selections, rfl⟩

/-- The left failed item is located in the generated work by evaluating its address. -/
private theorem left_located
    : Located work [0, 0, 1]
        (.stream left [({ result := .error 1, cause := some 1 }, .empty)]) none [] := by
  cbv

/-- The right failed item has a distinct structural address, checked by evaluation. -/
private theorem right_located
    : Located work [0, 1, 0, 1]
        (.stream right [({ result := .error 1, cause := some 1 }, .empty)]) none [] := by
  cbv

/-- Both failures come from real execution after one item was included initially.
Witness: exact failed item locations, root source readiness, and fresh closure refs.
-/
theorem source_valid
    : ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true := by
  have first : ValidGraphEvents work [.streamFailure left 1] :=
    .append .nil
      ⟨_, _, _, _, left_located,
        { result := .error 1, cause := some 1 }, .empty, List.mem_cons_self, rfl⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, _, left_located, (by intro source impossible; cases impossible),
        { result := .error 1, cause := some 1 }, .empty, rfl, rfl⟩
  refine ⟨.append first ?_ ?_ ?_, by cbv⟩
  · exact ⟨_, _, _, _, right_located,
    { result := .error 1, cause := some 1 }, .empty, List.mem_cons_self, rfl⟩
  · simp [GraphEvent.Fresh, GraphEvent.identities, left, right]
  · exact ⟨_, _, _, _, right_located,
      (by intro source impossible; cases impossible),
        { result := .error 1, cause := some 1 }, .empty, rfl, rfl⟩

/-- The two generated streams close in source order, followed by actual queue termination.
Witness: evaluation of the normalized runner, not a hand-picked output history.
-/
theorem output
    : atoms = [.streamFailure left 1, .streamFailure right 1, .workQueueTermination] := by
  cbv

/-- Both output-aligned cuts name the exact failed tasks; located item descriptors witness this. -/
private theorem cut_origins : StreamFailureCuts work atoms cuts := by
  refine ⟨by rw [output]; rfl, ?_⟩
  intro entry member
  rcases List.mem_cons.mp member with same | last
  · subst entry
    exact ⟨left, 1, none, by rw [output]; rfl,
      TaskAt.item (result := { result := .error 1, cause := some 1 })
        left_located rfl⟩
  · have same := List.mem_singleton.mp last
    subst entry
    exact ⟨right, 1, none, by rw [output]; rfl,
      TaskAt.item (result := { result := .error 1, cause := some 1 })
        right_located rfl⟩

/-- Every failure notice names one of the two producer-free, dependency-free streams.
Witness: actual output membership and the two structural stream locations.
-/
private theorem roots (index : Nat) (stream : DeliveryNode) (errors : Nat)
    (selected : atoms[index]? = some (.streamFailure stream errors))
    : NodeAt work stream .stream [] none := by
  have member := List.mem_of_getElem? selected
  rw [output] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    Execution.WorkQueueEvent.streamFailure.injEq] at member
  rcases member with ⟨same, _⟩ | ⟨same, _⟩ | impossible
  · subst stream; exact NodeAt.stream left_located
  · subst stream; exact NodeAt.stream right_located
  · cases impossible

/-- Both candidate cuts are licensed, including the second after the first failure.
Witness: root-stream causal health and actual closure order rule out prior cancellation;
each failed item is structurally reachable and its notice is independently proved open.
The theorem works for every matching because this history contains no publications.
-/
theorem cuts_licensed (matching : PublicationMatching)
    : FailureWitness work
        (((State.initialize (Work.fromExecution work)).initialGroups
          ++ (State.initialize (Work.fromExecution work)).initialStreams).map
          DeliveryNode.ref)
        matching atoms cuts := by
  apply cut_origins.rootStream_failureWitness generated
    (createWorkQueue_runNormalized_atomicStreamActions_ordered source_valid.1) roots
  intro entry member
  obtain ⟨stream, errors, producer, atEvent, task⟩ := cut_origins.2 entry member
  obtain ⟨dependencies, located⟩ := (itemTask_owner_nodeAt task).2
  have same := generated.streamProducer_unique located (roots _ _ _ atEvent) rfl
  subst producer
  exact ⟨.root ⟨[stream.ref], _, task⟩, stream.ref, ⟨none, _, task⟩,
    createWorkQueue_runNormalized_streamOpenAt generated source_valid.1 atEvent
      List.mem_cons_self⟩

/-- Every nonterminal output in the two-failure run satisfies the complete event rule.
Witness: apply actual stream-failure admission under the same licensed cut list; no
cut is removed when proving the later event, and each notice reports one error.
-/
theorem events_allowed (matching : PublicationMatching) (index : Nat)
    (stream : DeliveryNode) (errors : Nat)
    (selected : atoms[index]? = some (.streamFailure stream errors))
    : EventAllowed work
        (((State.initialize (Work.fromExecution work)).initialGroups
          ++ (State.initialize (Work.fromExecution work)).initialStreams).map
          DeliveryNode.ref)
        matching (atoms.take index) cuts (.streamFailure stream errors) :=
  createWorkQueue_runNormalized_streamFailure_eventAllowed generated source_valid.1
    matching cut_origins selected

end RootFailures

-----------------------------------------------------------------------------------------
-- An unrelated root-stream failure does not block successful empty-stream completion
-----------------------------------------------------------------------------------------

namespace RootSuccess

private def selections : List Selection :=
  [
    field "strict" [] [.stream (.boolean true) none (.int 1)] (some "left"),
    field "empty" [] [.stream] (some "right")
  ]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1.work

private def inputs : List (List GraphEvent) :=
  [[.streamFailure left 1], [.streamSuccess right]]

private def atoms : List Execution.WorkQueueEvent :=
  ((State.initialize (Work.fromExecution work)).runNormalized inputs).2.flatten.flatMap
    publicationAtoms

private def cuts : FailureCuts := [(0, .item [0, 0, 1] 0)]

/-- This fixture is real root execution, with one failed stream and one exhausted stream. -/
private theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0, selections, rfl⟩

/-- The failed stream's location retains its single error outcome; evaluation is the witness. -/
private theorem left_located
    : Located work [0, 0, 1]
        (.stream left [({ result := .error 1, cause := some 1 }, .empty)]) none [] := by
  cbv

/-- The exhausted stream has no items or producer; its exact address is checked by evaluation. -/
private theorem right_located : Located work [0, 1, 0, 1] (.stream right []) none [] := by
  cbv

/-- Failure followed by empty-stream success satisfies the host source and start contracts.
Witness: exact outcomes and zero-length exhaustion, with distinct root closure identities.
-/
theorem source_valid
    : ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true := by
  have first : ValidGraphEvents work [.streamFailure left 1] :=
    .append .nil
      ⟨_, _, _, _, left_located,
        { result := .error 1, cause := some 1 }, .empty, List.mem_cons_self, rfl⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, _, left_located, (by intro source impossible; cases impossible),
        { result := .error 1, cause := some 1 }, .empty, rfl, rfl⟩
  refine ⟨.append first ?_ ?_ ?_, by cbv⟩
  · exact ⟨[], none, NodeAt.stream right_located⟩
  · simp [GraphEvent.Fresh, GraphEvent.identities, left, right]
  · exact ⟨_, _, _, _, right_located, (by intro source impossible; cases impossible), rfl⟩

/-- The actual normalized output preserves both distinct completion kinds before termination. -/
theorem output
    : atoms = [.streamFailure left 1, .streamSuccess right, .workQueueTermination] := by
  cbv

/-- The prior failed stream does not invalidate the right stream's complete success rule.
Witness: root-stream causal health supplies the missing health clause; actual source
coverage and notice ordering supply accounting and Open under the retained failure cut.
-/
theorem success_allowed
    : ∃ matching : PublicationMatching,
        EventAllowed work
          (((State.initialize (Work.fromExecution work)).initialGroups
            ++ (State.initialize (Work.fromExecution work)).initialStreams).map
            DeliveryNode.ref)
          matching (atoms.take 1) cuts (.streamSuccess right) := by
  obtain ⟨matching, _, values, _, covered⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching_withItemCoverage generated
      source_valid.1 source_valid.2
  have origins : StreamFailureCuts work atoms cuts := by
    refine ⟨by rw [output]; rfl, ?_⟩
    intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    exact ⟨left, 1, none, by rw [output]; rfl,
      TaskAt.item (result := { result := .error 1, cause := some 1 })
        left_located rfl⟩
  exact ⟨
    matching,
    createWorkQueue_runNormalized_rootStreamSuccess_eventAllowed generated source_valid.1
      matching (fun index event atEvent value => (values index event atEvent value).1)
      covered origins (NodeAt.stream right_located)
      (by
        change atoms[1]? = some (.streamSuccess right)
        rw [output]; rfl)
  ⟩

end RootSuccess

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerFailureCuts
