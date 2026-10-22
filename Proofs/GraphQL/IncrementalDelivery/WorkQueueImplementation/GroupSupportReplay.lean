import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupSupportSettlement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedPublications
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedStreamRelease

/-! Actual contributor-ref support through every matched source batch. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Exact task provenance supplies the handler premises, not a new host-source law
-----------------------------------------------------------------------------------------

/-- A matching host event preserves structural support for contents and active roots.
Witness: registered tasks identify failed-task owners, while source matching identifies
new task owners revealed by successful settlements and stream items.
-/
theorem State.GroupRefSupport.handleGraphEvent_support {queue : State}
    {work : Execution.Work}
    (valid
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (_registered : queue.StartedTasksRegistered)
    (_tasks : queue.RegisteredTasksMatch work) (event : GraphEvent)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies)
      ∧ (∀ output ∈ (queue.handleGraphEvent event available).2.1,
          output.GroupClosureRefSupported
            (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
      ∧ ∀ failure ∈ (queue.handleGraphEvent event available).2.2,
          ∃ dependencies,
            NodeHasDependencies work failure.group.ref .group dependencies := by
  have cached := valid.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result =>
      apply cached.taskSuccess_support occurrence result (available := available)
      intro task member group owner
      obtain ⟨address, payload, occurrenceEq, located⟩ := matching.childTask_producer member
      have known : TaskMatches work task :=
        ⟨⟨address, payload, some occurrence, occurrenceEq, located⟩,
          matching.childTask_groupsExact member⟩
      exact known.contributorKnown (List.mem_map.mpr ⟨group, owner, rfl⟩)
  | taskFailure occurrence errors =>
      obtain ⟨next, outputs⟩ := cached.taskFailure_support_all occurrence errors
      exact ⟨next, outputs, by simp [State.handleGraphEvent]⟩
  | streamItems stream items =>
      apply cached.streamItems_support stream items (available := available)
      intro item member task taskMember group owner
      obtain ⟨address, payload, occurrenceEq, located⟩ :=
        matching.streamItem_childTask_producer member taskMember
      have known : TaskMatches work task :=
        ⟨⟨address, payload, some item.occurrence, occurrenceEq, located⟩,
          matching.streamItem_childTask_groupsExact member taskMember⟩
      exact known.contributorKnown (List.mem_map.mpr ⟨group, owner, rfl⟩)
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact ⟨⟨cached.contents, cached.roots⟩,
        by simp [WorkQueueEvent.GroupClosureRefSupported], by simp⟩
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact ⟨⟨cached.contents, cached.roots⟩,
        by simp [WorkQueueEvent.GroupClosureRefSupported], by simp⟩

  | groupFailure failure =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · exact ⟨⟨cached.contents, cached.roots⟩, by simp, by simp⟩
      · split
        · rename_i head rest headEq accepted
          refine ⟨⟨cached.contents, cached.roots⟩, ?_, by simp⟩
          intro output member
          obtain rfl := List.mem_singleton.mp member
          obtain ⟨dependencies, producer, known⟩ := matching.1
          exact ⟨dependencies, failure.group, producer, known,
            (beq_iff_eq.mp (Bool.and_eq_true_iff.mp accepted).1).symm⟩
        · exact ⟨⟨cached.contents, cached.roots⟩, by simp, by simp⟩

/-- Matching graph events preserve the state support invariant.
Witness: project the joint state/output support theorem.
-/
theorem State.GroupRefSupport.handleGraphEvent {queue : State} {work : Execution.Work}
    (valid
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (registered : queue.StartedTasksRegistered) (tasks : queue.RegisteredTasksMatch work)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies) :=
  (valid.handleGraphEvent_support registered tasks event matching available).1

/-- The induction packages actual task provenance alongside contributor-ref support.
It is proof evidence for the concrete state, not additional implementation state.
-/
private structure ReplaySupport (work : Execution.Work) (queue : State) : Prop where
  groups
    : queue.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies)
  registered : queue.StartedTasksRegistered
  tasks : queue.RegisteredTasksMatch work

/-- One matching event preserves all three replay facts.
Witness: combine independent task-registry preservation with the support handler theorem.
-/
private theorem ReplaySupport.handleGraphEvent {queue work}
    (known : ReplaySupport work queue) (event : GraphEvent)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat))
    : ReplaySupport work (queue.handleGraphEvent event available).1
      ∧ (∀ output ∈ (queue.handleGraphEvent event available).2.1,
          output.GroupClosureRefSupported
            (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
      ∧ ∀ failure ∈ (queue.handleGraphEvent event available).2.2,
          ∃ dependencies,
            NodeHasDependencies work failure.group.ref .group dependencies :=
  let next :=
    known.groups.handleGraphEvent_support known.registered known.tasks event matching
      available
  ⟨
    ⟨
      next.1,
      known.registered.handleGraphEvent event available,
      known.tasks.handleGraphEvent event matching available
    ⟩,
    next.2.1,
    next.2.2
  ⟩

/-- Dispatch realizes startup effects and retains state and closure-ref support. -/
private theorem ReplaySupport.dispatchGraphEvent {queue work}
    (known : ReplaySupport work queue) (event : GraphEvent)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat))
    : ReplaySupport work (queue.dispatchGraphEvent event available).1
      ∧ (∀ output ∈ (queue.dispatchGraphEvent event available).2,
          output.GroupClosureRefSupported
            (fun ref =>
              ∃ dependencies, NodeHasDependencies work ref .group dependencies)) := by
  have next := known.handleGraphEvent event matching available
  exact ⟨⟨⟨next.1.groups.contents, next.1.groups.roots⟩,
    next.1.registered, next.1.tasks⟩, next.2.1⟩

/-- The complete FIFO fold retains every emitted closure's contributor support. -/
private theorem ReplaySupport.rawEventReplay {queue work}
    (known : ReplaySupport work queue) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    : ReplaySupport work (queue.rawEventReplay events available).1
      ∧ (∀ output ∈ (queue.rawEventReplay events available).2,
          output.GroupClosureRefSupported
            (fun ref =>
              ∃ dependencies, NodeHasDependencies work ref .group dependencies)) := by
  induction events generalizing queue with
  | nil => exact ⟨known, by simp [State.rawEventReplay]⟩
  | cons event rest ih =>
      have next := known.dispatchGraphEvent event (matching event List.mem_cons_self) available
      have later := ih next.1 (fun _ member => matching _ (List.mem_cons_of_mem _ member))
      rw [State.rawEventReplay_cons queue event rest available]
      refine ⟨later.1, ?_⟩
      intro output member
      exact (List.mem_append.mp member).elim (next.2 output) (later.2 output)

/-- Actual batching preserves supported closures at their FIFO positions. -/
private theorem ReplaySupport.handleGraphEvents {queue work}
    (known : ReplaySupport work queue) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : ReplaySupport work (queue.handleGraphEvents events).1
      ∧ ∀ output ∈ (queue.handleGraphEvents events).2,
          output.GroupClosureRefSupported
            (fun ref =>
              ∃ dependencies, NodeHasDependencies work ref .group dependencies) := by
  obtain ⟨next, outputs⟩ := known.rawEventReplay events matching (GraphEvent.availableFailures events)
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact ⟨known, by simp⟩
  · dsimp only
    split
    · refine ⟨⟨⟨next.groups.contents, next.groups.roots⟩, next.registered, next.tasks⟩, ?_⟩
      intro output member
      rcases List.mem_append.mp member with old | terminal
      · exact outputs output old
      · have same := List.mem_singleton.mp terminal
        subst output
        trivial
    · exact ⟨next, outputs⟩

-----------------------------------------------------------------------------------------
-- Publisher normalization preserves the exact closing ref
-----------------------------------------------------------------------------------------

/-- A raw host batch preserves contributor support and closes only supported refs.
This generic projection exposes the existing joint replay proof for any initial state.
-/
theorem State.GroupRefSupport.handleGraphEvents_support {queue : State}
    {work : Execution.Work}
    (known
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (registered : queue.StartedTasksRegistered) (tasks : queue.RegisteredTasksMatch work)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : (queue.handleGraphEvents events).1.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies)
      ∧ ∀ event ∈ (queue.handleGraphEvents events).2,
          event.GroupClosureRefSupported
            (fun ref =>
              ∃ dependencies, NodeHasDependencies work ref .group dependencies) := by
  have frame : ReplaySupport work queue := ⟨known, registered, tasks⟩
  have next := frame.handleGraphEvents events matching
  exact ⟨next.1.groups, next.2⟩

/-- Normalized group closures name supported refs; other events impose no condition.
The exact descriptor bridge is intentionally separate from contributor-ref existence.
-/
def GroupClosureRefSupported (supported : Nat → Prop) : Execution.WorkQueueEvent → Prop
  | .groupSuccess group _ _ | .groupFailure group _ => supported group.ref
  | _ => True

/-- Publication normalization does not change any closing group's ref.
Witness: publisher case analysis followed by induction over its actual event fold.
-/
theorem IncrementalPublisher.normalizeBatch_groupClosureRefSupport {supported events}
    (publisher : IncrementalPublisher)
    (known : ∀ event ∈ events, event.GroupClosureRefSupported supported)
    : ∀ output ∈ (publisher.normalizeBatch events).2,
        GroupClosureRefSupported supported output := by
  have one (current : IncrementalPublisher) (event : WorkQueueEvent)
      (valid : event.GroupClosureRefSupported supported)
      : ∀ output ∈ (current.handleWorkQueueEvent event).2,
          GroupClosureRefSupported supported output := by
    cases event <;> simp_all [IncrementalPublisher.handleWorkQueueEvent,
      GroupClosureRefSupported, WorkQueueEvent.GroupClosureRefSupported]
  induction events generalizing publisher with
  | nil => simp [IncrementalPublisher.normalizeBatch]
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      intro output member
      exact (List.mem_append.mp member).elim
        (one publisher event (known event List.mem_cons_self) output)
        (ih _ (fun next within => known next (List.mem_cons_of_mem _ within)) output)

/-- Every populated or active group ref after normalized replay has an actual contributor.
Witness: joint replay induction from the pruning-based initialization theorem. Fixed source
matching suffices; no output-admission, generated-work, or start-discipline law is assumed.
-/
theorem createWorkQueue_runNormalized_groupSupport {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies)
      ∧ ∀ event ∈
          ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten,
          GroupClosureRefSupported
            (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies)
            event := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (known : ReplaySupport work acc.1)
      (outputs : ∀ event ∈ acc.2.2.flatten, GroupClosureRefSupported
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies) event)
      (matching : ∀ batch ∈ more, ∀ event ∈ batch, event.MatchesWork work)
      : ReplaySupport work (more.foldl normalizedStep acc).1
        ∧ ∀ event ∈ (more.foldl normalizedStep acc).2.2.flatten, GroupClosureRefSupported
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies)
          event := by
    induction more generalizing acc with
    | nil => exact ⟨known, outputs⟩
    | cons batch rest ih =>
        rw [List.foldl_cons]
        obtain ⟨next, raw⟩ := known.handleGraphEvents batch (matching batch List.mem_cons_self)
        apply ih
        · rw [normalizedStep_queue]
          exact next
        · have emitted := acc.2.1.normalizeBatch_groupClosureRefSupport raw
          dsimp only [normalizedStep]
          split
          · exact outputs
          · intro event member
            simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
              List.append_nil, List.mem_append] at member
            exact member.elim (outputs event) (emitted event)
        · exact fun next member => matching next (List.mem_cons_of_mem _ member)
  obtain ⟨final, outputs⟩ := loop batches (_, _, [])
    ⟨createWorkQueue_fromSpec_groupRefSupport work,
      createWorkQueue_startedTasksRegistered (Work.fromExecution work),
      createWorkQueue_fromSpec_registeredTasksMatch work⟩ (by simp)
    (fun batch member event within =>
      valid.eachMatches (List.mem_flatten.mpr ⟨batch, member, within⟩))
  exact ⟨final.groups, outputs⟩

/-- Normalized replay retains contributor support for contents and all active roots.
Witness: project the joint state/output replay theorem.
-/
theorem createWorkQueue_runNormalized_groupRefSupport {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies) :=
  (createWorkQueue_runNormalized_groupSupport valid).1

/-- Every actual normalized group closure has a ref belonging to a structural contributor.
Witness: project output support from the same concrete replay invariant.
-/
theorem createWorkQueue_runNormalized_groupClosureRefs {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ∀ event ∈
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten,
        GroupClosureRefSupported
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies)
          event :=
  (createWorkQueue_runNormalized_groupSupport valid).2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
