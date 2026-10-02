import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupSupportSettlement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedPublications
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedStreamRelease

/-! Actual contributor-key support through every matched source batch. -/

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
theorem State.GroupKeySupport.handleGraphEvent_support {queue : State}
    {work : Execution.Work}
    (valid
      : queue.GroupKeySupport
          (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies))
    (registered : queue.StartedTasksRegistered) (tasks : queue.RegisteredTasksMatch work)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.GroupKeySupport
        (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies)
      ∧ ∀ output ∈ (queue.handleGraphEvent event).2,
          output.GroupClosureKeySupported
            (fun key =>
              ∃ dependencies, NodeHasDependencies work key .group dependencies) := by
  cases event with
  | taskSuccess occurrence result =>
      apply valid.taskSuccess_support occurrence result
      intro task member group owner
      obtain ⟨address, payload, occurrenceEq, located⟩ := matching.childTask_producer member
      have known : TaskMatches work task :=
        ⟨⟨address, payload, some occurrence, occurrenceEq, located⟩,
          matching.childTask_groupsExact member⟩
      exact known.contributorKnown (List.mem_map.mpr ⟨group, owner, rfl⟩)
  | taskFailure occurrence errors =>
      apply valid.taskFailure_support occurrence errors
      intro node found group owner
      have known := tasks node.task (registered node (List.mem_of_find?_eq_some found))
      exact known.contributorKnown (List.mem_map.mpr ⟨group, owner, rfl⟩)
  | streamItems stream items =>
      apply valid.streamItems_support stream items
      intro item member task taskMember group owner
      obtain ⟨address, payload, occurrenceEq, located⟩ :=
        matching.streamItem_childTask_producer member taskMember
      have known : TaskMatches work task :=
        ⟨⟨address, payload, some item.occurrence, occurrenceEq, located⟩,
          matching.streamItem_childTask_groupsExact member taskMember⟩
      exact known.contributorKnown (List.mem_map.mpr ⟨group, owner, rfl⟩)
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact ⟨⟨valid.contents, valid.roots⟩,
        by simp [WorkQueueEvent.GroupClosureKeySupported]⟩
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact ⟨⟨valid.contents, valid.roots⟩,
        by simp [WorkQueueEvent.GroupClosureKeySupported]⟩

/-- Matching graph events preserve the state support invariant.
Witness: project the joint state/output support theorem.
-/
theorem State.GroupKeySupport.handleGraphEvent {queue : State} {work : Execution.Work}
    (valid
      : queue.GroupKeySupport
          (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies))
    (registered : queue.StartedTasksRegistered) (tasks : queue.RegisteredTasksMatch work)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.GroupKeySupport
        (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies) :=
  (valid.handleGraphEvent_support registered tasks event matching).1

/-- The induction packages actual task provenance alongside contributor-key support.
It is proof evidence for the concrete state, not additional implementation state.
-/
private structure ReplaySupport (work : Execution.Work) (queue : State) : Prop where
  groups
    : queue.GroupKeySupport
        (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies)
  registered : queue.StartedTasksRegistered
  tasks : queue.RegisteredTasksMatch work

/-- One matching event preserves all three replay facts.
Witness: combine independent task-registry preservation with the support handler theorem.
-/
private theorem ReplaySupport.handleGraphEvent {queue work}
    (known : ReplaySupport work queue) (event : GraphEvent)
    (matching : event.MatchesWork work)
    : ReplaySupport work (queue.handleGraphEvent event).1
      ∧ ∀ output ∈ (queue.handleGraphEvent event).2,
          output.GroupClosureKeySupported
            (fun key =>
              ∃ dependencies, NodeHasDependencies work key .group dependencies) :=
  let next :=
    known.groups.handleGraphEvent_support known.registered known.tasks event matching
  ⟨
    ⟨
      next.1,
      known.registered.handleGraphEvent event,
      known.tasks.handleGraphEvent event matching
    ⟩,
    next.2
  ⟩

/-- Eventwise replay preserves contributor support before and after every settlement.
Witness: induction on the actual source-event sequence, retaining both task registries.
-/
private theorem ReplaySupport.rawEventReplay {queue work}
    (known : ReplaySupport work queue) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : ReplaySupport work (queue.rawEventReplay events).1
      ∧ ∀ output ∈ (queue.rawEventReplay events).2,
          output.GroupClosureKeySupported
            (fun key =>
              ∃ dependencies, NodeHasDependencies work key .group dependencies) := by
  induction events generalizing queue with
  | nil => exact ⟨known, by simp [State.rawEventReplay]⟩
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      obtain ⟨next, outputs⟩ := known.handleGraphEvent event (matching event List.mem_cons_self)
      obtain ⟨final, later⟩ := ih next
        (fun next member => matching next (List.mem_cons_of_mem _ member))
      exact ⟨final, fun output member =>
        (List.mem_append.mp member).elim (outputs output) (later output)⟩

/-- Host batching and setting the terminal flag do not change group-key support.
Witness: eventwise replay supplies the actual post-batch queue; only termination changes.
-/
private theorem ReplaySupport.handleGraphEvents {queue work}
    (known : ReplaySupport work queue) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : ReplaySupport work (queue.handleGraphEvents events).1
      ∧ ∀ output ∈ (queue.handleGraphEvents events).2,
          output.GroupClosureKeySupported
            (fun key =>
              ∃ dependencies, NodeHasDependencies work key .group dependencies) := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact ⟨known, by simp⟩
  · obtain ⟨next, outputs⟩ := known.rawEventReplay events matching
    dsimp only
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
-- Publisher normalization preserves the exact closing key
-----------------------------------------------------------------------------------------

/-- Normalized group closures name supported keys; other events impose no condition.
The exact descriptor bridge is intentionally separate from contributor-key existence.
-/
def GroupClosureKeySupported (supported : Nat → Prop) : Execution.WorkQueueEvent → Prop
  | .groupSuccess group _ _ | .groupFailure group _ => supported group.key
  | _ => True

/-- Publication normalization does not change any closing group's key.
Witness: publisher case analysis followed by induction over its actual event fold.
-/
theorem IncrementalPublisher.normalizeBatch_groupClosureKeySupport {supported events}
    (publisher : IncrementalPublisher)
    (known : ∀ event ∈ events, event.GroupClosureKeySupported supported)
    : ∀ output ∈ (publisher.normalizeBatch events).2,
        GroupClosureKeySupported supported output := by
  have one (current : IncrementalPublisher) (event : WorkQueueEvent)
      (valid : event.GroupClosureKeySupported supported)
      : ∀ output ∈ (current.handleWorkQueueEvent event).2,
          GroupClosureKeySupported supported output := by
    cases event <;> simp_all [IncrementalPublisher.handleWorkQueueEvent,
      GroupClosureKeySupported, WorkQueueEvent.GroupClosureKeySupported]
  induction events generalizing publisher with
  | nil => simp [IncrementalPublisher.normalizeBatch]
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      intro output member
      exact (List.mem_append.mp member).elim
        (one publisher event (known event List.mem_cons_self) output)
        (ih _ (fun next within => known next (List.mem_cons_of_mem _ within)) output)

/-- Every populated or active group key after normalized replay has an actual contributor.
Witness: joint replay induction from the pruning-based initialization theorem. Fixed source
matching suffices; no output-admission, generated-work, or start-discipline law is assumed.
-/
theorem createWorkQueue_runNormalized_groupSupport {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.GroupKeySupport
        (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies)
      ∧ ∀ event ∈
          ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten,
          GroupClosureKeySupported
            (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies)
            event := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (known : ReplaySupport work acc.1)
      (outputs : ∀ event ∈ acc.2.2.flatten, GroupClosureKeySupported
        (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies) event)
      (matching : ∀ batch ∈ more, ∀ event ∈ batch, event.MatchesWork work)
      : ReplaySupport work (more.foldl normalizedStep acc).1
        ∧ ∀ event ∈ (more.foldl normalizedStep acc).2.2.flatten, GroupClosureKeySupported
          (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies)
          event := by
    induction more generalizing acc with
    | nil => exact ⟨known, outputs⟩
    | cons batch rest ih =>
        rw [List.foldl_cons]
        obtain ⟨next, raw⟩ := known.handleGraphEvents batch (matching batch List.mem_cons_self)
        apply ih
        · rw [normalizedStep_queue]
          exact next
        · have emitted := acc.2.1.normalizeBatch_groupClosureKeySupport raw
          dsimp only [normalizedStep]
          split
          · exact outputs
          · intro event member
            simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
              List.append_nil, List.mem_append] at member
            exact member.elim (outputs event) (emitted event)
        · exact fun next member => matching next (List.mem_cons_of_mem _ member)
  obtain ⟨final, outputs⟩ := loop batches (_, _, [])
    ⟨createWorkQueue_fromSpec_groupKeySupport work,
      createWorkQueue_startedTasksRegistered (Work.fromExecution work),
      createWorkQueue_fromSpec_registeredTasksMatch work⟩ (by simp)
    (fun batch member event within =>
      valid.eachMatches (List.mem_flatten.mpr ⟨batch, member, within⟩))
  exact ⟨final.groups, outputs⟩

/-- Normalized replay retains contributor support for contents and all active roots.
Witness: project the joint state/output replay theorem.
-/
theorem createWorkQueue_runNormalized_groupKeySupport {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.GroupKeySupport
        (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies) :=
  (createWorkQueue_runNormalized_groupSupport valid).1

/-- Every actual normalized group closure has a key belonging to a structural contributor.
Witness: project output support from the same concrete replay invariant.
-/
theorem createWorkQueue_runNormalized_groupClosureKeys {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ∀ event ∈
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten,
        GroupClosureKeySupported
          (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies)
          event :=
  (createWorkQueue_runNormalized_groupSupport valid).2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
