import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CacheEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveRejectionReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.LiveRootReplay

/-! Initial-frontier health under the actual accepted object-failure inventory. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- This proof-side event class closes tasks or streams without releasing new work.
It includes task failures, so its cleanup proof is independent of failure-free replay.
-/
def GraphEvent.OnlyCloses : GraphEvent → Prop
  | .taskFailure .. | .groupFailure .. | .streamSuccess .. | .streamFailure .. => True
  | .taskSuccess .. | .streamItems .. => False

-----------------------------------------------------------------------------------------
-- Accepted failures preserve the initially protected frontier
-----------------------------------------------------------------------------------------

/-- Concrete replay evidence for roots that remain within the initial frontier.
`failed` contains accepted contributions, not every failure reported by the host. -/
private structure ClosingFrontier (queue : State) (work : Execution.Work)
    (groups : List Execution.DeliveryNode) (failed : List Occurrence)
    : Prop where
  healthy : queue.RootGroupsHealthy work failed
  frontier : queue.rootGroups.Subset (groups.map Execution.DeliveryNode.ref)
  present : queue.RootGroupsPresent
  registered : queue.StartedTasksRegistered
  matching : queue.RegisteredTasksMatch work

/-- Closing inputs preserve root health and the fixed initial frontier.
Witness: use the real healthy-owner guard for failures; stream closure leaves groups
unchanged. Missing or ignored inputs do not invent accepted failure tokens. -/
private theorem ClosingFrontier.handleGraphEvent
    {queue : State} {work groups streams failed}
    (frontier : ClosingFrontier queue work groups failed)
    (generated : ExecutedWork work) (initialized : Initializes work groups streams)
    {event : GraphEvent} (closes : event.OnlyCloses)
    (matching : event.MatchesWork work)
    : ClosingFrontier (queue.handleGraphEvent event).1 work groups
        (queue.objectFailureContribution event ++ failed) := by
  cases event with
  | taskSuccess occurrence result => cases closes
  | streamItems stream items => cases closes
  | taskFailure occurrence errors =>
      exact {
        healthy := frontier.healthy.taskFailure_initialFrontier_contributions generated
          initialized frontier.frontier frontier.present frontier.registered
          frontier.matching occurrence errors
        frontier := (queue.taskFailure_rootsSubset occurrence errors).trans frontier.frontier
        present := frontier.present.taskFailure occurrence errors
        registered := frontier.registered.handleGraphEvent (.taskFailure occurrence errors)
        matching := frontier.matching.handleGraphEvent (.taskFailure occurrence errors) matching
      }
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess, State.objectFailureContribution,
        List.nil_append]
      split <;> exact ⟨frontier.healthy, frontier.frontier, frontier.present,
        frontier.registered, frontier.matching⟩
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure, State.objectFailureContribution,
        List.nil_append]
      split <;> exact ⟨frontier.healthy, frontier.frontier, frontier.present,
        frontier.registered, frontier.matching⟩
  | groupFailure failure =>
      simp only [State.handleGraphEvent, State.groupFailure, State.objectFailureContribution,
        List.nil_append]
      split
      · exact frontier
      · split <;> exact ⟨frontier.healthy, frontier.frontier, frontier.present,
          frontier.registered, frontier.matching⟩

/-- Successive closing inputs preserve health under their accepted contributions.
Witness: handler induction threads both the real state and reverse failure inventory;
no assumption that each supplied failure is accepted is used. -/
private theorem ClosingFrontier.replayGraphEvents
    {queue : State} {work groups streams failed}
    (frontier : ClosingFrontier queue work groups failed)
    (generated : ExecutedWork work) (initialized : Initializes work groups streams)
    (events : List GraphEvent) (closes : ∀ event ∈ events, event.OnlyCloses)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : ClosingFrontier (queue.replayGraphEvents events) work groups
        (queue.objectFailureContributions events ++ failed) := by
  induction events generalizing queue failed with
  | nil =>
      simpa [State.replayGraphEvents, State.objectFailureContributions] using frontier
  | cons event rest ih =>
      have next := frontier.handleGraphEvent generated initialized (closes event (by simp))
        (matching event (by simp))
      have dispatched : ClosingFrontier (queue.dispatchGraphEvent event).1 work groups
          (queue.objectFailureContribution event ++ failed) :=
        ⟨next.healthy, next.frontier, next.present, next.registered, next.matching⟩
      have later := ih dispatched (fun event member => closes event (by simp [member]))
        (fun event member => matching event (by simp [member]))
      simpa only [State.replayGraphEvents, List.foldl_cons,
        State.objectFailureContributions, List.append_assoc]
        using later

/-- Queue initialization supplies healthy roots, live records, and task provenance.
Witness: the independent initialization invariants and the exact initial root equation. -/
private theorem createWorkQueue_closingFrontier (work : Execution.Work)
    : ClosingFrontier (State.initialize (Work.fromExecution work)) work
        (State.initialize (Work.fromExecution work)).initialGroups [] := by
  exact {
    healthy := createWorkQueue_rootGroupsHealthy work
    frontier := by rw [createWorkQueue_rootGroups]; exact List.Subset.refl _
    present := createWorkQueue_rootGroupsPresent (Work.fromExecution work)
    registered := createWorkQueue_startedTasksRegistered (Work.fromExecution work)
    matching := createWorkQueue_fromSpec_registeredTasksMatch work
  }

-----------------------------------------------------------------------------------------
-- Actual event prefixes and normalized batches
-----------------------------------------------------------------------------------------

/-- Every matching closing-only replay has healthy remaining initial roots.
Witness: the frontier induction uses the actual accepted contributions. Even eventwise
start discipline is unnecessary for this local state invariant. -/
theorem createWorkQueue_replayRootsHealthy_closingContributions
    {work : Execution.Work} (generated : ExecutedWork work)
    (initialized
      : Initializes work (State.initialize (Work.fromExecution work)).initialGroups
          (State.initialize (Work.fromExecution work)).initialStreams)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (closes : ∀ event ∈ events, event.OnlyCloses)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).RootGroupsHealthy
        work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          events) := by
  have final := (createWorkQueue_closingFrontier work).replayGraphEvents generated
    initialized events closes matching
  simpa only [List.append_nil] using final.healthy

private theorem closing_replay_roots_subset (queue : State) (events : List GraphEvent)
    (available : List (Occurrence × Nat)) (closes : ∀ event ∈ events, event.OnlyCloses)
    : (queue.replayGraphEvents events available).rootGroups.Subset queue.rootGroups := by
  have one (current : State) (event : GraphEvent) (closes : event.OnlyCloses)
      : (current.dispatchGraphEvent event available).1.rootGroups.Subset current.rootGroups := by
    let cached := current.cacheTaskFailures available
    cases event with
    | taskSuccess | streamItems => cases closes
    | taskFailure occurrence errors =>
        simpa only [State.dispatchGraphEvent, State.enqueueGroupFailures,
          State.handleGraphEvent, cached, State.cacheTaskFailures_rootGroups]
          using cached.taskFailure_rootsSubset occurrence errors
    | streamSuccess stream =>
        intro ref member
        change ref ∈ (cached.streamSuccess stream).1.rootGroups at member
        unfold State.streamSuccess at member
        split at member <;> simpa only [cached, State.cacheTaskFailures_rootGroups] using member
    | streamFailure stream errors =>
        intro ref member
        change ref ∈ (cached.streamFailure stream errors).1.rootGroups at member
        unfold State.streamFailure at member
        split at member <;> simpa only [cached, State.cacheTaskFailures_rootGroups] using member
    | groupFailure failure =>
        intro ref member
        change ref ∈ (cached.groupFailure failure).1.rootGroups at member
        unfold State.groupFailure at member
        split at member
        · simpa only [cached, State.cacheTaskFailures_rootGroups] using member
        · split at member <;> simpa only [cached, State.cacheTaskFailures_rootGroups] using member
  induction events generalizing queue with
  | nil => exact List.Subset.refl _
  | cons event rest ih =>
      intro ref active
      exact one queue event (closes _ List.mem_cons_self)
        (ih _ (fun next member => closes next (List.mem_cons_of_mem _ member)) active)

private theorem closing_batches_roots_subset (queue : State)
    (batches : List (List GraphEvent))
    (closes : ∀ event ∈ batches.flatten, event.OnlyCloses)
    : (queue.replayBatches batches).rootGroups.Subset queue.rootGroups := by
  induction batches generalizing queue with
  | nil => exact List.Subset.refl _
  | cons batch rest ih =>
      intro ref active
      have later := ih (queue.handleGraphEvents batch).1
        (fun event member => closes event (List.mem_append_right _ member)) active
      cases running : queue.terminated with
      | true => simpa only [State.handleGraphEvents, running, ite_true] using later
      | false =>
          obtain ⟨terminal, core⟩ := queue.handleGraphEvents_stateCore batch running
          rw [core] at later
          exact closing_replay_roots_subset queue batch (GraphEvent.availableFailures batch)
            (fun event member => closes event (List.mem_append_left _ member)) later

/-- Normalized closing-only replay preserves health under all admitted source failures.
Witness: roots remain in the protected initial frontier; source failure retention and
active-cache exclusion rule out a direct failed contributor to a surviving root.
Initialization independently protects every represented defer dependency.
-/
theorem createWorkQueue_runNormalized_rootsHealthy_closingContributions
    {work : Execution.Work} (generated : ExecutedWork work)
    (initialized
      : Initializes work (State.initialize (Work.fromExecution work)).initialGroups
          (State.initialize (Work.fromExecution work)).initialStreams)
    (batches : List (List GraphEvent)) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (closes : ∀ event ∈ batches.flatten, event.OnlyCloses)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.RootGroupsHealthy
        work
        ((State.initialize
            (Work.fromExecution work)).admittedObjectFailureContributionsForBatches
          batches) := by
  let initial := State.initialize (Work.fromExecution work)
  let final := (initial.runNormalized batches).1
  have checked : initial.batchesStarted batches = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  rw [State.admittedObjectFailureContributionsForBatches_eq_of_started _ batches checked]
  have frontier : final.rootGroups.Subset
      (initial.initialGroups.map Execution.DeliveryNode.ref) := by
    intro ref active
    have root : ref ∈ initial.rootGroups := by
      apply closing_batches_roots_subset initial batches closes
      simpa only [final, State.runNormalized_replayBatches] using active
    simpa only [initial, createWorkQueue_rootGroups] using root
  have present : final.RootGroupsPresent := generated.runNormalized_rootsPresent batches
    (fun event member => valid.eachMatches member)
  have retained := generated.runNormalized_retainedFailures batches valid started
  have clean := createWorkQueue_runNormalized_noActiveCachedFailure generated batches valid started
  intro ref active invalid
  obtain ⟨node, member, same⟩ := List.mem_map.mp (frontier active)
  obtain ⟨dependencies, producer, known, protection⟩ :=
    Initializes.groupDependencies_uninvalidated initialized member
  have failure : GroupInvalidated work (GraphEvent.failureSettlements batches.flatten) node.ref :=
    same.symm ▸ invalid
  rcases generated.groupInvalidated_causes known failure with
    ⟨occurrence, owners, taskKnown, owner, recorded⟩
      | ⟨dependency, inDependencies, ancestorFailure⟩
  · obtain ⟨group, live, refEq⟩ := List.mem_map.mp (present ref active)
    have contributes : group.group.node.ref ∈ owners := by
      rw [refEq, ← same]
      exact owner
    obtain ⟨listed, task, lookup, rejected, rest⟩ :=
      retained.retained occurrence recorded owners taskKnown group live contributes
    have none := (State.rejectedTask?_eq_none_iff.mp
      (clean group live (refEq.symm ▸ active))) occurrence listed task lookup
    rw [none] at rejected
    cases rejected
  · exact protection (GraphEvent.failureSettlements batches.flatten) dependency
      inDependencies ancestorFailure

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
