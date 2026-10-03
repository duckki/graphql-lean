import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRemoval

/-! Initial-frontier health under the actual accepted object-failure inventory. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- This proof-side event class closes tasks or streams without releasing new work.
It includes task failures, so its cleanup proof is independent of failure-free replay.
-/
def GraphEvent.OnlyCloses : GraphEvent → Prop
  | .taskFailure .. | .streamSuccess .. | .streamFailure .. => True
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
      have later := ih next (fun event member => closes event (by simp [member]))
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

/-- Normalized closing-only replay preserves health with the same accepted inventory.
Witness: source matching instantiates eventwise health; start discipline transports the
state through batch termination and publisher normalization without changing roots. -/
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
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          batches.flatten) := by
  have healthy := createWorkQueue_replayRootsHealthy_closingContributions generated
    initialized batches.flatten (fun _ member => valid.eachMatches member) closes
  rw [inputsStarted_eq_batchesStarted] at started
  obtain ⟨terminal, same⟩ := State.runNormalized_stateCore _ batches started
  rw [same]
  exact healthy

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
