import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailureOutput
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedTaskErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingReplay

/-! Failed group outputs select one positive contributing task cause. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A matching present rejected task supplies a positive cause for every stored owner. -/
theorem State.incomingFailureCause {queue : State} {work failed occurrence errors task}
    (generated : ExecutedWork work) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (found : queue.taskNode? occurrence = some task)
    (source : (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : ∀ group ∈ task.task.groups,
        NodeFailureCause work (occurrence :: failed) group.ref errors := by
  have taskMember := registered task (List.mem_of_find?_eq_some found)
  obtain ⟨⟨_, _, _, _, descriptor⟩, _⟩ := matching task.task taskMember
  rw [(State.taskNode?_some found).2] at descriptor
  obtain ⟨owners, producer, path, known⟩ := source
  intro group member
  refine ⟨
    occurrence,
    by simp,
    owners,
    producer,
    .object path (.error errors),
    known,
    (descriptor.unique known).1 ▸ List.mem_map.mpr ⟨group, member, rfl⟩,
    rfl,
    ?_
  ⟩
  exact generated.taskFailure_positive known rfl

/-- One handler preserves causes against its actual presence-filtered failure inventory.
Witness: successful handlers preserve retained causes; rejection stores the new cause and
closes active owners without aggregating it with earlier rejections.
-/
theorem State.CachedErrorsSatisfy.handleGraphEvent_causes {queue : State} {work failed}
    (causes : queue.CachedErrorsSatisfy (NodeFailureCause work failed))
    (generated : ExecutedWork work) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (event : GraphEvent)
    (source : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.CachedErrorsSatisfy
        (NodeFailureCause work (queue.objectFailureContribution event ++ failed)) := by
  cases event with
  | taskSuccess occurrence result => exact causes.taskSuccess occurrence result
  | taskFailure occurrence errors =>
      cases found : queue.taskNode? occurrence with
      | none => simpa [State.handleGraphEvent, State.taskFailure, found,
          State.objectFailureContribution] using causes
      | some task =>
          simp only [State.objectFailureContribution, found, List.singleton_append]
          apply (causes.mono
                  (fun _ _ cause =>
                    cause.mono
                      (by
                        intro other member; exact List.mem_cons_of_mem _
                          member))).taskFailure
            occurrence errors
          intro node lookup
          have same := Option.some.inj (lookup.symm.trans found)
          subst node
          exact State.incomingFailureCause generated registered matching found source
  | streamItems stream items => exact causes.streamItems stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess, State.objectFailureContribution,
        List.nil_append]
      split <;> exact causes
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure, State.objectFailureContribution,
        List.nil_append]
      split <;> exact causes

/-- Every raw failed group output copies either the incoming task rejection or a retained
positive task cause. No group error total, clear-cache premise, or healthy-owner guard is
needed to identify its count.
-/
theorem State.CachedErrorsSatisfy.handleGraphEvent_failureCause {queue : State}
    {work failed} (causes : queue.CachedErrorsSatisfy (NodeFailureCause work failed))
    (generated : ExecutedWork work) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (event : GraphEvent)
    (source : event.MatchesWork work) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (queue.handleGraphEvent event).2)
    : NodeFailureCause work (queue.objectFailureContribution event ++ failed) group.ref
        errors := by
  cases event with
  | taskSuccess occurrence result =>
      exact causes.taskSuccess_output occurrence result emitted
  | taskFailure occurrence count =>
      obtain ⟨task, found, owner, rfl⟩ :=
        queue.taskFailure_groupFailure_current occurrence count emitted
      obtain ⟨contributor, member, same⟩ := List.mem_map.mp owner
      have cause := State.incomingFailureCause (failed := failed) generated registered matching
        found source contributor member
      simpa only [State.objectFailureContribution, found, List.singleton_append, same] using cause
  | streamItems stream items => exact causes.streamItems_output stream items emitted
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess] at emitted
      split at emitted <;> simp at emitted
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure] at emitted
      split at emitted <;> simp at emitted

/-- Sequential handlers retain selected causes from the same presence-filtered inventory. -/
theorem State.CachedErrorsSatisfy.replayGraphEvents_causes {queue : State}
    {work failed before}
    (causes : queue.CachedErrorsSatisfy (NodeFailureCause work failed))
    (generated : ExecutedWork work) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    : (queue.replayGraphEvents events).CachedErrorsSatisfy
        (NodeFailureCause work (queue.objectFailureContributions events ++ failed)) := by
  induction events generalizing queue before failed with
  | nil => simpa [State.replayGraphEvents, State.objectFailureContributions] using causes
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp [List.append_assoc]⟩
      obtain ⟨_, source, _⟩ := validGraphEvents_last (valid.prefix earlier)
      have next := causes.handleGraphEvent_causes generated registered matching event source
      have result := ih (before := before ++ [event]) next (registered.handleGraphEvent event)
        (matching.handleGraphEvent event source) (by simpa [List.append_assoc] using valid)
      simpa only [State.replayGraphEvents, State.objectFailureContributions,
        List.foldl_cons, List.append_assoc]
        using result

/-- Batch termination changes no retained computation or selected cause. -/
theorem State.CachedErrorsSatisfy.handleGraphEvents_causes {queue : State}
    {work failed before}
    (causes : queue.CachedErrorsSatisfy (NodeFailureCause work failed))
    (generated : ExecutedWork work) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false)
    : (queue.handleGraphEvents events).1.CachedErrorsSatisfy
        (NodeFailureCause work (queue.objectFailureContributions events ++ failed)) := by
  have replayed := causes.replayGraphEvents_causes generated registered matching events valid
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact replayed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
