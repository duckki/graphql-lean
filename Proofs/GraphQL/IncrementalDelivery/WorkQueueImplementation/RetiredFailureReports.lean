import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailureReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedErrorAccumulation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedFailureReports
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeRegistrationHistory

/-! Retired error caches yield actual positive completion reports on the common witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A live contributor of an accepted task failure retains a cache or cancellation marker.
Witness: uncancelled cleanup retains the ref; exact contributor accumulation installs
`some` errors on each surviving contributor. This does not assume a report yet.
-/
theorem State.taskFailure_contributorRetained {queue : State} {occurrence errors task ref}
    (found : queue.taskNode? occurrence = some task)
    (distinct : (task.task.groups.map Execution.DeliveryNode.ref).Nodup)
    (accepted : queue.taskHasHealthyOwner task.task = true)
    (contributes : ref ∈ task.task.groups.map Execution.DeliveryNode.ref)
    (live : ∃ node, queue.groupNode? ref = some node)
    : (queue.taskFailure occurrence errors).1.FailureRetained ref := by
  classical
  by_cases cancelled : ref ∈ (queue.taskFailure occurrence errors).1.cancelledGroups
  · exact .inl cancelled
  · obtain ⟨owner, ownerFound⟩ := live
    have present : ref ∈ queue.groupNodes.map (fun node => node.group.node.ref) :=
      List.mem_map.mpr ⟨owner, List.mem_of_find?_eq_some ownerFound,
        State.groupNode?_ref ownerFound⟩
    obtain ⟨node, member, same⟩ := List.mem_map.mp
      (queue.taskFailure_uncancelled_present occurrence errors present cancelled)
    obtain ⟨old, _, _, count⟩ := queue.taskFailure_cachedErrors occurrence errors task
      found distinct member
    exact .inr ⟨node, member, same, by simp [count, accepted, same, contributes]⟩

/-- A retained failure with no final live record has a concrete cancellation marker.
Witness: unique refs reflect the live-cache alternative into the forbidden lookup.
-/
theorem State.FailureRetained.cancelled_of_absent {queue : State} {ref}
    (retained : queue.FailureRetained ref) (unique : queue.GroupRefsUnique)
    (absent : queue.groupNode? ref = none)
    : ref ∈ queue.cancelledGroups := by
  rcases retained with cancelled | ⟨node, member, same, cached⟩
  · exact cancelled
  · have found := unique.groupNode?_of_mem member
    rw [same, absent] at found
    contradiction

namespace ConformancePlan

/-- A concretely retained failure on an absent final contributor covers its object task.
Witness: absence forces a permanent marker, and normalized replay supplies its positive
same-group or ancestor report on the existing publication matching and failure cuts.
This uses no terminal reporting law.
-/
theorem retainedContributor_task_reported {work inputs address owners producer payload}
    {w : Witness} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    {group dependencies birth} (record : NodeAt work group .group dependencies birth)
    (contributes : group.ref ∈ owners)
    (retained : ((initialQueue work).runNormalized inputs).1.FailureRetained group.ref)
    (absent : ((initialQueue work).runNormalized inputs).1.groupNode? group.ref = none)
    : FailureReportedFor w.events payload.path := by
  exact cancelledContributor_task_reported generated valid started history explained known
    record contributes (retained.cancelled_of_absent
      (createWorkQueue_runNormalized_groupRefsUnique _ inputs) absent)

/-- A cached failure at an earlier replay boundary covers the task once its ref retires.
Witness: cache-or-marker persistence through the exact raw continuation, followed by
the unchanged normalized state projection and concrete positive-report provenance.
The prefix is an actual source prefix, not an assumed semantic cancellation cut.
-/
theorem priorCachedContributor_task_reported
    {work inputs before after address owners producer payload} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    {group dependencies birth} (record : NodeAt work group .group dependencies birth)
    (contributes : group.ref ∈ owners) (splitInputs : inputs.flatten = before ++ after)
    (retained : ((initialQueue work).rawEventReplay before).1.FailureRetained group.ref)
    (absent : ((initialQueue work).runNormalized inputs).1.groupNode? group.ref = none)
    : FailureReportedFor w.events payload.path := by
  have continued := retained.rawEventReplay
    (by
      rw [State.rawEventReplay_state]
      exact State.GroupRefsUnique.replayGraphEvents (createWorkQueue_groupRefsUnique _) before)
    after
  have full : ((initialQueue work).rawEventReplay inputs.flatten).1.FailureRetained
      group.ref := by
    rw [splitInputs, State.rawEventReplay_append]
    exact continued
  rw [State.rawEventReplay_state] at full
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
  have final : ((initialQueue work).runNormalized inputs).1.FailureRetained group.ref := by
    rw [same]
    exact full
  exact retainedContributor_task_reported generated valid started history explained known
    record contributes final absent

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
