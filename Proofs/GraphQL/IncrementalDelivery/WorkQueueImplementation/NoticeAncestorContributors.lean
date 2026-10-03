import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorHealthReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StructuralRetiredRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredContributorPublication

/-! Every structural contributor to a carried notice's ancestry has actually settled. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Structural removal and source-record health refer to the same actual handler
-----------------------------------------------------------------------------------------

/-- Each task-bearing ancestor of an actual carried group notice is concretely retired.
Witness: the matched-handler notice certificate applies to the child's full defer ancestry.
Silent pruning counts as retirement; no completion notice for the ancestor is required.
-/
theorem ExecutedWork.noticeAncestor_retired
    {work before event output child dependencies ref occurrence owners}
    (generated : ExecutedWork work)
    (matching : ∀ past ∈ before, past.MatchesWork work)
    (incoming : event.MatchesWork work)
    (emitted
      : output
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2)
    (noticed : child.ref ∈ rawGroupNoticeRefs output)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    (task : TaskHasOwners work occurrence owners) (contributes : ref ∈ owners)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        (before ++ [event])).RetiredGroup
        ref :=
  generated.replayGraphEvents_next_noticeAncestorsRetired matching incoming child.ref
    (List.mem_flatMap.mpr ⟨output, emitted, noticed⟩) child dependencies known rfl
    ref ancestor occurrence owners task contributes

-----------------------------------------------------------------------------------------
-- Recover all contributors, not merely memberships still present in the live queue
-----------------------------------------------------------------------------------------

/-- Every structural object contributor to a noticed group's ancestor has already succeeded.
Witness: actual notice retirement and independent ancestry health force permanent task
registration; the derived owner ledger excludes an unsettled contributor at that boundary.
The source event is recovered without assuming storage, registration, or output admission.
Publication before the particular internal carrier remains a separate obligation.
-/
theorem ExecutedWork.noticeAncestor_structuralContributor_succeeded
    {work before event output child dependencies ref address owners producer payload}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (emitted
      : output
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2)
    (noticed : child.ref ∈ rawGroupNoticeRefs output)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    : ∃ result,
        GraphEvent.taskSuccess (.executionGroup address) result ∈ before ++ [event] := by
  have retired := generated.noticeAncestor_retired
    (fun _ member => (valid.prefix (List.prefix_append before [event])).eachMatches member)
    (valid.eachMatches (List.mem_append_right before List.mem_cons_self))
    emitted noticed known ancestor ⟨producer, payload, task⟩ contributes
  have healthy := (generated.noticeAncestor_healthy_uncancelled valid
    (State.acceptsBatch_prefix started) emitted noticed known ancestor).1
  obtain ⟨registeredTask, registered, occurrenceEq, groupsEq⟩ :=
    generated.retired_structuralContributor_registered valid started task contributes
      retired healthy
  obtain ⟨result, succeeded⟩ := generated.replayGraphEvents_retiredContributor_succeeded
    valid started registered (groupsEq.symm ▸ contributes) retired healthy
  exact ⟨result, occurrenceEq ▸ succeeded⟩

-----------------------------------------------------------------------------------------
-- Recover an exact buffer at handler entry or identify the current successful input
-----------------------------------------------------------------------------------------

/-- A notice ancestor's contributor is prior output, an exact buffer, or this input's value.
Witness: structural contributor accounting recovers its successful source event. An
earlier success is conserved on the supplied replay ledger under backward ancestor health;
the only other possibility is the current task-success input itself. No storage premise
or replacement publication matching is introduced.
-/
theorem ExecutedWork.noticeAncestor_contributor_published_buffered_or_current
    {work before event output child dependencies ref address owners producer payload
      published}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ [event]) published)
    (emitted
      : output
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2)
    (noticed : child.ref ∈ rawGroupNoticeRefs output)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    : ∃ result,
        event = .taskSuccess (.executionGroup address) result
        ∨ (GraphEvent.taskSuccess (.executionGroup address) result ∈ before
            ∧ ((Occurrence.executionGroup address, result.value)
                  ∈ published.take
                      (((State.initialize (Work.fromExecution work)).rawEventReplay
                          before).2.flatMap
                        WorkQueueEvent.objectValues).length
                ∨ ∃ node,
                    ((State.initialize (Work.fromExecution work)).replayGraphEvents
                        before).taskNode?
                        (.executionGroup address)
                      = some node
                    ∧ node.value = some result.value
                    ∧ TaskHasOwners work (.executionGroup address)
                        (node.task.groups.map Execution.DeliveryNode.ref)
                    ∧ ref ∈ node.task.groups.map Execution.DeliveryNode.ref
                    ∧ ref
                      ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
                          before).groupNodes.map
                          (fun owner => owner.group.node.ref))) := by
  obtain ⟨result, succeeded⟩ := generated.noticeAncestor_structuralContributor_succeeded
    valid started emitted noticed known ancestor task contributes
  refine ⟨result, ?_⟩
  rcases List.mem_append.mp succeeded with earlier | current
  · right
    have healthy := (generated.noticeAncestor_healthy_uncancelled valid
      (State.acceptsBatch_prefix started) emitted noticed known ancestor).1
    have priorHealthy : ¬GroupRecordInvalidated work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions before) ref := by
      intro invalid
      apply healthy
      apply invalid.mono
      rw [State.objectFailureContributions_append]
      exact List.subset_append_right _ _
    exact ⟨earlier, generated.healthy_success_published_or_buffered
      (valid.prefix (List.prefix_append before [event])) (State.acceptsBatch_prefix started)
      (covered.prefix before [event]) task contributes priorHealthy earlier⟩
  · exact .inl (List.mem_singleton.mp current).symm

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
