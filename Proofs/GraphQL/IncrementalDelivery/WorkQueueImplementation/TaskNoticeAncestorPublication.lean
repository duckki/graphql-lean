import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorContributors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorDrainPublication

/-! Actual task-success notices account for every structural ancestor contribution. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Source accounting supplies prepared storage, including the current successful input
-----------------------------------------------------------------------------------------

/-- An actual task-handler notice's ancestor contributor is prior output or a prepared buffer.
Witness: recover its source success without a registry premise. Freshness preserves an
earlier exact buffer through preparation; the current input installs its own value with
unchanged structural owners. Every retained branch includes a genuinely live contributor.
-/
theorem ExecutedWork.taskSuccess_noticeAncestor_prepared_or_published
    {work before occurrence result output child dependencies key address owners producer
      payload published incoming}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [.taskSuccess occurrence result]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch
          (before ++ [.taskSuccess occurrence result])
        = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ [.taskSuccess occurrence result]) published)
    (emitted
      : output
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).taskSuccess
            occurrence result).2)
    (noticed : child.key ∈ rawGroupNoticeKeys output)
    (known : GroupRecordAt work child dependencies) (ancestor : key ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : key ∈ owners)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let prepared :=
        ((queue.putTaskNode
            { incoming with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      queue.taskNode? occurrence = some incoming
      → ∃ value,
          (Occurrence.executionGroup address, value)
            ∈ published.take
                (((State.initialize (Work.fromExecution work)).rawEventReplay
                    before).2.flatMap
                  WorkQueueEvent.objectValues).length
          ∨ ∃ node,
              prepared.taskNode? (.executionGroup address) = some node
              ∧ node.value = some value
              ∧ TaskHasOwners work (.executionGroup address)
                  (node.task.groups.map Execution.DeliveryNode.key)
              ∧ key ∈ node.task.groups.map Execution.DeliveryNode.key
              ∧ key ∈ prepared.groupNodes.map (fun owner => owner.group.node.key) := by
  intro queue prepared found
  obtain ⟨sourceResult, current | ⟨succeeded, priorOutput | buffered⟩⟩ :=
    generated.noticeAncestor_contributor_published_buffered_or_current valid started covered
      emitted noticed known ancestor task contributes
  · obtain ⟨rfl, rfl⟩ := GraphEvent.taskSuccess.inj current
    have healthy := (generated.noticeAncestor_healthy_uncancelled valid
      (State.acceptsBatch_prefix started) emitted noticed known ancestor).1
    obtain ⟨liveNode, lookup, _, nodeContributes, present⟩ :=
      generated.success_with_finalHealthyOwner_live valid started task contributes healthy
        (result := result) (before := before) (after := []) (by simp)
    have same : liveNode = incoming := Option.some.inj (lookup.symm.trans found)
    subst liveNode
    have accounted := (createWorkQueue_pendingAccounting work).replayGraphEvents
      (before := []) generated before (valid.prefix (List.prefix_append before [_]))
        (State.acceptsBatch_prefix started)
    have member := State.taskNode?_some found
    obtain ⟨_, nodePayload, nodeProducer, _, descriptor⟩ :=
      (accounted.matching incoming.task (accounted.started incoming member.1)).1
    have taskOwners : TaskHasOwners work (.executionGroup address)
        (incoming.task.groups.map Execution.DeliveryNode.key) :=
      ⟨nodeProducer, nodePayload, member.2 ▸ descriptor⟩
    obtain ⟨node, installed, sameTask, stored⟩ := State.taskSuccess_prepared_value found
      result
    exact ⟨result.value, .inr ⟨node, installed, stored, sameTask.symm ▸ taskOwners,
      sameTask.symm ▸ nodeContributes,
      State.maybeIntegrateWork_includesKeys (queue.putTaskNode
        { incoming with value := some result.value }) result.work
          (some (.executionGroup address)) key present⟩⟩
  · exact ⟨sourceResult.value, .inl priorOutput⟩
  · obtain ⟨node, lookup, stored, taskOwners, nodeContributes, present⟩ := buffered
    have fresh := (valid.atPrefix (before := before)
      (event := .taskSuccess occurrence result) ⟨[], by simp⟩).2.1
    have different : occurrence ≠ .executionGroup address := by
      intro same
      apply fresh.2.2.1 occurrence List.mem_cons_self
      rw [same]
      exact GraphEvent.successes_mem_settled
        (List.mem_flatMap.mpr ⟨_, succeeded, List.mem_cons_self⟩)
    have retained := State.putTaskNode_lookup_other lookup
      { incoming with value := some result.value }
      ((State.taskNode?_some found).2 ▸ different)
    exact ⟨sourceResult.value, .inr ⟨node,
      State.maybeIntegrateWork_lookup_other retained result.work (some occurrence)
        (fun same => different (Option.some.inj same)), stored, taskOwners, nodeContributes,
      State.maybeIntegrateWork_includesKeys (queue.putTaskNode
        { incoming with value := some result.value }) result.work (some occurrence)
          key present⟩⟩

-----------------------------------------------------------------------------------------
-- Both owner-fold and drain carriers consume their ancestors on the same handler ledger
-----------------------------------------------------------------------------------------

/-- A prepared ancestor buffer precedes its exact task-handler notice in either phase.
Witness: split the actual output at the owner-fold boundary and apply that phase's common
prefix conservation theorem. Endpoint noncancellation propagates to the earlier boundary.
-/
theorem ExecutedWork.taskSuccess_noticeAncestor_bufferBefore
    {work before occurrence result incoming published}
    {index group groups streams child dependencies key buffered node value}
    (generated : ExecutedWork work)
    (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (known : GroupRecordAt work child dependencies) (ancestor : key ∈ dependencies)
    (task : TaskHasOwners work buffered (node.task.groups.map Execution.DeliveryNode.key))
    (contributes : key ∈ node.task.groups.map Execution.DeliveryNode.key)
    (stored : node.value = some value)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let prepared :=
        ((queue.putTaskNode
            { incoming with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      queue.PreparedReleaseOwners (.taskSuccess occurrence result) published
      → queue.taskNode? occurrence = some incoming
      → queue.taskHasHealthyOwner incoming.task = true
      → prepared.taskNode? buffered = some node
      → key ∈ prepared.groupNodes.map (fun owner => owner.group.node.key)
      → (queue.taskSuccess occurrence result).2[index]?
        = some (.groupSuccess group groups streams)
      → child ∈ groups
      → key ∉ (queue.taskSuccess occurrence result).1.cancelledGroups
      → (buffered, value)
        ∈ published.take
            (((queue.taskSuccess occurrence result).2.take index).flatMap
              WorkQueueEvent.objectValues).length := by
  intro queue prepared prefixes found healthy lookup present selected noticed uncancelled
  let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
  let active := released.1.startNewWork released.2.2
  have equation : queue.taskSuccess occurrence result
      = (active.drainReadyGroups.1, released.2.1 ++ active.drainReadyGroups.2) := by
    rw [queue.taskSuccess_eq occurrence result incoming found]
    simp only [healthy, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [equation] at selected uncancelled ⊢
  dsimp only at selected uncancelled ⊢
  by_cases inFold : index < released.2.1.length
  · rw [List.getElem?_append_left inFold] at selected
    rw [List.take_append_of_le_length (Nat.le_of_lt inFold)]
    obtain ⟨parents, canonical, records, links, live, tasks, roots, _⟩ :=
      generated.replayGraphEvents_preparedRetirement before matching matched incoming
    have preparedUncancelled : key ∉ prepared.cancelledGroups := by
      intro member
      apply uncancelled
      apply State.drainReadyGroups_go_cancelledGroups_subset
      simpa only [active, State.startNewWork_cancelledGroups, released,
        successGroupFold_cancelledGroups] using member
    exact (prefixes incoming found healthy).ownerCarrier_ancestorValue generated records
      links canonical live tasks roots selected noticed known ancestor lookup stored task
      contributes present preparedUncancelled
  · have inDrain : released.2.1.length ≤ index := by omega
    rw [List.getElem?_append_right inDrain] at selected
    rw [List.take_append, List.take_of_length_le inDrain]
    exact generated.taskSuccess_drainNoticeAncestorValue_before matching matched known
      ancestor task contributes stored prefixes found healthy lookup present selected noticed
      uncancelled

-----------------------------------------------------------------------------------------
-- No storage or registry premises remain at the actual source-to-output boundary
-----------------------------------------------------------------------------------------

/-- All structural ancestor contributions publish strictly before an actual task notice.
Witness: source accounting yields prior publication or exact prepared storage, including
the current successful input. Notice-ancestor health excludes cancellation. The original
replay ledger then supplies the exact owner-fold/drain prefix; no second matching is chosen.
-/
theorem ExecutedWork.taskSuccess_noticeAncestor_contributor_before
    {work before occurrence result published index group groups streams child dependencies
      key address owners producer payload}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [.taskSuccess occurrence result]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch
          (before ++ [.taskSuccess occurrence result])
        = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ [.taskSuccess occurrence result]) published)
    (selected
      : (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).taskSuccess
          occurrence result).2[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : key ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : key ∈ owners)
    : ∃ value,
        (Occurrence.executionGroup address, value)
        ∈ published.take
            ((((State.initialize (Work.fromExecution work)).rawEventReplay
                before).2.flatMap
                WorkQueueEvent.objectValues).length
              + (((((State.initialize (Work.fromExecution work)).replayGraphEvents
                      before).taskSuccess
                    occurrence result).2.take
                    index).flatMap
                  WorkQueueEvent.objectValues).length) := by
  let initial := State.initialize (Work.fromExecution work)
  let queue := initial.replayGraphEvents before
  change (queue.taskSuccess occurrence result).2[index]?
    = some (.groupSuccess group groups streams) at selected
  have keyNoticed : child.key ∈ rawGroupNoticeKeys (.groupSuccess group groups streams) :=
    List.mem_map_of_mem noticed
  have emitted := List.mem_of_getElem? selected
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found] at selected
  | some incoming =>
      cases healthy : queue.taskHasHealthyOwner incoming.task with
      | false =>
          rw [queue.taskSuccess_eq occurrence result incoming found] at selected
          simp [healthy] at selected
      | true =>
          obtain ⟨value, prior | ⟨node, lookup, stored, taskOwners, nodeContributes, present⟩⟩ :=
            generated.taskSuccess_noticeAncestor_prepared_or_published valid started covered
              emitted keyNoticed known ancestor task contributes found
          · exact ⟨value, List.take_subset_take_left _ (Nat.le_add_right ..) prior⟩
          · have notCancelled := (generated.noticeAncestor_healthy_uncancelled valid
              (State.acceptsBatch_prefix started) emitted keyNoticed known ancestor).2
            have endpoint : initial.replayGraphEvents
                (before ++ [.taskSuccess occurrence result])
                = (queue.taskSuccess occurrence result).1 := by
              simp only [State.replayGraphEvents, List.foldl_append, List.foldl_cons,
                List.foldl_nil, State.handleGraphEvent]
              rfl
            rw [endpoint] at notCancelled
            have prefixes := covered.atPrefixDrainOwners before
              (.taskSuccess occurrence result) []
            have delivered := generated.taskSuccess_noticeAncestor_bufferBefore
              (fun _ member => (valid.prefix (List.prefix_append before [_])).eachMatches member)
              (valid.eachMatches (List.mem_append_right before List.mem_cons_self))
              known ancestor taskOwners nodeContributes stored prefixes found healthy lookup
              present selected noticed notCancelled
            refine ⟨value, ?_⟩
            rw [List.take_add]
            apply List.mem_append_right
            rw [List.take_take] at delivered
            exact List.take_subset_take_left _ (Nat.min_le_left _ _) delivered

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
