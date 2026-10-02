import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureProjection

/-! Ignored settlements and the contributing object-failure ledger at actual replay states. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Actual queue evidence justifies the cancellation guard
-----------------------------------------------------------------------------------------

/-- A rejected fresh started task has no uninvalidated contributor left.
Witness: generated owner replay supplies every healthy owner, whose supported cache and
canonical ancestry would make the executable guard accept. No output admission is used.
-/
theorem State.OwnerAccounting.rejectedTask_ownersInvalidated {queue : State}
    {work parents before occurrence taskNode}
    (prior : queue.OwnerAccounting work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (found : queue.taskNode? occurrence = some taskNode)
    (fresh : occurrence ∉ GraphEvent.taskSettlements before)
    (rejected : queue.taskHasHealthyOwner taskNode.task = false)
    : ∀ key ∈ taskNode.task.groups.map Execution.DeliveryNode.key,
        GroupInvalidated work (GraphEvent.failureSettlements before) key := by
  have same : taskNode.task.occurrence = occurrence := (occurrence_beq_iff_eq _ _).mp
    (List.find?_some (p := fun candidate : TaskNode =>
      candidate.task.occurrence == occurrence) found)
  exact prior.owners.rejectedTask_ownersInvalidated prior.pending.matching
    prior.supported prior.cancelled generated
    (prior.toHealthyCounterAccounting.descriptors canonical)
    (prior.pending.started taskNode (List.mem_of_find?_eq_some found))
    (same.symm ▸ fresh) rejected

/-- An unpublished rejected task is cancelled by prior source failures.
Witness: registered task provenance and the generated nonempty-owner property combine
with the derived invalidation of every contributor. The publication predicate is supplied
explicitly; this is a snapshot result, not yet an ordered output-history failure witness.
-/
theorem State.OwnerAccounting.rejectedTask_cancelled {queue : State}
    {work parents before occurrence taskNode published}
    (prior : queue.OwnerAccounting work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (found : queue.taskNode? occurrence = some taskNode)
    (fresh : occurrence ∉ GraphEvent.taskSettlements before)
    (rejected : queue.taskHasHealthyOwner taskNode.task = false)
    (unpublished : ¬published occurrence)
    : Causality.TaskCancelled work (GraphEvent.failureSettlements before)
        published occurrence := by
  have registered := prior.pending.started taskNode (List.mem_of_find?_eq_some found)
  obtain ⟨⟨_, payload, producer, _, known⟩, _⟩ :=
    prior.pending.matching taskNode.task registered
  have same : taskNode.task.occurrence = occurrence := (occurrence_beq_iff_eq _ _).mp
    (List.find?_some (p := fun candidate : TaskNode =>
      candidate.task.occurrence == occurrence) found)
  rw [same] at known
  refine .owners ⟨producer, payload, known⟩ unpublished
    (generated.taskOwners_nonempty known) ?_
  intro key contributes
  exact (prior.rejectedTask_ownersInvalidated generated canonical found fresh rejected
    key contributes).toCausality published

/-- Adding an ignored failure token does not invalidate any additional group.
Witness: all of that task's contributors were already invalidated before the handler.
The coarse source-health ledger may keep the token, but error totals must not count it.
-/
theorem State.OwnerAccounting.rejectedTask_invalidation_iff {queue : State}
    {work parents before occurrence taskNode}
    (prior : queue.OwnerAccounting work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (found : queue.taskNode? occurrence = some taskNode)
    (fresh : occurrence ∉ GraphEvent.taskSettlements before)
    (rejected : queue.taskHasHealthyOwner taskNode.task = false) (key : Nat)
    : GroupInvalidated work (occurrence :: GraphEvent.failureSettlements before) key
      ↔ GroupInvalidated work (GraphEvent.failureSettlements before) key := by
  have registered := prior.pending.started taskNode (List.mem_of_find?_eq_some found)
  obtain ⟨⟨_, payload, producer, _, known⟩, _⟩ :=
    prior.pending.matching taskNode.task registered
  have same : taskNode.task.occurrence = occurrence := (occurrence_beq_iff_eq _ _).mp
    (List.find?_some (p := fun candidate : TaskNode =>
      candidate.task.occurrence == occurrence) found)
  rw [same] at known
  exact groupInvalidated_cons_iff_of_ownersInvalidated ⟨producer, payload, known⟩
    (prior.rejectedTask_ownersInvalidated generated canonical found fresh rejected)

-----------------------------------------------------------------------------------------
-- Ignore rejected failures in the proof-side contribution inventory
-----------------------------------------------------------------------------------------

/-- One valid started event has the same health effect with or without ignored failures.
Witness: only task failure adds a source token; its rejected branch is redundant by the
owner/cancellation invariant, while the eligible branch records exactly that token.
-/
theorem State.OwnerAccounting.objectFailureContribution_invalidation {queue : State}
    {work parents before} (prior : queue.OwnerAccounting work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (event : GraphEvent) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true) (key : Nat)
    : GroupInvalidated work (event.groupFailures ++ GraphEvent.failureSettlements before)
        key
      ↔ GroupInvalidated work
          (queue.objectFailureContribution event ++ GraphEvent.failureSettlements before)
          key := by
  cases event with
  | taskSuccess | streamItems | streamSuccess | streamFailure => rfl
  | taskFailure occurrence errors =>
      cases found : queue.taskNode? occurrence with
      | none => simp [State.acceptsGraphEvent, found] at accepted
      | some node =>
          cases eligible : queue.taskHasHealthyOwner node.task with
          | true =>
              simp [objectFailureContribution, found, eligible, GraphEvent.groupFailures]
          | false =>
              simp only [objectFailureContribution, found, eligible, Bool.false_eq_true,
                ↓reduceIte, GraphEvent.groupFailures, List.singleton_append, List.nil_append]
              apply prior.rejectedTask_invalidation_iff generated canonical found _
                eligible key
              exact fun member =>
                fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
                  (GraphEvent.taskSettlements_subsetIdentities before member)

/-- Pointwise-equivalent invalidation ledgers stay equivalent after identical new failures.
Witness: induction on invalidation, replacing only prior-ledger contributing-task causes.
-/
private theorem groupInvalidated_append_congr {work before after}
    (same : ∀ key, GroupInvalidated work before key ↔ GroupInvalidated work after key)
    (newFailures : List Occurrence) (key : Nat)
    : GroupInvalidated work (newFailures ++ before) key
      ↔ GroupInvalidated work (newFailures ++ after) key := by
  have forward {left right}
      (prior : ∀ key, GroupInvalidated work left key → GroupInvalidated work right key)
      {key} (failure : GroupInvalidated work (newFailures ++ left) key)
      : GroupInvalidated work (newFailures ++ right) key := by
    induction failure with
    | task known owner member =>
        rcases List.mem_append.mp member with recent | earlier
        · exact .task known owner (List.mem_append_left _ recent)
        · exact (prior _ (.task known owner earlier)).mono (List.subset_append_right _ _)
    | groupDependency known member _ ih => exact .groupDependency known member ih
  exact ⟨forward (fun key => (same key).mp), forward (fun key => (same key).mpr)⟩

/-- Dropping ignored object failures preserves all cleanup invalidation on generated replay.
Witness: source-prefix induction, unconditional owner/ancestry replay, and the one-event
redundancy theorem. No output admission, failure-cut licensing, or root-health premise is
assumed; contributing failures still need a separate ordered causal witness.
-/
theorem ExecutedWork.replayGraphEvents_objectFailureContributions {work : Execution.Work}
    (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    (acceptedAt
      : ∀ before event,
          (before ++ [event]).IsPrefix events
          → State.acceptsGraphEvent
              ((State.initialize (Work.fromExecution work)).replayGraphEvents before)
              event
            = true)
    : ∀ key,
        GroupInvalidated work (GraphEvent.failureSettlements events) key
        ↔ GroupInvalidated work
            ((State.initialize (Work.fromExecution work)).objectFailureContributions
              events)
            key := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  induction valid with
  | nil => intro key; rfl
  | @append before event validBefore matching fresh ready ih =>
      have acceptedBefore := fun past next (earlier : (past ++ [next]).IsPrefix before) =>
        acceptedAt past next
        (earlier.trans (List.prefix_append before [event]))
      have earlier := ih acceptedBefore
      have accounting :=
        (generated.replayGraphEvents_ownerAncestry parents canonical validBefore
          acceptedBefore).accounting
      intro key
      rw [GraphEvent.failureSettlements_append, State.objectFailureContributions_append]
      simp only [State.objectFailureContributions, List.nil_append]
      exact (accounting.objectFailureContribution_invalidation generated canonical event fresh
        (acceptedAt before event (List.prefix_refl _)) key).trans
          (groupInvalidated_append_congr earlier _ key)

/-- Started source batches also admit the smaller, guard-filtered health ledger.
Witness: the existing start checker supplies acceptance at each flattened source prefix;
normalization and response batching never select which object failures contribute.
-/
theorem ExecutedWork.inputsStarted_objectFailureContributions {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) (key : Nat)
    : GroupInvalidated work (GraphEvent.failureSettlements batches.flatten) key
      ↔ GroupInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions
            batches.flatten)
          key :=
  generated.replayGraphEvents_objectFailureContributions valid
    (inputsStarted_eachAccepted work batches started) key

/-- A fresh rejected task at an actual normalized boundary is already causally cancelled.
Witness: unconditional owner replay identifies invalidated contributors, and the ledger
equivalence traces their failure to earlier eligible settlements only. The explicit
nonpublication premise belongs to the later publication bridge, not to source semantics.
-/
theorem ExecutedWork.runNormalized_rejectedTask_cancelled {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    {occurrence taskNode published}
    (found
      : ((State.initialize (Work.fromExecution work)).runNormalized batches).1.taskNode?
          occurrence
        = some taskNode)
    (fresh : occurrence ∉ GraphEvent.taskSettlements batches.flatten)
    (rejected
      : State.taskHasHealthyOwner
          ((State.initialize (Work.fromExecution work)).runNormalized batches).1
          taskNode.task
        = false)
    (unpublished : ¬published occurrence)
    : Causality.TaskCancelled work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          batches.flatten)
        published occurrence := by
  obtain ⟨parents, canonical, replayed⟩ := generated.runNormalized_ownerAncestry _ valid started
  have prior := replayed.accounting
  have registered := prior.pending.started taskNode (List.mem_of_find?_eq_some found)
  obtain ⟨⟨_, payload, producer, _, known⟩, _⟩ :=
    prior.pending.matching taskNode.task registered
  have same : taskNode.task.occurrence = occurrence := (occurrence_beq_iff_eq _ _).mp
    (List.find?_some (p := fun candidate : TaskNode =>
      candidate.task.occurrence == occurrence) found)
  rw [same] at known
  refine .owners ⟨producer, payload, known⟩ unpublished
    (generated.taskOwners_nonempty known) ?_
  intro key contributes
  have invalid := prior.rejectedTask_ownersInvalidated generated canonical found fresh
    rejected key contributes
  exact ((generated.inputsStarted_objectFailureContributions valid started key).mp
    invalid).toCausality published

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
