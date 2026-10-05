import Proofs.GraphQL.IncrementalDelivery.Correctness.OwnerAvailability
import Proofs.GraphQL.IncrementalDelivery.Correctness.TaskErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureReporting

/-! Complete-run existence for finite streams without child work and with positive
failure counts. Actual closure events supply reports; no terminal history is assumed.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

/-- A child-free stream has only its root stream boundary and empty located subtrees.
Witness: structural navigation and the supplied empty-child equations for every item.
-/
theorem childFreeStream_located {node items address current producer owners}
    (childrenEmpty : ∀ item ∈ items, item.2 = Work.empty)
    (located : Located (.stream node items) address current producer owners)
    : (address = [] ∧ current = .stream node items ∧ producer = none ∧ owners = [])
      ∨ current = .empty := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | left _ ih | right _ ih | executionGroup _ ih =>
      rcases ih with ⟨_, impossible, _, _⟩ | impossible <;> cases impossible
  | item located selected ih =>
      rcases ih with ⟨rfl, same, rfl, rfl⟩ | impossible
      · cases same
        exact Or.inr (childrenEmpty _ (List.mem_of_getElem? selected))
      · cases impossible

/-- Every task in a child-free stream has the stream's sole owner and no producer.
Witness: its only nonempty located boundary; no deferred task can occur there.
-/
theorem childFreeStream_task {node items occurrence owners producer payload}
    (childrenEmpty : ∀ item ∈ items, item.2 = Work.empty)
    (known : TaskAt (.stream node items) occurrence owners producer payload)
    : owners = [node.ref] ∧ producer = none := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      rcases childFreeStream_located childrenEmpty located.toCurrent with
        ⟨_, impossible, _, _⟩ | impossible <;> cases impossible
  | item located selected =>
      rcases childFreeStream_located childrenEmpty located.toCurrent with
        ⟨rfl, same, rfl, rfl⟩ | impossible
      · cases same
        exact ⟨rfl, rfl⟩
      · cases impossible

/-- A child-free stream has exactly its root descriptor and no release dependencies.
Witness: structural node navigation; every other located subtree is empty.
-/
theorem childFreeStream_node {node items descriptor kind dependencies producer}
    (childrenEmpty : ∀ item ∈ items, item.2 = Work.empty)
    (known : NodeAt (.stream node items) descriptor kind dependencies producer)
    : descriptor = node ∧ kind = .stream ∧ dependencies = [] ∧ producer = none := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      rcases childFreeStream_located childrenEmpty located.toCurrent with
        ⟨_, impossible, _, _⟩ | impossible <;> cases impossible
  | stream located =>
      rcases childFreeStream_located childrenEmpty located.toCurrent with
        ⟨rfl, same, rfl, rfl⟩ | impossible
      · cases same
        exact ⟨rfl, rfl, rfl, rfl⟩
      · cases impossible

/-- Snapshot cancellation in a child-free stream requires failure of its sole owner.
Witness: the task has no producer, so only the nonempty-owner cancellation rule applies.
-/
theorem childFreeStream_cancelled_owner {node items failed published occurrence}
    (childrenEmpty : ∀ item ∈ items, item.2 = Work.empty)
    (cancelled : Causality.TaskCancelled (.stream node items) failed published occurrence)
    : Causality.NodeFailed (.stream node items) failed published node.ref := by
  cases cancelled with
  | owners known _ _ failures =>
      obtain ⟨producer, payload, task⟩ := known
      obtain ⟨rfl, _⟩ := childFreeStream_task childrenEmpty task
      exact failures node.ref (by simp)
  | producerFailed known _ _ | producerCancelled known _ _ =>
      obtain ⟨owners, payload, task⟩ := known
      have impossible := (childFreeStream_task childrenEmpty task).2
      cases impossible

/-- Snapshot failure of a child-free stream has an actual recorded contributing task.
Witness: its root descriptor has neither dependencies nor a producer, excluding all
inherited-failure rules. Only a direct failed item can fail this stream.
-/
theorem childFreeStream_failed_task {node items failed published}
    (childrenEmpty : ∀ item ∈ items, item.2 = Work.empty)
    (failure : Causality.NodeFailed (.stream node items) failed published node.ref)
    : ∃ occurrence owners producer payload,
        TaskAt (.stream node items) occurrence owners producer payload
        ∧ occurrence ∈ failed
        ∧ node.ref ∈ owners := by
  cases failure with
  | task known owner finished =>
      obtain ⟨producer, payload, known⟩ := known
      exact ⟨_, _, producer, payload, known, finished, owner⟩
  | groupDependency known _ _ =>
      obtain ⟨descriptor, producer, known, _⟩ := known
      have impossible := (childFreeStream_node childrenEmpty known).2.1
      cases impossible
  | streamDependencies known nonempty _ =>
      obtain ⟨descriptor, producer, known, _⟩ := known
      exact False.elim (nonempty (childFreeStream_node childrenEmpty known).2.2.1)
  | producers _ noRoot _ _ =>
      exact False.elim (noRoot ⟨node, .stream, [], .stream .root, rfl⟩)

/-- Closing a child-free stream reports every unpublished attachment when failures count.
Witness: a successful closure would cancel an unpublished item while asserting health.
A failure closure must count a recorded positive item failure, and its scope is the
common stream attachment. No terminal reporting law is assumed in this construction.
-/
theorem childFreeStream_closed_reports
    {node items groups streams events matching failures}
    (childrenEmpty : ∀ item ∈ items, item.2 = Work.empty)
    (positive : ExecutionErrors.ItemsPositive items)
    (explained : Explains (.stream node items) groups streams events matching failures)
    (closed : node.ref ∈ completedRefs events) {occurrence owners producer payload}
    (known : TaskAt (.stream node items) occurrence owners producer payload)
    (unpublished : ¬Published matching events occurrence)
    : FailureReportedFor events payload.path := by
  obtain ⟨event, member, closes⟩ := List.mem_flatMap.mp closed
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  have allowed := explained.2.2 index event selected
  have notEarlier : ¬Published matching (events.take index) occurrence := by
    intro earlier
    apply unpublished
    simpa only [List.take_append_drop] using earlier.append (events.drop index)
  have nodeEq {descriptor kind dependencies producer}
      (located : NodeAt (.stream node items) descriptor kind dependencies producer) :=
    childFreeStream_node childrenEmpty located
  cases event <;>
    simp only [EventAllowed, nodeFailed_filter (Nat.le_refl _),
      nodeAccounted_filter (Nat.le_refl _), failedBefore_filter _ (Nat.le_refl _)] at allowed
  case groupValues | streamValues => simp [eventCompleted] at closes
  case groupSuccess descriptor groups streams | groupFailure descriptor errors =>
    obtain ⟨dependencies, birth, located⟩ := allowed.1
    have impossible := (nodeEq located).2.1
    cases impossible
  case streamSuccess descriptor =>
    obtain ⟨dependencies, birth, located⟩ := allowed.1
    obtain ⟨same, _, _, _⟩ := nodeEq located
    subst descriptor
    have contributes : node.ref ∈ owners := by
      rw [(childFreeStream_task childrenEmpty known).1]
      simp
    have cancelled := (allowed.2.2.2 _ _ ⟨producer, payload, known⟩ contributes).resolve_right
      notEarlier
    obtain ⟨cut, _, bound, cancelled⟩ := cancelled
    have failed : NodeFailed (.stream node items) matching (events.take index) failures node.ref :=
      ⟨cut, by assumption, bound, childFreeStream_cancelled_owner childrenEmpty cancelled⟩
    exact False.elim (allowed.2.2.1 failed)
  case streamFailure descriptor errors =>
    obtain ⟨dependencies, birth, located⟩ := allowed.1
    obtain ⟨same, _, _, _⟩ := nodeEq located
    subst descriptor
    obtain ⟨cut, _, bound, failure⟩ := allowed.2.2.1
    obtain ⟨failedOccurrence, failedOwners, failedProducer, failedPayload, failedTask,
      recorded, contributes⟩ := childFreeStream_failed_task childrenEmpty failure
    have recordedBefore
        : failedOccurrence ∈ failedBefore failures (events.take index).length := by
      obtain ⟨entry, present, same⟩ := List.mem_map.mp recorded
      obtain ⟨present, within⟩ := List.mem_filter.mp present
      have within : entry.1 ≤ cut := by simpa only [decide_eq_true_eq] using within
      exact List.mem_map.mpr
        ⟨
          entry,
          List.mem_filter.mpr
            ⟨present, by simpa only [decide_eq_true_eq] using Nat.le_trans within bound⟩,
          same
        ⟩
    have fails : failedPayload.failure.isSome = true := by
      obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp recordedBefore
      have entryMember : entry ∈ failures := (List.mem_filter.mp entryMember).1
      obtain ⟨before, after, equal⟩ := List.mem_iff_append.mp entryMember
      obtain ⟨more, otherProducer, otherPayload, task, fails, _⟩ :=
        (explained.2.1 before entry.1 entry.2 after equal).2.2.1
      have occurrenceEq : entry.2 = failedOccurrence := same
      subst occurrenceEq
      obtain ⟨_, _, payloadEq⟩ := failedTask.unique task
      exact payloadEq.symm ▸ fails
    have workPositive : ExecutionErrors.WorkPositive (.stream node items) := positive
    have positiveCount := workPositive.task failedTask fails
    have countBound := allowed.2.2.2.contribution_le recordedBefore failedTask contributes
    have attachment : payload.path = node.path := by
      cases StructuralEquivalence.taskAt_of_current known with
      | executionGroup located =>
          rcases childFreeStream_located childrenEmpty located.toCurrent with
            ⟨_, impossible, _, _⟩ | impossible <;> cases impossible
      | item located _ =>
          rcases childFreeStream_located childrenEmpty located.toCurrent with
            ⟨rfl, same, rfl, rfl⟩ | impossible
          · cases same
            rfl
          · cases impossible
    exact ⟨
      node,
      errors,
      by omega,
      attachment ▸ ⟨[], by simp⟩,
      Or.inr (List.mem_of_getElem? selected)
    ⟩

/-- A finite child-free stream with positive failure counts admits a complete run.
Witness: root owner coverage constructs internal accounting, then actual closures report
unpublished attachments and satisfy the reporting-aware terminal characterization.
Successful item error counts are unrestricted, and the empty stream is included.
-/
theorem childFreeStream_completeRun_exists (node : DeliveryNode)
    (items : List (Result ResponseValue × Work))
    (childrenEmpty : ∀ item ∈ items, item.2 = Work.empty)
    (positive : ExecutionErrors.ItemsPositive items)
    : ∃ history, AdmissibleRun (.stream node items) history := by
  have coherent : MixedOwnerPaths.WorkAt (fun _ => node.path) (node.ref + 1)
      (.stream node items) := by
    rw [MixedOwnerPaths.WorkAt]
    exact ⟨⟨Nat.lt_succ_self node.ref, rfl⟩, fun item member => by
      rw [childrenEmpty item member, MixedOwnerPaths.WorkAt]
      trivial⟩
  have initialized : Initializes (.stream node items) [] [node] := by
    refine ⟨⟨by simp, by simp, ?_⟩, by simp⟩
    intro stream member
    have same := List.mem_singleton.mp member
    subst stream
    refine ⟨[], none, .stream .root, ?_⟩
    exact ⟨by simp [announcedRefs, pendingRefs],
      Or.inl ⟨fun failure => failure.nonempty rfl, Or.inl rfl⟩, by simp, Or.inl rfl⟩
  obtain ⟨events, matching, failures, explained, accounted⟩ :=
    accountedHistory_exists_of_initial_owner_coverage coherent initialized (by
      intro occurrence owners producer payload known
      obtain ⟨rfl, _⟩ := childFreeStream_task childrenEmpty known
      simp)
  obtain ⟨tail, _, _, closedHistory, allClosed⟩ :=
    explained.close_open_refs accounted
      (announcedRefs (([] ++ [node]).map DeliveryNode.ref) events) (fun _ opened => opened.1)
  apply (admissibleRun_exists_iff_reported_history (.stream node items)).mpr
  refine ⟨[], [node], events ++ tail, matching, failures, closedHistory, ?_⟩
  intro occurrence owners producer payload known
  by_cases published : Published matching (events ++ tail) occurrence
  · exact Or.inr published
  · refine Or.inl ⟨((accounted _ _ _ _ known).append tail).resolve_right published, ?_⟩
    apply childFreeStream_closed_reports childrenEmpty positive closedHistory ?_ known published
    apply allClosed
    simp [announcedRefs]

end GraphQL.IncrementalDelivery.Correctness
