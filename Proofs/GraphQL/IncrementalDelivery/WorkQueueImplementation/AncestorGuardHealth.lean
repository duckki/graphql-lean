import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GeneratedAncestry
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RecordInvalidation

/-! Reflect the finite health guard through live ancestors and isolate missing parents. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The walk's missing-parent boundary needs historical evidence
-----------------------------------------------------------------------------------------

/-- An uncached live record with an absent, uncancelled parent has healthy defer ancestry.
`failed` is the accepted object-failure inventory. Registration descriptors include
taskless ancestors; they do not assert task ownership. This is proof-side boundary evidence,
not an additional source or conformance premise. Recorded cancellation rejects the guard
directly; only its other missing-parent branch needs this historical health evidence.
Checking live error caches alone cannot establish it.
-/
def State.MissingParentAncestorsHealthy (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : Prop :=
  ∀ node ∈ queue.groupNodes,
    node.failure = none
    → ∀ dependencies,
        GroupRecordAt work node.group.node dependencies
        → ∀ parent,
            node.group.parent = some parent
            → queue.groupNode? parent = none
            → parent ∉ queue.cancelledGroups
            → ∀ ancestor ∈ dependencies, ¬GroupRecordInvalidated work failed ancestor

/-- Before the first accepted failure, every missing-parent boundary is healthy.
Witness: record invalidation always has a failed contributing task at its origin.
-/
theorem State.MissingParentAncestorsHealthy.of_empty (queue : State)
    (work : Execution.Work)
    : queue.MissingParentAncestorsHealthy work [] := by
  intro node member uncached dependencies known parent parentEq missing uncancelled
  intro ancestor inAncestors invalid
  exact invalid.nonempty rfl

/-- Present or recorded-cancelled parents require no historical stopping-boundary proof.
Witness: a successful lookup excludes the absent case; a cancellation marker excludes
the guard's accepting branch. This also covers child-first registration order.
-/
theorem State.MissingParentAncestorsHealthy.of_presentOrCancelledParents {queue : State}
    (work : Execution.Work) (failed : List Occurrence)
    (covered
      : ∀ node ∈ queue.groupNodes,
          ∀ parent,
            node.group.parent = some parent
            → (queue.groupNode? parent).isSome = true ∨ parent ∈ queue.cancelledGroups)
    : queue.MissingParentAncestorsHealthy work failed := by
  intro node member uncached dependencies known parent parentEq missing notCancelled
  rcases covered node member parent parentEq with available | cancelled
  · simp [missing] at available
  · exact False.elim (notCancelled cancelled)

/-- If no live parent link is missing, the stopping-boundary obligation is vacuous.
Witness: specialize the present-or-cancelled parent criterion to existing lookups.
-/
theorem State.MissingParentAncestorsHealthy.of_presentParents {queue : State}
    (work : Execution.Work) (failed : List Occurrence)
    (present
      : ∀ node ∈ queue.groupNodes,
          ∀ parent,
            node.group.parent = some parent → (queue.groupNode? parent).isSome = true)
    : queue.MissingParentAncestorsHealthy work failed := by
  exact .of_presentOrCancelledParents work failed
    (fun node member parent parentEq => Or.inl (present node member parent parentEq))

-----------------------------------------------------------------------------------------
-- Every visited cache excludes a direct cause; generated chains cover all ancestors
-----------------------------------------------------------------------------------------

/-- A successful finite guard excludes direct and ancestor invalidation once its missing
parent boundaries are justified. Witness: recurse over the guard's actual fuel, use exact
positive error totals at each visited record, and identify full generated ancestry with
the immediate parent's chain. No output admission or publication support is assumed.
-/
theorem State.GroupErrorAccounting.groupIsHealthy_recordUninvalidated
    {queue : State} {work failed key}
    (counts : queue.GroupErrorAccounting work failed) (generated : ExecutedWork work)
    (descriptors
      : ∀ node ∈ queue.groupNodes,
          ∃ dependencies,
            GroupRecordAt work node.group.node dependencies
            ∧ node.group.parent = dependencies.head?)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (missing : queue.MissingParentAncestorsHealthy work failed)
    (healthy : queue.groupIsHealthy key = true)
    : ¬GroupRecordInvalidated work failed key := by
  have walk (fuel : Nat) (node : GroupNode) (member : node ∈ queue.groupNodes)
      (uncached : node.failure = none)
      (checked : State.groupIsHealthy.ancestorsHealthy queue fuel node.group.parent = true)
      : ¬GroupRecordInvalidated work failed node.group.node.key := by
    induction fuel generalizing node with
    | zero | succ fuel ih =>
        all_goals
          obtain ⟨dependencies, known, parentEq⟩ := descriptors node member
          intro invalid
          rcases generated.groupRecordInvalidated_causes known invalid with
            ⟨occurrence, owners, ⟨birth, payload, task⟩, owner, recorded⟩
            | ⟨ancestor, contributes, failedAncestor⟩
          · obtain ⟨otherOwners, otherBirth, otherPayload, otherTask, fails⟩ :=
              failedKnown occurrence recorded
            have same := task.unique otherTask
            exact counts.uncached_noFailedContributor generated member uncached otherTask fails
              (same.1 ▸ owner) recorded
          · cases parentLookup : node.group.parent with
            | none =>
                have empty : dependencies = [] := List.head?_eq_none_iff.mp
                  (parentEq.symm.trans parentLookup)
                simp [empty] at contributes
            | some parent =>
                rw [parentLookup] at checked
                first
                | cases checked
                | cases found : queue.groupNode? parent with
                  | none =>
                      have notCancelled : parent ∉ queue.cancelledGroups := by
                        simpa [State.groupIsHealthy.ancestorsHealthy, found] using checked
                      exact missing node member uncached dependencies known parent
                        parentLookup found notCancelled ancestor contributes failedAncestor
                  | some parentNode =>
                      simp only [State.groupIsHealthy.ancestorsHealthy, found,
                        Bool.and_eq_true] at checked
                      have parentMember := List.mem_of_find?_eq_some found
                      obtain ⟨parentDependencies, parentKnown, _⟩ :=
                        descriptors parentNode parentMember
                      have parentKey := State.groupNode?_key found
                      have chain := generated.groupRecordAncestryChain known parentKnown
                        (by rw [parentKey]; exact parentEq.symm.trans parentLookup)
                      have safe := ih parentNode parentMember
                        (Option.isNone_iff_eq_none.mp checked.1) checked.2
                      rw [chain] at contributes
                      rcases List.mem_cons.mp contributes with same | earlier
                      · exact safe (same ▸ failedAncestor)
                      · exact safe (.ancestor parentKnown earlier failedAncestor)
  obtain ⟨node, found, uncached⟩ := State.groupIsHealthy_present healthy
  have checked := healthy
  simp only [State.groupIsHealthy, found, Bool.and_eq_true] at checked
  have safe := walk queue.groupNodes.length node (List.mem_of_find?_eq_some found)
    uncached checked.2
  simpa only [State.groupNode?_key found] using safe

/-- The record-aware guard theorem also excludes contributor-only causal invalidation.
Witness: contributor invalidation embeds in registration-record invalidation; taskless
ancestors need no fabricated producer or task descriptor during the parent walk.
-/
theorem State.GroupErrorAccounting.groupIsHealthy_uninvalidated
    {queue : State} {work failed key}
    (counts : queue.GroupErrorAccounting work failed) (generated : ExecutedWork work)
    (descriptors
      : ∀ node ∈ queue.groupNodes,
          ∃ dependencies,
            GroupRecordAt work node.group.node dependencies
            ∧ node.group.parent = dependencies.head?)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (missing : queue.MissingParentAncestorsHealthy work failed)
    (healthy : queue.groupIsHealthy key = true)
    : ¬GroupInvalidated work failed key := by
  intro invalid
  exact counts.groupIsHealthy_recordUninvalidated generated descriptors failedKnown
    missing healthy invalid.toRecordInvalidated

/-- At an actual accepted source prefix, missing-parent evidence is the only additional
queue-local premise needed to reflect the health guard into absence of invalidation.
Witness: replay derives complete counts, failed descriptors, and canonical live metadata;
the finite-walk theorem discharges the remaining live-ancestor cases.
-/
theorem createWorkQueue_replayGraphEvents_groupIsHealthy_recordUninvalidated
    {work : Execution.Work} (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    (accepted : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (missing
      : State.MissingParentAncestorsHealthy
          ((State.initialize (Work.fromExecution work)).replayGraphEvents events) work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions
            events))
    {key : Nat}
    (healthy
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          events).groupIsHealthy
          key
        = true)
    : ¬GroupRecordInvalidated work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions events)
        key := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have initial := createWorkQueue_healthyCounterAccounting work parents canonical
  have metadata := initial.replayGraphEvents (before := []) generated canonical events valid
    accepted
  have initialCounts := createWorkQueue_groupErrorAccounting (Work.fromExecution work) work
  have counts := initialCounts.replayGraphEvents (before := [])
    (createWorkQueue_pendingAccounting work)
      generated events valid accepted
  simp only [List.append_nil] at counts
  apply counts.groupIsHealthy_recordUninvalidated generated (metadata.descriptors canonical)
    ?_ missing healthy
  intro occurrence member
  obtain ⟨owners, producer, path, errors, known⟩ := valid.failureSettlements_known occurrence
    (((State.initialize (Work.fromExecution work)).objectFailureContributions_sublist events).subset
      member)
  exact ⟨owners, producer, _, known, rfl⟩

/-- Record-aware replay reflection retains the contributor-only interface.
Witness: the stronger record conclusion excludes its embedded contributor invalidation.
Missing-parent evidence is still a proof obligation, not a source assumption.
-/
theorem createWorkQueue_replayGraphEvents_groupIsHealthy_uninvalidated
    {work : Execution.Work} (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    (accepted : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (missing
      : State.MissingParentAncestorsHealthy
          ((State.initialize (Work.fromExecution work)).replayGraphEvents events) work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions
            events))
    {key : Nat}
    (healthy
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          events).groupIsHealthy
          key
        = true)
    : ¬GroupInvalidated work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions events)
        key := by
  intro invalid
  exact createWorkQueue_replayGraphEvents_groupIsHealthy_recordUninvalidated
    generated valid accepted missing healthy invalid.toRecordInvalidated

-----------------------------------------------------------------------------------------
-- Ordered accepted cuts retain the same guard and failure inventory
-----------------------------------------------------------------------------------------

/-- An accepted object cut has an owner uninvalidated by every earlier accepted failure.
Witness: recover its exact pre-handler state, reflect the executable guard, and identify
the ordered predecessor cuts with the replay's accepted-error ledger. `GuardHealthCuts`
discharges the missing-parent premise from replay, not from a host-source assumption.
-/
theorem createWorkQueue_eligibleObjectFailureCuts_uninvalidatedOwner
    {work : Execution.Work} (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (missing
      : ∀ received : List GraphEvent,
          received.IsPrefix batches.flatten
          → State.MissingParentAncestorsHealthy
              ((State.initialize (Work.fromExecution work)).replayGraphEvents received)
              work
              ((State.initialize (Work.fromExecution work)).objectFailureContributions
                received))
    {before after : FailureCuts} {cut : Nat} {occurrence : Occurrence}
    (split
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
        = before ++ (cut, occurrence) :: after)
    : ∃ owners key,
        TaskHasOwners work occurrence owners
        ∧ key ∈ owners
        ∧ ¬GroupRecordInvalidated work (before.map Prod.snd) key := by
  let queue := State.initialize (Work.fromExecution work)
  obtain ⟨earlier, _, _, _, node, _, _, _, sourcePrefix, priorValid, _, _, ledger,
    found, healthy⟩ := createWorkQueue_eligibleObjectFailureCuts_split valid started split
  have accepted := queue.batchesStarted_acceptsBatch batches
    (by rwa [← inputsStarted_eq_batchesStarted])
  have beforePrefix : (earlier.filterMap Prod.fst).IsPrefix batches.flatten :=
    (List.prefix_append _ _).trans sourcePrefix
  have boundary := missing _ beforePrefix
  obtain ⟨suffix, inputEq⟩ := beforePrefix
  rw [← inputEq] at accepted
  have priorAccepted := State.acceptsBatch_prefix accepted
  have bookkeeping := (createWorkQueue_pendingAccounting work).replayGraphEvents
    (before := []) generated (earlier.filterMap Prod.fst) priorValid priorAccepted
  obtain ⟨nodeMember, occurrenceEq⟩ := State.taskNode?_some found
  obtain ⟨⟨_, payload, producer, _, task⟩, _⟩ :=
    bookkeeping.matching node.task (bookkeeping.started node nodeMember)
  obtain ⟨owner, contributes, guard⟩ := State.taskHasHealthyOwner_iff.mp healthy
  refine ⟨node.task.groups.map Execution.DeliveryNode.key, owner.key,
    ⟨producer, payload, occurrenceEq ▸ task⟩,
    List.mem_map.mpr ⟨owner, contributes, rfl⟩, ?_⟩
  have safe := createWorkQueue_replayGraphEvents_groupIsHealthy_recordUninvalidated
    generated priorValid priorAccepted boundary guard
  intro invalid
  apply safe (invalid.mono ?_)
  intro occurrence member
  rw [← ledger, List.mem_reverse]
  exact member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
