import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation
import Tests.GraphQL.IncrementalDelivery.WorkSchedulerStreamAvailability

/-! Fresh stream-root activation after successful group release and task failure. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerStreamRoots
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- The mixed continuation preserves healthy counters, owners, and retired ancestry.
Witness: current joint replay accounting on the checked success/failure/item history.
-/
theorem continuation_accounting
    : ∃ parents,
        ((State.initialize (Work.fromExecution work)).runNormalized
          (before ++ [[second]])).1.OwnerAncestry
          work parents (before ++ [[second]]).flatten := by
  obtain ⟨parents, _, ledger⟩ := generated.runNormalized_ownerAncestry
    (before ++ [[second]]) (by simpa using continuation_valid) inputs_started.2
  exact ⟨parents, ledger⟩

-----------------------------------------------------------------------------------------
-- The new stream root theorem applies past successful settlement
-----------------------------------------------------------------------------------------

/-- Both earlier groups have closed, while the next item activates its two fresh roots.
Witness: execute the actual prefix and stream handler; the new-root conclusion is not
vacuous, and no task-success event is excluded from the prefix. -/
theorem activated_roots
    : queue.rootGroups = []
      ∧ (queue.streamItems stream [item 1]).1.rootGroups
        = [(successGroup 1).key, (failureGroup 1).key] := by
  constructor <;> cbv

/-- Next-item pruning cannot promote descendants after success and failure.
Witness: task-supported fresh-root integration, without any prior pending-count ledger. -/
theorem no_promotion_after_success
    : let integrated := queue.maybeIntegrateWork (item 1).work
      (integrated.1.pruneEmptyGroups integrated.2.newGroups).1 = integrated.1
      ∧ (integrated.1.pruneEmptyGroups integrated.2.newGroups).2.Subset
          integrated.2.newGroups :=
  State.maybeIntegrateWork_prune_freshRoots
    (createWorkQueue_runNormalized_groupKeysUnique _ _) (item 1).work
    (by cbv; simp)

/-- New item-local groups are independent of the first item's failed contributor.
Witness: generated invalidation flattens to the one recorded failed task; the second
item's descriptors have distinct keys and no defer ancestors.
-/
private theorem next_group_healthy {node producer}
    (known : NodeAt work node .group [] producer)
    (different : node.key ≠ (failureGroup 0).key)
    : ¬GroupInvalidated work [failedTask] node.key := by
  intro failure
  obtain ⟨occurrence, owners, owner, task, member, contributes, related⟩ :=
    (generated.groupInvalidated_iff known).mp failure
  have same := List.mem_singleton.mp member
  subst occurrence
  obtain ⟨birth, payload, taskKnown⟩ := task
  have ownersEq := (taskKnown.unique failureKnown).1
  rw [ownersEq] at contributes
  have ownerEq := List.mem_singleton.mp contributes
  have nodeEq := List.mem_singleton.mp related
  exact different (nodeEq.symm.trans ownerEq)

/-- Both new active roots are healthy, not merely available registration keys.
Witness: exact root activation and the independent second-item descriptors.
-/
theorem new_roots_healthy
    : (queue.streamItems stream [item 1]).1.RootGroupsHealthy work [failedTask] := by
  intro key active
  rw [activated_roots.2] at active
  rcases List.mem_cons.mp active with same | last
  · subst key
    apply next_group_healthy (different := by decide)
    exact ⟨[0, 0, 1, 1, 1, 0], [⟨successGroup 1, []⟩], _, _, _, [],
      ⟨successGroup 1, []⟩, by cbv, by simp, rfl, rfl⟩
  · have same := List.mem_singleton.mp last
    subst key
    apply next_group_healthy (different := by decide)
    exact ⟨[0, 0, 1, 1, 1, 1, 0], [⟨failureGroup 1, []⟩], _, _, _, [],
      ⟨failureGroup 1, []⟩, by cbv, by simp, rfl, rfl⟩

-----------------------------------------------------------------------------------------
-- Failed-owner retirement and live-group health after the complete continuation
-----------------------------------------------------------------------------------------

/-- The earlier failed owner's node remains absent when the next item adds fresh groups.
Witness: evaluate the actual continuation's lookup after adding the second item. -/
theorem failed_owner_stays_absent
    : ((State.initialize (Work.fromExecution work)).runNormalized
        (before ++ [[second]])).1.groupNode?
        (failureGroup 0).key
      = none := by
  cbv

/-- A genuinely live, ancestor-free group is healthy beyond earlier success and failure.
Witness: its structural descriptor and the independently failed first-item task. -/
theorem live_group_healthy_after_continuation
    : ¬GroupInvalidated work [failedTask] (successGroup 1).key := by
  have known : NodeAt work (successGroup 1) .group [] (some (item 1).occurrence) := by
    refine ⟨[0, 0, 1, 1, 1, 0], [⟨successGroup 1, []⟩], (successGroup 1).path,
      .ok (data 1, 0), .combine .empty .empty, [], ⟨successGroup 1, []⟩,
      ?_, List.mem_cons_self, rfl, rfl⟩
    cbv
  exact next_group_healthy known (by decide)

-----------------------------------------------------------------------------------------
-- Item payloads appear once across separate arrivals and multi-item arrivals
-----------------------------------------------------------------------------------------

/-- The two equal item payloads have distinct sources despite intervening success/failure.
Witness: the normalized runner's exact item-source theorem, applied to the valid started
continuation. The two inputs are not collapsed merely because their object data agree. -/
theorem separate_items_once
    : ∃ publications : List ItemPublication,
        (publications.map Prod.fst).Nodup
        ∧ publications.map Prod.snd
          = ((State.initialize (Work.fromExecution work)).runNormalized
              (before ++ [[second]])).2.flatten.flatMap
              normalizedItemValues
        ∧ publications
          = [
            ((item 0).occurrence, stream, ⟨.object [], 0⟩),
            ((item 1).occurrence, stream, ⟨.object [], 0⟩)
          ] := by
  have valid : ValidGraphEvents work (before ++ [[second]]).flatten := by
    simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      using continuation_valid
  obtain ⟨unique, output, _⟩ :=
    createWorkQueue_runNormalized_itemSources valid inputs_started.2
  exact ⟨_, unique, output, rfl⟩

/-- One multi-item arrival publishes both equal payloads once and in source order.
Witness: the same general normalized item-source theorem as separate arrivals; the
source occurrences remain distinct even within one queue event. -/
theorem together_items_once
    : ∃ publications : List ItemPublication,
        (publications.map Prod.fst).Nodup
        ∧ publications.map Prod.snd
          = ((State.initialize (Work.fromExecution work)).runNormalized
              [[.streamItems stream [item 0, item 1]]]).2.flatten.flatMap
              normalizedItemValues
        ∧ publications
          = [
            ((item 0).occurrence, stream, ⟨.object [], 0⟩),
            ((item 1).occurrence, stream, ⟨.object [], 0⟩)
          ] := by
  obtain ⟨unique, output, _⟩ := createWorkQueue_runNormalized_itemSources
    (batches := [[.streamItems stream [item 0, item 1]]])
    together_valid_started.1 together_valid_started.2
  exact ⟨_, unique, output, rfl⟩

-----------------------------------------------------------------------------------------
-- One matching spans object publications, item publications, and intervening closures
-----------------------------------------------------------------------------------------

/-- Mixed output has one occurrence matching, with every value fresh at its output index.
Witness: the general matching theorem for item zero, successful and failed child tasks,
and item one. Control events keep their positions but consume no publication occurrence.
-/
theorem mixed_publication_matching
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized
          (before ++ [[second]])).2
      ∃ matching : PublicationMatching,
        WorkBatching (outputs.flatten.flatMap publicationAtoms) outputs
        ∧ ∀ index event,
            (outputs.flatten.flatMap publicationAtoms)[index]? = some event
            → IsValue event
            → PublicationAt work (matching index) event
              ∧ ¬Published matching
                  ((outputs.flatten.flatMap publicationAtoms).take index)
                  (matching index) := by
  have valid : ValidGraphEvents work (before ++ [[second]]).flatten := by
    simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      using continuation_valid
  exact createWorkQueue_runNormalized_publicationMatching valid inputs_started.2

/-- Splitting one multi-item output preserves its exact notice lists and batch boundary.
Witness: evaluation of the actual output and the general value-grouping construction;
all four child notices remain attached to the final singleton item atom.
-/
theorem together_atomic_batching
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized
          [[.streamItems stream [item 0, item 1]]]).2
      outputs.flatten.flatMap publicationAtoms
        = [
          .streamValues stream [⟨.object [], 0⟩] [] [],
          .streamValues stream [⟨.object [], 0⟩]
            [successGroup 0, failureGroup 0, successGroup 1, failureGroup 1] []
        ]
      ∧ WorkBatching (outputs.flatten.flatMap publicationAtoms) outputs := by
  refine ⟨?_, createWorkQueue_runNormalized_atomicBatching
    (batches := [[.streamItems stream [item 0, item 1]]]) together_valid_started.1⟩
  cbv

/-- Equal item payloads retain their source-occurrence order under the joint matching.
Witness: the actual runner annotation theorem preserves the input item sequence, not
merely a permutation or a duplicate-free set of possible source occurrences.
-/
theorem together_matching_keeps_item_order
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized
          [[.streamItems stream [item 0, item 1]]]).2
      ∃ annotated : List PublicationAnnotation,
        annotated.map Prod.snd = outputs.flatten.flatMap publicationAtoms
        ∧ (annotated.filterMap Prod.fst).Nodup
        ∧ annotated.filterMap itemAnnotation = [(item 0).occurrence, (item 1).occurrence]
        ∧ ∀ entry ∈ annotated, AnnotationMatches work entry := by
  exact createWorkQueue_runNormalized_annotations
    (batches := [[.streamItems stream [item 0, item 1]]])
    together_valid_started.1 together_valid_started.2

-----------------------------------------------------------------------------------------
-- The same output matching respects stream predecessors in either arrival shape
-----------------------------------------------------------------------------------------

/-- Earlier items are published first, both within one arrival and across child failures.
Witness: the ordered matching theorem for generated work, retaining exact source payloads,
freshness, and the existing batch witness under the same occurrence matching.
-/
theorem ordered_publication_matching
    : ∀ batches ∈ [before ++ [[second]], [[.streamItems stream [item 0, item 1]]]],
        let outputs :=
          ((State.initialize (Work.fromExecution work)).runNormalized batches).2
        ∃ matching : PublicationMatching,
          WorkBatching (outputs.flatten.flatMap publicationAtoms) outputs
          ∧ ∀ index event,
              (outputs.flatten.flatMap publicationAtoms)[index]? = some event
              → IsValue event
              → PublicationAt work (matching index) event
                ∧ ¬Published matching
                    ((outputs.flatten.flatMap publicationAtoms).take index)
                    (matching index)
                ∧ ∀ address first second,
                    matching index = .item address second
                    → first < second
                    → Published matching
                        ((outputs.flatten.flatMap publicationAtoms).take index)
                        (.item address first) := by
  intro batches member
  have choices : batches = before ++ [[second]]
      ∨ batches = [[.streamItems stream [item 0, item 1]]] := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  have valid : ValidGraphEvents work batches.flatten := by
    rcases choices with rfl | rfl
    · simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil]
        using continuation_valid
    · exact together_valid_started.1
  have started : inputsStarted work batches = true := by
    rcases choices with rfl | rfl
    · exact inputs_started.2
    · exact together_valid_started.2
  exact createWorkQueue_runNormalized_orderedMatching generated valid started

-----------------------------------------------------------------------------------------
-- Duplicate raw stream keys explain the generated-work premise in the order theorem
-----------------------------------------------------------------------------------------

private def duplicateStreamWork : Execution.Work :=
  .combine (.stream stream [(.ok (.null, 0), .empty)])
    (.stream stream [(.ok (.null, 0), .empty), (.ok (.null, 0), .empty)])

private def leftItem : StreamItem :=
  { occurrence := .item [0] 0, value := { item := .null } }

private def rightItem : StreamItem :=
  { occurrence := .item [1] 1, value := { item := .null } }

private def duplicateStreamInputs : List GraphEvent :=
  [.streamItems stream [leftItem], .streamItems stream [rightItem]]

/-- Raw duplicate keys let one stream's first item advance the other stream's source cursor.
Witness: both inputs match their fixed outcomes and satisfy the existing key-based source
readiness and start checks. This raw work is deliberately not claimed to be generated.
-/
theorem duplicate_stream_inputs_valid_started
    : ValidGraphEvents duplicateStreamWork duplicateStreamInputs
      ∧ inputsStarted duplicateStreamWork [duplicateStreamInputs] = true := by
  have leftLocated : Located duplicateStreamWork [0]
      (.stream stream [(.ok (.null, 0), .empty)]) none [] := by cbv
  have rightLocated : Located duplicateStreamWork [1]
      (.stream stream [(.ok (.null, 0), .empty), (.ok (.null, 0), .empty)]) none [] := by cbv
  have firstValid : ValidGraphEvents duplicateStreamWork [.streamItems stream [leftItem]] := by
    refine .append .nil ?_ (by simp [GraphEvent.Fresh, GraphEvent.identities]) ?_
    · intro item member
      have same := List.mem_singleton.mp member
      subst item
      exact ⟨[stream.key], none,
        ⟨stream, _, [], .ok (.null, 0), .empty, leftLocated, rfl, rfl, rfl⟩, by cbv⟩
    · exact ⟨[0], _, none, [], leftLocated, by simp, by simp,
        (by intro source impossible; cases impossible), by cbv⟩
  constructor
  · refine .append firstValid ?_ ?_ ?_
    · intro item member
      have same := List.mem_singleton.mp member
      subst item
      exact ⟨[stream.key], none,
        ⟨stream, _, [], .ok (.null, 0), .empty, rightLocated, rfl, rfl, rfl⟩, by cbv⟩
    · simp [GraphEvent.Fresh, GraphEvent.identities, leftItem, rightItem]
    · exact ⟨[1], _, none, [], rightLocated, by simp, by simp [GraphEvent.identities],
        (by intro source impossible; cases impossible), by cbv⟩
  · cbv

/-- The raw second stream supplies ordinal one without ever supplying its ordinal zero.
Witness: evaluation of the source identity sequence, not a failure of the generated-work
order theorem. -/
theorem duplicate_stream_missing_predecessor
    : .item [1] 1
        ∈ (duplicateStreamInputs.flatMap GraphEvent.itemPublications).map Prod.fst
      ∧ .item [1] 0
        ∉ (duplicateStreamInputs.flatMap GraphEvent.itemPublications).map Prod.fst := by
  simp [duplicateStreamInputs, GraphEvent.itemPublications, leftItem, rightItem]

/-- The counterexample cannot be produced by execution, because it allocates a key twice.
Witness: generated stream-allocation uniqueness contradicts its repeated allocation list.
-/
theorem duplicate_stream_not_generated : ¬ExecutedWork duplicateStreamWork := by
  intro generated
  have unique := generated.streamKeysUnique
  simp [duplicateStreamWork, Semantics.GeneralScheduling.streamAllocationKeys] at unique

-----------------------------------------------------------------------------------------
-- Older counter equations are genuinely unnecessary for the local pruning result
-----------------------------------------------------------------------------------------

private def stale : State :=
  {
    groupNodes :=
      [{
        group := ⟨{ key := 99, path := [] }, none⟩
        tasks := [.executionGroup []]
        pending := 0
      }]
    registeredGroups := [99]
  }

/-- This deliberately raw old state violates initial pending accounting.
Witness: its existing group has one unsettled task but zero pending; it is not claimed
to arise from a valid source replay. -/
theorem stale_counters : ¬stale.PendingTracks [] := by
  intro counts
  have bad := counts _ List.mem_cons_self
  simp [GroupNode.PendingTracks, unsettledCount] at bad

/-- Even inconsistent old counters cannot empty a newly registered, supported root.
Witness: the general local no-pruning theorem; no global count equation is assumed. -/
theorem fresh_roots_ignore_stale_counters
    : let integrated := stale.maybeIntegrateWork (item 1).work
      (integrated.1.pruneEmptyGroups integrated.2.newGroups).1 = integrated.1
      ∧ (integrated.1.pruneEmptyGroups integrated.2.newGroups).2.Subset
          integrated.2.newGroups :=
  State.maybeIntegrateWork_prune_freshRoots
    (by change ([99] : List Nat).Nodup; decide)
    (item 1).work
    (by cbv; simp)

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerStreamRoots
