import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupNoticeAncestorAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupNoticeCarrierCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupSourceEventFrames

/-! Leading item notices account for their defer ancestry before the recursive drain. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

/-- An item-carried group notice's ancestor contributors are published on the same matching.
Witness: the joint raw/atomic carrier bridge preserves the strict object count. Interpret
that prefix with the original buffered closure ledger, without choosing new labels.
-/
theorem startup_itemGroupNoticeAncestor_objectContributor_published
    {work inputs w index owner values groups streams child dependencies ref address owners
      producer payload}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    : Published w.matching (w.events.take index) (.executionGroup address) := by
  obtain ⟨published, batched, _, interpret, _⟩ := ledger
  obtain ⟨earlier, batch, later, fifo, stream, items, tail, split, batchEq,
    active, notices, count⟩ := Witness.startup_itemNotice_sourceBoundary startup started history
      selected
      (List.mem_append_left _ noticed)
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := generated.startup_ownerPublicationFrame_atBatchPrefix canonical startup matched
    valid started batched
    earlier batch later fifo split ⟨.streamItems stream items :: tail, batchEq.symm⟩
  let initial := (State.initialize (Work.fromExecution work) startup)
  let boundary := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let current := boundary.replayGraphEvents fifo available
  let offset := ((initial.rawBatches earlier).2.flatMap WorkQueueEvent.objectValues).length
  let fifoCount := ((boundary.rawEventReplay fifo available).2.flatMap
    WorkQueueEvent.objectValues).length
  let batchCount := ((boundary.handleGraphEvents batch).2.flatMap
    WorkQueueEvent.objectValues).length
  have batchCovered := (State.BatchClosuresCovered.atBatch earlier batch later
    (split ▸ batched)).1
  have atFifo := State.ReplayClosuresCovered.afterPrefix fifo
    (.streamItems stream items :: tail)
    (show boundary.ReplayClosuresCovered (fifo ++ .streamItems stream items :: tail)
      ((published.drop offset).take batchCount) available from batchEq ▸ batchCovered)
  have handlerCovered := State.ReplayClosuresCovered.prefix [.streamItems stream items] tail atFifo
  obtain ⟨sourceValid, _, _, _⟩ := generated.startup_uncancelledFrames_atBatchEvent startup
    matched canonical
    valid started earlier batch later fifo (.streamItems stream items) tail split batchEq
  have licensed : ∀ occurrence errors, (occurrence, errors) ∈ available →
      (GraphEvent.taskFailure occurrence errors).MatchesWork work := by
    intro occurrence errors member
    obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    apply valid.eachMatches
    rw [split, List.flatten_append, List.flatten_cons]
    exact List.mem_append_right _ (List.mem_append_left _ received)
  have activeCache : (current.cacheTaskFailures available).rootStreams.contains stream.ref
      = true := by
    have same := congrArg State.rootStreams (current.cacheTaskFailures_frame available)
    rw [show (current.cacheTaskFailures available).rootStreams = current.rootStreams from same]
    exact active
  obtain ⟨value, delivered⟩ := frame.streamItems_leadingAncestor_contributor_before generated
    canonical sourceValid active available licensed handlerCovered activeCache
    (notices ▸ noticed) known ancestor task contributes
  apply interpret index (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
    (.executionGroup address)
  rw [count, ← List.map_take]
  exact List.mem_map.mpr ⟨(_, value), delivered, rfl⟩

/-- An item-carried group notice accounts for all tasks belonging to each defer ancestor.
Witness: object contributors precede the item handler, and execution-generated roles
exclude stream contributors. This holds for arbitrary failure cuts, without cancellation.
-/
theorem startup_itemGroupNoticeAncestor_nodeAccounted
    {work inputs w index owner values groups streams child dependencies ref}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies) (failures : FailureCuts)
    : NodeAccounted work w.matching (w.events.take index) failures ref := by
  intro occurrence owners ⟨producer, payload, task⟩ contributes
  cases occurrence with
  | executionGroup address =>
      exact Or.inr (startup_itemGroupNoticeAncestor_objectContributor_published generated startup
        matched valid started
        history ledger selected noticed known ancestor task contributes)
  | item address ordinal =>
      obtain ⟨stream, items, enclosing, result, children, located, _, sameOwners, _⟩ := task
      rw [sameOwners] at contributes
      exact False.elim (generated.groupRecord_ancestor_ne_stream known ancestor (.stream located)
        (List.mem_singleton.mp contributes))

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
