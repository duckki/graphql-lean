import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedStreamRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationReplay

/-! Successful storage and failure handlers conserve actual buffered stream releases. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The new value is protected from immediately after its complete child attachment
-----------------------------------------------------------------------------------------

private theorem storedValues_successGroupFold {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (groups : List Execution.DeliveryNode)
    : (groups.foldl successGroupStep (queue, [], {})).1.StoredValuesSatisfy property := by
  have loop (more : List Execution.DeliveryNode)
      (acc : State × List Execution.WorkQueueEvent × NewWork)
      (known : acc.1.StoredValuesSatisfy property)
      : (more.foldl successGroupStep acc).1.StoredValuesSatisfy property := by
    induction more generalizing acc with
    | nil => exact known
    | cons group rest ih =>
        obtain ⟨current, events, released⟩ := acc
        dsimp only [List.foldl_cons, successGroupStep]
        split
        · exact ih _ known
        · split
          · exact ih _ ((known.putGroupNode _).finishGroupSuccess _)
          · exact ih _ (known.putGroupNode _)
  exact loop groups (queue, [], {}) stored

/-- Successful processing releases or retains each stream attached in its prepared state.
Witness: unsettled memberships justify the newly stored value; complete integration,
the original owner fold, activation, and draining preserve the same producer and links.
-/
theorem State.taskSuccess_preparedBufferedStreams {queue : State} {work settled}
    (accounted : queue.PendingAccounting work settled) (links : queue.StoredTaskLinks)
    (inventory : queue.ChildStreamInventory) {occurrence result node}
    (found : queue.taskNode? occurrence = some node)
    (fresh : occurrence ∉ settled)
    (available : List (Occurrence × Nat) := [])
    (clean
      : queue.StoredValuesSatisfy
          (fun occurrence _ => ∀ errors, (occurrence, errors) ∉ available) := by
        intro node member value stored errors impossible; cases impossible)
    (own : ∀ errors, (occurrence, errors) ∉ available := by
      intro errors impossible; cases impossible)
    : let prepared :=
        ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      prepared.BufferedStreamsConserved
        (queue.taskSuccess occurrence result available).2.1
        (queue.taskSuccess occurrence result available).1 := by
  let stored := queue.putTaskNode { node with value := some result.value }
  let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
  let released := node.task.groups.foldl successGroupStep (prepared, [], {})
  have known := State.taskNode?_some found
  have registered := accounted.started node known.1
  have taskLinks := accounted.links node.task registered (known.2.symm ▸ fresh)
  have installed := links.putTaskNode { node with value := some result.value }
    (fun _ => taskLinks)
  have started := accounted.started.putTaskNode
    { node with value := some result.value } registered
  have preparedLinks := installed.maybeIntegrateWork accounted.refs accounted.taskGroups
    started result.work (some occurrence)
  have initialInventory := inventory node known.1
  have preparedInventory := (inventory.putTaskNode { node with value := some result.value }
    initialInventory.1 initialInventory.2).maybeIntegrateWork result.work (some occurrence)
  have storedRefs : stored.GroupRefsUnique := accounted.refs
  have fold := State.successGroupFold_bufferedStreamsConserved
    (storedRefs.maybeIntegrateWork result.work (some occurrence)) preparedLinks
    preparedInventory node.task.groups
  have cleanPrepared := (clean.putTaskNode { node with value := some result.value }
    (fun _ _ => known.2 ▸ own)).maybeIntegrateWork result.work (some occurrence)
  have cleanFolded := storedValues_successGroupFold cleanPrepared node.task.groups
  have activation := State.BufferedStreamsConserved.of_emptyOwners
    (released.1.startNewWork_storedOwnersConserved released.2.2 available cleanFolded) []
  have first := fold.append activation
    (State.startNewWork_cancelledGroups_subset _ _ available)
  simp only [List.append_nil] at first
  have activeLinks := links.taskSuccess_release accounted occurrence result node found fresh
    available
  have foldedInventory := preparedInventory.successGroupFold node.task.groups [] {}
  have activeInventory := foldedInventory.startNewWork released.2.2 available
  have final := first.append
    (State.drainReadyGroups_bufferedStreamsConserved activeLinks activeInventory available
      (cleanFolded.startNewWork released.2.2 available))
    (State.drainReadyGroups_go_cancelledGroups_subset _ _ (available := available))
  rw [queue.taskSuccess_eq occurrence result node found available]
  simpa only [stored, prepared, released] using final

-----------------------------------------------------------------------------------------
-- Fresh source identity prevents overwriting an earlier buffered producer
-----------------------------------------------------------------------------------------

/-- A fresh successful input conserves streams of all earlier buffered values.
Witness: source provenance excludes the new identity from old stored nodes. Preparation
retains their exact lookups; the prepared handler theorem then covers every later release.
-/
theorem State.taskSuccess_bufferedStreamsConserved {queue : State} {work settled before}
    (accounted : queue.PendingAccounting work settled) (links : queue.StoredTaskLinks)
    (inventory : queue.ChildStreamInventory)
    (sources : queue.StoredValuesSatisfy (ObjectValueFrom before))
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (occurrence : Occurrence) (result : TaskResult)
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    (available : List (Occurrence × Nat) := [])
    (clean
      : queue.StoredValuesSatisfy
          (fun occurrence _ => ∀ errors, (occurrence, errors) ∉ available) := by
        intro node member value stored errors impossible; cases impossible)
    (own : ∀ errors, (occurrence, errors) ∉ available := by
      intro errors impossible; cases impossible)
    : queue.BufferedStreamsConserved (queue.taskSuccess occurrence result available).2.1
        (queue.taskSuccess occurrence result available).1 := by
  have different {task buffered value} (lookup : queue.taskNode? task = some buffered)
      (stored : buffered.value = some value) : occurrence ≠ task := by
    intro same
    have known := State.taskNode?_some lookup
    exact fresh.2.2.1 occurrence List.mem_cons_self
      (same.symm ▸ known.2 ▸ (sources buffered known.1 value stored).identity)
  cases found : queue.taskNode? occurrence with
  | none =>
      simpa only [State.taskSuccess, found] using State.BufferedStreamsConserved.refl queue
  | some node =>
      apply (State.taskSuccess_preparedBufferedStreams accounted links inventory found
        (fun member => fresh.2.2.1 occurrence List.mem_cons_self (included member))
        available clean own).of_lookups
      · intro task buffered value lookup stored
        have retained := State.putTaskNode_lookup_other lookup
          { node with value := some result.value }
          ((State.taskNode?_some found).2 ▸ different lookup stored)
        exact State.maybeIntegrateWork_lookup_other retained result.work (some occurrence)
          (fun same => different lookup stored (Option.some.inj same))
      · exact State.maybeIntegrateWork_includesRefs
          (queue.putTaskNode { node with value := some result.value })
          result.work (some occurrence)

/-- Fresh failure cannot discard an older buffered child while its contributor survives.
Witness: exact empty-publication owner conservation from source provenance and retained
cancellation history. Failed input produces no successful release branch of its own.
-/
theorem State.taskFailure_bufferedStreamsConserved {queue : State} {before}
    (sources : queue.StoredValuesSatisfy (ObjectValueFrom before))
    (occurrence : Occurrence) (errors : Nat)
    (fresh : (GraphEvent.taskFailure occurrence errors).Fresh before)
    : queue.BufferedStreamsConserved (queue.taskFailure occurrence errors).2
        (queue.taskFailure occurrence errors).1 := by
  have inventory : queue.PublicationInventory (ObjectValueFrom before) [] :=
    ⟨by simp, by simp, sources.mono (fun _ _ known => ⟨known, by simp⟩)⟩
  exact .of_emptyOwners
    (inventory.taskFailure_storedOwnersConserved occurrence errors fresh) _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
