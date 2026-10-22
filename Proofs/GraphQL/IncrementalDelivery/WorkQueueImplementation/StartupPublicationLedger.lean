import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReplayPublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedStreamRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawValueLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReplay

/-! Publication ledgers follow actual normalized FIFO dispatch from arbitrary initial state. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Source-valid replay retains one exact ledger for buffered/prepared closures and
stream-producer release. Pending startup controls stay in the actual input queue, and
normalization retains each supplied batch boundary. -/
theorem State.runNormalized_startup_bufferedCoverage {work : Execution.Work}
    (queue : State) (generated : ExecutedWork work)
    (inventory : queue.PublicationInventory (ObjectValueFrom []) [])
    (accounted : queue.PendingAccounting work []) (links : queue.StoredTaskLinks)
    (settled : queue.ChildStreamsSettled) (children : queue.ChildStreamsMatchWork work)
    (memberships : queue.GroupMembershipOrder) (cancelled : queue.CancellationsRetired)
    (batches : List (List GraphEvent)) (valid : ValidGraphEvents work batches.flatten)
    (started : queue.batchesStarted batches = true)
    : ∃ published : List ObjectPublication,
        published.map Prod.snd
          = (queue.runNormalized batches).2.flatten.flatMap normalizedObjectValues
        ∧ (queue.runNormalized batches).1.PublicationInventory
            (ObjectValueFrom batches.flatten) published
        ∧ queue.BatchClosuresCovered batches published
        ∧ NormalizedStreamReleasePublications work published
            (queue.runNormalized batches).2.flatten
        ∧ published.map Prod.snd = queue.batchedObjectValues batches := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (before : List GraphEvent) (published : List ObjectPublication)
      (inventory : acc.1.PublicationInventory (ObjectValueFrom before) published)
      (accounted : acc.1.PendingAccounting work (GraphEvent.taskSettlements before))
      (links : acc.1.StoredTaskLinks) (settled : acc.1.ChildStreamsSettled)
      (children : acc.1.ChildStreamsMatchWork work)
      (memberships : acc.1.GroupMembershipOrder) (cancelled : acc.1.CancellationsRetired)
      (values : published.map (fun publication => publication.2)
        = acc.2.2.flatten.flatMap normalizedObjectValues)
      (supported : NormalizedStreamReleasePublications work published acc.2.2.flatten)
      (valid : ValidGraphEvents work (before ++ more.flatten))
      (accepted : acc.1.batchesStarted more = true)
      : ∃ added : List ObjectPublication,
          (published ++ added).map (fun publication => publication.2)
            = (more.foldl normalizedStep acc).2.2.flatten.flatMap normalizedObjectValues
          ∧ (more.foldl normalizedStep acc).1.PublicationInventory
              (ObjectValueFrom (before ++ more.flatten)) (published ++ added)
          ∧ acc.1.BatchClosuresCovered more added
          ∧ NormalizedStreamReleasePublications work (published ++ added)
              (more.foldl normalizedStep acc).2.2.flatten
          ∧ added.map Prod.snd = acc.1.batchedObjectValues more := by
    induction more generalizing acc before published with
    | nil =>
        refine ⟨[], ?_, ?_, trivial, ?_, rfl⟩
        · simpa only [List.append_nil, List.foldl_nil] using values
        · simpa only [List.flatten_nil, List.append_nil, List.foldl_nil] using inventory
        · simpa only [List.append_nil, List.foldl_nil] using supported
    | cons batch rest ih =>
        obtain ⟨running, batchAccepted, restStarted⟩ :=
          acc.1.batchesStarted_cons batch rest accepted
        have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
          ⟨rest.flatten, by simp only [List.flatten_cons, List.append_assoc]⟩
        have firstValid := valid.prefix earlier
        obtain ⟨first, firstValues, current, firstCoverage, firstStreams, firstOrder⟩ :=
          inventory.handleGraphEvents_bufferedCoverage generated accounted links settled
            children batch firstValid running batchAccepted memberships cancelled
        have nextInventory : (normalizedStep acc batch).1.PublicationInventory
            (ObjectValueFrom (before ++ batch)) (published ++ first) := by
          rw [normalizedStep_queue]
          exact current
        have nextAccounting : (normalizedStep acc batch).1.PendingAccounting work
            (GraphEvent.taskSettlements (before ++ batch)) := by
          rw [normalizedStep_queue]
          exact accounted.handleGraphEvents generated batch firstValid running batchAccepted
        have nextLinks : (normalizedStep acc batch).1.StoredTaskLinks := by
          rw [normalizedStep_queue]
          exact links.handleGraphEvents accounted generated batch firstValid running batchAccepted
        have nextSettled : (normalizedStep acc batch).1.ChildStreamsSettled := by
          rw [normalizedStep_queue]
          exact settled.handleGraphEvents batch
        have nextChildren : (normalizedStep acc batch).1.ChildStreamsMatchWork work := by
          rw [normalizedStep_queue]
          exact children.handleGraphEvents batch (fun event member =>
            firstValid.event_matches (List.mem_append_right before member))
        have nextMemberships : (normalizedStep acc batch).1.GroupMembershipOrder := by
          rw [normalizedStep_queue]
          exact memberships.handleGraphEvents batch
        have nextCancellations : (normalizedStep acc batch).1.CancellationsRetired := by
          rw [normalizedStep_queue]
          exact cancelled.handleGraphEvents accounted.liveGroups accounted.taskGroups batch
            (fun event member => firstValid.event_matches (List.mem_append_right before member))
        have nextValues : (published ++ first).map (fun publication => publication.2)
            = (normalizedStep acc batch).2.2.flatten.flatMap normalizedObjectValues := by
          rw [normalizedStep_objectValues, List.map_append, values]
          exact congrArg (acc.2.2.flatten.flatMap normalizedObjectValues ++ ·) firstValues
        have nextSupport : NormalizedStreamReleasePublications work (published ++ first)
            (normalizedStep acc batch).2.2.flatten := by
          rw [normalizedStep_flatten]
          exact supported.append (firstStreams.normalizeBatch acc.2.1) values
        obtain ⟨later, finalValues, finalInventory, finalCoverage, finalSupport, rawValues⟩ :=
          ih _ (before ++ batch) (published ++ first) nextInventory nextAccounting nextLinks
            nextSettled nextChildren nextMemberships nextCancellations nextValues nextSupport
            (by simpa only [List.flatten_cons, List.append_assoc] using valid)
            (by rwa [normalizedStep_queue])
        refine ⟨
          first ++ later,
          ?_,
          ?_,
          .cons firstValues firstCoverage firstOrder ?_,
          ?_,
          ?_
        ⟩
        · simpa only [List.append_assoc, List.foldl_cons] using finalValues
        · simpa only [List.flatten_cons, List.append_assoc, List.foldl_cons]
            using finalInventory
        · rwa [normalizedStep_queue] at finalCoverage
        · simpa only [List.append_assoc, List.foldl_cons] using finalSupport
        · rw [List.map_append, firstValues, rawValues, normalizedStep_queue]
          rfl
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  have replay := loop batches (queue, publisher, []) [] [] inventory accounted links
    settled children memberships cancelled rfl (.nil work) valid started
  have runner : queue.runNormalized batches =
      ((batches.foldl normalizedStep (queue, publisher, [])).1,
        (batches.foldl normalizedStep (queue, publisher, [])).2.2) := rfl
  rw [runner]
  simpa only [List.nil_append] using replay

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
