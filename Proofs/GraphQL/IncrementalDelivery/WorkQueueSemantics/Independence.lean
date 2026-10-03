import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.PublicationExtension

/-! Conservative local independence, without identifying ordered wire observations. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Distinct already-ready object publications preserve each other's enabledness
-----------------------------------------------------------------------------------------

/-- Assigning a fresh final value preserves readiness of any different ready task.
Witness: split publication lookup at the appended index; old prerequisites persist.
-/
theorem CanPublish.after_other_value
    {work matching events failed occurrence producer other}
    (ready : CanPublish work matching events failed occurrence producer)
    (bounded : ∀ entry ∈ failed, entry.1 ≤ events.length)
    (distinct : other ≠ occurrence) (event : WorkQueueEvent)
    : CanPublish work (matchNext matching events.length other) (events ++ [event])
        failed occurrence producer := by
  have same := published_matching_eq
    (fun _ earlier => matchNext_before matching other earlier) (events := events)
  have persists {task} (published : Published matching events task)
      : Published (matchNext matching events.length other) (events ++ [event]) task :=
    (same ▸ published).append [event]
  have unchanged : TaskCancelled work
      (matchNext matching events.length other) (events ++ [event]) failed
        = TaskCancelled work matching events failed := by
    rw [(causality_append_eq bounded [event]).2,
      ← taskCancelled_matching_eq (fun _ earlier => matchNext_before matching other earlier)]
  refine ⟨?_, unchanged.symm ▸ ready.2.1,
    fun producerOccurrence equal =>
      persists (ready.2.2.1 producerOccurrence equal), ?_⟩
  · intro published
    rcases published_append_singleton_iff.mp published with old | current
    · exact ready.1 (same.symm ▸ old)
    · exact distinct (by simpa [matchNext] using current.2)
  · cases occurrence with
    | executionGroup => trivial
    | item address index =>
        cases index with
        | zero => trivial
        | succ index => exact persists ready.2.2.2

/-- Object publications change neither notices nor closures, hence no owner choice.
Witness: the pending/completed projections of a group-value event are both empty.
-/
theorem owner_after_object
    {work initial matching events failed owners node carrier values}
    (bounded : ∀ entry ∈ failed, entry.1 ≤ events.length)
    : PublicationOwner work initial matching (events ++ [.groupValues carrier values])
        failed owners node
      ↔ PublicationOwner work initial matching events failed owners node := by
  simp [PublicationOwner, HealthyOpenOwner, OpenOwner, Open, announcedRefs, pendingRefs, completedRefs,
    List.flatMap_append, eventPending, eventCompleted, (causality_append_eq bounded _).1]

/-- Two distinct ready object tasks may publish in this order with the same owners.
Witness: publish the first, transport readiness and owner availability, then the second.
The existential matching records the chosen order without changing earlier entries.
-/
theorem Explains.publish_two_objects
    {work groups streams events matching failures
      first firstOwners firstProducer firstPath firstData firstErrors firstOwner
      second secondOwners secondProducer secondPath secondData secondErrors secondOwner}
    (explained : Explains work groups streams events matching failures)
    (firstKnown
      : TaskAt work first firstOwners firstProducer
          (.object firstPath (.ok (firstData, firstErrors))))
    (secondKnown
      : TaskAt work second secondOwners secondProducer
          (.object secondPath (.ok (secondData, secondErrors))))
    (firstReady : CanPublish work matching events failures first firstProducer)
    (secondReady : CanPublish work matching events failures second secondProducer)
    (firstSelected
      : PublicationOwner work ((groups ++ streams).map DeliveryNode.ref) matching events
          failures firstOwners firstOwner)
    (secondSelected
      : PublicationOwner work ((groups ++ streams).map DeliveryNode.ref) matching events
          failures secondOwners secondOwner)
    (distinct : first ≠ second)
    : ∃ next,
        Explains work groups streams
          (events
            ++ [
              .groupValues firstOwner
                [{ path := firstPath, data := firstData, errors := firstErrors }],
              .groupValues secondOwner
                [{ path := secondPath, data := secondData, errors := secondErrors }]
            ]) next failures
        ∧ (∀ index < events.length, next index = matching index)
        ∧ ∀ occurrence,
            Published next
              (events
                ++ [
                  .groupValues firstOwner
                    [{ path := firstPath, data := firstData, errors := firstErrors }],
                  .groupValues secondOwner
                    [{ path := secondPath, data := secondData, errors := secondErrors }]
                ]) occurrence
            ↔ Published matching events occurrence
              ∨ first = occurrence
              ∨ second = occurrence := by
  let firstEvent := WorkQueueEvent.groupValues firstOwner
    [{path := firstPath, data := firstData, errors := firstErrors}]
  let secondEvent := WorkQueueEvent.groupValues secondOwner
    [{path := secondPath, data := secondData, errors := secondErrors}]
  have step := explained.publish_object firstKnown firstReady firstSelected
  have bounded := fun entry member => explained.2.1.cut_le (entry := entry) member
  have ready := secondReady.after_other_value bounded distinct firstEvent
  have rematched : PublicationOwner work ((groups ++ streams).map DeliveryNode.ref)
      (matchNext matching events.length first) (events ++ [firstEvent])
      failures secondOwners secondOwner := by
    rw [(owner_after_object bounded)]
    simp only [PublicationOwner, HealthyOpenOwner,
      ← nodeFailed_matching_eq (fun _ earlier => matchNext_before matching first earlier)]
    exact secondSelected
  have both := step.publish_object secondKnown ready rematched
  refine ⟨
    matchNext (matchNext matching events.length first)
      (events ++ [firstEvent]).length second,
    by simpa [List.append_assoc, firstEvent, secondEvent] using both,
    ?_,
    ?_
  ⟩
  · intro index earlier
    have beforeNext : index < (events ++ [firstEvent]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [← matchNext_before _ second beforeNext,
      ← matchNext_before matching first earlier]
  intro occurrence
  change Published
    (matchNext (matchNext matching events.length first) (events ++ [firstEvent]).length second)
    (events ++ [firstEvent, secondEvent]) occurrence ↔ _
  rw [show events ++ [firstEvent, secondEvent] =
    (events ++ [firstEvent]) ++ [secondEvent] by simp]
  rw [published_append_singleton_iff,
    ← published_matching_eq (fun _ earlier => matchNext_before _ second earlier),
    published_append_singleton_iff,
    ← published_matching_eq (fun _ earlier => matchNext_before matching first earlier)]
  simp [firstEvent, secondEvent, IsValue, matchNext, or_assoc]

/-- Distinct simultaneously ready object publications commute at the accounting level.
Witness: construct both orders with fresh matching entries; each adds exactly the same
two published occurrences. Notice lists, failures, owners, and the existing prefix are
unchanged; this local lemma does not assert equality of ordered response patches.
-/
theorem Explains.objects_commute
    {work groups streams events matching failures
      first firstOwners firstProducer firstPath firstData firstErrors firstOwner
      second secondOwners secondProducer secondPath secondData secondErrors secondOwner}
    (explained : Explains work groups streams events matching failures)
    (firstKnown
      : TaskAt work first firstOwners firstProducer
          (.object firstPath (.ok (firstData, firstErrors))))
    (secondKnown
      : TaskAt work second secondOwners secondProducer
          (.object secondPath (.ok (secondData, secondErrors))))
    (firstReady : CanPublish work matching events failures first firstProducer)
    (secondReady : CanPublish work matching events failures second secondProducer)
    (firstSelected
      : PublicationOwner work ((groups ++ streams).map DeliveryNode.ref) matching events
          failures firstOwners firstOwner)
    (secondSelected
      : PublicationOwner work ((groups ++ streams).map DeliveryNode.ref) matching events
          failures secondOwners secondOwner)
    (distinct : first ≠ second)
    : let left :=
        WorkQueueEvent.groupValues firstOwner
          [{ path := firstPath, data := firstData, errors := firstErrors }]
      let right :=
        WorkQueueEvent.groupValues secondOwner
          [{ path := secondPath, data := secondData, errors := secondErrors }]
      ∃ forward backward,
        Explains work groups streams (events ++ [left, right]) forward failures
        ∧ Explains work groups streams (events ++ [right, left]) backward failures
        ∧ ∀ occurrence,
            TaskAccounted work forward (events ++ [left, right]) failures occurrence
            ↔ TaskAccounted work backward (events ++ [right, left]) failures
                occurrence := by
  obtain ⟨forward, forwardExplained, forwardMatching, forwardPublications⟩ :=
    explained.publish_two_objects firstKnown secondKnown firstReady secondReady
      firstSelected secondSelected distinct
  obtain ⟨backward, backwardExplained, backwardMatching, backwardPublications⟩ :=
    explained.publish_two_objects secondKnown firstKnown secondReady firstReady
      secondSelected firstSelected (Ne.symm distinct)
  refine ⟨forward, backward, forwardExplained, backwardExplained, ?_⟩
  intro occurrence
  have bounded := fun entry member => explained.2.1.cut_le (entry := entry) member
  simp only [TaskAccounted, forwardPublications, backwardPublications,
    (causality_append_eq bounded _).2,
    taskCancelled_matching_eq forwardMatching, taskCancelled_matching_eq backwardMatching,
    or_comm, or_assoc]

-----------------------------------------------------------------------------------------
-- Notice-free healthy group closures preserve each other's enabledness
-----------------------------------------------------------------------------------------

/-- Closing a different ref without notices preserves a permitted healthy group closure.
Witness: its open ref remains open, and all node-accounting facts persist on extension.
-/
theorem EventAllowed.groupSuccess_after_other
    {work initial matching events failed node other}
    (allowed
      : EventAllowed work initial matching events failed (.groupSuccess node [] []))
    (bounded : ∀ entry ∈ failed, entry.1 ≤ events.length)
    (distinct : other.ref ≠ node.ref)
    : EventAllowed work initial matching (events ++ [.groupSuccess other [] []]) failed
        (.groupSuccess node [] []) := by
  simp only [EventAllowed, nodeFailed_filter (Nat.le_refl _),
    nodeAccounted_filter (Nat.le_refl _)] at allowed ⊢
  refine ⟨allowed.1, ?_, ?_, ?_, by simp [Announcements]⟩
  · simpa [Open, announcedRefs, pendingRefs, completedRefs, List.flatMap_append,
      eventPending, eventCompleted, Ne.symm distinct] using allowed.2.1
  · rw [(causality_append_eq bounded _).1]
    exact allowed.2.2.1
  · exact allowed.2.2.2.1.append [.groupSuccess other [] []]

/-- Distinct notice-free healthy group closures can be appended in either order.
Witness: neither closure disables the other; fixed failure evidence extends unchanged.
Completed-ref membership agrees, but the ordered completion lists need not agree.
-/
theorem Explains.group_closures_commute
    {work groups streams events matching failures left right}
    (explained : Explains work groups streams events matching failures)
    (leftAllowed
      : EventAllowed work ((groups ++ streams).map DeliveryNode.ref) matching
          events failures (.groupSuccess left [] []))
    (rightAllowed
      : EventAllowed work ((groups ++ streams).map DeliveryNode.ref) matching
          events failures (.groupSuccess right [] []))
    (distinct : left.ref ≠ right.ref)
    : Explains work groups streams
        (events ++ [.groupSuccess left [] [], .groupSuccess right [] []]) matching
        failures
      ∧ Explains work groups streams
          (events ++ [.groupSuccess right [] [], .groupSuccess left [] []]) matching
          failures
      ∧ ∀ ref,
          ref
            ∈ completedRefs
                (events ++ [.groupSuccess left [] [], .groupSuccess right [] []])
          ↔ ref
            ∈ completedRefs
                (events ++ [.groupSuccess right [] [], .groupSuccess left [] []]) := by
  have ordered {first second : DeliveryNode}
      (firstAllowed : EventAllowed work ((groups ++ streams).map DeliveryNode.ref) matching
        events failures (.groupSuccess first [] []))
      (secondAllowed : EventAllowed work ((groups ++ streams).map DeliveryNode.ref) matching
        events failures (.groupSuccess second [] []))
      (different : first.ref ≠ second.ref)
      : Explains work groups streams
          (events ++ [.groupSuccess first [] [], .groupSuccess second [] []]) matching
          failures := by
    have next := secondAllowed.groupSuccess_after_other
      (fun _ member => explained.2.1.cut_le member) different
    simpa [List.append_assoc] using (explained.append_event firstAllowed).append_event next
  refine ⟨ordered leftAllowed rightAllowed distinct,
    ordered rightAllowed leftAllowed (Ne.symm distinct), ?_⟩
  intro ref
  simp [completedRefs, List.flatMap_append, eventCompleted, or_assoc, or_comm]

end GraphQL.IncrementalDelivery.WorkQueueSemantics
