import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.PublicationExtension

/-! Conservative local independence, without identifying ordered wire observations. -/

namespace GraphQL.IncrementalDelivery.WorkScheduler
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
    (distinct : other ≠ occurrence) (event : WorkEvent)
    : CanPublish work (matchNext matching events.length other) (events ++ [event])
        failed occurrence producer := by
  have same := published_matching_eq
    (fun _ earlier => matchNext_before matching other earlier) (events := events)
  have persists {task} (published : Published matching events task)
      : Published (matchNext matching events.length other) (events ++ [event]) task :=
    (same ▸ published).append [event]
  refine ⟨?_, ready.2.1, fun parent equal => persists (ready.2.2.1 parent equal), ?_⟩
  · intro published
    rcases published_append_singleton_iff.mp published with old | current
    · exact ready.1 (same.symm ▸ old)
    · exact distinct (by simpa [matchNext] using current.2)
  · cases occurrence with
    | deferred => trivial
    | item address index =>
        cases index with
        | zero => trivial
        | succ index => exact persists ready.2.2.2

/-- Object publications change neither notices nor closures, hence no owner choice.
Witness: the pending/completed projections of a group-value event are both empty.
-/
theorem owner_after_object {work initial events failed owners node carrier values}
    : Owner work initial (events ++ [.groupValues carrier values]) failed owners node
      ↔ Owner work initial events failed owners node := by
  simp [Owner, AvailableOwner, Open, announcedKeys, pendingKeys, completedKeys,
    List.flatMap_append, eventPending, eventCompleted]

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
    (firstReady
      : CanPublish work matching events (failedBefore failures events.length)
          first firstProducer)
    (secondReady
      : CanPublish work matching events (failedBefore failures events.length)
          second secondProducer)
    (firstSelected
      : Owner work ((groups ++ streams).map DeliveryNode.key) events
          (failedBefore failures events.length) firstOwners firstOwner)
    (secondSelected
      : Owner work ((groups ++ streams).map DeliveryNode.key) events
          (failedBefore failures events.length) secondOwners secondOwner)
    (distinct : first ≠ second)
    : ∃ next,
        Explains work groups streams
          (events
            ++ [
              .groupValues firstOwner [⟨firstPath, firstData, firstErrors⟩],
              .groupValues secondOwner [⟨secondPath, secondData, secondErrors⟩]
            ]) next failures
        ∧ ∀ occurrence,
            Published next
              (events
                ++ [
                  .groupValues firstOwner [⟨firstPath, firstData, firstErrors⟩],
                  .groupValues secondOwner [⟨secondPath, secondData, secondErrors⟩]
                ]) occurrence
            ↔ Published matching events occurrence
              ∨ first = occurrence
              ∨ second = occurrence := by
  let firstEvent := WorkEvent.groupValues firstOwner
    [{path := firstPath, data := firstData, errors := firstErrors}]
  let secondEvent := WorkEvent.groupValues secondOwner
    [{path := secondPath, data := secondData, errors := secondErrors}]
  have step := explained.publish_object firstKnown firstReady firstSelected
  have failed : failedBefore failures (events ++ [firstEvent]).length
      = failedBefore failures events.length := by
    rw [explained.2.1.failedBefore_eq (by simp),
      explained.2.1.failedBefore_eq (Nat.le_refl _)]
  have ready := secondReady.after_other_value distinct firstEvent
  have selected := (owner_after_object
    (carrier := firstOwner) (values := [⟨firstPath, firstData, firstErrors⟩])).mpr secondSelected
  rw [← failed] at ready selected
  have both := step.publish_object secondKnown ready selected
  refine ⟨
    matchNext (matchNext matching events.length first)
      (events ++ [firstEvent]).length second,
    by simpa [List.append_assoc, firstEvent, secondEvent] using both,
    ?_
  ⟩
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
    (firstReady
      : CanPublish work matching events (failedBefore failures events.length)
          first firstProducer)
    (secondReady
      : CanPublish work matching events (failedBefore failures events.length)
          second secondProducer)
    (firstSelected
      : Owner work ((groups ++ streams).map DeliveryNode.key) events
          (failedBefore failures events.length) firstOwners firstOwner)
    (secondSelected
      : Owner work ((groups ++ streams).map DeliveryNode.key) events
          (failedBefore failures events.length) secondOwners secondOwner)
    (distinct : first ≠ second)
    : let left := WorkEvent.groupValues firstOwner [⟨firstPath, firstData, firstErrors⟩]
      let right :=
        WorkEvent.groupValues secondOwner [⟨secondPath, secondData, secondErrors⟩]
      ∃ forward backward,
        Explains work groups streams (events ++ [left, right]) forward failures
        ∧ Explains work groups streams (events ++ [right, left]) backward failures
        ∧ ∀ occurrence,
            Accounted work forward (events ++ [left, right])
              (failedBefore failures events.length) occurrence
            ↔ Accounted work backward (events ++ [right, left])
                (failedBefore failures events.length) occurrence := by
  obtain ⟨forward, forwardExplained, forwardPublications⟩ :=
    explained.publish_two_objects firstKnown secondKnown firstReady secondReady
      firstSelected secondSelected distinct
  obtain ⟨backward, backwardExplained, backwardPublications⟩ :=
    explained.publish_two_objects secondKnown firstKnown secondReady firstReady
      secondSelected firstSelected (Ne.symm distinct)
  refine ⟨forward, backward, forwardExplained, backwardExplained, ?_⟩
  intro occurrence
  simp only [Accounted, forwardPublications, backwardPublications, or_comm, or_assoc]

-----------------------------------------------------------------------------------------
-- Notice-free healthy group closures preserve each other's enabledness
-----------------------------------------------------------------------------------------

/-- Closing a different key without notices preserves a permitted healthy group closure.
Witness: its open key remains open, and all node-accounting facts persist on extension.
-/
theorem EventAllowed.groupSuccess_after_other
    {work initial matching events failed node other}
    (allowed
      : EventAllowed work initial matching events failed (.groupSuccess node [] []))
    (distinct : other.key ≠ node.key)
    : EventAllowed work initial matching (events ++ [.groupSuccess other [] []]) failed
        (.groupSuccess node [] []) := by
  refine ⟨allowed.1, ?_, allowed.2.2.1, ?_, by simp [Announcements]⟩
  · simpa [Open, announcedKeys, pendingKeys, completedKeys, List.flatMap_append,
      eventPending, eventCompleted, Ne.symm distinct] using allowed.2.1
  · exact allowed.2.2.2.1.append [.groupSuccess other [] []]

/-- Distinct notice-free healthy group closures can be appended in either order.
Witness: neither closure disables the other; fixed failure evidence extends unchanged.
Completed-key membership agrees, but the ordered completion lists need not agree.
-/
theorem Explains.group_closures_commute
    {work groups streams events matching failures left right}
    (explained : Explains work groups streams events matching failures)
    (leftAllowed
      : EventAllowed work ((groups ++ streams).map DeliveryNode.key) matching
          events (failedBefore failures events.length) (.groupSuccess left [] []))
    (rightAllowed
      : EventAllowed work ((groups ++ streams).map DeliveryNode.key) matching
          events (failedBefore failures events.length) (.groupSuccess right [] []))
    (distinct : left.key ≠ right.key)
    : Explains work groups streams
        (events ++ [.groupSuccess left [] [], .groupSuccess right [] []]) matching
        failures
      ∧ Explains work groups streams
          (events ++ [.groupSuccess right [] [], .groupSuccess left [] []]) matching
          failures
      ∧ ∀ key,
          key
            ∈ completedKeys
                (events ++ [.groupSuccess left [] [], .groupSuccess right [] []])
          ↔ key
            ∈ completedKeys
                (events ++ [.groupSuccess right [] [], .groupSuccess left [] []]) := by
  have ordered {first second : DeliveryNode}
      (firstAllowed : EventAllowed work ((groups ++ streams).map DeliveryNode.key) matching
        events (failedBefore failures events.length) (.groupSuccess first [] []))
      (secondAllowed : EventAllowed work ((groups ++ streams).map DeliveryNode.key) matching
        events (failedBefore failures events.length) (.groupSuccess second [] []))
      (different : first.key ≠ second.key)
      : Explains work groups streams
          (events ++ [.groupSuccess first [] [], .groupSuccess second [] []]) matching failures := by
    have next := secondAllowed.groupSuccess_after_other different
    have failed : failedBefore failures (events ++ [WorkEvent.groupSuccess first [] []]).length
        = failedBefore failures events.length := by
      rw [explained.2.1.failedBefore_eq (by simp),
        explained.2.1.failedBefore_eq (Nat.le_refl _)]
    rw [← failed] at next
    simpa [List.append_assoc] using (explained.append_event firstAllowed).append_event next
  refine ⟨ordered leftAllowed rightAllowed distinct,
    ordered rightAllowed leftAllowed (Ne.symm distinct), ?_⟩
  intro key
  simp [completedKeys, List.flatMap_append, eventCompleted, or_assoc, or_comm]

end GraphQL.IncrementalDelivery.WorkScheduler
