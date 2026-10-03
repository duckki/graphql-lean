import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamCompletionAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceReachability

/-! Actual stream failures identify a reachable unpublished item after its published prefix. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A source stream failure identifies the exact next finite item, not an arbitrary error
-----------------------------------------------------------------------------------------

/-- A source stream failure identifies a reachable failed item after all received ordinals.
Witness: readiness selects the next fixed failed outcome and its successful producer chain;
the source cursor range covers every lower ordinal with that stream's sole ownership.
This supplies no cancellation or output-admission premise.
-/
theorem ValidGraphEvents.streamFailure_itemInventory {work events}
    (valid : ValidGraphEvents work events) (generated : ExecutedWork work)
    {stream errors} (completed : GraphEvent.streamFailure stream errors ∈ events)
    : ∃ address ordinal producer,
        TaskAt work (.item address ordinal) [stream.ref] producer
          (.item stream (.error errors))
        ∧ Reachable work (.item address ordinal)
        ∧ ∀ earlier,
            earlier < ordinal
            → TaskHasOwners work (.item address earlier) [stream.ref]
              ∧ .item address earlier
                ∈ (events.flatMap GraphEvent.itemPublications).map Prod.fst := by
  obtain ⟨before, after, same, validBefore, ready⟩ := valid.event_ready_context completed
  obtain ⟨address, entries, producer, dependencies, located, supported, children, atItem⟩ := ready
  have task := TaskAt.item located atItem
  refine ⟨
    address,
    (GraphEvent.itemsBefore before stream.ref).length,
    producer,
    task,
    task_reachable_of_source_support validBefore
      (validBefore.successes_reachable generated) task supported,
    ?_
  ⟩
  intro earlier less
  have bound : earlier < entries.length :=
    Nat.lt_trans less (List.getElem?_eq_some_iff.mp atItem).choose
  have entry : entries[earlier]? = some entries[earlier] :=
    List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩
  refine ⟨⟨producer, _, TaskAt.item located entry⟩, ?_⟩
  have received : .item address earlier ∈
      (GraphEvent.itemsBefore before stream.ref).map StreamItem.occurrence := by
    rw [validBefore.itemsBefore_order generated located]
    exact List.mem_map.mpr ⟨earlier, List.mem_range.mpr less, rfl⟩
  have inventory := (GraphEvent.itemsBefore_occurrences_sublist before stream.ref).subset received
  rw [same, List.flatMap_append, List.map_append]
  exact List.mem_append_left _ inventory

-----------------------------------------------------------------------------------------
-- Exact successful payload provenance excludes any publication of a failed occurrence
-----------------------------------------------------------------------------------------

/-- An exact publication descriptor always denotes a successful task outcome.
Witness: the singleton object/item payload constructors both contain Result.ok.
-/
theorem PublicationAt.succeeds {work occurrence event}
    (source : PublicationAt work occurrence event)
    : TaskSucceeds work occurrence := by
  cases event with
  | groupValues node values | streamValues node values _ _ =>
      cases values with
      | nil => cases source
      | cons value rest =>
          cases rest with
          | cons next tail => cases source
          | nil =>
              obtain ⟨owners, producer, known⟩ := source
              exact ⟨owners, producer, _, known, rfl⟩
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases source

/-- No failed fixed-outcome task is published under an exact output matching.
Witness: a supposed publication has a successful payload, contradicting uniqueness of
the structural descriptor. This needs neither a failure witness nor explained history.
-/
theorem failedTask_unpublished_of_exactValues {work : Execution.Work}
    {events : List Execution.WorkQueueEvent} {matching : PublicationMatching}
    (exactValues
      : ∀ index event,
          events[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    (failed : payload.failure.isSome = true)
    : ¬Published matching events occurrence := by
  rintro ⟨index, event, atEvent, value, same⟩
  have source := (exactValues index event atEvent value).succeeds
  rw [same] at source
  obtain ⟨otherOwners, otherProducer, other, task, success⟩ := source
  rw [(known.unique task).2.2, success] at failed
  cases failed

-----------------------------------------------------------------------------------------
-- The actual failure notice has an open owner and a completely published earlier prefix
-----------------------------------------------------------------------------------------

/-- An actual failed stream closure identifies its exact reachable, unpublished failing item.
Witness: recover the source failure and error count; readiness supplies its item cursor.
The common matching publishes every lower ordinal before the closing atom, and exact
successful payloads rule out publication of the failing occurrence anywhere in the output.
Open is derived independently. Failure-cut licensing still needs absence of cancellation.
-/
theorem createWorkQueue_runNormalized_streamFailure_accounting {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten) (matching : PublicationMatching)
    (exactValues
      : let atoms :=
          ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
        ∀ index event,
          atoms[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    (covered
      : ∀ occurrence ∈ (batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst,
          Published matching
            (((State.initialize (Work.fromExecution work)).runNormalized
                batches).2.flatten.flatMap
              publicationAtoms) occurrence)
    {index stream errors}
    (atFailure
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.streamFailure stream errors))
    : let queue := State.initialize (Work.fromExecution work)
      let atoms := (queue.runNormalized batches).2.flatten.flatMap publicationAtoms
      ∃ address ordinal producer,
        TaskAt work (.item address ordinal) [stream.ref] producer
          (.item stream (.error errors))
        ∧ Reachable work (.item address ordinal)
        ∧ Open
            ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
            (atoms.take index) stream.ref
        ∧ ¬Published matching atoms (.item address ordinal)
        ∧ ∀ earlier,
            earlier < ordinal
            → Published matching (atoms.take index) (.item address earlier) := by
  have completed := createWorkQueue_runNormalized_streamCompletion_source
    (Work.fromExecution work) batches (List.mem_of_getElem? atFailure) rfl
  obtain ⟨address, ordinal, producer, task, reachable, inventory⟩ :=
    valid.streamFailure_itemInventory generated completed
  refine ⟨address, ordinal, producer, task, reachable,
    createWorkQueue_runNormalized_streamOpenAt generated valid atFailure List.mem_cons_self,
    failedTask_unpublished_of_exactValues exactValues task rfl, ?_⟩
  intro earlier less
  obtain ⟨known, received⟩ := inventory earlier less
  exact published_item_before_streamClosure exactValues
    (createWorkQueue_runNormalized_atomicStreamActions_ordered valid) atFailure rfl known
    List.mem_cons_self (covered _ received)

/-- One actual-output matching supports both successful and failed stream completion accounting.
Witness: retain the joint producer/value matching and its full item inventory, then derive
each failure's exact reachable item, open owner, and already-published lower ordinals.
This is evidence for constructing failure cuts, not a FailureWitness or full admission.
-/
theorem createWorkQueue_runNormalized_streamFailureMatching {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let queue := State.initialize (Work.fromExecution work)
      let atoms := (queue.runNormalized batches).2.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        (∀ index event,
          atoms[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event
            ∧ ¬Published matching (atoms.take index) (matching index))
        ∧ (∀ index stream,
            atoms[index]? = some (.streamSuccess stream)
            → ∀ failures,
                NodeAccounted work matching (atoms.take index) failures stream.ref)
        ∧ (∀ index stream errors,
            atoms[index]? = some (.streamFailure stream errors)
            → ∃ address ordinal producer,
                TaskAt work (.item address ordinal) [stream.ref] producer
                  (.item stream (.error errors))
                ∧ Reachable work (.item address ordinal)
                ∧ Open
                    ((queue.initialGroups ++ queue.initialStreams).map
                      Execution.DeliveryNode.ref)
                    (atoms.take index) stream.ref
                ∧ ¬Published matching atoms (.item address ordinal)
                ∧ ∀ earlier,
                    earlier < ordinal
                    → Published matching (atoms.take index) (.item address earlier)) := by
  obtain ⟨matching, _, values, _, covered⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching_withItemCoverage generated valid started
  have exactValues := fun index event atEvent value => (values index event atEvent value).1
  refine ⟨matching, fun index event atEvent value =>
    ⟨(values index event atEvent value).1, (values index event atEvent value).2.1⟩, ?_, ?_⟩
  · intro index stream atSuccess
    exact createWorkQueue_runNormalized_streamSuccess_accounted generated valid matching
      exactValues covered atSuccess
  · intro index stream errors atFailure
    exact createWorkQueue_runNormalized_streamFailure_accounting generated valid matching
      exactValues covered atFailure

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
