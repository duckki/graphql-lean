import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamCompletionInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPublicationReadiness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamOpenness

/-! Successful stream closure accounts for all items under the joint publication matching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Source item coverage becomes publication strictly before successful stream closure
-----------------------------------------------------------------------------------------

/-- A published item references its sole structural stream owner.
Witness: item provenance excludes object events, and unique task descriptors identify the
publication's stream key with the contributing owner. No generated-work premise is needed.
-/
theorem PublicationAt.itemOwner_action {work address ordinal event owners key}
    (source : PublicationAt work (.item address ordinal) event)
    (known : TaskHasOwners work (.item address ordinal) owners) (owner : key ∈ owners)
    : streamAction event = some (key, false) := by
  have item := source.itemAnnotation
  cases event with
  | streamValues stream values groups streams =>
      cases values with
      | nil => cases source
      | cons value rest =>
          cases rest with
          | cons next tail => cases source
          | nil =>
              obtain ⟨actualOwners, producer, task⟩ := source
              obtain ⟨otherProducer, payload, other⟩ := known
              rw [← (task.unique other).1, (itemTask_owner_nodeAt task).1] at owner
              have same := List.mem_singleton.mp owner
              subst key
              rfl
  | groupValues | groupSuccess | groupFailure | streamSuccess | streamFailure
  | workQueueTermination => cases item

/-- Every published contributing item precedes its stream's successful or failed closure.
Witness: exact item provenance fixes its action key; closure ordering forbids a later
publication, while value/control separation excludes publication at the closing position.
The matching is supplied unchanged, not chosen independently for completion accounting.
-/
theorem published_item_before_streamClosure {work : Execution.Work}
    {events : List Execution.WorkQueueEvent} {matching : PublicationMatching}
    (exactValues
      : ∀ index event,
          events[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    {index closing address ordinal owners} {stream : Execution.DeliveryNode}
    (atClosure : events[index]? = some closing)
    (closed : streamAction closing = some (stream.key, true))
    (known : TaskHasOwners work (.item address ordinal) owners)
    (owner : stream.key ∈ owners)
    (published : Published matching events (.item address ordinal))
    : Published matching (events.take index) (.item address ordinal) := by
  obtain ⟨position, event, atEvent, value, same⟩ := published
  have source := exactValues position event atEvent value
  rw [same] at source
  have action := source.itemOwner_action known owner
  have less : position < index := by
    by_cases earlier : position < index
    · exact earlier
    apply False.elim
    have distinct : index ≠ position := by
      intro equal
      subst position
      have sameEvent := Option.some.inj (atClosure.symm.trans atEvent)
      rw [sameEvent, action] at closed
      cases closed
    have before : index < position := by omega
    obtain ⟨leftBound, leftEq⟩ := List.getElem?_eq_some_iff.mp atClosure
    obtain ⟨rightBound, rightEq⟩ := List.getElem?_eq_some_iff.mp atEvent
    have relation := (List.pairwise_filterMap.mp ordered).rel_getElem_of_lt
      leftBound rightBound before
    rw [leftEq, rightEq] at relation
    exact relation (stream.key, true) closed (stream.key, false) action rfl rfl
  exact ⟨position, event, (List.getElem?_take_of_lt less).trans atEvent, value, same⟩

/-- Successful closure retains the strict-prefix item-publication interface.
Witness: specialize the closure-order argument to a successful stream event.
-/
theorem published_item_before_streamSuccess {work : Execution.Work}
    {events : List Execution.WorkQueueEvent} {matching : PublicationMatching}
    (exactValues
      : ∀ index event,
          events[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    {index stream address ordinal owners}
    (atSuccess : events[index]? = some (.streamSuccess stream))
    (known : TaskHasOwners work (.item address ordinal) owners)
    (owner : stream.key ∈ owners)
    (published : Published matching events (.item address ordinal))
    : Published matching (events.take index) (.item address ordinal) :=
  published_item_before_streamClosure exactValues ordered atSuccess rfl known owner
    published

/-- All contributing tasks are already published at an actual successful stream closure.
Witness: source-success readiness covers every structural item; the supplied matching
publishes the exact item inventory, and closure order moves those publications into the
strict prefix. This establishes NodeAccounted for any retained failure-cut list.
-/
theorem createWorkQueue_runNormalized_streamSuccess_accounted {work : Execution.Work}
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
    {index stream}
    (atSuccess
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.streamSuccess stream))
    : ∀ failures,
        NodeAccounted work matching
          ((((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
              publicationAtoms).take
            index) failures stream.key := by
  obtain ⟨⟨dependencies, producer, address, entries, located⟩, inventory⟩ :=
    createWorkQueue_runNormalized_streamSuccess_itemInventory generated valid
      (List.mem_of_getElem? atSuccess)
  intro failures occurrence owners known owner
  obtain ⟨ordinal, same, _⟩ := generated.streamContributor_ordinal located known owner
  subst occurrence
  exact Or.inr (published_item_before_streamSuccess exactValues
    (createWorkQueue_runNormalized_atomicStreamActions_ordered valid) atSuccess known owner
    (covered _ (inventory _ owners known owner)))

-----------------------------------------------------------------------------------------
-- One matching supports producer notices, ordered fresh values, and stream completion
-----------------------------------------------------------------------------------------

/-- Actual successful stream closures account for every item under the existing joint matching.
Witness: retain exact/fresh/ordered publications and producer-supported notices, expose
the annotation's source-item coverage, and derive strict-prefix completion accounting.
Open is independently checked; absence of causal failure remains a separate obligation.
-/
theorem createWorkQueue_runNormalized_streamCompletionMatching {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let queue := State.initialize (Work.fromExecution work)
      let outputs := (queue.runNormalized batches).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ (∀ index event,
            atoms[index]? = some event
            → IsValue event
            → PublicationAt work (matching index) event
              ∧ ¬Published matching (atoms.take index) (matching index)
              ∧ ∀ address first second,
                  matching index = .item address second
                  → first < second
                  → Published matching (atoms.take index) (.item address first))
        ∧ (∀ index event,
            atoms[index]? = some event
            → StreamNoticesSatisfy
                (fun child =>
                  ∃ dependencies occurrence,
                    NodeAt work child .stream dependencies (some occurrence)
                    ∧ Published matching (atoms.take (index + 1)) occurrence) event)
        ∧ (∀ index stream,
            atoms[index]? = some (.streamSuccess stream)
            → Open
                ((queue.initialGroups ++ queue.initialStreams).map
                  Execution.DeliveryNode.key)
                (atoms.take index) stream.key
              ∧ ∀ failures,
                  NodeAccounted work matching (atoms.take index) failures
                    stream.key) := by
  obtain ⟨matching, batching, values, notices, covered⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching_withItemCoverage generated valid started
  refine ⟨matching, batching, values, notices, ?_⟩
  intro index stream atSuccess
  exact ⟨createWorkQueue_runNormalized_streamOpenAt generated valid atSuccess List.mem_cons_self,
    createWorkQueue_runNormalized_streamSuccess_accounted generated valid matching
      (fun index event atEvent value => (values index event atEvent value).1) covered atSuccess⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
