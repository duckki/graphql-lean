import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducedStreamNoticeCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ClosureWitness

/-! The common matching cannot invent an item outside the actual successful source inventory. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Count actual item positions without selecting or changing their occurrence matching
-----------------------------------------------------------------------------------------

/-- Select the supplied matching's label only at a stream-value position.
`entry` pairs an already emitted event with its zero-based output index.
-/
def matchedItemLabel (matching : PublicationMatching)
    (entry : Execution.WorkQueueEvent × Nat)
    : Option Occurrence :=
  match entry.1 with
  | .streamValues .. => some (matching entry.2)
  | _ => none

/-- Item-source labels from actual output positions under an unchanged matching. -/
def matchedItemLabels (matching : PublicationMatching)
    (events : List Execution.WorkQueueEvent)
    : List Occurrence :=
  events.zipIdx.filterMap (matchedItemLabel matching)

/-- Membership in the label list is exactly an indexed stream-value publication.
Witness: filter-map inversion and the index-preserving zip projection.
-/
theorem matchedItemLabels_mem_iff {matching events occurrence}
    : occurrence ∈ matchedItemLabels matching events
      ↔ ∃ index stream values groups children,
          events[index]? = some (.streamValues stream values groups children)
          ∧ matching index = occurrence := by
  constructor
  · intro member
    obtain ⟨⟨event, index⟩, included, same⟩ := List.mem_filterMap.mp member
    have selected := List.mk_mem_zipIdx_iff_getElem?.mp included
    cases event with
    | streamValues stream values groups children =>
        exact ⟨index, stream, values, groups, children, selected, Option.some.inj same⟩
    | groupValues | groupSuccess | groupFailure | streamSuccess | streamFailure
      | workQueueTermination => cases same
  · rintro ⟨index, stream, values, groups, children, selected, same⟩
    exact List.mem_filterMap.mpr ⟨(_, index), List.mk_mem_zipIdx_iff_getElem?.mpr selected,
      congrArg some same⟩

/-- For atomic output, the label count is exactly the emitted item count.
Witness: each stream atom contributes one label and one item; other constructors add neither.
-/
theorem matchedItemLabels_length {matching events}
    (atomic : ∀ event ∈ events, AtomicValues event)
    : (matchedItemLabels matching events).length
      = (events.flatMap normalizedItemValues).length := by
  have loop (entries : List Execution.WorkQueueEvent) (start : Nat)
      (shape : ∀ event ∈ entries, AtomicValues event)
      : ((entries.zipIdx start).filterMap (matchedItemLabel matching)).length
        = (entries.flatMap normalizedItemValues).length := by
    induction entries generalizing start with
    | nil => rfl
    | cons event rest ih =>
        have tail := ih (start + 1) (fun next member => shape next (List.mem_cons_of_mem _ member))
        have head := shape event List.mem_cons_self
        cases event with
        | streamValues stream values groups children =>
            change values.length = 1 at head
            simp only [List.zipIdx_cons, List.filterMap_cons, matchedItemLabel,
              List.flatMap_cons, normalizedItemValues, List.length_append, List.length_map,
              head, List.length_cons, tail, Nat.add_comm]
        | groupValues | groupSuccess | groupFailure | streamSuccess | streamFailure
          | workQueueTermination =>
            simpa only [List.zipIdx_cons, List.filterMap_cons, matchedItemLabel,
              List.flatMap_cons, normalizedItemValues, List.nil_append] using tail
  exact loop events 0 atomic

/-- A published structural item contributes its occurrence to the stream-position labels.
Witness: exact publication provenance rules out an object event for an item occurrence.
-/
theorem published_item_mem_matchedLabels {work matching events address index}
    (exactValues
      : ∀ position event,
          events[position]? = some event
          → IsValue event
          → PublicationAt work (matching position) event)
    (published : Published matching events (.item address index))
    : Occurrence.item address index ∈ matchedItemLabels matching events := by
  obtain ⟨position, event, selected, value, same⟩ := published
  have item := (same ▸ exactValues position event selected value).itemAnnotation
  cases event <;> try cases item
  case streamValues stream values groups children =>
    exact matchedItemLabels_mem_iff.mpr ⟨position, stream, values, groups, children,
      selected, same⟩

/-- Equal-sized output cannot contain an extra label after covering a distinct source list.
Witness: adding any alleged extra label produces a longer duplicate-free subset of output.
Output labels need not themselves be assumed duplicate-free.
-/
private theorem reverse_subset_of_count {α : Type} {source output : List α}
    (unique : source.Nodup) (covered : source.Subset output)
    (size : source.length = output.length)
    : output.Subset source := by
  intro label present
  apply Classical.byContradiction
  intro absent
  have distinct : (label :: source).Nodup := List.nodup_cons.mpr ⟨absent, unique⟩
  have included : (label :: source).Subset output := by
    intro next member
    rcases List.mem_cons.mp member with rfl | old
    · exact present
    · exact covered old
  have bound := distinct.length_le_of_subset included
  simp only [List.length_cons] at bound
  omega

/-- Every source item-publication label is one of that source history's successful identities.
Witness: stream-item events have identical occurrence projections; other constructors
contribute no item labels. No validity or output premise is needed.
-/
theorem GraphEvent.itemPublications_successes (events : List GraphEvent)
    : ((events.flatMap GraphEvent.itemPublications).map Prod.fst).Subset
        (events.flatMap GraphEvent.successes) := by
  have single : ∀ event : GraphEvent,
      (event.itemPublications.map Prod.fst).Subset event.successes := by
    intro event
    cases event <;> simp [GraphEvent.itemPublications, GraphEvent.successes, List.map_map,
      Function.comp_def, List.Subset]
  intro occurrence member
  rw [List.map_flatMap] at member
  obtain ⟨event, received, included⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨event, received, single event included⟩

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Exact input/output item counts close the converse direction of the prefix ledger
-----------------------------------------------------------------------------------------

/-- Admitted value atoms retain their exact successful payload and matched occurrence.
Witness: invert the corresponding value rule and identify the strict prefix's length.
-/
theorem PublicationAdmission.publicationAt {work w}
    (admitted : PublicationAdmission work w) {index event}
    (selected : w.events[index]? = some event) (value : IsValue event)
    : PublicationAt work (w.matching index) event := by
  have allowed := admitted index event selected value
  have size : (w.events.take index).length = index := by
    simp only [List.length_take, Nat.min_eq_left
      (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)]
  cases event <;> try cases value
  case groupValues node values =>
    obtain ⟨owners, producer, ⟨path, data, errors, deliveryGroups⟩, rfl, known, _⟩ := allowed
    exact ⟨owners, producer, size ▸ known⟩
  case streamValues node values groups children =>
    obtain ⟨owners, producer, ⟨item, errors⟩, rfl, known, _⟩ := allowed
    exact ⟨owners, producer, size ▸ known⟩

/-- Publication admission makes every output value atomic, independently of controls.
Witness: both value rules require a singleton payload; control constructors are already atomic.
-/
theorem PublicationAdmission.atomic {work w} (admitted : PublicationAdmission work w)
    : ∀ event ∈ w.events, AtomicValues event := by
  intro event member
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  cases event <;> try trivial
  case groupValues node values | streamValues node values groups children =>
    have source := admitted.publicationAt selected trivial
    cases values with
    | nil => cases source
    | cons value rest =>
        cases rest with
        | nil => rfl
        | cons next more => cases source

/-- Canonical output retains the exact source item-value sequence, not just its size.
Witness: accepted raw replay copies source items, and normalization/atomization preserves
that projection. Removing termination cannot remove an item.
-/
theorem Witness.itemValues_eq_source {work inputs} {w : Witness}
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    : w.events.flatMap normalizedItemValues
      = (inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.snd := by
  have accepted : (initialQueue work).batchesStarted inputs = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  rw [history, createWorkQueue_nonterminalAtoms_flattened inputs started,
    publicationAtoms_list_itemValues, IncrementalPublisher.normalizeBatch_itemValues]
  exact (initialQueue work).rawEventReplay_itemValues inputs.flatten
    ((initialQueue work).batchesStarted_acceptsBatch inputs accepted)

/-- The common matching's published items all belong to the actual source item inventory.
Witness: the closure ledger already publishes every source label; distinct source labels
fill exactly all emitted item positions. An extra matched label would exceed that count.
This reflection uses no response payload equality to identify a source occurrence.
-/
theorem published_item_source {work inputs w address index}
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger : BufferedClosureLedger work inputs w)
    (published : Published w.matching w.events (.item address index))
    : Occurrence.item address index
      ∈ (inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.fst := by
  let source := (inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.fst
  have count : (w.events.flatMap normalizedItemValues).length = source.length := by
    rw [Witness.itemValues_eq_source started history]
    simp only [source, List.length_map]
  have unique : source.Nodup := (GraphEvent.itemPublications_sublist _).nodup
    valid.identities_nodup.1
  obtain ⟨_, _, _, _, prefixes⟩ := ledger
  have covered : source.Subset (matchedItemLabels w.matching w.events) := by
    intro occurrence member
    have delivered : Published w.matching w.events occurrence := by
      have present : occurrence ∈ source.take
          (((w.events.take w.events.length).flatMap normalizedItemValues).length) := by
        rw [List.take_length, count, List.take_length]
        exact member
      simpa only [List.take_length] using prefixes w.events.length occurrence present
    obtain ⟨publication, included, identity⟩ := List.mem_map.mp member
    obtain ⟨event, received, inEvent⟩ := List.mem_flatMap.mp included
    have known := (valid.eachMatches received).itemPublications inEvent
    have isItem : ∃ address index, occurrence = .item address index := by
      obtain ⟨owners, producer, descriptor⟩ := known
      cases same : publication.1 with
      | item address index => exact ⟨address, index, identity.symm.trans same⟩
      | executionGroup address =>
          rw [same] at descriptor
          cases StructuralEquivalence.taskAt_of_current descriptor
    obtain ⟨address, index, rfl⟩ := isItem
    exact published_item_mem_matchedLabels
      (fun _ _ atEvent value => admitted.publicationAt atEvent value) delivered
  apply reverse_subset_of_count unique covered
    ((matchedItemLabels_length admitted.atomic).trans count).symm
  exact published_item_mem_matchedLabels
    (fun _ _ atEvent value => admitted.publicationAt atEvent value) published

/-- A published item in the common witness was received as an actual successful source item.
Witness: reflect the canonical label into the exact input item inventory, then project
that inventory to successful source identities. Equal item values do not affect the result.
-/
theorem published_item_success {work inputs w address index}
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger : BufferedClosureLedger work inputs w)
    (published : Published w.matching w.events (.item address index))
    : Occurrence.item address index ∈ inputs.flatten.flatMap GraphEvent.successes :=
  GraphEvent.itemPublications_successes inputs.flatten
    (published_item_source valid started history admitted ledger published)

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
