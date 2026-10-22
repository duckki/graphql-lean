import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemPublicationReflection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupItemPublications
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationHistory

/-! Published startup item identities are exact actual successful source occurrences. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

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

/-- Actual startup atoms retain the complete successful source-item value sequence.
Neither diagnostic forwarding nor removing termination changes the item projection.
-/
theorem Witness.startup_itemValues_eq_source {work inputs} {w : Witness}
    (startup : InitialStartup) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    : w.events.flatMap normalizedItemValues
      = (inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.snd := by
  let initial := State.initialize (Work.fromExecution work) startup
  have full : ((initial.runNormalized inputs).2.flatten.flatMap
    publicationAtoms).flatMap normalizedItemValues
      = (inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.snd := by
    rw [publicationAtoms_list_itemValues]
    exact initial.runNormalized_itemValues inputs valid
      (by rwa [← inputsStartedWithStartup_eq_batchesStarted])
  have shape := initial.runNormalized_terminalShape inputs
    (State.initializeWithStartup_terminated _ startup)
  dsimp only at history
  rw [← history] at shape
  rw [shape] at full
  split at full <;> simpa only [List.flatMap_append, List.flatMap_cons, normalizedItemValues,
    List.flatMap_nil, List.append_nil] using full

/-- The common matching's published items all belong to the actual source item inventory.
Witness: the closure ledger already publishes every source label; distinct source labels
fill exactly all emitted item positions. An extra matched label would exceed that count.
This reflection uses no response payload equality to identify a source occurrence.
-/
theorem startup_published_item_source {work inputs w address index}
    (startup : InitialStartup) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (published : Published w.matching w.events (.item address index))
    : Occurrence.item address index
      ∈ (inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.fst := by
  let source := (inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.fst
  have count : (w.events.flatMap normalizedItemValues).length = source.length := by
    rw [Witness.startup_itemValues_eq_source startup valid started history]
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
theorem startup_published_item_success {work inputs w address index}
    (startup : InitialStartup) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (published : Published w.matching w.events (.item address index))
    : Occurrence.item address index ∈ inputs.flatten.flatMap GraphEvent.successes :=
  GraphEvent.itemPublications_successes inputs.flatten
    (startup_published_item_source startup valid started history admitted ledger
      published)

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
