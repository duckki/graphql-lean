import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationSupport

/-! Available raw contributors belong to the exact task selected by the shared matching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Structural owner keys agree with the source's retained contributor descriptors
-----------------------------------------------------------------------------------------

/-- A structural task's owner keys are exactly its retained contributor descriptors' keys.
Witness: both projections read the same located execution group; items have no task-group
descriptor list. No response payload comparison or generated-key assumption is needed.
-/
theorem taskAt_owners_of_taskGroups {work occurrence owners producer payload groups}
    (known : TaskAt work occurrence owners producer payload)
    (exactGroups : taskGroups? work occurrence = some groups)
    : owners = groups.map Execution.DeliveryNode.key := by
  cases occurrence with
  | item address ordinal => simp [taskGroups?] at exactGroups
  | executionGroup address =>
      obtain ⟨fragments, path, outcome, children, enclosing, located, ownerEq, _⟩ := known
      change locateWork work address
        = some ⟨.executionGroup fragments path outcome children, producer, enclosing⟩ at located
      have nodes : fragments.map Execution.DeferredFragment.node = groups := by
        simpa [taskGroups?, located] using exactGroups
      rw [← nodes]
      simpa only [List.map_map, Function.comp_def] using ownerEq

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- The same full raw value, ledger entry, and output matching identify one task
-----------------------------------------------------------------------------------------

/-- A recovered raw value has the canonical matching's exact structural task and owners.
Witness: preserved object rank selects the same full raw value and source occurrence from
the strengthened closure ledger. Distinct tasks with equal wire data cannot be confused.
-/
theorem Witness.groupPublication_taskAt {work inputs w index owner payload}
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.groupValues owner payload))
    (origin
      : GroupPublicationOrigin
          {
            active :=
              (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
          }
          ((initialQueue work).rawEventReplay inputs.flatten).2 index owner payload)
    : ∃ producer,
        TaskAt work (w.matching index)
          (origin.value.deliveryGroups.map Execution.DeliveryNode.key) producer
          (.object origin.value.path (.ok (origin.value.data, origin.value.errors))) := by
  obtain ⟨_, _, exactLedger, _⟩ := ledger
  have raw := origin.rawValue_atRank
  dsimp only at raw
  have historyEq := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  rw [← historyEq] at raw
  obtain ⟨result, _, same, source⟩ := exactLedger.source_at selected raw
  obtain ⟨owners, producer, known, groups, _⟩ := source
  have keys := taskAt_owners_of_taskGroups known groups
  rw [same] at keys known
  exact ⟨producer, keys ▸ known⟩

/-- Every actual object publication has an available owner of its exact matched task.
Witness: combine raw contributor availability with indexed source-ledger agreement,
retaining the same origin, history, matching, and failure cuts in both arguments.
-/
theorem GroupPublicationReleases.matched_available {work inputs w}
    (releases : GroupPublicationReleases work inputs w)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w) {index owner payload}
    (selected : w.events[index]? = some (.groupValues owner payload))
    : ∃ origin
          : GroupPublicationOrigin
              {
                active :=
                  (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
              }
              ((initialQueue work).rawEventReplay inputs.flatten).2 index owner payload,
        (∃ producer,
          TaskAt work (w.matching index)
            (origin.value.deliveryGroups.map Execution.DeliveryNode.key) producer
            (.object origin.value.path (.ok (origin.value.data, origin.value.errors))))
        ∧ HealthyOpenOwner work (initialKeys work) w.matching (w.events.take index)
            w.failures (origin.value.deliveryGroups.map Execution.DeliveryNode.key)
            origin.group := by
  obtain ⟨origin, available⟩ := releases.available valid selected
  exact ⟨origin, Witness.groupPublication_taskAt started history ledger selected origin,
    available⟩

/-- The exact matched object task succeeds and has a healthy contributing key.
Witness: indexed full-value agreement and available raw release support. The remaining
`PublicationSupport` clause is earlier publication of the structural producer.
-/
theorem GroupPublicationReleases.matching_healthy {work inputs w}
    (releases : GroupPublicationReleases work inputs w)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w) {index owner values}
    (selected : w.events[index]? = some (.groupValues owner values))
    : ∃ owners producer payload key,
        TaskAt work (w.matching index) owners producer payload
        ∧ payload.failure = none
        ∧ key ∈ owners
        ∧ ¬NodeFailed work w.matching (w.events.take index) w.failures key := by
  obtain ⟨origin, ⟨producer, known⟩, available⟩ :=
    releases.matched_available valid started history ledger selected
  exact ⟨_, producer, _, origin.group.key, known, rfl, available.1.2.1, available.2⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
